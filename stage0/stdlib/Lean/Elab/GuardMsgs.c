// Lean compiler output
// Module: Lean.Elab.GuardMsgs
// Imports: Lean.Elab.Notation Lean.Util.Diff Lean.Server.CodeActions.Attr
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
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5(lean_object*, lean_object*);
lean_object* l_Lean_FileMap_utf8RangeToLspRange(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Diff_Histogram_addLeft___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__9_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_takeWhileAux___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_findSomeMAux___at___Lean_PersistentArray_findSomeM_x3f___at___Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Diff_Histogram_addLeft___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__9_spec__10___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__20___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__28(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__29___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__18___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Language_SnapshotTask_get___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_matchPrefix_go___at___Lean_Diff_matchPrefix___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__5_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Diff_Histogram_addLeft___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__9_spec__9___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_toString(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Diff_Histogram_addLeft___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__9_spec__11_spec__11(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_findSomeMAux___at___Lean_PersistentArray_findSomeM_x3f___at___Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Option_register___at___Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_6__spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_SpecResult_toCtorIdx___boxed(lean_object*);
lean_object* l_Lean_Elab_Command_elabCommandTopLevel(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Diff_Histogram_addLeft___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__9_spec__14(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1(lean_object*);
lean_object* l_Array_reverse(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Array_qsort_sort___at___Lean_Parser_Error_toString_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_matchSuffix___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_SpecResult_noConfusion___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__34___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at___Lean_PersistentArray_findSomeM_x3f___at___Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at___Lean_PersistentArray_findSomeM_x3f___at___Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0___boxed(lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__17___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Lsp_WorkspaceEdit_ofTextEdit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Diff_Histogram_addLeft___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__9_spec__9___redArg___boxed(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__25_spec__25___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_takeRightWhileAux___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__34_spec__34___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__30___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_String_split___at___Lean_stringToMessageData_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_removeTrailingWhitespaceMarker___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Diff_Histogram_addLeft___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__9_spec__10___boxed(lean_object*, lean_object*, lean_object*);
uint64_t lean_string_hash(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_splitAux___at___String_split___at___Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_toCtorIdx(uint8_t);
lean_object* l_List_head_x21(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__16___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Language_SnapshotTree_getAll(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_toCtorIdx___boxed(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT lean_object* l_Substring_takeRightWhileAux___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Diff_Histogram_addLeft___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__9_spec__14___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__19(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_noConfusion___redArg(uint8_t, uint8_t);
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__27___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_takeWhileAux___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__20(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_commandElabAttribute;
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
lean_object* l_Lean_MessageLog_toList(lean_object*);
lean_object* l_Lean_Elab_Command_getRef(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_noConfusion(lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Diff_Histogram_addLeft___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__9_spec__11_spec__11_spec__11(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_split___at___Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__30(size_t, size_t, lean_object*);
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply(uint8_t, lean_object*);
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___at___Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0___boxed(lean_object*);
lean_object* l_Array_ofSubarray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__34(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_get___redArg(lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_matchSuffix_go___at___Lean_Diff_matchSuffix___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__7_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_findSomeMAux___at___Lean_PersistentArray_findSomeM_x3f___at___Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_findSomeMAux___at___Lean_PersistentArray_findSomeM_x3f___at___Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0_spec__1(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Diff_Action_linePrefix(uint8_t);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_findSomeMAux___at___Lean_PersistentArray_findSomeM_x3f___at___Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0_spec__1_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_MessageLog_empty;
lean_object* lean_string_utf8_prev(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_noConfusion___redArg(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Diff_linesToString___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__32___boxed(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0_spec__0___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__16___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_removeTrailingWhitespaceMarker(lean_object*);
lean_object* lean_usize_to_nat(size_t);
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToStringWithoutPos(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Diff_linesToString___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__32_spec__32___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_setArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_String_anyAux___at___Lean_Parser_checkTailLinebreak_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__18___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0(lean_object*, size_t, size_t, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_SpecResult_noConfusion___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_take(lean_object*, lean_object*, lean_object*);
lean_object* l_String_replace(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_splitAux___at___String_split___at___Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___at___Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_noConfusion___redArg___boxed(lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Diff_Histogram_addLeft___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__9_spec__10___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_getDocStringText___at___Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_noConfusion___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__28___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__25_spec__25(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_SpecResult_noConfusion___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__25(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Diff_Histogram_addLeft___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__9_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_SpecResult_noConfusion___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_declare__1____x40_Lean_Elab_GuardMsgs___hyg_3378_(lean_object*);
uint8_t l_String_isPrefixOf(lean_object*, lean_object*);
uint8_t l_Lean_KVMap_getBool(lean_object*, lean_object*, uint8_t);
lean_object* l_Array_append(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__24(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_RequestM_readDoc___at___Lean_Server_RequestM_withWaitFindSnapAtPos_spec__0(lean_object*, lean_object*);
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__19___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_matchSuffix___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__7___boxed(lean_object*, lean_object*);
uint8_t l_instDecidableNot___redArg(uint8_t);
lean_object* l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Diff_Histogram_addLeft___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__9_spec__11_spec__11___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_noConfusion___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_CodeAction_insertBuiltin(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_FileWorker_EditableDocument_versionedIdentifier(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Diff_Histogram_addLeft___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__9_spec__11(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_split___at___Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__27(lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_noConfusion___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_size___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0_spec__0___lam__0(uint8_t, uint8_t, lean_object*, lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope;
lean_object* lean_array_mk(lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_linesToString___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__32(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_toCtorIdx___boxed(lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_SpecResult_noConfusion(lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_initFn____x40_Lean_Elab_GuardMsgs___hyg_6_(lean_object*);
lean_object* l_Lean_MessageLog_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_matchPrefix___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__5(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_matchPrefix___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__5___boxed(lean_object*, lean_object*);
uint8_t l___private_Lean_Message_0__Lean_beqMessageSeverity____x40_Lean_Message___hyg_107_(uint8_t, uint8_t);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Diff_Histogram_addLeft___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__9_spec__11_spec__11_spec__11___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_SpecResult_toCtorIdx(uint8_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_matchSuffix_go___at___Lean_Diff_matchSuffix___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__7_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Diff_Histogram_addLeft___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__9_spec__9___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Diff_linesToString___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__32_spec__32(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Diff_Histogram_addLeft___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__9_spec__11___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__34_spec__34(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_guard__msgs_diff;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__21(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__23(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Subarray_drop(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_logErrorAt___at___Lean_Elab_logException___at___Lean_Elab_Command_runLinters_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_instDecidableEqPos(lean_object*, lean_object*);
lean_object* l_Subarray_split(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__9___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0_spec__0___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_SpecResult_noConfusion___redArg(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__29(size_t, size_t, lean_object*);
lean_object* l_Lean_Elab_pushInfoLeaf___at___Lean_Elab_addCompletionInfo___at___Lean_Elab_elabSetOption___at___Lean_withSetOptionIn_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_instDecidableEqChar(uint32_t, uint32_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_matchPrefix_go___at___Lean_Diff_matchPrefix___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__5_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Linter_initFn____x40_Lean_Linter_UnusedVariables___hyg_1427__spec__2(uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_findSomeMAux___at___Lean_PersistentArray_findSomeM_x3f___at___Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__25___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t l_Char_ofNat(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_instTypeNameGuardMsgFailure;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_instImpl____x40_Lean_Elab_GuardMsgs___hyg_1820_;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_noConfusion(lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_initFn____x40_Lean_Elab_GuardMsgs___hyg_6_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("guard_msgs", 10, 10);
x_3 = lean_mk_string_unchecked("diff", 4, 4);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(0);
x_6 = lean_mk_string_unchecked("", 0, 0);
x_7 = lean_mk_string_unchecked("When true, show a diff between expected and actual messages if they don't match. ", 81, 81);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_6);
lean_ctor_set(x_8, 2, x_7);
lean_inc(x_4);
x_9 = l_Lean_Option_register___at___Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_6__spec__0(x_4, x_8, x_4, x_1);
lean_dec(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToStringWithoutPos(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_14; lean_object* x_15; lean_object* x_25; lean_object* x_26; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_35 = lean_ctor_get(x_1, 4);
lean_inc(x_35);
x_36 = l_Lean_MessageData_toString(x_35, x_2);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_45 = lean_ctor_get(x_1, 3);
lean_inc(x_45);
x_46 = lean_mk_string_unchecked("", 0, 0);
x_47 = lean_string_dec_eq(x_45, x_46);
lean_dec(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_mk_string_unchecked(":\n", 2, 2);
x_49 = lean_string_append(x_45, x_48);
lean_dec(x_48);
x_50 = lean_string_append(x_49, x_37);
lean_dec(x_37);
x_39 = x_50;
goto block_44;
}
else
{
lean_dec(x_45);
x_39 = x_37;
goto block_44;
}
block_8:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_mk_string_unchecked("\n", 1, 1);
x_6 = lean_string_append(x_3, x_5);
lean_dec(x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
return x_7;
}
block_13:
{
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
x_3 = x_9;
x_4 = x_10;
goto block_8;
}
}
block_24:
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_string_utf8_byte_size(x_14);
x_17 = lean_unsigned_to_nat(0u);
x_18 = l_instDecidableEqPos(x_16, x_17);
if (x_18 == 0)
{
lean_object* x_19; uint32_t x_20; lean_object* x_21; uint32_t x_22; uint8_t x_23; 
x_19 = lean_string_utf8_prev(x_14, x_16);
lean_dec(x_16);
x_20 = lean_string_utf8_get(x_14, x_19);
lean_dec(x_19);
x_21 = lean_unsigned_to_nat(10u);
x_22 = l_Char_ofNat(x_21);
x_23 = l_instDecidableEqChar(x_20, x_22);
if (x_23 == 0)
{
x_3 = x_14;
x_4 = x_15;
goto block_8;
}
else
{
x_9 = x_14;
x_10 = x_15;
x_11 = x_18;
goto block_13;
}
}
else
{
lean_dec(x_16);
x_9 = x_14;
x_10 = x_15;
x_11 = x_18;
goto block_13;
}
}
block_34:
{
uint8_t x_27; 
x_27 = lean_ctor_get_uint8(x_1, sizeof(void*)*5 + 1);
lean_dec(x_1);
switch (x_27) {
case 0:
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_mk_string_unchecked("info:", 5, 5);
x_29 = lean_string_append(x_28, x_25);
lean_dec(x_25);
x_14 = x_29;
x_15 = x_26;
goto block_24;
}
case 1:
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_mk_string_unchecked("warning:", 8, 8);
x_31 = lean_string_append(x_30, x_25);
lean_dec(x_25);
x_14 = x_31;
x_15 = x_26;
goto block_24;
}
default: 
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_mk_string_unchecked("error:", 6, 6);
x_33 = lean_string_append(x_32, x_25);
lean_dec(x_25);
x_14 = x_33;
x_15 = x_26;
goto block_24;
}
}
}
block_44:
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_mk_string_unchecked("\n", 1, 1);
x_41 = l_String_isPrefixOf(x_40, x_39);
lean_dec(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_mk_string_unchecked(" ", 1, 1);
x_43 = lean_string_append(x_42, x_39);
lean_dec(x_39);
x_25 = x_43;
x_26 = x_38;
goto block_34;
}
else
{
x_25 = x_39;
x_26 = x_38;
goto block_34;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_SpecResult_toCtorIdx(uint8_t x_1) {
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
default: 
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_SpecResult_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Elab_Tactic_GuardMsgs_SpecResult_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_SpecResult_noConfusion___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_SpecResult_noConfusion___redArg(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_SpecResult_noConfusion___redArg___lam__0___boxed), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_SpecResult_noConfusion(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Tactic_GuardMsgs_SpecResult_noConfusion___redArg(x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_SpecResult_noConfusion___redArg___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Tactic_GuardMsgs_SpecResult_noConfusion___redArg___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_SpecResult_noConfusion___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lean_Elab_Tactic_GuardMsgs_SpecResult_noConfusion___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_SpecResult_noConfusion___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l_Lean_Elab_Tactic_GuardMsgs_SpecResult_noConfusion(x_1, x_5, x_6, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_toCtorIdx(uint8_t x_1) {
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
default: 
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_noConfusion___redArg(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_SpecResult_noConfusion___redArg___lam__0___boxed), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_noConfusion(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_noConfusion___redArg(x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_noConfusion___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_noConfusion___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_noConfusion___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_noConfusion(x_1, x_5, x_6, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_toCtorIdx(uint8_t x_1) {
_start:
{
if (x_1 == 0)
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_noConfusion___redArg(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_SpecResult_noConfusion___redArg___lam__0___boxed), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_noConfusion(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_noConfusion___redArg(x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_noConfusion___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_noConfusion___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_noConfusion___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_noConfusion(x_1, x_5, x_6, x_4);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0_spec__0___lam__0(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; 
x_5 = lean_ctor_get_uint8(x_4, sizeof(void*)*5 + 1);
x_6 = l___private_Lean_Message_0__Lean_beqMessageSeverity____x40_Lean_Message___hyg_107_(x_5, x_1);
if (x_6 == 0)
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_7; uint8_t x_8; 
lean_dec(x_4);
x_7 = lean_box(2);
x_8 = lean_unbox(x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
lean_dec(x_3);
x_10 = lean_apply_1(x_9, x_4);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
return x_11;
}
}
else
{
lean_dec(x_4);
lean_dec(x_3);
if (x_2 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_box(0);
x_13 = lean_unbox(x_12);
return x_13;
}
else
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_box(1);
x_15 = lean_unbox(x_14);
return x_15;
}
}
}
}
LEAN_EXPORT uint8_t l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0_spec__0___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_box(0);
x_4 = lean_unbox(x_3);
return x_4;
}
else
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_box(1);
x_6 = lean_unbox(x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_15; 
x_15 = lean_usize_dec_lt(x_3, x_2);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_4);
lean_ctor_set(x_16, 1, x_7);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_17 = lean_ctor_get(x_4, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_4, 1);
lean_inc(x_18);
lean_dec(x_4);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_array_uget(x_1, x_3);
x_22 = lean_mk_string_unchecked("Lean", 4, 4);
x_23 = lean_mk_string_unchecked("guardMsgsSpecElt", 16, 16);
lean_inc(x_22);
x_24 = l_Lean_Name_mkStr2(x_22, x_23);
lean_inc(x_21);
x_25 = l_Lean_Syntax_isOfKind(x_21, x_24);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_17);
x_26 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_5, x_6, x_7);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
return x_26;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_26);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
else
{
uint8_t x_31; lean_object* x_32; uint8_t x_33; uint8_t x_41; lean_object* x_42; uint8_t x_43; uint8_t x_51; lean_object* x_52; uint8_t x_53; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_112; lean_object* x_113; uint8_t x_114; 
x_61 = lean_unsigned_to_nat(0u);
x_62 = l_Lean_Syntax_getArg(x_21, x_61);
lean_dec(x_21);
x_112 = lean_mk_string_unchecked("guardMsgsFilter", 15, 15);
lean_inc(x_22);
x_113 = l_Lean_Name_mkStr2(x_22, x_112);
lean_inc(x_62);
x_114 = l_Lean_Syntax_isOfKind(x_62, x_113);
lean_dec(x_113);
if (x_114 == 0)
{
lean_object* x_115; lean_object* x_116; uint8_t x_117; 
x_115 = lean_mk_string_unchecked("guardMsgsWhitespace", 19, 19);
lean_inc(x_22);
x_116 = l_Lean_Name_mkStr2(x_22, x_115);
lean_inc(x_62);
x_117 = l_Lean_Syntax_isOfKind(x_62, x_116);
lean_dec(x_116);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; uint8_t x_120; 
lean_dec(x_17);
x_118 = lean_mk_string_unchecked("guardMsgsOrdering", 17, 17);
lean_inc(x_22);
x_119 = l_Lean_Name_mkStr2(x_22, x_118);
lean_inc(x_62);
x_120 = l_Lean_Syntax_isOfKind(x_62, x_119);
lean_dec(x_119);
if (x_120 == 0)
{
lean_object* x_121; uint8_t x_122; 
lean_dec(x_62);
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_19);
x_121 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_5, x_6, x_7);
x_122 = !lean_is_exclusive(x_121);
if (x_122 == 0)
{
return x_121;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_ctor_get(x_121, 0);
x_124 = lean_ctor_get(x_121, 1);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_121);
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
return x_125;
}
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; uint8_t x_130; 
x_126 = lean_unsigned_to_nat(2u);
x_127 = l_Lean_Syntax_getArg(x_62, x_126);
lean_dec(x_62);
x_128 = lean_mk_string_unchecked("guardMsgsOrderingArg", 20, 20);
x_129 = l_Lean_Name_mkStr2(x_22, x_128);
lean_inc(x_127);
x_130 = l_Lean_Syntax_isOfKind(x_127, x_129);
lean_dec(x_129);
if (x_130 == 0)
{
lean_object* x_131; uint8_t x_132; 
lean_dec(x_127);
lean_dec(x_20);
lean_dec(x_19);
x_131 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_5, x_6, x_7);
x_132 = !lean_is_exclusive(x_131);
if (x_132 == 0)
{
return x_131;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_ctor_get(x_131, 0);
x_134 = lean_ctor_get(x_131, 1);
lean_inc(x_134);
lean_inc(x_133);
lean_dec(x_131);
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_134);
return x_135;
}
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; 
x_136 = l_Lean_Syntax_getArg(x_127, x_61);
lean_dec(x_127);
x_137 = lean_mk_string_unchecked("token", 5, 5);
x_138 = lean_mk_string_unchecked("exact", 5, 5);
lean_inc(x_137);
x_139 = l_Lean_Name_mkStr2(x_137, x_138);
lean_inc(x_136);
x_140 = l_Lean_Syntax_isOfKind(x_136, x_139);
lean_dec(x_139);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; uint8_t x_143; 
x_141 = lean_mk_string_unchecked("sorted", 6, 6);
x_142 = l_Lean_Name_mkStr2(x_137, x_141);
x_143 = l_Lean_Syntax_isOfKind(x_136, x_142);
lean_dec(x_142);
if (x_143 == 0)
{
lean_object* x_144; uint8_t x_145; 
lean_dec(x_20);
lean_dec(x_19);
x_144 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_5, x_6, x_7);
x_145 = !lean_is_exclusive(x_144);
if (x_145 == 0)
{
return x_144;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_ctor_get(x_144, 0);
x_147 = lean_ctor_get(x_144, 1);
lean_inc(x_147);
lean_inc(x_146);
lean_dec(x_144);
x_148 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set(x_148, 1, x_147);
return x_148;
}
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_149 = lean_box(1);
x_150 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_150, 0, x_19);
lean_ctor_set(x_150, 1, x_20);
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_149);
lean_ctor_set(x_151, 1, x_150);
x_8 = x_151;
x_9 = x_7;
goto block_14;
}
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; 
lean_dec(x_137);
lean_dec(x_136);
x_152 = lean_box(0);
x_153 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_153, 0, x_19);
lean_ctor_set(x_153, 1, x_20);
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_152);
lean_ctor_set(x_154, 1, x_153);
x_8 = x_154;
x_9 = x_7;
goto block_14;
}
}
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; 
lean_dec(x_20);
x_155 = lean_unsigned_to_nat(2u);
x_156 = l_Lean_Syntax_getArg(x_62, x_155);
lean_dec(x_62);
x_157 = lean_mk_string_unchecked("guardMsgsWhitespaceArg", 22, 22);
x_158 = l_Lean_Name_mkStr2(x_22, x_157);
lean_inc(x_156);
x_159 = l_Lean_Syntax_isOfKind(x_156, x_158);
lean_dec(x_158);
if (x_159 == 0)
{
lean_object* x_160; uint8_t x_161; 
lean_dec(x_156);
lean_dec(x_19);
lean_dec(x_17);
x_160 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_5, x_6, x_7);
x_161 = !lean_is_exclusive(x_160);
if (x_161 == 0)
{
return x_160;
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_162 = lean_ctor_get(x_160, 0);
x_163 = lean_ctor_get(x_160, 1);
lean_inc(x_163);
lean_inc(x_162);
lean_dec(x_160);
x_164 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_164, 0, x_162);
lean_ctor_set(x_164, 1, x_163);
return x_164;
}
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; uint8_t x_169; 
x_165 = l_Lean_Syntax_getArg(x_156, x_61);
lean_dec(x_156);
x_166 = lean_mk_string_unchecked("token", 5, 5);
x_167 = lean_mk_string_unchecked("exact", 5, 5);
lean_inc(x_166);
x_168 = l_Lean_Name_mkStr2(x_166, x_167);
lean_inc(x_165);
x_169 = l_Lean_Syntax_isOfKind(x_165, x_168);
lean_dec(x_168);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; uint8_t x_172; 
x_170 = lean_mk_string_unchecked("normalized", 10, 10);
lean_inc(x_166);
x_171 = l_Lean_Name_mkStr2(x_166, x_170);
lean_inc(x_165);
x_172 = l_Lean_Syntax_isOfKind(x_165, x_171);
lean_dec(x_171);
if (x_172 == 0)
{
lean_object* x_173; lean_object* x_174; uint8_t x_175; 
x_173 = lean_mk_string_unchecked("lax", 3, 3);
x_174 = l_Lean_Name_mkStr2(x_166, x_173);
x_175 = l_Lean_Syntax_isOfKind(x_165, x_174);
lean_dec(x_174);
if (x_175 == 0)
{
lean_object* x_176; uint8_t x_177; 
lean_dec(x_19);
lean_dec(x_17);
x_176 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_5, x_6, x_7);
x_177 = !lean_is_exclusive(x_176);
if (x_177 == 0)
{
return x_176;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_178 = lean_ctor_get(x_176, 0);
x_179 = lean_ctor_get(x_176, 1);
lean_inc(x_179);
lean_inc(x_178);
lean_dec(x_176);
x_180 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_180, 0, x_178);
lean_ctor_set(x_180, 1, x_179);
return x_180;
}
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_181 = lean_box(2);
x_182 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_182, 0, x_19);
lean_ctor_set(x_182, 1, x_181);
x_183 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_183, 0, x_17);
lean_ctor_set(x_183, 1, x_182);
x_8 = x_183;
x_9 = x_7;
goto block_14;
}
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; 
lean_dec(x_166);
lean_dec(x_165);
x_184 = lean_box(1);
x_185 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_185, 0, x_19);
lean_ctor_set(x_185, 1, x_184);
x_186 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_186, 0, x_17);
lean_ctor_set(x_186, 1, x_185);
x_8 = x_186;
x_9 = x_7;
goto block_14;
}
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; 
lean_dec(x_166);
lean_dec(x_165);
x_187 = lean_box(0);
x_188 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_188, 0, x_19);
lean_ctor_set(x_188, 1, x_187);
x_189 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_189, 0, x_17);
lean_ctor_set(x_189, 1, x_188);
x_8 = x_189;
x_9 = x_7;
goto block_14;
}
}
}
}
else
{
lean_object* x_190; uint8_t x_191; 
x_190 = l_Lean_Syntax_getArg(x_62, x_61);
x_191 = l_Lean_Syntax_isNone(x_190);
if (x_191 == 0)
{
lean_object* x_192; uint8_t x_193; 
x_192 = lean_unsigned_to_nat(1u);
lean_inc(x_190);
x_193 = l_Lean_Syntax_matchesNull(x_190, x_192);
if (x_193 == 0)
{
lean_object* x_194; uint8_t x_195; 
lean_dec(x_190);
lean_dec(x_62);
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_17);
x_194 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_5, x_6, x_7);
x_195 = !lean_is_exclusive(x_194);
if (x_195 == 0)
{
return x_194;
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_196 = lean_ctor_get(x_194, 0);
x_197 = lean_ctor_get(x_194, 1);
lean_inc(x_197);
lean_inc(x_196);
lean_dec(x_194);
x_198 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_198, 0, x_196);
lean_ctor_set(x_198, 1, x_197);
return x_198;
}
}
else
{
lean_object* x_199; lean_object* x_200; 
x_199 = l_Lean_Syntax_getArg(x_190, x_61);
lean_dec(x_190);
x_200 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_200, 0, x_199);
x_63 = x_200;
x_64 = x_5;
x_65 = x_6;
x_66 = x_7;
goto block_111;
}
}
else
{
lean_object* x_201; 
lean_dec(x_190);
x_201 = lean_box(0);
x_63 = x_201;
x_64 = x_5;
x_65 = x_6;
x_66 = x_7;
goto block_111;
}
}
block_40:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_34 = lean_box(x_31);
x_35 = lean_box(x_33);
x_36 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0_spec__0___lam__0___boxed), 4, 3);
lean_closure_set(x_36, 0, x_34);
lean_closure_set(x_36, 1, x_35);
lean_closure_set(x_36, 2, x_19);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_20);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_17);
lean_ctor_set(x_39, 1, x_38);
x_8 = x_39;
x_9 = x_32;
goto block_14;
}
block_50:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_44 = lean_box(x_41);
x_45 = lean_box(x_43);
x_46 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0_spec__0___lam__0___boxed), 4, 3);
lean_closure_set(x_46, 0, x_44);
lean_closure_set(x_46, 1, x_45);
lean_closure_set(x_46, 2, x_19);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_20);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_17);
lean_ctor_set(x_49, 1, x_48);
x_8 = x_49;
x_9 = x_42;
goto block_14;
}
block_60:
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_54 = lean_box(x_51);
x_55 = lean_box(x_53);
x_56 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0_spec__0___lam__0___boxed), 4, 3);
lean_closure_set(x_56, 0, x_54);
lean_closure_set(x_56, 1, x_55);
lean_closure_set(x_56, 2, x_19);
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_56);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_20);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_17);
lean_ctor_set(x_59, 1, x_58);
x_8 = x_59;
x_9 = x_52;
goto block_14;
}
block_111:
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_67 = lean_unsigned_to_nat(1u);
x_68 = l_Lean_Syntax_getArg(x_62, x_67);
lean_dec(x_62);
x_69 = lean_mk_string_unchecked("guardMsgsFilterSeverity", 23, 23);
x_70 = l_Lean_Name_mkStr2(x_22, x_69);
lean_inc(x_68);
x_71 = l_Lean_Syntax_isOfKind(x_68, x_70);
lean_dec(x_70);
if (x_71 == 0)
{
lean_object* x_72; uint8_t x_73; 
lean_dec(x_68);
lean_dec(x_63);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_17);
x_72 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_64, x_65, x_66);
x_73 = !lean_is_exclusive(x_72);
if (x_73 == 0)
{
return x_72;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_72, 0);
x_75 = lean_ctor_get(x_72, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_72);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_77 = l_Lean_Syntax_getArg(x_68, x_61);
lean_dec(x_68);
x_78 = lean_mk_string_unchecked("token", 5, 5);
x_79 = lean_mk_string_unchecked("info", 4, 4);
lean_inc(x_78);
x_80 = l_Lean_Name_mkStr2(x_78, x_79);
lean_inc(x_77);
x_81 = l_Lean_Syntax_isOfKind(x_77, x_80);
lean_dec(x_80);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_82 = lean_mk_string_unchecked("warning", 7, 7);
lean_inc(x_78);
x_83 = l_Lean_Name_mkStr2(x_78, x_82);
lean_inc(x_77);
x_84 = l_Lean_Syntax_isOfKind(x_77, x_83);
lean_dec(x_83);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_85 = lean_mk_string_unchecked("error", 5, 5);
lean_inc(x_78);
x_86 = l_Lean_Name_mkStr2(x_78, x_85);
lean_inc(x_77);
x_87 = l_Lean_Syntax_isOfKind(x_77, x_86);
lean_dec(x_86);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; uint8_t x_90; 
lean_dec(x_19);
x_88 = lean_mk_string_unchecked("all", 3, 3);
x_89 = l_Lean_Name_mkStr2(x_78, x_88);
x_90 = l_Lean_Syntax_isOfKind(x_77, x_89);
lean_dec(x_89);
if (x_90 == 0)
{
lean_object* x_91; uint8_t x_92; 
lean_dec(x_63);
lean_dec(x_20);
lean_dec(x_17);
x_91 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_64, x_65, x_66);
x_92 = !lean_is_exclusive(x_91);
if (x_92 == 0)
{
return x_91;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_91, 0);
x_94 = lean_ctor_get(x_91, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_91);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_96 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0_spec__0___lam__1___boxed), 2, 1);
lean_closure_set(x_96, 0, x_63);
x_97 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_97, 0, x_96);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_20);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_17);
lean_ctor_set(x_99, 1, x_98);
x_8 = x_99;
x_9 = x_66;
goto block_14;
}
}
else
{
lean_object* x_100; 
lean_dec(x_78);
lean_dec(x_77);
x_100 = lean_box(2);
if (lean_obj_tag(x_63) == 0)
{
uint8_t x_101; 
x_101 = lean_unbox(x_100);
x_51 = x_101;
x_52 = x_66;
x_53 = x_84;
goto block_60;
}
else
{
uint8_t x_102; 
lean_dec(x_63);
x_102 = lean_unbox(x_100);
x_51 = x_102;
x_52 = x_66;
x_53 = x_87;
goto block_60;
}
}
}
else
{
lean_object* x_103; 
lean_dec(x_78);
lean_dec(x_77);
x_103 = lean_box(1);
if (lean_obj_tag(x_63) == 0)
{
uint8_t x_104; 
x_104 = lean_unbox(x_103);
x_41 = x_104;
x_42 = x_66;
x_43 = x_81;
goto block_50;
}
else
{
uint8_t x_105; 
lean_dec(x_63);
x_105 = lean_unbox(x_103);
x_41 = x_105;
x_42 = x_66;
x_43 = x_84;
goto block_50;
}
}
}
else
{
lean_object* x_106; 
lean_dec(x_78);
lean_dec(x_77);
x_106 = lean_box(0);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_107; uint8_t x_108; uint8_t x_109; 
x_107 = lean_box(0);
x_108 = lean_unbox(x_106);
x_109 = lean_unbox(x_107);
x_31 = x_108;
x_32 = x_66;
x_33 = x_109;
goto block_40;
}
else
{
uint8_t x_110; 
lean_dec(x_63);
x_110 = lean_unbox(x_106);
x_31 = x_110;
x_32 = x_66;
x_33 = x_81;
goto block_40;
}
}
}
}
}
}
block_14:
{
lean_object* x_10; size_t x_11; size_t x_12; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_usize_of_nat(x_10);
x_12 = lean_usize_add(x_3, x_11);
x_3 = x_12;
x_4 = x_8;
x_7 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_15; 
x_15 = lean_usize_dec_lt(x_3, x_2);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_4);
lean_ctor_set(x_16, 1, x_7);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_17 = lean_ctor_get(x_4, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_4, 1);
lean_inc(x_18);
lean_dec(x_4);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_array_uget(x_1, x_3);
x_22 = lean_mk_string_unchecked("Lean", 4, 4);
x_23 = lean_mk_string_unchecked("guardMsgsSpecElt", 16, 16);
lean_inc(x_22);
x_24 = l_Lean_Name_mkStr2(x_22, x_23);
lean_inc(x_21);
x_25 = l_Lean_Syntax_isOfKind(x_21, x_24);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_17);
x_26 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_5, x_6, x_7);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
return x_26;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_26);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
else
{
lean_object* x_31; uint8_t x_32; uint8_t x_33; lean_object* x_41; uint8_t x_42; uint8_t x_43; uint8_t x_51; lean_object* x_52; uint8_t x_53; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_112; lean_object* x_113; uint8_t x_114; 
x_61 = lean_unsigned_to_nat(0u);
x_62 = l_Lean_Syntax_getArg(x_21, x_61);
lean_dec(x_21);
x_112 = lean_mk_string_unchecked("guardMsgsFilter", 15, 15);
lean_inc(x_22);
x_113 = l_Lean_Name_mkStr2(x_22, x_112);
lean_inc(x_62);
x_114 = l_Lean_Syntax_isOfKind(x_62, x_113);
lean_dec(x_113);
if (x_114 == 0)
{
lean_object* x_115; lean_object* x_116; uint8_t x_117; 
x_115 = lean_mk_string_unchecked("guardMsgsWhitespace", 19, 19);
lean_inc(x_22);
x_116 = l_Lean_Name_mkStr2(x_22, x_115);
lean_inc(x_62);
x_117 = l_Lean_Syntax_isOfKind(x_62, x_116);
lean_dec(x_116);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; uint8_t x_120; 
lean_dec(x_17);
x_118 = lean_mk_string_unchecked("guardMsgsOrdering", 17, 17);
lean_inc(x_22);
x_119 = l_Lean_Name_mkStr2(x_22, x_118);
lean_inc(x_62);
x_120 = l_Lean_Syntax_isOfKind(x_62, x_119);
lean_dec(x_119);
if (x_120 == 0)
{
lean_object* x_121; uint8_t x_122; 
lean_dec(x_62);
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_19);
x_121 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_5, x_6, x_7);
x_122 = !lean_is_exclusive(x_121);
if (x_122 == 0)
{
return x_121;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_ctor_get(x_121, 0);
x_124 = lean_ctor_get(x_121, 1);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_121);
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
return x_125;
}
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; uint8_t x_130; 
x_126 = lean_unsigned_to_nat(2u);
x_127 = l_Lean_Syntax_getArg(x_62, x_126);
lean_dec(x_62);
x_128 = lean_mk_string_unchecked("guardMsgsOrderingArg", 20, 20);
x_129 = l_Lean_Name_mkStr2(x_22, x_128);
lean_inc(x_127);
x_130 = l_Lean_Syntax_isOfKind(x_127, x_129);
lean_dec(x_129);
if (x_130 == 0)
{
lean_object* x_131; uint8_t x_132; 
lean_dec(x_127);
lean_dec(x_20);
lean_dec(x_19);
x_131 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_5, x_6, x_7);
x_132 = !lean_is_exclusive(x_131);
if (x_132 == 0)
{
return x_131;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_ctor_get(x_131, 0);
x_134 = lean_ctor_get(x_131, 1);
lean_inc(x_134);
lean_inc(x_133);
lean_dec(x_131);
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_134);
return x_135;
}
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; 
x_136 = l_Lean_Syntax_getArg(x_127, x_61);
lean_dec(x_127);
x_137 = lean_mk_string_unchecked("token", 5, 5);
x_138 = lean_mk_string_unchecked("exact", 5, 5);
lean_inc(x_137);
x_139 = l_Lean_Name_mkStr2(x_137, x_138);
lean_inc(x_136);
x_140 = l_Lean_Syntax_isOfKind(x_136, x_139);
lean_dec(x_139);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; uint8_t x_143; 
x_141 = lean_mk_string_unchecked("sorted", 6, 6);
x_142 = l_Lean_Name_mkStr2(x_137, x_141);
x_143 = l_Lean_Syntax_isOfKind(x_136, x_142);
lean_dec(x_142);
if (x_143 == 0)
{
lean_object* x_144; uint8_t x_145; 
lean_dec(x_20);
lean_dec(x_19);
x_144 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_5, x_6, x_7);
x_145 = !lean_is_exclusive(x_144);
if (x_145 == 0)
{
return x_144;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_ctor_get(x_144, 0);
x_147 = lean_ctor_get(x_144, 1);
lean_inc(x_147);
lean_inc(x_146);
lean_dec(x_144);
x_148 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set(x_148, 1, x_147);
return x_148;
}
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_149 = lean_box(1);
x_150 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_150, 0, x_19);
lean_ctor_set(x_150, 1, x_20);
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_149);
lean_ctor_set(x_151, 1, x_150);
x_8 = x_151;
x_9 = x_7;
goto block_14;
}
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; 
lean_dec(x_137);
lean_dec(x_136);
x_152 = lean_box(0);
x_153 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_153, 0, x_19);
lean_ctor_set(x_153, 1, x_20);
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_152);
lean_ctor_set(x_154, 1, x_153);
x_8 = x_154;
x_9 = x_7;
goto block_14;
}
}
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; 
lean_dec(x_20);
x_155 = lean_unsigned_to_nat(2u);
x_156 = l_Lean_Syntax_getArg(x_62, x_155);
lean_dec(x_62);
x_157 = lean_mk_string_unchecked("guardMsgsWhitespaceArg", 22, 22);
x_158 = l_Lean_Name_mkStr2(x_22, x_157);
lean_inc(x_156);
x_159 = l_Lean_Syntax_isOfKind(x_156, x_158);
lean_dec(x_158);
if (x_159 == 0)
{
lean_object* x_160; uint8_t x_161; 
lean_dec(x_156);
lean_dec(x_19);
lean_dec(x_17);
x_160 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_5, x_6, x_7);
x_161 = !lean_is_exclusive(x_160);
if (x_161 == 0)
{
return x_160;
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_162 = lean_ctor_get(x_160, 0);
x_163 = lean_ctor_get(x_160, 1);
lean_inc(x_163);
lean_inc(x_162);
lean_dec(x_160);
x_164 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_164, 0, x_162);
lean_ctor_set(x_164, 1, x_163);
return x_164;
}
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; uint8_t x_169; 
x_165 = l_Lean_Syntax_getArg(x_156, x_61);
lean_dec(x_156);
x_166 = lean_mk_string_unchecked("token", 5, 5);
x_167 = lean_mk_string_unchecked("exact", 5, 5);
lean_inc(x_166);
x_168 = l_Lean_Name_mkStr2(x_166, x_167);
lean_inc(x_165);
x_169 = l_Lean_Syntax_isOfKind(x_165, x_168);
lean_dec(x_168);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; uint8_t x_172; 
x_170 = lean_mk_string_unchecked("normalized", 10, 10);
lean_inc(x_166);
x_171 = l_Lean_Name_mkStr2(x_166, x_170);
lean_inc(x_165);
x_172 = l_Lean_Syntax_isOfKind(x_165, x_171);
lean_dec(x_171);
if (x_172 == 0)
{
lean_object* x_173; lean_object* x_174; uint8_t x_175; 
x_173 = lean_mk_string_unchecked("lax", 3, 3);
x_174 = l_Lean_Name_mkStr2(x_166, x_173);
x_175 = l_Lean_Syntax_isOfKind(x_165, x_174);
lean_dec(x_174);
if (x_175 == 0)
{
lean_object* x_176; uint8_t x_177; 
lean_dec(x_19);
lean_dec(x_17);
x_176 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_5, x_6, x_7);
x_177 = !lean_is_exclusive(x_176);
if (x_177 == 0)
{
return x_176;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_178 = lean_ctor_get(x_176, 0);
x_179 = lean_ctor_get(x_176, 1);
lean_inc(x_179);
lean_inc(x_178);
lean_dec(x_176);
x_180 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_180, 0, x_178);
lean_ctor_set(x_180, 1, x_179);
return x_180;
}
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_181 = lean_box(2);
x_182 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_182, 0, x_19);
lean_ctor_set(x_182, 1, x_181);
x_183 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_183, 0, x_17);
lean_ctor_set(x_183, 1, x_182);
x_8 = x_183;
x_9 = x_7;
goto block_14;
}
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; 
lean_dec(x_166);
lean_dec(x_165);
x_184 = lean_box(1);
x_185 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_185, 0, x_19);
lean_ctor_set(x_185, 1, x_184);
x_186 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_186, 0, x_17);
lean_ctor_set(x_186, 1, x_185);
x_8 = x_186;
x_9 = x_7;
goto block_14;
}
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; 
lean_dec(x_166);
lean_dec(x_165);
x_187 = lean_box(0);
x_188 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_188, 0, x_19);
lean_ctor_set(x_188, 1, x_187);
x_189 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_189, 0, x_17);
lean_ctor_set(x_189, 1, x_188);
x_8 = x_189;
x_9 = x_7;
goto block_14;
}
}
}
}
else
{
lean_object* x_190; uint8_t x_191; 
x_190 = l_Lean_Syntax_getArg(x_62, x_61);
x_191 = l_Lean_Syntax_isNone(x_190);
if (x_191 == 0)
{
lean_object* x_192; uint8_t x_193; 
x_192 = lean_unsigned_to_nat(1u);
lean_inc(x_190);
x_193 = l_Lean_Syntax_matchesNull(x_190, x_192);
if (x_193 == 0)
{
lean_object* x_194; uint8_t x_195; 
lean_dec(x_190);
lean_dec(x_62);
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_17);
x_194 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_5, x_6, x_7);
x_195 = !lean_is_exclusive(x_194);
if (x_195 == 0)
{
return x_194;
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_196 = lean_ctor_get(x_194, 0);
x_197 = lean_ctor_get(x_194, 1);
lean_inc(x_197);
lean_inc(x_196);
lean_dec(x_194);
x_198 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_198, 0, x_196);
lean_ctor_set(x_198, 1, x_197);
return x_198;
}
}
else
{
lean_object* x_199; lean_object* x_200; 
x_199 = l_Lean_Syntax_getArg(x_190, x_61);
lean_dec(x_190);
x_200 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_200, 0, x_199);
x_63 = x_200;
x_64 = x_5;
x_65 = x_6;
x_66 = x_7;
goto block_111;
}
}
else
{
lean_object* x_201; 
lean_dec(x_190);
x_201 = lean_box(0);
x_63 = x_201;
x_64 = x_5;
x_65 = x_6;
x_66 = x_7;
goto block_111;
}
}
block_40:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_34 = lean_box(x_32);
x_35 = lean_box(x_33);
x_36 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0_spec__0___lam__0___boxed), 4, 3);
lean_closure_set(x_36, 0, x_34);
lean_closure_set(x_36, 1, x_35);
lean_closure_set(x_36, 2, x_19);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_20);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_17);
lean_ctor_set(x_39, 1, x_38);
x_8 = x_39;
x_9 = x_31;
goto block_14;
}
block_50:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_44 = lean_box(x_42);
x_45 = lean_box(x_43);
x_46 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0_spec__0___lam__0___boxed), 4, 3);
lean_closure_set(x_46, 0, x_44);
lean_closure_set(x_46, 1, x_45);
lean_closure_set(x_46, 2, x_19);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_20);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_17);
lean_ctor_set(x_49, 1, x_48);
x_8 = x_49;
x_9 = x_41;
goto block_14;
}
block_60:
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_54 = lean_box(x_51);
x_55 = lean_box(x_53);
x_56 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0_spec__0___lam__0___boxed), 4, 3);
lean_closure_set(x_56, 0, x_54);
lean_closure_set(x_56, 1, x_55);
lean_closure_set(x_56, 2, x_19);
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_56);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_20);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_17);
lean_ctor_set(x_59, 1, x_58);
x_8 = x_59;
x_9 = x_52;
goto block_14;
}
block_111:
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_67 = lean_unsigned_to_nat(1u);
x_68 = l_Lean_Syntax_getArg(x_62, x_67);
lean_dec(x_62);
x_69 = lean_mk_string_unchecked("guardMsgsFilterSeverity", 23, 23);
x_70 = l_Lean_Name_mkStr2(x_22, x_69);
lean_inc(x_68);
x_71 = l_Lean_Syntax_isOfKind(x_68, x_70);
lean_dec(x_70);
if (x_71 == 0)
{
lean_object* x_72; uint8_t x_73; 
lean_dec(x_68);
lean_dec(x_63);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_17);
x_72 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_64, x_65, x_66);
x_73 = !lean_is_exclusive(x_72);
if (x_73 == 0)
{
return x_72;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_72, 0);
x_75 = lean_ctor_get(x_72, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_72);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_77 = l_Lean_Syntax_getArg(x_68, x_61);
lean_dec(x_68);
x_78 = lean_mk_string_unchecked("token", 5, 5);
x_79 = lean_mk_string_unchecked("info", 4, 4);
lean_inc(x_78);
x_80 = l_Lean_Name_mkStr2(x_78, x_79);
lean_inc(x_77);
x_81 = l_Lean_Syntax_isOfKind(x_77, x_80);
lean_dec(x_80);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_82 = lean_mk_string_unchecked("warning", 7, 7);
lean_inc(x_78);
x_83 = l_Lean_Name_mkStr2(x_78, x_82);
lean_inc(x_77);
x_84 = l_Lean_Syntax_isOfKind(x_77, x_83);
lean_dec(x_83);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_85 = lean_mk_string_unchecked("error", 5, 5);
lean_inc(x_78);
x_86 = l_Lean_Name_mkStr2(x_78, x_85);
lean_inc(x_77);
x_87 = l_Lean_Syntax_isOfKind(x_77, x_86);
lean_dec(x_86);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; uint8_t x_90; 
lean_dec(x_19);
x_88 = lean_mk_string_unchecked("all", 3, 3);
x_89 = l_Lean_Name_mkStr2(x_78, x_88);
x_90 = l_Lean_Syntax_isOfKind(x_77, x_89);
lean_dec(x_89);
if (x_90 == 0)
{
lean_object* x_91; uint8_t x_92; 
lean_dec(x_63);
lean_dec(x_20);
lean_dec(x_17);
x_91 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_64, x_65, x_66);
x_92 = !lean_is_exclusive(x_91);
if (x_92 == 0)
{
return x_91;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_91, 0);
x_94 = lean_ctor_get(x_91, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_91);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_96 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0_spec__0___lam__1___boxed), 2, 1);
lean_closure_set(x_96, 0, x_63);
x_97 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_97, 0, x_96);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_20);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_17);
lean_ctor_set(x_99, 1, x_98);
x_8 = x_99;
x_9 = x_66;
goto block_14;
}
}
else
{
lean_object* x_100; 
lean_dec(x_78);
lean_dec(x_77);
x_100 = lean_box(2);
if (lean_obj_tag(x_63) == 0)
{
uint8_t x_101; 
x_101 = lean_unbox(x_100);
x_51 = x_101;
x_52 = x_66;
x_53 = x_84;
goto block_60;
}
else
{
uint8_t x_102; 
lean_dec(x_63);
x_102 = lean_unbox(x_100);
x_51 = x_102;
x_52 = x_66;
x_53 = x_87;
goto block_60;
}
}
}
else
{
lean_object* x_103; 
lean_dec(x_78);
lean_dec(x_77);
x_103 = lean_box(1);
if (lean_obj_tag(x_63) == 0)
{
uint8_t x_104; 
x_104 = lean_unbox(x_103);
x_41 = x_66;
x_42 = x_104;
x_43 = x_81;
goto block_50;
}
else
{
uint8_t x_105; 
lean_dec(x_63);
x_105 = lean_unbox(x_103);
x_41 = x_66;
x_42 = x_105;
x_43 = x_84;
goto block_50;
}
}
}
else
{
lean_object* x_106; 
lean_dec(x_78);
lean_dec(x_77);
x_106 = lean_box(0);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_107; uint8_t x_108; uint8_t x_109; 
x_107 = lean_box(0);
x_108 = lean_unbox(x_106);
x_109 = lean_unbox(x_107);
x_31 = x_66;
x_32 = x_108;
x_33 = x_109;
goto block_40;
}
else
{
uint8_t x_110; 
lean_dec(x_63);
x_110 = lean_unbox(x_106);
x_31 = x_66;
x_32 = x_110;
x_33 = x_81;
goto block_40;
}
}
}
}
}
}
block_14:
{
lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_usize_of_nat(x_10);
x_12 = lean_usize_add(x_3, x_11);
x_13 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0_spec__0(x_1, x_2, x_12, x_8, x_5, x_6, x_9);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__2(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
x_7 = lean_array_uget(x_3, x_2);
x_8 = lean_mk_string_unchecked("guardMsgsSpecElt", 16, 16);
x_9 = l_Lean_Name_mkStr2(x_6, x_8);
lean_inc(x_7);
x_10 = l_Lean_Syntax_isOfKind(x_7, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_7);
lean_dec(x_3);
x_11 = lean_box(0);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_12 = lean_box(0);
x_13 = lean_array_uset(x_3, x_2, x_12);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_usize_of_nat(x_14);
x_16 = lean_usize_add(x_2, x_15);
x_17 = lean_array_uset(x_13, x_2, x_7);
x_2 = x_16;
x_3 = x_17;
goto _start;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; uint8_t x_4; 
lean_dec(x_2);
x_3 = lean_box(0);
x_4 = lean_unbox(x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_1(x_5, x_2);
x_7 = lean_unbox(x_6);
lean_dec(x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_56; 
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_unsigned_to_nat(0u);
x_69 = lean_mk_empty_array_with_capacity(x_68);
x_5 = x_69;
x_6 = x_2;
x_7 = x_3;
x_8 = x_4;
goto block_55;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_70 = lean_ctor_get(x_1, 0);
lean_inc(x_70);
lean_dec(x_1);
x_71 = lean_mk_string_unchecked("Lean", 4, 4);
x_72 = lean_mk_string_unchecked("guardMsgsSpec", 13, 13);
x_73 = l_Lean_Name_mkStr2(x_71, x_72);
lean_inc(x_70);
x_74 = l_Lean_Syntax_isOfKind(x_70, x_73);
lean_dec(x_73);
if (x_74 == 0)
{
lean_object* x_75; uint8_t x_76; 
lean_dec(x_70);
x_75 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_2, x_3, x_4);
x_76 = !lean_is_exclusive(x_75);
if (x_76 == 0)
{
return x_75;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_75, 0);
x_78 = lean_ctor_get(x_75, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_75);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_80 = lean_unsigned_to_nat(1u);
x_81 = l_Lean_Syntax_getArg(x_70, x_80);
lean_dec(x_70);
x_82 = l_Lean_Syntax_getArgs(x_81);
lean_dec(x_81);
x_83 = l_Array_empty(lean_box(0));
x_84 = lean_unsigned_to_nat(0u);
x_85 = lean_array_get_size(x_82);
x_86 = lean_nat_dec_lt(x_84, x_85);
if (x_86 == 0)
{
lean_dec(x_85);
lean_dec(x_82);
x_56 = x_83;
goto block_67;
}
else
{
uint8_t x_87; 
x_87 = lean_nat_dec_le(x_85, x_85);
if (x_87 == 0)
{
lean_dec(x_85);
lean_dec(x_82);
x_56 = x_83;
goto block_67;
}
else
{
lean_object* x_88; lean_object* x_89; size_t x_90; size_t x_91; lean_object* x_92; lean_object* x_93; 
x_88 = lean_box(x_74);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_83);
x_90 = lean_usize_of_nat(x_84);
x_91 = lean_usize_of_nat(x_85);
lean_dec(x_85);
x_92 = l_Array_foldlMUnsafe_fold___at___Lean_Linter_initFn____x40_Lean_Linter_UnusedVariables___hyg_1427__spec__2(x_74, x_82, x_90, x_91, x_89);
lean_dec(x_82);
x_93 = lean_ctor_get(x_92, 1);
lean_inc(x_93);
lean_dec(x_92);
x_56 = x_93;
goto block_67;
}
}
}
}
block_55:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; lean_object* x_16; size_t x_17; lean_object* x_18; 
x_9 = lean_box(1);
x_10 = lean_box(0);
x_11 = lean_box(0);
x_12 = l_Array_reverse(lean_box(0), x_5);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_9);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_array_size(x_12);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_usize_of_nat(x_16);
x_18 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0(x_12, x_15, x_17, x_14, x_6, x_7, x_8);
lean_dec(x_12);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
x_21 = !lean_is_exclusive(x_18);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_18, 0);
lean_dec(x_22);
x_23 = !lean_is_exclusive(x_19);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_19, 0);
x_25 = lean_ctor_get(x_19, 1);
lean_dec(x_25);
x_26 = !lean_is_exclusive(x_20);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_20, 0);
x_28 = lean_ctor_get(x_20, 1);
x_29 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___lam__0___boxed), 2, 1);
lean_closure_set(x_29, 0, x_27);
lean_ctor_set(x_20, 1, x_29);
lean_ctor_set(x_20, 0, x_24);
lean_ctor_set(x_19, 0, x_28);
return x_18;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_20, 0);
x_31 = lean_ctor_get(x_20, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_20);
x_32 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___lam__0___boxed), 2, 1);
lean_closure_set(x_32, 0, x_30);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_24);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_19, 1, x_33);
lean_ctor_set(x_19, 0, x_31);
return x_18;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_34 = lean_ctor_get(x_19, 0);
lean_inc(x_34);
lean_dec(x_19);
x_35 = lean_ctor_get(x_20, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_20, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_37 = x_20;
} else {
 lean_dec_ref(x_20);
 x_37 = lean_box(0);
}
x_38 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___lam__0___boxed), 2, 1);
lean_closure_set(x_38, 0, x_35);
if (lean_is_scalar(x_37)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_37;
}
lean_ctor_set(x_39, 0, x_34);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_36);
lean_ctor_set(x_40, 1, x_39);
lean_ctor_set(x_18, 0, x_40);
return x_18;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_41 = lean_ctor_get(x_18, 1);
lean_inc(x_41);
lean_dec(x_18);
x_42 = lean_ctor_get(x_19, 0);
lean_inc(x_42);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_43 = x_19;
} else {
 lean_dec_ref(x_19);
 x_43 = lean_box(0);
}
x_44 = lean_ctor_get(x_20, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_20, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_46 = x_20;
} else {
 lean_dec_ref(x_20);
 x_46 = lean_box(0);
}
x_47 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___lam__0___boxed), 2, 1);
lean_closure_set(x_47, 0, x_44);
if (lean_is_scalar(x_46)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_46;
}
lean_ctor_set(x_48, 0, x_42);
lean_ctor_set(x_48, 1, x_47);
if (lean_is_scalar(x_43)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_43;
}
lean_ctor_set(x_49, 0, x_45);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_41);
return x_50;
}
}
else
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_18);
if (x_51 == 0)
{
return x_18;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_18, 0);
x_53 = lean_ctor_get(x_18, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_18);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
block_67:
{
size_t x_57; lean_object* x_58; size_t x_59; lean_object* x_60; 
x_57 = lean_array_size(x_56);
x_58 = lean_unsigned_to_nat(0u);
x_59 = lean_usize_of_nat(x_58);
x_60 = l_Array_mapMUnsafe_map___at___Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__2(x_57, x_59, x_56);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; uint8_t x_62; 
x_61 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_2, x_3, x_4);
x_62 = !lean_is_exclusive(x_61);
if (x_62 == 0)
{
return x_61;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_61, 0);
x_64 = lean_ctor_get(x_61, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_61);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
else
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_60, 0);
lean_inc(x_66);
lean_dec(x_60);
x_5 = x_66;
x_6 = x_2;
x_7 = x_3;
x_8 = x_4;
goto block_55;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0_spec__0___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0_spec__0___lam__0(x_5, x_6, x_3, x_4);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0_spec__0___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0_spec__0___lam__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0_spec__0(x_1, x_8, x_9, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0(x_1, x_8, x_9, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__2(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___lam__0(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardMsgs_instImpl____x40_Lean_Elab_GuardMsgs___hyg_1820_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Elab", 4, 4);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("GuardMsgs", 9, 9);
x_5 = lean_mk_string_unchecked("GuardMsgFailure", 15, 15);
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardMsgs_instTypeNameGuardMsgFailure() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Tactic_GuardMsgs_instImpl____x40_Lean_Elab_GuardMsgs___hyg_1820_;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_2 = lean_mk_string_unchecked("⏎\n", 4, 2);
x_3 = lean_mk_string_unchecked("⏎⏎\n", 7, 3);
x_4 = l_String_replace(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_mk_string_unchecked("\t\n", 2, 2);
x_6 = lean_mk_string_unchecked("\t⏎\n", 5, 3);
x_7 = l_String_replace(x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_8 = lean_mk_string_unchecked(" \n", 2, 2);
x_9 = lean_mk_string_unchecked(" ⏎\n", 5, 3);
x_10 = l_String_replace(x_7, x_8, x_9);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_removeTrailingWhitespaceMarker(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_mk_string_unchecked("⏎\n", 4, 2);
x_3 = lean_mk_string_unchecked("\n", 1, 1);
x_4 = l_String_replace(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_removeTrailingWhitespaceMarker___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Tactic_GuardMsgs_removeTrailingWhitespaceMarker(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_splitAux___at___String_split___at___Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_10; uint8_t x_14; 
x_14 = lean_string_utf8_at_end(x_1, x_3);
if (x_14 == 0)
{
uint32_t x_15; uint8_t x_16; lean_object* x_24; uint32_t x_25; uint8_t x_26; 
x_15 = lean_string_utf8_get(x_1, x_3);
x_24 = lean_unsigned_to_nat(32u);
x_25 = l_Char_ofNat(x_24);
x_26 = l_instDecidableEqChar(x_15, x_25);
if (x_26 == 0)
{
lean_object* x_27; uint32_t x_28; uint8_t x_29; 
x_27 = lean_unsigned_to_nat(9u);
x_28 = l_Char_ofNat(x_27);
x_29 = l_instDecidableEqChar(x_15, x_28);
x_16 = x_29;
goto block_23;
}
else
{
x_16 = x_26;
goto block_23;
}
block_23:
{
if (x_16 == 0)
{
lean_object* x_17; uint32_t x_18; uint8_t x_19; 
x_17 = lean_unsigned_to_nat(13u);
x_18 = l_Char_ofNat(x_17);
x_19 = l_instDecidableEqChar(x_15, x_18);
if (x_19 == 0)
{
lean_object* x_20; uint32_t x_21; uint8_t x_22; 
x_20 = lean_unsigned_to_nat(10u);
x_21 = l_Char_ofNat(x_20);
x_22 = l_instDecidableEqChar(x_15, x_21);
x_10 = x_22;
goto block_13;
}
else
{
x_10 = x_19;
goto block_13;
}
}
else
{
goto block_9;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_string_utf8_extract(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_4);
x_32 = l_List_reverse___redArg(x_31);
return x_32;
}
block_9:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_string_utf8_next(x_1, x_3);
x_6 = lean_string_utf8_extract(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
lean_inc(x_5);
x_2 = x_5;
x_3 = x_5;
x_4 = x_7;
goto _start;
}
block_13:
{
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_string_utf8_next(x_1, x_3);
lean_dec(x_3);
x_3 = x_11;
goto _start;
}
else
{
goto block_9;
}
}
}
}
LEAN_EXPORT lean_object* l_String_split___at___Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_box(0);
x_4 = l_String_splitAux___at___String_split___at___Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0_spec__0(x_1, x_2, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___redArg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_string_utf8_byte_size(x_5);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_instDecidableEqPos(x_7, x_8);
lean_dec(x_7);
if (x_9 == 0)
{
lean_ctor_set(x_1, 1, x_2);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_free_object(x_1);
lean_dec(x_5);
x_1 = x_6;
goto _start;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_1);
x_14 = lean_string_utf8_byte_size(x_12);
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_instDecidableEqPos(x_14, x_15);
lean_dec(x_14);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_12);
lean_ctor_set(x_17, 1, x_2);
x_1 = x_13;
x_2 = x_17;
goto _start;
}
else
{
lean_dec(x_12);
x_1 = x_13;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply(uint8_t x_1, lean_object* x_2) {
_start:
{
switch (x_1) {
case 0:
{
lean_inc(x_2);
return x_2;
}
case 1:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_mk_string_unchecked("\n", 1, 1);
x_4 = lean_mk_string_unchecked(" ", 1, 1);
x_5 = l_String_replace(x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
default: 
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_mk_string_unchecked(" ", 1, 1);
x_7 = l_String_split___at___Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0(x_2);
x_8 = lean_box(0);
x_9 = l_List_filterTR_loop___at___Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__2(x_7, x_8);
x_10 = l_String_intercalate(x_6, x_9);
lean_dec(x_6);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_String_splitAux___at___String_split___at___Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_String_splitAux___at___String_split___at___Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_split___at___Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_split___at___Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply(uint8_t x_1, lean_object* x_2) {
_start:
{
if (x_1 == 0)
{
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_array_mk(x_2);
x_4 = lean_array_get_size(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_13; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_4, x_7);
lean_dec(x_4);
x_13 = lean_nat_dec_le(x_5, x_8);
if (x_13 == 0)
{
lean_inc(x_8);
x_9 = x_8;
goto block_12;
}
else
{
x_9 = x_5;
goto block_12;
}
block_12:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Array_qsort_sort___at___Lean_Parser_Error_toString_spec__1___redArg(x_3, x_9, x_8);
lean_dec(x_8);
x_11 = lean_array_to_list(x_10);
return x_11;
}
}
else
{
lean_object* x_14; 
lean_dec(x_4);
x_14 = lean_array_to_list(x_3);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_MessageLog_append(x_4, x_8);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_usize_of_nat(x_10);
x_12 = lean_usize_add(x_2, x_11);
x_2 = x_12;
x_4 = x_9;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Substring_takeWhileAux___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_mk_string_unchecked("Lean", 4, 4);
x_10 = lean_mk_string_unchecked("guardMsgsCmd", 12, 12);
x_11 = lean_nat_dec_lt(x_4, x_3);
if (x_11 == 0)
{
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
return x_4;
}
else
{
lean_object* x_12; uint8_t x_13; uint32_t x_14; uint8_t x_15; uint8_t x_20; lean_object* x_25; uint32_t x_26; uint8_t x_27; 
x_12 = l_Lean_Name_mkStr2(x_9, x_10);
lean_inc(x_1);
x_13 = l_Lean_Syntax_isOfKind(x_1, x_12);
lean_dec(x_12);
x_14 = lean_string_utf8_get(x_2, x_4);
x_25 = lean_unsigned_to_nat(32u);
x_26 = l_Char_ofNat(x_25);
x_27 = l_instDecidableEqChar(x_14, x_26);
if (x_27 == 0)
{
lean_object* x_28; uint32_t x_29; uint8_t x_30; 
x_28 = lean_unsigned_to_nat(9u);
x_29 = l_Char_ofNat(x_28);
x_30 = l_instDecidableEqChar(x_14, x_29);
x_20 = x_30;
goto block_24;
}
else
{
x_20 = x_13;
goto block_24;
}
block_19:
{
if (x_15 == 0)
{
lean_object* x_16; uint32_t x_17; uint8_t x_18; 
x_16 = lean_unsigned_to_nat(10u);
x_17 = l_Char_ofNat(x_16);
x_18 = l_instDecidableEqChar(x_14, x_17);
x_5 = x_18;
goto block_8;
}
else
{
x_5 = x_13;
goto block_8;
}
}
block_24:
{
if (x_20 == 0)
{
lean_object* x_21; uint32_t x_22; uint8_t x_23; 
x_21 = lean_unsigned_to_nat(13u);
x_22 = l_Char_ofNat(x_21);
x_23 = l_instDecidableEqChar(x_14, x_22);
x_15 = x_23;
goto block_19;
}
else
{
x_15 = x_13;
goto block_19;
}
}
}
block_8:
{
if (x_5 == 0)
{
lean_dec(x_1);
return x_4;
}
else
{
lean_object* x_6; 
x_6 = lean_string_utf8_next(x_2, x_4);
lean_dec(x_4);
x_4 = x_6;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_takeRightWhileAux___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_mk_string_unchecked("Lean", 4, 4);
x_6 = lean_mk_string_unchecked("guardMsgsCmd", 12, 12);
x_7 = lean_nat_dec_lt(x_3, x_4);
if (x_7 == 0)
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_4;
}
else
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; uint8_t x_11; uint32_t x_14; uint8_t x_15; uint8_t x_20; lean_object* x_25; uint32_t x_26; uint8_t x_27; 
x_8 = l_Lean_Name_mkStr2(x_5, x_6);
lean_inc(x_1);
x_9 = l_Lean_Syntax_isOfKind(x_1, x_8);
lean_dec(x_8);
x_10 = lean_string_utf8_prev(x_2, x_4);
x_14 = lean_string_utf8_get(x_2, x_10);
x_25 = lean_unsigned_to_nat(32u);
x_26 = l_Char_ofNat(x_25);
x_27 = l_instDecidableEqChar(x_14, x_26);
if (x_27 == 0)
{
lean_object* x_28; uint32_t x_29; uint8_t x_30; 
x_28 = lean_unsigned_to_nat(9u);
x_29 = l_Char_ofNat(x_28);
x_30 = l_instDecidableEqChar(x_14, x_29);
x_20 = x_30;
goto block_24;
}
else
{
x_20 = x_9;
goto block_24;
}
block_13:
{
if (x_11 == 0)
{
lean_dec(x_10);
lean_dec(x_1);
return x_4;
}
else
{
lean_dec(x_4);
x_4 = x_10;
goto _start;
}
}
block_19:
{
if (x_15 == 0)
{
lean_object* x_16; uint32_t x_17; uint8_t x_18; 
x_16 = lean_unsigned_to_nat(10u);
x_17 = l_Char_ofNat(x_16);
x_18 = l_instDecidableEqChar(x_14, x_17);
x_11 = x_18;
goto block_13;
}
else
{
x_11 = x_9;
goto block_13;
}
}
block_24:
{
if (x_20 == 0)
{
lean_object* x_21; uint32_t x_22; uint8_t x_23; 
x_21 = lean_unsigned_to_nat(13u);
x_22 = l_Char_ofNat(x_21);
x_23 = l_instDecidableEqChar(x_14, x_22);
x_15 = x_23;
goto block_19;
}
else
{
x_15 = x_9;
goto block_19;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; 
lean_dec(x_1);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_ctor_get_uint8(x_6, sizeof(void*)*5 + 2);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_2);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_9 = lean_ctor_get(x_2, 1);
x_10 = lean_ctor_get(x_2, 0);
lean_dec(x_10);
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_dec(x_3);
lean_inc(x_1);
lean_inc(x_6);
x_13 = lean_apply_1(x_1, x_6);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
switch (x_14) {
case 0:
{
lean_object* x_15; 
x_15 = l_Lean_MessageLog_add(x_6, x_11);
lean_ctor_set_tag(x_2, 0);
lean_ctor_set(x_2, 1, x_12);
lean_ctor_set(x_2, 0, x_15);
{
lean_object* _tmp_1 = x_9;
lean_object* _tmp_2 = x_2;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
case 1:
{
lean_dec(x_6);
lean_ctor_set_tag(x_2, 0);
lean_ctor_set(x_2, 1, x_12);
lean_ctor_set(x_2, 0, x_11);
{
lean_object* _tmp_1 = x_9;
lean_object* _tmp_2 = x_2;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
default: 
{
lean_object* x_18; 
x_18 = l_Lean_MessageLog_add(x_6, x_12);
lean_ctor_set_tag(x_2, 0);
lean_ctor_set(x_2, 1, x_18);
lean_ctor_set(x_2, 0, x_11);
{
lean_object* _tmp_1 = x_9;
lean_object* _tmp_2 = x_2;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_20 = lean_ctor_get(x_2, 1);
lean_inc(x_20);
lean_dec(x_2);
x_21 = lean_ctor_get(x_3, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_3, 1);
lean_inc(x_22);
lean_dec(x_3);
lean_inc(x_1);
lean_inc(x_6);
x_23 = lean_apply_1(x_1, x_6);
x_24 = lean_unbox(x_23);
lean_dec(x_23);
switch (x_24) {
case 0:
{
lean_object* x_25; lean_object* x_26; 
x_25 = l_Lean_MessageLog_add(x_6, x_21);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_22);
x_2 = x_20;
x_3 = x_26;
goto _start;
}
case 1:
{
lean_object* x_28; 
lean_dec(x_6);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_21);
lean_ctor_set(x_28, 1, x_22);
x_2 = x_20;
x_3 = x_28;
goto _start;
}
default: 
{
lean_object* x_30; lean_object* x_31; 
x_30 = l_Lean_MessageLog_add(x_6, x_22);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_21);
lean_ctor_set(x_31, 1, x_30);
x_2 = x_20;
x_3 = x_31;
goto _start;
}
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_6);
x_33 = !lean_is_exclusive(x_2);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_2, 1);
x_35 = lean_ctor_get(x_2, 0);
lean_dec(x_35);
x_36 = lean_ctor_get(x_3, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_3, 1);
lean_inc(x_37);
lean_dec(x_3);
lean_ctor_set_tag(x_2, 0);
lean_ctor_set(x_2, 1, x_37);
lean_ctor_set(x_2, 0, x_36);
{
lean_object* _tmp_1 = x_34;
lean_object* _tmp_2 = x_2;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_ctor_get(x_2, 1);
lean_inc(x_39);
lean_dec(x_2);
x_40 = lean_ctor_get(x_3, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_3, 1);
lean_inc(x_41);
lean_dec(x_3);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_2 = x_39;
x_3 = x_42;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_List_forIn_x27_loop___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___redArg(x_1, x_3, x_4, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_List_reverse___redArg(x_2);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
x_9 = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToStringWithoutPos(x_7, x_3);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_10);
{
lean_object* _tmp_0 = x_8;
lean_object* _tmp_1 = x_1;
lean_object* _tmp_2 = x_11;
x_1 = _tmp_0;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_1);
x_15 = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToStringWithoutPos(x_13, x_3);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_2);
x_1 = x_14;
x_2 = x_18;
x_3 = x_17;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_List_mapM_loop___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__4___redArg(x_1, x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_matchPrefix_go___at___Lean_Diff_matchPrefix___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__5_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_10; uint8_t x_11; 
x_4 = lean_array_get_size(x_3);
x_10 = l_Subarray_size___redArg(x_1);
x_11 = lean_nat_dec_lt(x_4, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
goto block_9;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = l_Subarray_size___redArg(x_2);
x_13 = lean_nat_dec_lt(x_4, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
goto block_9;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = l_Subarray_get___redArg(x_1, x_4);
x_15 = l_Subarray_get___redArg(x_2, x_4);
x_16 = lean_string_dec_eq(x_14, x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_14);
x_17 = l_Subarray_drop(lean_box(0), x_1, x_4);
x_18 = l_Subarray_drop(lean_box(0), x_2, x_4);
lean_dec(x_4);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_3);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
else
{
lean_object* x_21; 
lean_dec(x_4);
x_21 = lean_array_push(x_3, x_14);
x_3 = x_21;
goto _start;
}
}
}
block_9:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = l_Subarray_drop(lean_box(0), x_1, x_4);
x_6 = l_Subarray_drop(lean_box(0), x_2, x_4);
lean_dec(x_4);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_matchPrefix___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_mk_empty_array_with_capacity(x_3);
x_5 = l_Lean_Diff_matchPrefix_go___at___Lean_Diff_matchPrefix___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__5_spec__5(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_matchSuffix_go___at___Lean_Diff_matchSuffix___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__7_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_15; 
x_4 = l_Subarray_size___redArg(x_1);
x_15 = lean_nat_dec_lt(x_3, x_4);
if (x_15 == 0)
{
goto block_14;
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = l_Subarray_size___redArg(x_2);
x_17 = lean_nat_dec_lt(x_3, x_16);
if (x_17 == 0)
{
lean_dec(x_16);
goto block_14;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_18 = lean_nat_sub(x_4, x_3);
lean_dec(x_4);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_sub(x_18, x_19);
x_21 = l_Subarray_get___redArg(x_1, x_20);
lean_dec(x_20);
x_22 = lean_nat_sub(x_16, x_3);
lean_dec(x_16);
x_23 = lean_nat_sub(x_22, x_19);
x_24 = l_Subarray_get___redArg(x_2, x_23);
lean_dec(x_23);
x_25 = lean_string_dec_eq(x_21, x_24);
lean_dec(x_24);
lean_dec(x_21);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_3);
x_26 = l_Subarray_take(lean_box(0), x_1, x_18);
x_27 = l_Subarray_take(lean_box(0), x_2, x_22);
lean_dec(x_22);
x_28 = l_Subarray_drop(lean_box(0), x_1, x_18);
lean_dec(x_18);
x_29 = l_Array_ofSubarray___redArg(x_28);
lean_dec(x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_27);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_26);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_22);
lean_dec(x_18);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_add(x_3, x_32);
lean_dec(x_3);
x_3 = x_33;
goto _start;
}
}
}
block_14:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_5 = lean_nat_sub(x_4, x_3);
lean_dec(x_4);
x_6 = l_Subarray_take(lean_box(0), x_1, x_5);
x_7 = l_Subarray_size___redArg(x_2);
x_8 = lean_nat_sub(x_7, x_3);
lean_dec(x_3);
lean_dec(x_7);
x_9 = l_Subarray_take(lean_box(0), x_2, x_8);
lean_dec(x_8);
x_10 = l_Subarray_drop(lean_box(0), x_1, x_5);
lean_dec(x_5);
x_11 = l_Array_ofSubarray___redArg(x_10);
lean_dec(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_matchSuffix___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__7(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Lean_Diff_matchSuffix_go___at___Lean_Diff_matchSuffix___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__7_spec__7(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Diff_Histogram_addLeft___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__9_spec__9___redArg(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_string_dec_eq(x_4, x_1);
if (x_7 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_9; 
lean_inc(x_5);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_5);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Diff_Histogram_addLeft___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__9_spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Diff_Histogram_addLeft___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__9_spec__9___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Diff_Histogram_addLeft___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__9_spec__10___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_box(0);
x_4 = lean_unbox(x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_string_dec_eq(x_5, x_1);
if (x_7 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
return x_7;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Diff_Histogram_addLeft___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__9_spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Diff_Histogram_addLeft___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__9_spec__10___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Diff_Histogram_addLeft___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__9_spec__11_spec__11_spec__11___redArg(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; lean_object* x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; lean_object* x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; size_t x_16; size_t x_17; lean_object* x_18; size_t x_19; size_t x_20; size_t x_21; lean_object* x_22; lean_object* x_23; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = lean_string_hash(x_4);
x_8 = lean_unsigned_to_nat(32u);
x_9 = lean_uint64_of_nat(x_8);
x_10 = lean_uint64_shift_right(x_7, x_9);
x_11 = lean_uint64_xor(x_7, x_10);
x_12 = lean_unsigned_to_nat(16u);
x_13 = lean_uint64_of_nat(x_12);
x_14 = lean_uint64_shift_right(x_11, x_13);
x_15 = lean_uint64_xor(x_11, x_14);
x_16 = lean_uint64_to_usize(x_15);
x_17 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_usize_of_nat(x_18);
x_20 = lean_usize_sub(x_17, x_19);
x_21 = lean_usize_land(x_16, x_20);
x_22 = lean_array_uget(x_1, x_21);
lean_ctor_set(x_2, 2, x_22);
x_23 = lean_array_uset(x_1, x_21, x_2);
x_1 = x_23;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint64_t x_29; lean_object* x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; lean_object* x_34; uint64_t x_35; uint64_t x_36; uint64_t x_37; size_t x_38; size_t x_39; lean_object* x_40; size_t x_41; size_t x_42; size_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_25 = lean_ctor_get(x_2, 0);
x_26 = lean_ctor_get(x_2, 1);
x_27 = lean_ctor_get(x_2, 2);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_2);
x_28 = lean_array_get_size(x_1);
x_29 = lean_string_hash(x_25);
x_30 = lean_unsigned_to_nat(32u);
x_31 = lean_uint64_of_nat(x_30);
x_32 = lean_uint64_shift_right(x_29, x_31);
x_33 = lean_uint64_xor(x_29, x_32);
x_34 = lean_unsigned_to_nat(16u);
x_35 = lean_uint64_of_nat(x_34);
x_36 = lean_uint64_shift_right(x_33, x_35);
x_37 = lean_uint64_xor(x_33, x_36);
x_38 = lean_uint64_to_usize(x_37);
x_39 = lean_usize_of_nat(x_28);
lean_dec(x_28);
x_40 = lean_unsigned_to_nat(1u);
x_41 = lean_usize_of_nat(x_40);
x_42 = lean_usize_sub(x_39, x_41);
x_43 = lean_usize_land(x_38, x_42);
x_44 = lean_array_uget(x_1, x_43);
x_45 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_45, 0, x_25);
lean_ctor_set(x_45, 1, x_26);
lean_ctor_set(x_45, 2, x_44);
x_46 = lean_array_uset(x_1, x_43, x_45);
x_1 = x_46;
x_2 = x_27;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Diff_Histogram_addLeft___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__9_spec__11_spec__11_spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Diff_Histogram_addLeft___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__9_spec__11_spec__11_spec__11___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Diff_Histogram_addLeft___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__9_spec__11_spec__11___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Diff_Histogram_addLeft___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__9_spec__11_spec__11_spec__11___redArg(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Diff_Histogram_addLeft___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__9_spec__11_spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Diff_Histogram_addLeft___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__9_spec__11_spec__11___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Diff_Histogram_addLeft___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__9_spec__11___redArg(lean_object* x_1) {
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
x_8 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Diff_Histogram_addLeft___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__9_spec__11_spec__11___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Diff_Histogram_addLeft___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__9_spec__11(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Diff_Histogram_addLeft___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__9_spec__11___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Diff_Histogram_addLeft___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__9_spec__14___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_3, 2);
x_8 = lean_string_dec_eq(x_5, x_1);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Diff_Histogram_addLeft___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__9_spec__14___redArg(x_1, x_2, x_7);
lean_ctor_set(x_3, 2, x_9);
return x_3;
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
x_12 = lean_ctor_get(x_3, 2);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
x_13 = lean_string_dec_eq(x_10, x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Diff_Histogram_addLeft___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__9_spec__14___redArg(x_1, x_2, x_12);
x_15 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_11);
lean_ctor_set(x_15, 2, x_14);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_10);
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_2);
lean_ctor_set(x_16, 2, x_12);
return x_16;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Diff_Histogram_addLeft___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__9_spec__14(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Diff_Histogram_addLeft___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__9_spec__14___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__9___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; lean_object* x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; lean_object* x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; size_t x_17; size_t x_18; lean_object* x_19; size_t x_20; size_t x_21; size_t x_22; lean_object* x_23; lean_object* x_24; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = lean_string_hash(x_3);
x_9 = lean_unsigned_to_nat(32u);
x_10 = lean_uint64_of_nat(x_9);
x_11 = lean_uint64_shift_right(x_8, x_10);
x_12 = lean_uint64_xor(x_8, x_11);
x_13 = lean_unsigned_to_nat(16u);
x_14 = lean_uint64_of_nat(x_13);
x_15 = lean_uint64_shift_right(x_12, x_14);
x_16 = lean_uint64_xor(x_12, x_15);
x_17 = lean_uint64_to_usize(x_16);
x_18 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_usize_of_nat(x_19);
x_21 = lean_usize_sub(x_18, x_20);
x_22 = lean_usize_land(x_17, x_21);
x_23 = lean_array_uget(x_6, x_22);
x_24 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Diff_Histogram_addLeft___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__9_spec__9___redArg(x_3, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_2);
x_26 = lean_unsigned_to_nat(0u);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_28, 0, x_19);
lean_ctor_set(x_28, 1, x_25);
lean_ctor_set(x_28, 2, x_26);
lean_ctor_set(x_28, 3, x_27);
x_29 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Diff_Histogram_addLeft___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__9_spec__10___redArg(x_3, x_23);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_30 = lean_nat_add(x_5, x_19);
lean_dec(x_5);
x_31 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_31, 0, x_3);
lean_ctor_set(x_31, 1, x_28);
lean_ctor_set(x_31, 2, x_23);
x_32 = lean_array_uset(x_6, x_22, x_31);
x_33 = lean_unsigned_to_nat(2u);
x_34 = lean_nat_shiftl(x_30, x_33);
x_35 = lean_unsigned_to_nat(3u);
x_36 = lean_nat_div(x_34, x_35);
lean_dec(x_34);
x_37 = lean_array_get_size(x_32);
x_38 = lean_nat_dec_le(x_36, x_37);
lean_dec(x_37);
lean_dec(x_36);
if (x_38 == 0)
{
lean_object* x_39; 
x_39 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Diff_Histogram_addLeft___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__9_spec__11___redArg(x_32);
lean_ctor_set(x_1, 1, x_39);
lean_ctor_set(x_1, 0, x_30);
return x_1;
}
else
{
lean_ctor_set(x_1, 1, x_32);
lean_ctor_set(x_1, 0, x_30);
return x_1;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_box(0);
x_41 = lean_array_uset(x_6, x_22, x_40);
x_42 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Diff_Histogram_addLeft___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__9_spec__14___redArg(x_3, x_28, x_23);
x_43 = lean_array_uset(x_41, x_22, x_42);
lean_ctor_set(x_1, 1, x_43);
return x_1;
}
}
else
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_24);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_45 = lean_ctor_get(x_24, 0);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_nat_add(x_46, x_19);
lean_dec(x_46);
lean_ctor_set(x_24, 0, x_2);
x_48 = lean_ctor_get(x_45, 2);
lean_inc(x_48);
x_49 = lean_ctor_get(x_45, 3);
lean_inc(x_49);
lean_dec(x_45);
x_50 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_24);
lean_ctor_set(x_50, 2, x_48);
lean_ctor_set(x_50, 3, x_49);
x_51 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Diff_Histogram_addLeft___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__9_spec__10___redArg(x_3, x_23);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_52 = lean_nat_add(x_5, x_19);
lean_dec(x_5);
x_53 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_53, 0, x_3);
lean_ctor_set(x_53, 1, x_50);
lean_ctor_set(x_53, 2, x_23);
x_54 = lean_array_uset(x_6, x_22, x_53);
x_55 = lean_unsigned_to_nat(2u);
x_56 = lean_nat_shiftl(x_52, x_55);
x_57 = lean_unsigned_to_nat(3u);
x_58 = lean_nat_div(x_56, x_57);
lean_dec(x_56);
x_59 = lean_array_get_size(x_54);
x_60 = lean_nat_dec_le(x_58, x_59);
lean_dec(x_59);
lean_dec(x_58);
if (x_60 == 0)
{
lean_object* x_61; 
x_61 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Diff_Histogram_addLeft___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__9_spec__11___redArg(x_54);
lean_ctor_set(x_1, 1, x_61);
lean_ctor_set(x_1, 0, x_52);
return x_1;
}
else
{
lean_ctor_set(x_1, 1, x_54);
lean_ctor_set(x_1, 0, x_52);
return x_1;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_62 = lean_box(0);
x_63 = lean_array_uset(x_6, x_22, x_62);
x_64 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Diff_Histogram_addLeft___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__9_spec__14___redArg(x_3, x_50, x_23);
x_65 = lean_array_uset(x_63, x_22, x_64);
lean_ctor_set(x_1, 1, x_65);
return x_1;
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_66 = lean_ctor_get(x_24, 0);
lean_inc(x_66);
lean_dec(x_24);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_nat_add(x_67, x_19);
lean_dec(x_67);
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_2);
x_70 = lean_ctor_get(x_66, 2);
lean_inc(x_70);
x_71 = lean_ctor_get(x_66, 3);
lean_inc(x_71);
lean_dec(x_66);
x_72 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_72, 0, x_68);
lean_ctor_set(x_72, 1, x_69);
lean_ctor_set(x_72, 2, x_70);
lean_ctor_set(x_72, 3, x_71);
x_73 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Diff_Histogram_addLeft___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__9_spec__10___redArg(x_3, x_23);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_74 = lean_nat_add(x_5, x_19);
lean_dec(x_5);
x_75 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_75, 0, x_3);
lean_ctor_set(x_75, 1, x_72);
lean_ctor_set(x_75, 2, x_23);
x_76 = lean_array_uset(x_6, x_22, x_75);
x_77 = lean_unsigned_to_nat(2u);
x_78 = lean_nat_shiftl(x_74, x_77);
x_79 = lean_unsigned_to_nat(3u);
x_80 = lean_nat_div(x_78, x_79);
lean_dec(x_78);
x_81 = lean_array_get_size(x_76);
x_82 = lean_nat_dec_le(x_80, x_81);
lean_dec(x_81);
lean_dec(x_80);
if (x_82 == 0)
{
lean_object* x_83; 
x_83 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Diff_Histogram_addLeft___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__9_spec__11___redArg(x_76);
lean_ctor_set(x_1, 1, x_83);
lean_ctor_set(x_1, 0, x_74);
return x_1;
}
else
{
lean_ctor_set(x_1, 1, x_76);
lean_ctor_set(x_1, 0, x_74);
return x_1;
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_84 = lean_box(0);
x_85 = lean_array_uset(x_6, x_22, x_84);
x_86 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Diff_Histogram_addLeft___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__9_spec__14___redArg(x_3, x_72, x_23);
x_87 = lean_array_uset(x_85, x_22, x_86);
lean_ctor_set(x_1, 1, x_87);
return x_1;
}
}
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; uint64_t x_91; lean_object* x_92; uint64_t x_93; uint64_t x_94; uint64_t x_95; lean_object* x_96; uint64_t x_97; uint64_t x_98; uint64_t x_99; size_t x_100; size_t x_101; lean_object* x_102; size_t x_103; size_t x_104; size_t x_105; lean_object* x_106; lean_object* x_107; 
x_88 = lean_ctor_get(x_1, 0);
x_89 = lean_ctor_get(x_1, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_1);
x_90 = lean_array_get_size(x_89);
x_91 = lean_string_hash(x_3);
x_92 = lean_unsigned_to_nat(32u);
x_93 = lean_uint64_of_nat(x_92);
x_94 = lean_uint64_shift_right(x_91, x_93);
x_95 = lean_uint64_xor(x_91, x_94);
x_96 = lean_unsigned_to_nat(16u);
x_97 = lean_uint64_of_nat(x_96);
x_98 = lean_uint64_shift_right(x_95, x_97);
x_99 = lean_uint64_xor(x_95, x_98);
x_100 = lean_uint64_to_usize(x_99);
x_101 = lean_usize_of_nat(x_90);
lean_dec(x_90);
x_102 = lean_unsigned_to_nat(1u);
x_103 = lean_usize_of_nat(x_102);
x_104 = lean_usize_sub(x_101, x_103);
x_105 = lean_usize_land(x_100, x_104);
x_106 = lean_array_uget(x_89, x_105);
x_107 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Diff_Histogram_addLeft___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__9_spec__9___redArg(x_3, x_106);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; 
x_108 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_108, 0, x_2);
x_109 = lean_unsigned_to_nat(0u);
x_110 = lean_box(0);
x_111 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_111, 0, x_102);
lean_ctor_set(x_111, 1, x_108);
lean_ctor_set(x_111, 2, x_109);
lean_ctor_set(x_111, 3, x_110);
x_112 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Diff_Histogram_addLeft___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__9_spec__10___redArg(x_3, x_106);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; 
x_113 = lean_nat_add(x_88, x_102);
lean_dec(x_88);
x_114 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_114, 0, x_3);
lean_ctor_set(x_114, 1, x_111);
lean_ctor_set(x_114, 2, x_106);
x_115 = lean_array_uset(x_89, x_105, x_114);
x_116 = lean_unsigned_to_nat(2u);
x_117 = lean_nat_shiftl(x_113, x_116);
x_118 = lean_unsigned_to_nat(3u);
x_119 = lean_nat_div(x_117, x_118);
lean_dec(x_117);
x_120 = lean_array_get_size(x_115);
x_121 = lean_nat_dec_le(x_119, x_120);
lean_dec(x_120);
lean_dec(x_119);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; 
x_122 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Diff_Histogram_addLeft___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__9_spec__11___redArg(x_115);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_113);
lean_ctor_set(x_123, 1, x_122);
return x_123;
}
else
{
lean_object* x_124; 
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_113);
lean_ctor_set(x_124, 1, x_115);
return x_124;
}
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_125 = lean_box(0);
x_126 = lean_array_uset(x_89, x_105, x_125);
x_127 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Diff_Histogram_addLeft___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__9_spec__14___redArg(x_3, x_111, x_106);
x_128 = lean_array_uset(x_126, x_105, x_127);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_88);
lean_ctor_set(x_129, 1, x_128);
return x_129;
}
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; 
x_130 = lean_ctor_get(x_107, 0);
lean_inc(x_130);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 x_131 = x_107;
} else {
 lean_dec_ref(x_107);
 x_131 = lean_box(0);
}
x_132 = lean_ctor_get(x_130, 0);
lean_inc(x_132);
x_133 = lean_nat_add(x_132, x_102);
lean_dec(x_132);
if (lean_is_scalar(x_131)) {
 x_134 = lean_alloc_ctor(1, 1, 0);
} else {
 x_134 = x_131;
}
lean_ctor_set(x_134, 0, x_2);
x_135 = lean_ctor_get(x_130, 2);
lean_inc(x_135);
x_136 = lean_ctor_get(x_130, 3);
lean_inc(x_136);
lean_dec(x_130);
x_137 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_137, 0, x_133);
lean_ctor_set(x_137, 1, x_134);
lean_ctor_set(x_137, 2, x_135);
lean_ctor_set(x_137, 3, x_136);
x_138 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Diff_Histogram_addLeft___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__9_spec__10___redArg(x_3, x_106);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; 
x_139 = lean_nat_add(x_88, x_102);
lean_dec(x_88);
x_140 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_140, 0, x_3);
lean_ctor_set(x_140, 1, x_137);
lean_ctor_set(x_140, 2, x_106);
x_141 = lean_array_uset(x_89, x_105, x_140);
x_142 = lean_unsigned_to_nat(2u);
x_143 = lean_nat_shiftl(x_139, x_142);
x_144 = lean_unsigned_to_nat(3u);
x_145 = lean_nat_div(x_143, x_144);
lean_dec(x_143);
x_146 = lean_array_get_size(x_141);
x_147 = lean_nat_dec_le(x_145, x_146);
lean_dec(x_146);
lean_dec(x_145);
if (x_147 == 0)
{
lean_object* x_148; lean_object* x_149; 
x_148 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Diff_Histogram_addLeft___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__9_spec__11___redArg(x_141);
x_149 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_149, 0, x_139);
lean_ctor_set(x_149, 1, x_148);
return x_149;
}
else
{
lean_object* x_150; 
x_150 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_150, 0, x_139);
lean_ctor_set(x_150, 1, x_141);
return x_150;
}
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_151 = lean_box(0);
x_152 = lean_array_uset(x_89, x_105, x_151);
x_153 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Diff_Histogram_addLeft___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__9_spec__14___redArg(x_3, x_137, x_106);
x_154 = lean_array_uset(x_152, x_105, x_153);
x_155 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_155, 0, x_88);
lean_ctor_set(x_155, 1, x_154);
return x_155;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Diff_Histogram_addLeft___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__9___redArg(x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__16___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_nat_dec_lt(x_6, x_7);
if (x_8 == 0)
{
lean_dec(x_6);
return x_5;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = l_Subarray_get___redArg(x_3, x_6);
lean_inc(x_6);
x_10 = l_Lean_Diff_Histogram_addLeft___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__9___redArg(x_5, x_6, x_9);
x_11 = lean_ctor_get(x_4, 2);
x_12 = lean_nat_add(x_6, x_11);
lean_dec(x_6);
x_5 = x_10;
x_6 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__16(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_Range_forIn_x27_loop___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__16___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__17___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; lean_object* x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; lean_object* x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; size_t x_17; size_t x_18; lean_object* x_19; size_t x_20; size_t x_21; size_t x_22; lean_object* x_23; lean_object* x_24; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = lean_string_hash(x_3);
x_9 = lean_unsigned_to_nat(32u);
x_10 = lean_uint64_of_nat(x_9);
x_11 = lean_uint64_shift_right(x_8, x_10);
x_12 = lean_uint64_xor(x_8, x_11);
x_13 = lean_unsigned_to_nat(16u);
x_14 = lean_uint64_of_nat(x_13);
x_15 = lean_uint64_shift_right(x_12, x_14);
x_16 = lean_uint64_xor(x_12, x_15);
x_17 = lean_uint64_to_usize(x_16);
x_18 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_usize_of_nat(x_19);
x_21 = lean_usize_sub(x_18, x_20);
x_22 = lean_usize_land(x_17, x_21);
x_23 = lean_array_uget(x_6, x_22);
x_24 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Diff_Histogram_addLeft___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__9_spec__9___redArg(x_3, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_25 = lean_unsigned_to_nat(0u);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_2);
x_28 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_26);
lean_ctor_set(x_28, 2, x_19);
lean_ctor_set(x_28, 3, x_27);
x_29 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Diff_Histogram_addLeft___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__9_spec__10___redArg(x_3, x_23);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_30 = lean_nat_add(x_5, x_19);
lean_dec(x_5);
x_31 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_31, 0, x_3);
lean_ctor_set(x_31, 1, x_28);
lean_ctor_set(x_31, 2, x_23);
x_32 = lean_array_uset(x_6, x_22, x_31);
x_33 = lean_unsigned_to_nat(2u);
x_34 = lean_nat_shiftl(x_30, x_33);
x_35 = lean_unsigned_to_nat(3u);
x_36 = lean_nat_div(x_34, x_35);
lean_dec(x_34);
x_37 = lean_array_get_size(x_32);
x_38 = lean_nat_dec_le(x_36, x_37);
lean_dec(x_37);
lean_dec(x_36);
if (x_38 == 0)
{
lean_object* x_39; 
x_39 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Diff_Histogram_addLeft___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__9_spec__11___redArg(x_32);
lean_ctor_set(x_1, 1, x_39);
lean_ctor_set(x_1, 0, x_30);
return x_1;
}
else
{
lean_ctor_set(x_1, 1, x_32);
lean_ctor_set(x_1, 0, x_30);
return x_1;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_box(0);
x_41 = lean_array_uset(x_6, x_22, x_40);
x_42 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Diff_Histogram_addLeft___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__9_spec__14___redArg(x_3, x_28, x_23);
x_43 = lean_array_uset(x_41, x_22, x_42);
lean_ctor_set(x_1, 1, x_43);
return x_1;
}
}
else
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_24);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_45 = lean_ctor_get(x_24, 0);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_nat_add(x_46, x_19);
lean_ctor_set(x_24, 0, x_2);
x_49 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_47);
lean_ctor_set(x_49, 2, x_48);
lean_ctor_set(x_49, 3, x_24);
x_50 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Diff_Histogram_addLeft___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__9_spec__10___redArg(x_3, x_23);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_51 = lean_nat_add(x_5, x_19);
lean_dec(x_5);
x_52 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_52, 0, x_3);
lean_ctor_set(x_52, 1, x_49);
lean_ctor_set(x_52, 2, x_23);
x_53 = lean_array_uset(x_6, x_22, x_52);
x_54 = lean_unsigned_to_nat(2u);
x_55 = lean_nat_shiftl(x_51, x_54);
x_56 = lean_unsigned_to_nat(3u);
x_57 = lean_nat_div(x_55, x_56);
lean_dec(x_55);
x_58 = lean_array_get_size(x_53);
x_59 = lean_nat_dec_le(x_57, x_58);
lean_dec(x_58);
lean_dec(x_57);
if (x_59 == 0)
{
lean_object* x_60; 
x_60 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Diff_Histogram_addLeft___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__9_spec__11___redArg(x_53);
lean_ctor_set(x_1, 1, x_60);
lean_ctor_set(x_1, 0, x_51);
return x_1;
}
else
{
lean_ctor_set(x_1, 1, x_53);
lean_ctor_set(x_1, 0, x_51);
return x_1;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_61 = lean_box(0);
x_62 = lean_array_uset(x_6, x_22, x_61);
x_63 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Diff_Histogram_addLeft___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__9_spec__14___redArg(x_3, x_49, x_23);
x_64 = lean_array_uset(x_62, x_22, x_63);
lean_ctor_set(x_1, 1, x_64);
return x_1;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_65 = lean_ctor_get(x_24, 0);
lean_inc(x_65);
lean_dec(x_24);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = lean_nat_add(x_66, x_19);
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_2);
x_70 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_70, 0, x_66);
lean_ctor_set(x_70, 1, x_67);
lean_ctor_set(x_70, 2, x_68);
lean_ctor_set(x_70, 3, x_69);
x_71 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Diff_Histogram_addLeft___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__9_spec__10___redArg(x_3, x_23);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_72 = lean_nat_add(x_5, x_19);
lean_dec(x_5);
x_73 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_73, 0, x_3);
lean_ctor_set(x_73, 1, x_70);
lean_ctor_set(x_73, 2, x_23);
x_74 = lean_array_uset(x_6, x_22, x_73);
x_75 = lean_unsigned_to_nat(2u);
x_76 = lean_nat_shiftl(x_72, x_75);
x_77 = lean_unsigned_to_nat(3u);
x_78 = lean_nat_div(x_76, x_77);
lean_dec(x_76);
x_79 = lean_array_get_size(x_74);
x_80 = lean_nat_dec_le(x_78, x_79);
lean_dec(x_79);
lean_dec(x_78);
if (x_80 == 0)
{
lean_object* x_81; 
x_81 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Diff_Histogram_addLeft___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__9_spec__11___redArg(x_74);
lean_ctor_set(x_1, 1, x_81);
lean_ctor_set(x_1, 0, x_72);
return x_1;
}
else
{
lean_ctor_set(x_1, 1, x_74);
lean_ctor_set(x_1, 0, x_72);
return x_1;
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_82 = lean_box(0);
x_83 = lean_array_uset(x_6, x_22, x_82);
x_84 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Diff_Histogram_addLeft___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__9_spec__14___redArg(x_3, x_70, x_23);
x_85 = lean_array_uset(x_83, x_22, x_84);
lean_ctor_set(x_1, 1, x_85);
return x_1;
}
}
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; uint64_t x_89; lean_object* x_90; uint64_t x_91; uint64_t x_92; uint64_t x_93; lean_object* x_94; uint64_t x_95; uint64_t x_96; uint64_t x_97; size_t x_98; size_t x_99; lean_object* x_100; size_t x_101; size_t x_102; size_t x_103; lean_object* x_104; lean_object* x_105; 
x_86 = lean_ctor_get(x_1, 0);
x_87 = lean_ctor_get(x_1, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_1);
x_88 = lean_array_get_size(x_87);
x_89 = lean_string_hash(x_3);
x_90 = lean_unsigned_to_nat(32u);
x_91 = lean_uint64_of_nat(x_90);
x_92 = lean_uint64_shift_right(x_89, x_91);
x_93 = lean_uint64_xor(x_89, x_92);
x_94 = lean_unsigned_to_nat(16u);
x_95 = lean_uint64_of_nat(x_94);
x_96 = lean_uint64_shift_right(x_93, x_95);
x_97 = lean_uint64_xor(x_93, x_96);
x_98 = lean_uint64_to_usize(x_97);
x_99 = lean_usize_of_nat(x_88);
lean_dec(x_88);
x_100 = lean_unsigned_to_nat(1u);
x_101 = lean_usize_of_nat(x_100);
x_102 = lean_usize_sub(x_99, x_101);
x_103 = lean_usize_land(x_98, x_102);
x_104 = lean_array_uget(x_87, x_103);
x_105 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Diff_Histogram_addLeft___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__9_spec__9___redArg(x_3, x_104);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; 
x_106 = lean_unsigned_to_nat(0u);
x_107 = lean_box(0);
x_108 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_108, 0, x_2);
x_109 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_109, 0, x_106);
lean_ctor_set(x_109, 1, x_107);
lean_ctor_set(x_109, 2, x_100);
lean_ctor_set(x_109, 3, x_108);
x_110 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Diff_Histogram_addLeft___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__9_spec__10___redArg(x_3, x_104);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; 
x_111 = lean_nat_add(x_86, x_100);
lean_dec(x_86);
x_112 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_112, 0, x_3);
lean_ctor_set(x_112, 1, x_109);
lean_ctor_set(x_112, 2, x_104);
x_113 = lean_array_uset(x_87, x_103, x_112);
x_114 = lean_unsigned_to_nat(2u);
x_115 = lean_nat_shiftl(x_111, x_114);
x_116 = lean_unsigned_to_nat(3u);
x_117 = lean_nat_div(x_115, x_116);
lean_dec(x_115);
x_118 = lean_array_get_size(x_113);
x_119 = lean_nat_dec_le(x_117, x_118);
lean_dec(x_118);
lean_dec(x_117);
if (x_119 == 0)
{
lean_object* x_120; lean_object* x_121; 
x_120 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Diff_Histogram_addLeft___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__9_spec__11___redArg(x_113);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_111);
lean_ctor_set(x_121, 1, x_120);
return x_121;
}
else
{
lean_object* x_122; 
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_111);
lean_ctor_set(x_122, 1, x_113);
return x_122;
}
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_123 = lean_box(0);
x_124 = lean_array_uset(x_87, x_103, x_123);
x_125 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Diff_Histogram_addLeft___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__9_spec__14___redArg(x_3, x_109, x_104);
x_126 = lean_array_uset(x_124, x_103, x_125);
x_127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_127, 0, x_86);
lean_ctor_set(x_127, 1, x_126);
return x_127;
}
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; 
x_128 = lean_ctor_get(x_105, 0);
lean_inc(x_128);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 x_129 = x_105;
} else {
 lean_dec_ref(x_105);
 x_129 = lean_box(0);
}
x_130 = lean_ctor_get(x_128, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_128, 1);
lean_inc(x_131);
lean_dec(x_128);
x_132 = lean_nat_add(x_130, x_100);
if (lean_is_scalar(x_129)) {
 x_133 = lean_alloc_ctor(1, 1, 0);
} else {
 x_133 = x_129;
}
lean_ctor_set(x_133, 0, x_2);
x_134 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_134, 0, x_130);
lean_ctor_set(x_134, 1, x_131);
lean_ctor_set(x_134, 2, x_132);
lean_ctor_set(x_134, 3, x_133);
x_135 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Diff_Histogram_addLeft___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__9_spec__10___redArg(x_3, x_104);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; uint8_t x_144; 
x_136 = lean_nat_add(x_86, x_100);
lean_dec(x_86);
x_137 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_137, 0, x_3);
lean_ctor_set(x_137, 1, x_134);
lean_ctor_set(x_137, 2, x_104);
x_138 = lean_array_uset(x_87, x_103, x_137);
x_139 = lean_unsigned_to_nat(2u);
x_140 = lean_nat_shiftl(x_136, x_139);
x_141 = lean_unsigned_to_nat(3u);
x_142 = lean_nat_div(x_140, x_141);
lean_dec(x_140);
x_143 = lean_array_get_size(x_138);
x_144 = lean_nat_dec_le(x_142, x_143);
lean_dec(x_143);
lean_dec(x_142);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; 
x_145 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Diff_Histogram_addLeft___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__9_spec__11___redArg(x_138);
x_146 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_146, 0, x_136);
lean_ctor_set(x_146, 1, x_145);
return x_146;
}
else
{
lean_object* x_147; 
x_147 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_147, 0, x_136);
lean_ctor_set(x_147, 1, x_138);
return x_147;
}
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_148 = lean_box(0);
x_149 = lean_array_uset(x_87, x_103, x_148);
x_150 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Diff_Histogram_addLeft___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__9_spec__14___redArg(x_3, x_134, x_104);
x_151 = lean_array_uset(x_149, x_103, x_150);
x_152 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_152, 0, x_86);
lean_ctor_set(x_152, 1, x_151);
return x_152;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__17(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Diff_Histogram_addRight___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__17___redArg(x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__18___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_nat_dec_lt(x_6, x_7);
if (x_8 == 0)
{
lean_dec(x_6);
return x_5;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = l_Subarray_get___redArg(x_2, x_6);
lean_inc(x_6);
x_10 = l_Lean_Diff_Histogram_addRight___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__17___redArg(x_5, x_6, x_9);
x_11 = lean_ctor_get(x_4, 2);
x_12 = lean_nat_add(x_6, x_11);
lean_dec(x_6);
x_5 = x_10;
x_6 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__18(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_Range_forIn_x27_loop___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__18___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__19___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_1 = x_6;
goto _start;
}
else
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_4, 3);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_dec(x_1);
x_1 = x_9;
goto _start;
}
else
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_1);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_1, 1);
x_13 = lean_ctor_get(x_1, 0);
lean_dec(x_13);
x_14 = !lean_is_exclusive(x_3);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_15 = lean_ctor_get(x_3, 0);
x_16 = lean_ctor_get(x_3, 1);
lean_dec(x_16);
x_17 = lean_ctor_get(x_4, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_4, 2);
lean_inc(x_18);
lean_dec(x_4);
x_19 = lean_ctor_get(x_5, 0);
lean_inc(x_19);
lean_dec(x_5);
x_20 = !lean_is_exclusive(x_8);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_8, 0);
x_22 = lean_nat_add(x_17, x_18);
lean_dec(x_18);
lean_dec(x_17);
lean_ctor_set(x_3, 1, x_21);
lean_ctor_set(x_3, 0, x_19);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_3);
lean_ctor_set(x_1, 0, x_15);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_1);
lean_ctor_set(x_8, 0, x_23);
x_1 = x_12;
x_2 = x_8;
goto _start;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_8, 0);
lean_inc(x_25);
lean_dec(x_8);
x_26 = lean_nat_add(x_17, x_18);
lean_dec(x_18);
lean_dec(x_17);
lean_ctor_set(x_3, 1, x_25);
lean_ctor_set(x_3, 0, x_19);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_3);
lean_ctor_set(x_1, 0, x_15);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_1);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_1 = x_12;
x_2 = x_28;
goto _start;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_30 = lean_ctor_get(x_3, 0);
lean_inc(x_30);
lean_dec(x_3);
x_31 = lean_ctor_get(x_4, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_4, 2);
lean_inc(x_32);
lean_dec(x_4);
x_33 = lean_ctor_get(x_5, 0);
lean_inc(x_33);
lean_dec(x_5);
x_34 = lean_ctor_get(x_8, 0);
lean_inc(x_34);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 x_35 = x_8;
} else {
 lean_dec_ref(x_8);
 x_35 = lean_box(0);
}
x_36 = lean_nat_add(x_31, x_32);
lean_dec(x_32);
lean_dec(x_31);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_33);
lean_ctor_set(x_37, 1, x_34);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_37);
lean_ctor_set(x_1, 0, x_30);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_1);
if (lean_is_scalar(x_35)) {
 x_39 = lean_alloc_ctor(1, 1, 0);
} else {
 x_39 = x_35;
}
lean_ctor_set(x_39, 0, x_38);
x_1 = x_12;
x_2 = x_39;
goto _start;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_41 = lean_ctor_get(x_1, 1);
lean_inc(x_41);
lean_dec(x_1);
x_42 = lean_ctor_get(x_3, 0);
lean_inc(x_42);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_43 = x_3;
} else {
 lean_dec_ref(x_3);
 x_43 = lean_box(0);
}
x_44 = lean_ctor_get(x_4, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_4, 2);
lean_inc(x_45);
lean_dec(x_4);
x_46 = lean_ctor_get(x_5, 0);
lean_inc(x_46);
lean_dec(x_5);
x_47 = lean_ctor_get(x_8, 0);
lean_inc(x_47);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 x_48 = x_8;
} else {
 lean_dec_ref(x_8);
 x_48 = lean_box(0);
}
x_49 = lean_nat_add(x_44, x_45);
lean_dec(x_45);
lean_dec(x_44);
if (lean_is_scalar(x_43)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_43;
}
lean_ctor_set(x_50, 0, x_46);
lean_ctor_set(x_50, 1, x_47);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_42);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_49);
lean_ctor_set(x_52, 1, x_51);
if (lean_is_scalar(x_48)) {
 x_53 = lean_alloc_ctor(1, 1, 0);
} else {
 x_53 = x_48;
}
lean_ctor_set(x_53, 0, x_52);
x_1 = x_41;
x_2 = x_53;
goto _start;
}
}
else
{
lean_object* x_55; uint8_t x_56; 
x_55 = lean_ctor_get(x_2, 0);
lean_inc(x_55);
x_56 = !lean_is_exclusive(x_1);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_57 = lean_ctor_get(x_1, 1);
x_58 = lean_ctor_get(x_1, 0);
lean_dec(x_58);
x_59 = !lean_is_exclusive(x_3);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_60 = lean_ctor_get(x_3, 0);
x_61 = lean_ctor_get(x_3, 1);
lean_dec(x_61);
x_62 = lean_ctor_get(x_4, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_4, 2);
lean_inc(x_63);
lean_dec(x_4);
x_64 = lean_ctor_get(x_5, 0);
lean_inc(x_64);
lean_dec(x_5);
x_65 = lean_ctor_get(x_8, 0);
lean_inc(x_65);
lean_dec(x_8);
x_66 = !lean_is_exclusive(x_55);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_67 = lean_ctor_get(x_55, 0);
x_68 = lean_ctor_get(x_55, 1);
lean_dec(x_68);
x_69 = lean_nat_add(x_62, x_63);
lean_dec(x_63);
lean_dec(x_62);
x_70 = lean_nat_dec_lt(x_69, x_67);
lean_dec(x_67);
if (x_70 == 0)
{
lean_dec(x_69);
lean_free_object(x_55);
lean_dec(x_65);
lean_dec(x_64);
lean_free_object(x_3);
lean_dec(x_60);
lean_free_object(x_1);
x_1 = x_57;
goto _start;
}
else
{
uint8_t x_72; 
x_72 = !lean_is_exclusive(x_2);
if (x_72 == 0)
{
lean_object* x_73; 
x_73 = lean_ctor_get(x_2, 0);
lean_dec(x_73);
lean_ctor_set(x_55, 1, x_65);
lean_ctor_set(x_55, 0, x_64);
lean_ctor_set(x_3, 1, x_55);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_3);
lean_ctor_set(x_1, 0, x_69);
lean_ctor_set(x_2, 0, x_1);
x_1 = x_57;
goto _start;
}
else
{
lean_object* x_75; 
lean_dec(x_2);
lean_ctor_set(x_55, 1, x_65);
lean_ctor_set(x_55, 0, x_64);
lean_ctor_set(x_3, 1, x_55);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_3);
lean_ctor_set(x_1, 0, x_69);
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_1);
x_1 = x_57;
x_2 = x_75;
goto _start;
}
}
}
else
{
lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_77 = lean_ctor_get(x_55, 0);
lean_inc(x_77);
lean_dec(x_55);
x_78 = lean_nat_add(x_62, x_63);
lean_dec(x_63);
lean_dec(x_62);
x_79 = lean_nat_dec_lt(x_78, x_77);
lean_dec(x_77);
if (x_79 == 0)
{
lean_dec(x_78);
lean_dec(x_65);
lean_dec(x_64);
lean_free_object(x_3);
lean_dec(x_60);
lean_free_object(x_1);
x_1 = x_57;
goto _start;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 x_81 = x_2;
} else {
 lean_dec_ref(x_2);
 x_81 = lean_box(0);
}
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_64);
lean_ctor_set(x_82, 1, x_65);
lean_ctor_set(x_3, 1, x_82);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_3);
lean_ctor_set(x_1, 0, x_78);
if (lean_is_scalar(x_81)) {
 x_83 = lean_alloc_ctor(1, 1, 0);
} else {
 x_83 = x_81;
}
lean_ctor_set(x_83, 0, x_1);
x_1 = x_57;
x_2 = x_83;
goto _start;
}
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_85 = lean_ctor_get(x_3, 0);
lean_inc(x_85);
lean_dec(x_3);
x_86 = lean_ctor_get(x_4, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_4, 2);
lean_inc(x_87);
lean_dec(x_4);
x_88 = lean_ctor_get(x_5, 0);
lean_inc(x_88);
lean_dec(x_5);
x_89 = lean_ctor_get(x_8, 0);
lean_inc(x_89);
lean_dec(x_8);
x_90 = lean_ctor_get(x_55, 0);
lean_inc(x_90);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_91 = x_55;
} else {
 lean_dec_ref(x_55);
 x_91 = lean_box(0);
}
x_92 = lean_nat_add(x_86, x_87);
lean_dec(x_87);
lean_dec(x_86);
x_93 = lean_nat_dec_lt(x_92, x_90);
lean_dec(x_90);
if (x_93 == 0)
{
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_85);
lean_free_object(x_1);
x_1 = x_57;
goto _start;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 x_95 = x_2;
} else {
 lean_dec_ref(x_2);
 x_95 = lean_box(0);
}
if (lean_is_scalar(x_91)) {
 x_96 = lean_alloc_ctor(0, 2, 0);
} else {
 x_96 = x_91;
}
lean_ctor_set(x_96, 0, x_88);
lean_ctor_set(x_96, 1, x_89);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_85);
lean_ctor_set(x_97, 1, x_96);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_97);
lean_ctor_set(x_1, 0, x_92);
if (lean_is_scalar(x_95)) {
 x_98 = lean_alloc_ctor(1, 1, 0);
} else {
 x_98 = x_95;
}
lean_ctor_set(x_98, 0, x_1);
x_1 = x_57;
x_2 = x_98;
goto _start;
}
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; 
x_100 = lean_ctor_get(x_1, 1);
lean_inc(x_100);
lean_dec(x_1);
x_101 = lean_ctor_get(x_3, 0);
lean_inc(x_101);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_102 = x_3;
} else {
 lean_dec_ref(x_3);
 x_102 = lean_box(0);
}
x_103 = lean_ctor_get(x_4, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_4, 2);
lean_inc(x_104);
lean_dec(x_4);
x_105 = lean_ctor_get(x_5, 0);
lean_inc(x_105);
lean_dec(x_5);
x_106 = lean_ctor_get(x_8, 0);
lean_inc(x_106);
lean_dec(x_8);
x_107 = lean_ctor_get(x_55, 0);
lean_inc(x_107);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_108 = x_55;
} else {
 lean_dec_ref(x_55);
 x_108 = lean_box(0);
}
x_109 = lean_nat_add(x_103, x_104);
lean_dec(x_104);
lean_dec(x_103);
x_110 = lean_nat_dec_lt(x_109, x_107);
lean_dec(x_107);
if (x_110 == 0)
{
lean_dec(x_109);
lean_dec(x_108);
lean_dec(x_106);
lean_dec(x_105);
lean_dec(x_102);
lean_dec(x_101);
x_1 = x_100;
goto _start;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 x_112 = x_2;
} else {
 lean_dec_ref(x_2);
 x_112 = lean_box(0);
}
if (lean_is_scalar(x_108)) {
 x_113 = lean_alloc_ctor(0, 2, 0);
} else {
 x_113 = x_108;
}
lean_ctor_set(x_113, 0, x_105);
lean_ctor_set(x_113, 1, x_106);
if (lean_is_scalar(x_102)) {
 x_114 = lean_alloc_ctor(0, 2, 0);
} else {
 x_114 = x_102;
}
lean_ctor_set(x_114, 0, x_101);
lean_ctor_set(x_114, 1, x_113);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_109);
lean_ctor_set(x_115, 1, x_114);
if (lean_is_scalar(x_112)) {
 x_116 = lean_alloc_ctor(1, 1, 0);
} else {
 x_116 = x_112;
}
lean_ctor_set(x_116, 0, x_115);
x_1 = x_100;
x_2 = x_116;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__19(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_forIn_x27_loop___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__19___redArg(x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__20(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_inc(x_1);
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
x_6 = l_Std_DHashMap_Internal_AssocList_foldrM___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__20(x_1, x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_4);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__21(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_usize_of_nat(x_6);
x_8 = lean_usize_sub(x_2, x_7);
x_9 = lean_array_uget(x_1, x_8);
x_10 = l_Std_DHashMap_Internal_AssocList_foldrM___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__20(x_4, x_9);
lean_dec(x_9);
lean_dec(x_4);
x_2 = x_8;
x_4 = x_10;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_3 = l_Lean_Diff_matchPrefix___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__5(x_1, x_2);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec(x_4);
x_8 = l_Lean_Diff_matchSuffix___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__7(x_6, x_7);
lean_dec(x_7);
lean_dec(x_6);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_12 = lean_ctor_get(x_9, 0);
x_13 = lean_ctor_get(x_9, 1);
x_14 = lean_unsigned_to_nat(8u);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_unsigned_to_nat(2u);
x_17 = lean_nat_shiftl(x_14, x_16);
x_18 = lean_unsigned_to_nat(3u);
x_19 = lean_nat_div(x_17, x_18);
lean_dec(x_17);
x_20 = l_Nat_nextPowerOfTwo(x_19);
lean_dec(x_19);
x_21 = lean_box(0);
x_22 = lean_mk_array(x_20, x_21);
lean_ctor_set(x_9, 1, x_22);
lean_ctor_set(x_9, 0, x_15);
x_23 = l_Subarray_size___redArg(x_10);
x_24 = lean_unsigned_to_nat(1u);
lean_inc(x_23);
x_25 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_25, 0, x_15);
lean_ctor_set(x_25, 1, x_23);
lean_ctor_set(x_25, 2, x_24);
x_26 = l_Std_Range_forIn_x27_loop___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__16___redArg(x_12, x_23, x_10, x_25, x_9, x_15);
lean_dec(x_25);
x_27 = l_Subarray_size___redArg(x_12);
lean_inc(x_27);
x_28 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_28, 0, x_15);
lean_ctor_set(x_28, 1, x_27);
lean_ctor_set(x_28, 2, x_24);
x_29 = lean_box(0);
x_56 = l_Std_Range_forIn_x27_loop___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__18___redArg(x_27, x_12, x_23, x_28, x_26, x_15);
lean_dec(x_28);
lean_dec(x_23);
lean_dec(x_27);
x_57 = lean_box(0);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_array_get_size(x_58);
x_60 = lean_nat_dec_lt(x_15, x_59);
if (x_60 == 0)
{
lean_dec(x_59);
lean_dec(x_58);
x_30 = x_57;
goto block_55;
}
else
{
size_t x_61; size_t x_62; lean_object* x_63; 
x_61 = lean_usize_of_nat(x_59);
lean_dec(x_59);
x_62 = lean_usize_of_nat(x_15);
x_63 = l_Array_foldrMUnsafe_fold___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__21(x_58, x_61, x_62, x_57);
lean_dec(x_58);
x_30 = x_63;
goto block_55;
}
block_55:
{
lean_object* x_31; 
x_31 = l_List_forIn_x27_loop___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__19___redArg(x_30, x_29);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; 
lean_dec(x_12);
lean_dec(x_10);
x_32 = l_Array_append(lean_box(0), x_5, x_13);
lean_dec(x_13);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 0);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
x_39 = l_Subarray_split(lean_box(0), x_10, x_37);
lean_dec(x_37);
lean_dec(x_10);
x_40 = l_Subarray_split(lean_box(0), x_12, x_38);
lean_dec(x_38);
lean_dec(x_12);
x_41 = lean_ctor_get(x_39, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 0);
lean_inc(x_42);
x_43 = l_Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5(x_41, x_42);
lean_dec(x_42);
lean_dec(x_41);
x_44 = l_Array_append(lean_box(0), x_5, x_43);
lean_dec(x_43);
x_45 = lean_mk_empty_array_with_capacity(x_24);
x_46 = lean_array_push(x_45, x_36);
x_47 = l_Array_append(lean_box(0), x_44, x_46);
lean_dec(x_46);
x_48 = lean_ctor_get(x_39, 1);
lean_inc(x_48);
lean_dec(x_39);
x_49 = l_Subarray_drop(lean_box(0), x_48, x_24);
lean_dec(x_48);
x_50 = lean_ctor_get(x_40, 1);
lean_inc(x_50);
lean_dec(x_40);
x_51 = l_Subarray_drop(lean_box(0), x_50, x_24);
lean_dec(x_50);
x_52 = l_Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5(x_49, x_51);
lean_dec(x_51);
lean_dec(x_49);
x_53 = l_Array_append(lean_box(0), x_47, x_52);
lean_dec(x_52);
x_54 = l_Array_append(lean_box(0), x_53, x_13);
lean_dec(x_13);
return x_54;
}
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; 
x_64 = lean_ctor_get(x_9, 0);
x_65 = lean_ctor_get(x_9, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_9);
x_66 = lean_unsigned_to_nat(8u);
x_67 = lean_unsigned_to_nat(0u);
x_68 = lean_unsigned_to_nat(2u);
x_69 = lean_nat_shiftl(x_66, x_68);
x_70 = lean_unsigned_to_nat(3u);
x_71 = lean_nat_div(x_69, x_70);
lean_dec(x_69);
x_72 = l_Nat_nextPowerOfTwo(x_71);
lean_dec(x_71);
x_73 = lean_box(0);
x_74 = lean_mk_array(x_72, x_73);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_67);
lean_ctor_set(x_75, 1, x_74);
x_76 = l_Subarray_size___redArg(x_10);
x_77 = lean_unsigned_to_nat(1u);
lean_inc(x_76);
x_78 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_78, 0, x_67);
lean_ctor_set(x_78, 1, x_76);
lean_ctor_set(x_78, 2, x_77);
x_79 = l_Std_Range_forIn_x27_loop___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__16___redArg(x_64, x_76, x_10, x_78, x_75, x_67);
lean_dec(x_78);
x_80 = l_Subarray_size___redArg(x_64);
lean_inc(x_80);
x_81 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_81, 0, x_67);
lean_ctor_set(x_81, 1, x_80);
lean_ctor_set(x_81, 2, x_77);
x_82 = lean_box(0);
x_109 = l_Std_Range_forIn_x27_loop___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__18___redArg(x_80, x_64, x_76, x_81, x_79, x_67);
lean_dec(x_81);
lean_dec(x_76);
lean_dec(x_80);
x_110 = lean_box(0);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
lean_dec(x_109);
x_112 = lean_array_get_size(x_111);
x_113 = lean_nat_dec_lt(x_67, x_112);
if (x_113 == 0)
{
lean_dec(x_112);
lean_dec(x_111);
x_83 = x_110;
goto block_108;
}
else
{
size_t x_114; size_t x_115; lean_object* x_116; 
x_114 = lean_usize_of_nat(x_112);
lean_dec(x_112);
x_115 = lean_usize_of_nat(x_67);
x_116 = l_Array_foldrMUnsafe_fold___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__21(x_111, x_114, x_115, x_110);
lean_dec(x_111);
x_83 = x_116;
goto block_108;
}
block_108:
{
lean_object* x_84; 
x_84 = l_List_forIn_x27_loop___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__19___redArg(x_83, x_82);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; 
lean_dec(x_64);
lean_dec(x_10);
x_85 = l_Array_append(lean_box(0), x_5, x_65);
lean_dec(x_65);
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_86 = lean_ctor_get(x_84, 0);
lean_inc(x_86);
lean_dec(x_84);
x_87 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
lean_dec(x_86);
x_88 = lean_ctor_get(x_87, 1);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 0);
lean_inc(x_89);
lean_dec(x_87);
x_90 = lean_ctor_get(x_88, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_88, 1);
lean_inc(x_91);
lean_dec(x_88);
x_92 = l_Subarray_split(lean_box(0), x_10, x_90);
lean_dec(x_90);
lean_dec(x_10);
x_93 = l_Subarray_split(lean_box(0), x_64, x_91);
lean_dec(x_91);
lean_dec(x_64);
x_94 = lean_ctor_get(x_92, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 0);
lean_inc(x_95);
x_96 = l_Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5(x_94, x_95);
lean_dec(x_95);
lean_dec(x_94);
x_97 = l_Array_append(lean_box(0), x_5, x_96);
lean_dec(x_96);
x_98 = lean_mk_empty_array_with_capacity(x_77);
x_99 = lean_array_push(x_98, x_89);
x_100 = l_Array_append(lean_box(0), x_97, x_99);
lean_dec(x_99);
x_101 = lean_ctor_get(x_92, 1);
lean_inc(x_101);
lean_dec(x_92);
x_102 = l_Subarray_drop(lean_box(0), x_101, x_77);
lean_dec(x_101);
x_103 = lean_ctor_get(x_93, 1);
lean_inc(x_103);
lean_dec(x_93);
x_104 = l_Subarray_drop(lean_box(0), x_103, x_77);
lean_dec(x_103);
x_105 = l_Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5(x_102, x_104);
lean_dec(x_104);
lean_dec(x_102);
x_106 = l_Array_append(lean_box(0), x_100, x_105);
lean_dec(x_105);
x_107 = l_Array_append(lean_box(0), x_106, x_65);
lean_dec(x_65);
return x_107;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__23(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_19; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec(x_4);
x_19 = lean_nat_dec_lt(x_6, x_5);
lean_dec(x_5);
if (x_19 == 0)
{
x_8 = x_19;
goto block_18;
}
else
{
lean_object* x_20; uint8_t x_21; 
lean_inc(x_1);
x_20 = lean_array_get(x_1, x_2, x_6);
x_21 = lean_string_dec_eq(x_20, x_3);
lean_dec(x_20);
if (x_21 == 0)
{
x_8 = x_19;
goto block_18;
}
else
{
lean_object* x_22; 
lean_dec(x_1);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_6);
lean_ctor_set(x_22, 1, x_7);
return x_22;
}
}
block_18:
{
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_box(1);
lean_inc(x_1);
x_11 = lean_array_get(x_1, x_2, x_6);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_array_push(x_7, x_12);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_6, x_14);
lean_dec(x_6);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
x_4 = x_16;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__24(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_19; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec(x_4);
x_19 = lean_nat_dec_lt(x_6, x_5);
lean_dec(x_5);
if (x_19 == 0)
{
x_8 = x_19;
goto block_18;
}
else
{
lean_object* x_20; uint8_t x_21; 
lean_inc(x_1);
x_20 = lean_array_get(x_1, x_2, x_6);
x_21 = lean_string_dec_eq(x_20, x_3);
lean_dec(x_20);
if (x_21 == 0)
{
x_8 = x_19;
goto block_18;
}
else
{
lean_object* x_22; 
lean_dec(x_1);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_6);
lean_ctor_set(x_22, 1, x_7);
return x_22;
}
}
block_18:
{
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_box(0);
lean_inc(x_1);
x_11 = lean_array_get(x_1, x_2, x_6);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_array_push(x_7, x_12);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_6, x_14);
lean_dec(x_6);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
x_4 = x_16;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__25_spec__25(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_6, x_5);
if (x_8 == 0)
{
lean_dec(x_1);
return x_7;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_9 = lean_array_uget(x_4, x_6);
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_7, 1);
lean_inc(x_11);
lean_dec(x_7);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
lean_inc(x_1);
x_14 = l_Lean_Loop_forIn_loop___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__23(x_1, x_2, x_9, x_13);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_11, 0);
lean_inc(x_17);
lean_dec(x_11);
lean_ctor_set(x_14, 0, x_17);
lean_inc(x_1);
x_18 = l_Lean_Loop_forIn_loop___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__24(x_1, x_3, x_9, x_14);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; size_t x_31; size_t x_32; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
x_22 = lean_box(2);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_9);
x_24 = lean_array_push(x_21, x_23);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_add(x_16, x_25);
lean_dec(x_16);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_20, x_27);
lean_dec(x_20);
lean_ctor_set(x_18, 1, x_24);
lean_ctor_set(x_18, 0, x_28);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_18);
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_usize_of_nat(x_30);
x_32 = lean_usize_add(x_6, x_31);
x_6 = x_32;
x_7 = x_29;
goto _start;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; size_t x_46; size_t x_47; 
x_34 = lean_ctor_get(x_18, 0);
x_35 = lean_ctor_get(x_18, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_18);
x_36 = lean_box(2);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_9);
x_38 = lean_array_push(x_35, x_37);
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_nat_add(x_16, x_39);
lean_dec(x_16);
x_41 = lean_unsigned_to_nat(1u);
x_42 = lean_nat_add(x_34, x_41);
lean_dec(x_34);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_38);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_40);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_unsigned_to_nat(1u);
x_46 = lean_usize_of_nat(x_45);
x_47 = lean_usize_add(x_6, x_46);
x_6 = x_47;
x_7 = x_44;
goto _start;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; size_t x_67; size_t x_68; 
x_49 = lean_ctor_get(x_14, 0);
x_50 = lean_ctor_get(x_14, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_14);
x_51 = lean_ctor_get(x_11, 0);
lean_inc(x_51);
lean_dec(x_11);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
lean_inc(x_1);
x_53 = l_Lean_Loop_forIn_loop___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__24(x_1, x_3, x_9, x_52);
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
x_57 = lean_box(2);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_9);
x_59 = lean_array_push(x_55, x_58);
x_60 = lean_unsigned_to_nat(1u);
x_61 = lean_nat_add(x_49, x_60);
lean_dec(x_49);
x_62 = lean_unsigned_to_nat(1u);
x_63 = lean_nat_add(x_54, x_62);
lean_dec(x_54);
if (lean_is_scalar(x_56)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_56;
}
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_59);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_61);
lean_ctor_set(x_65, 1, x_64);
x_66 = lean_unsigned_to_nat(1u);
x_67 = lean_usize_of_nat(x_66);
x_68 = lean_usize_add(x_6, x_67);
x_6 = x_68;
x_7 = x_65;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__25(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_6, x_5);
if (x_8 == 0)
{
lean_dec(x_1);
lean_inc(x_7);
return x_7;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_9 = lean_array_uget(x_4, x_6);
x_10 = lean_ctor_get(x_7, 0);
x_11 = lean_ctor_get(x_7, 1);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_inc(x_10);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
lean_inc(x_1);
x_14 = l_Lean_Loop_forIn_loop___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__23(x_1, x_3, x_9, x_13);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_11, 0);
lean_inc(x_17);
lean_ctor_set(x_14, 0, x_17);
lean_inc(x_1);
x_18 = l_Lean_Loop_forIn_loop___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__24(x_1, x_2, x_9, x_14);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; size_t x_31; size_t x_32; lean_object* x_33; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
x_22 = lean_box(2);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_9);
x_24 = lean_array_push(x_21, x_23);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_add(x_16, x_25);
lean_dec(x_16);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_20, x_27);
lean_dec(x_20);
lean_ctor_set(x_18, 1, x_24);
lean_ctor_set(x_18, 0, x_28);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_18);
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_usize_of_nat(x_30);
x_32 = lean_usize_add(x_6, x_31);
x_33 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__25_spec__25(x_1, x_3, x_2, x_4, x_5, x_32, x_29);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; size_t x_46; size_t x_47; lean_object* x_48; 
x_34 = lean_ctor_get(x_18, 0);
x_35 = lean_ctor_get(x_18, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_18);
x_36 = lean_box(2);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_9);
x_38 = lean_array_push(x_35, x_37);
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_nat_add(x_16, x_39);
lean_dec(x_16);
x_41 = lean_unsigned_to_nat(1u);
x_42 = lean_nat_add(x_34, x_41);
lean_dec(x_34);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_38);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_40);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_unsigned_to_nat(1u);
x_46 = lean_usize_of_nat(x_45);
x_47 = lean_usize_add(x_6, x_46);
x_48 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__25_spec__25(x_1, x_3, x_2, x_4, x_5, x_47, x_44);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; size_t x_67; size_t x_68; lean_object* x_69; 
x_49 = lean_ctor_get(x_14, 0);
x_50 = lean_ctor_get(x_14, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_14);
x_51 = lean_ctor_get(x_11, 0);
lean_inc(x_51);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
lean_inc(x_1);
x_53 = l_Lean_Loop_forIn_loop___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__24(x_1, x_2, x_9, x_52);
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
x_57 = lean_box(2);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_9);
x_59 = lean_array_push(x_55, x_58);
x_60 = lean_unsigned_to_nat(1u);
x_61 = lean_nat_add(x_49, x_60);
lean_dec(x_49);
x_62 = lean_unsigned_to_nat(1u);
x_63 = lean_nat_add(x_54, x_62);
lean_dec(x_54);
if (lean_is_scalar(x_56)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_56;
}
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_59);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_61);
lean_ctor_set(x_65, 1, x_64);
x_66 = lean_unsigned_to_nat(1u);
x_67 = lean_usize_of_nat(x_66);
x_68 = lean_usize_add(x_6, x_67);
x_69 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__25_spec__25(x_1, x_3, x_2, x_4, x_5, x_68, x_65);
return x_69;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__27(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_nat_dec_lt(x_4, x_3);
lean_dec(x_3);
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_box(1);
x_9 = lean_array_fget(x_1, x_4);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_array_push(x_5, x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_4, x_12);
lean_dec(x_4);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
x_2 = x_14;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__28(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_nat_dec_lt(x_4, x_3);
lean_dec(x_3);
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_box(0);
x_9 = lean_array_fget(x_1, x_4);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_array_push(x_5, x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_4, x_12);
lean_dec(x_4);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
x_2 = x_14;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__29(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_8 = lean_box(1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_5);
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__30(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_5);
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
LEAN_EXPORT lean_object* l_Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_7; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_4, x_5);
x_7 = l_instDecidableNot___redArg(x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; uint8_t x_10; 
x_8 = lean_array_get_size(x_3);
x_9 = lean_nat_dec_lt(x_4, x_8);
x_10 = l_instDecidableNot___redArg(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_11 = lean_mk_empty_array_with_capacity(x_4);
lean_inc(x_2);
x_12 = l_Array_toSubarray___redArg(x_2, x_4, x_5);
lean_inc(x_3);
x_13 = l_Array_toSubarray___redArg(x_3, x_4, x_8);
x_14 = l_Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5(x_12, x_13);
lean_dec(x_13);
lean_dec(x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_11);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_4);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_array_size(x_14);
x_18 = lean_usize_of_nat(x_4);
x_19 = l_Array_forIn_x27Unsafe_loop___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__25(x_1, x_3, x_2, x_14, x_17, x_18, x_16);
lean_dec(x_16);
lean_dec(x_14);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec(x_19);
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_20, 0);
lean_ctor_set(x_20, 0, x_21);
x_24 = l_Lean_Loop_forIn_loop___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__27(x_2, x_20);
lean_dec(x_2);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_24, 0);
lean_dec(x_26);
lean_ctor_set(x_24, 0, x_23);
x_27 = l_Lean_Loop_forIn_loop___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__28(x_3, x_24);
lean_dec(x_3);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
lean_dec(x_24);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_23);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Lean_Loop_forIn_loop___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__28(x_3, x_30);
lean_dec(x_3);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_33 = lean_ctor_get(x_20, 0);
x_34 = lean_ctor_get(x_20, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_20);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_21);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_Loop_forIn_loop___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__27(x_2, x_35);
lean_dec(x_2);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_38 = x_36;
} else {
 lean_dec_ref(x_36);
 x_38 = lean_box(0);
}
if (lean_is_scalar(x_38)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_38;
}
lean_ctor_set(x_39, 0, x_33);
lean_ctor_set(x_39, 1, x_37);
x_40 = l_Lean_Loop_forIn_loop___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__28(x_3, x_39);
lean_dec(x_3);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
return x_41;
}
}
else
{
size_t x_42; size_t x_43; lean_object* x_44; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_42 = lean_array_size(x_2);
x_43 = lean_usize_of_nat(x_4);
x_44 = l_Array_mapMUnsafe_map___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__29(x_42, x_43, x_2);
return x_44;
}
}
else
{
size_t x_45; size_t x_46; lean_object* x_47; 
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_45 = lean_array_size(x_3);
x_46 = lean_usize_of_nat(x_4);
x_47 = l_Array_mapMUnsafe_map___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__30(x_45, x_46, x_3);
return x_47;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Diff_linesToString___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__32_spec__32(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_3, x_2);
if (x_11 == 0)
{
return x_4;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_array_uget(x_1, x_3);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_mk_string_unchecked("", 0, 0);
x_16 = lean_string_dec_eq(x_14, x_15);
lean_dec(x_15);
if (x_16 == 0)
{
uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_17 = lean_unbox(x_13);
lean_dec(x_13);
x_18 = l_Lean_Diff_Action_linePrefix(x_17);
x_19 = lean_mk_string_unchecked(" ", 1, 1);
x_20 = lean_string_append(x_18, x_19);
lean_dec(x_19);
x_21 = lean_string_append(x_20, x_14);
lean_dec(x_14);
x_22 = lean_mk_string_unchecked("\n", 1, 1);
x_23 = lean_string_append(x_21, x_22);
lean_dec(x_22);
x_24 = lean_string_append(x_4, x_23);
lean_dec(x_23);
x_5 = x_24;
goto block_10;
}
else
{
uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_14);
x_25 = lean_unbox(x_13);
lean_dec(x_13);
x_26 = l_Lean_Diff_Action_linePrefix(x_25);
x_27 = lean_mk_string_unchecked("\n", 1, 1);
x_28 = lean_string_append(x_26, x_27);
lean_dec(x_27);
x_29 = lean_string_append(x_4, x_28);
lean_dec(x_28);
x_5 = x_29;
goto block_10;
}
}
block_10:
{
lean_object* x_6; size_t x_7; size_t x_8; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_usize_of_nat(x_6);
x_8 = lean_usize_add(x_3, x_7);
x_3 = x_8;
x_4 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_linesToString___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__32(lean_object* x_1) {
_start:
{
lean_object* x_2; size_t x_3; lean_object* x_4; size_t x_5; lean_object* x_6; 
x_2 = lean_mk_string_unchecked("", 0, 0);
x_3 = lean_array_size(x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_usize_of_nat(x_4);
x_6 = l_Array_forIn_x27Unsafe_loop___at___Lean_Diff_linesToString___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__32_spec__32(x_1, x_3, x_5, x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__34_spec__34(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_2, x_3);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; lean_object* x_17; lean_object* x_18; size_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_uget(x_1, x_2);
x_14 = lean_unsigned_to_nat(2u);
x_15 = lean_unsigned_to_nat(5u);
x_16 = lean_usize_of_nat(x_15);
x_17 = lean_usize_to_nat(x_16);
x_18 = lean_nat_pow(x_14, x_17);
lean_dec(x_17);
x_19 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_20 = lean_usize_to_nat(x_19);
x_21 = lean_mk_empty_array_with_capacity(x_20);
lean_dec(x_20);
lean_inc(x_21);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
lean_ctor_set(x_23, 2, x_12);
lean_ctor_set(x_23, 3, x_12);
lean_ctor_set_usize(x_23, 4, x_16);
x_24 = lean_box(0);
lean_inc(x_23);
x_25 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_23);
lean_ctor_set(x_25, 2, x_24);
x_26 = l_Lean_Language_SnapshotTask_get___redArg(x_13);
x_27 = l_Lean_Language_SnapshotTree_getAll(x_26);
x_28 = lean_array_get_size(x_27);
x_29 = lean_nat_dec_lt(x_12, x_28);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_28);
lean_dec(x_27);
x_30 = l_Lean_MessageLog_append(x_4, x_25);
x_5 = x_30;
goto block_10;
}
else
{
uint8_t x_31; 
x_31 = lean_nat_dec_le(x_28, x_28);
if (x_31 == 0)
{
lean_object* x_32; 
lean_dec(x_28);
lean_dec(x_27);
x_32 = l_Lean_MessageLog_append(x_4, x_25);
x_5 = x_32;
goto block_10;
}
else
{
size_t x_33; size_t x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_usize_of_nat(x_12);
x_34 = lean_usize_of_nat(x_28);
lean_dec(x_28);
x_35 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0(x_27, x_33, x_34, x_25);
lean_dec(x_27);
x_36 = l_Lean_MessageLog_append(x_4, x_35);
x_5 = x_36;
goto block_10;
}
}
}
else
{
return x_4;
}
block_10:
{
lean_object* x_6; size_t x_7; size_t x_8; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_usize_of_nat(x_6);
x_8 = lean_usize_add(x_2, x_7);
x_2 = x_8;
x_4 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__34(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_2, x_3);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; lean_object* x_17; lean_object* x_18; size_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_uget(x_1, x_2);
x_14 = lean_unsigned_to_nat(2u);
x_15 = lean_unsigned_to_nat(5u);
x_16 = lean_usize_of_nat(x_15);
x_17 = lean_usize_to_nat(x_16);
x_18 = lean_nat_pow(x_14, x_17);
lean_dec(x_17);
x_19 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_20 = lean_usize_to_nat(x_19);
x_21 = lean_mk_empty_array_with_capacity(x_20);
lean_dec(x_20);
lean_inc(x_21);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
lean_ctor_set(x_23, 2, x_12);
lean_ctor_set(x_23, 3, x_12);
lean_ctor_set_usize(x_23, 4, x_16);
x_24 = lean_box(0);
lean_inc(x_23);
x_25 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_23);
lean_ctor_set(x_25, 2, x_24);
x_26 = l_Lean_Language_SnapshotTask_get___redArg(x_13);
x_27 = l_Lean_Language_SnapshotTree_getAll(x_26);
x_28 = lean_array_get_size(x_27);
x_29 = lean_nat_dec_lt(x_12, x_28);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_28);
lean_dec(x_27);
x_30 = l_Lean_MessageLog_append(x_4, x_25);
x_5 = x_30;
goto block_10;
}
else
{
uint8_t x_31; 
x_31 = lean_nat_dec_le(x_28, x_28);
if (x_31 == 0)
{
lean_object* x_32; 
lean_dec(x_28);
lean_dec(x_27);
x_32 = l_Lean_MessageLog_append(x_4, x_25);
x_5 = x_32;
goto block_10;
}
else
{
size_t x_33; size_t x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_usize_of_nat(x_12);
x_34 = lean_usize_of_nat(x_28);
lean_dec(x_28);
x_35 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0(x_27, x_33, x_34, x_25);
lean_dec(x_27);
x_36 = l_Lean_MessageLog_append(x_4, x_35);
x_5 = x_36;
goto block_10;
}
}
}
else
{
return x_4;
}
block_10:
{
lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_usize_of_nat(x_6);
x_8 = lean_usize_add(x_2, x_7);
x_9 = l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__34_spec__34(x_1, x_8, x_3, x_5);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_51 = lean_mk_string_unchecked("Lean", 4, 4);
x_52 = lean_mk_string_unchecked("guardMsgsCmd", 12, 12);
lean_inc(x_51);
x_53 = l_Lean_Name_mkStr2(x_51, x_52);
lean_inc(x_1);
x_54 = l_Lean_Syntax_isOfKind(x_1, x_53);
lean_dec(x_53);
if (x_54 == 0)
{
lean_object* x_55; 
lean_dec(x_51);
lean_dec(x_1);
x_55 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_358; uint8_t x_359; 
x_56 = lean_unsigned_to_nat(0u);
x_358 = l_Lean_Syntax_getArg(x_1, x_56);
x_359 = l_Lean_Syntax_isNone(x_358);
if (x_359 == 0)
{
lean_object* x_360; uint8_t x_361; 
x_360 = lean_unsigned_to_nat(1u);
lean_inc(x_358);
x_361 = l_Lean_Syntax_matchesNull(x_358, x_360);
if (x_361 == 0)
{
lean_object* x_362; 
lean_dec(x_358);
lean_dec(x_51);
lean_dec(x_1);
x_362 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_362;
}
else
{
lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; uint8_t x_368; 
x_363 = l_Lean_Syntax_getArg(x_358, x_56);
lean_dec(x_358);
x_364 = lean_mk_string_unchecked("Parser", 6, 6);
x_365 = lean_mk_string_unchecked("Command", 7, 7);
x_366 = lean_mk_string_unchecked("docComment", 10, 10);
x_367 = l_Lean_Name_mkStr4(x_51, x_364, x_365, x_366);
lean_inc(x_363);
x_368 = l_Lean_Syntax_isOfKind(x_363, x_367);
lean_dec(x_367);
if (x_368 == 0)
{
lean_object* x_369; 
lean_dec(x_363);
lean_dec(x_1);
x_369 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_369;
}
else
{
lean_object* x_370; 
x_370 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_370, 0, x_363);
x_343 = x_370;
x_344 = x_2;
x_345 = x_3;
x_346 = x_4;
goto block_357;
}
}
}
else
{
lean_object* x_371; 
lean_dec(x_358);
lean_dec(x_51);
x_371 = lean_box(0);
x_343 = x_371;
x_344 = x_2;
x_345 = x_3;
x_346 = x_4;
goto block_357;
}
block_241:
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_68 = lean_st_ref_take(x_59, x_61);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = lean_ctor_get(x_69, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_69, 1);
lean_inc(x_72);
x_73 = lean_ctor_get(x_69, 2);
lean_inc(x_73);
x_74 = lean_ctor_get(x_69, 3);
lean_inc(x_74);
x_75 = lean_ctor_get(x_69, 4);
lean_inc(x_75);
x_76 = lean_ctor_get(x_69, 5);
lean_inc(x_76);
x_77 = lean_ctor_get(x_69, 6);
lean_inc(x_77);
x_78 = lean_ctor_get(x_69, 7);
lean_inc(x_78);
lean_dec(x_69);
x_79 = lean_mk_empty_array_with_capacity(x_56);
x_80 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_80, 0, x_71);
lean_ctor_set(x_80, 1, x_72);
lean_ctor_set(x_80, 2, x_73);
lean_ctor_set(x_80, 3, x_74);
lean_ctor_set(x_80, 4, x_75);
lean_ctor_set(x_80, 5, x_76);
lean_ctor_set(x_80, 6, x_77);
lean_ctor_set(x_80, 7, x_78);
lean_ctor_set(x_80, 8, x_79);
x_81 = lean_st_ref_set(x_59, x_80, x_70);
x_82 = !lean_is_exclusive(x_81);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; 
x_83 = lean_ctor_get(x_81, 1);
x_84 = lean_ctor_get(x_81, 0);
lean_dec(x_84);
x_85 = l_Lean_MessageLog_append(x_64, x_67);
x_86 = l_Lean_MessageLog_empty;
x_87 = l_Lean_MessageLog_toList(x_85);
lean_ctor_set(x_81, 1, x_86);
lean_ctor_set(x_81, 0, x_86);
x_88 = l_List_forIn_x27_loop___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___redArg(x_58, x_87, x_81, x_83);
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
x_91 = lean_ctor_get(x_89, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_89, 1);
lean_inc(x_92);
lean_dec(x_89);
x_93 = l_Lean_MessageLog_toList(x_91);
lean_dec(x_91);
x_94 = lean_box(0);
x_95 = l_List_mapM_loop___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__4___redArg(x_93, x_94, x_90);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
x_98 = l_Lean_Elab_Tactic_GuardMsgs_removeTrailingWhitespaceMarker(x_57);
lean_dec(x_57);
x_99 = lean_ctor_get(x_66, 1);
lean_inc(x_99);
lean_dec(x_66);
x_100 = l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply(x_63, x_96);
x_101 = lean_mk_string_unchecked("---\n", 4, 4);
x_102 = l_String_intercalate(x_101, x_100);
lean_dec(x_101);
x_103 = lean_string_utf8_byte_size(x_102);
lean_inc(x_1);
x_104 = l_Substring_takeWhileAux___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1(x_1, x_102, x_103, x_56);
x_105 = l_Substring_takeRightWhileAux___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2(x_1, x_102, x_104, x_103);
x_106 = lean_string_utf8_extract(x_102, x_104, x_105);
x_107 = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply(x_60, x_98);
x_108 = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply(x_60, x_106);
x_109 = lean_string_dec_eq(x_107, x_108);
lean_dec(x_108);
lean_dec(x_107);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; 
lean_dec(x_92);
x_110 = lean_st_ref_take(x_59, x_97);
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
lean_dec(x_110);
x_113 = lean_ctor_get(x_111, 0);
lean_inc(x_113);
x_114 = l_Lean_MessageLog_append(x_99, x_85);
x_115 = lean_ctor_get(x_111, 2);
lean_inc(x_115);
x_116 = lean_ctor_get(x_111, 3);
lean_inc(x_116);
x_117 = lean_ctor_get(x_111, 4);
lean_inc(x_117);
x_118 = lean_ctor_get(x_111, 5);
lean_inc(x_118);
x_119 = lean_ctor_get(x_111, 6);
lean_inc(x_119);
x_120 = lean_ctor_get(x_111, 7);
lean_inc(x_120);
x_121 = lean_ctor_get(x_111, 8);
lean_inc(x_121);
lean_dec(x_111);
x_122 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_122, 0, x_113);
lean_ctor_set(x_122, 1, x_114);
lean_ctor_set(x_122, 2, x_115);
lean_ctor_set(x_122, 3, x_116);
lean_ctor_set(x_122, 4, x_117);
lean_ctor_set(x_122, 5, x_118);
lean_ctor_set(x_122, 6, x_119);
lean_ctor_set(x_122, 7, x_120);
lean_ctor_set(x_122, 8, x_121);
x_123 = lean_st_ref_set(x_59, x_122, x_112);
x_124 = lean_ctor_get(x_123, 1);
lean_inc(x_124);
lean_dec(x_123);
x_125 = lean_st_ref_get(x_59, x_124);
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
lean_dec(x_125);
x_128 = l_Lean_Elab_Command_instInhabitedScope;
x_129 = lean_ctor_get(x_126, 2);
lean_inc(x_129);
lean_dec(x_126);
x_130 = l_List_head_x21(lean_box(0), x_128, x_129);
lean_dec(x_129);
x_131 = lean_ctor_get(x_130, 1);
lean_inc(x_131);
lean_dec(x_130);
x_132 = lean_mk_string_unchecked("guard_msgs", 10, 10);
x_133 = lean_mk_string_unchecked("diff", 4, 4);
x_134 = l_Lean_Name_mkStr2(x_132, x_133);
x_135 = l_Lean_KVMap_getBool(x_131, x_134, x_109);
lean_dec(x_134);
lean_dec(x_131);
if (x_135 == 0)
{
lean_dec(x_98);
x_5 = x_59;
x_6 = x_105;
x_7 = x_62;
x_8 = x_104;
x_9 = x_102;
x_10 = x_65;
x_11 = x_127;
x_12 = x_106;
goto block_50;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_136 = lean_mk_string_unchecked("", 0, 0);
x_137 = l_String_split___at___Lean_stringToMessageData_spec__0(x_98);
lean_dec(x_98);
x_138 = lean_array_mk(x_137);
x_139 = l_String_split___at___Lean_stringToMessageData_spec__0(x_106);
lean_dec(x_106);
x_140 = lean_array_mk(x_139);
x_141 = l_Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5(x_136, x_138, x_140);
x_142 = l_Lean_Diff_linesToString___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__32(x_141);
lean_dec(x_141);
x_5 = x_59;
x_6 = x_105;
x_7 = x_62;
x_8 = x_104;
x_9 = x_102;
x_10 = x_65;
x_11 = x_127;
x_12 = x_142;
goto block_50;
}
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; uint8_t x_157; 
lean_dec(x_106);
lean_dec(x_105);
lean_dec(x_104);
lean_dec(x_102);
lean_dec(x_98);
lean_dec(x_85);
lean_dec(x_65);
lean_dec(x_62);
x_143 = lean_st_ref_take(x_59, x_97);
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_143, 1);
lean_inc(x_145);
lean_dec(x_143);
x_146 = lean_ctor_get(x_144, 0);
lean_inc(x_146);
x_147 = l_Lean_MessageLog_append(x_99, x_92);
x_148 = lean_ctor_get(x_144, 2);
lean_inc(x_148);
x_149 = lean_ctor_get(x_144, 3);
lean_inc(x_149);
x_150 = lean_ctor_get(x_144, 4);
lean_inc(x_150);
x_151 = lean_ctor_get(x_144, 5);
lean_inc(x_151);
x_152 = lean_ctor_get(x_144, 6);
lean_inc(x_152);
x_153 = lean_ctor_get(x_144, 7);
lean_inc(x_153);
x_154 = lean_ctor_get(x_144, 8);
lean_inc(x_154);
lean_dec(x_144);
x_155 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_155, 0, x_146);
lean_ctor_set(x_155, 1, x_147);
lean_ctor_set(x_155, 2, x_148);
lean_ctor_set(x_155, 3, x_149);
lean_ctor_set(x_155, 4, x_150);
lean_ctor_set(x_155, 5, x_151);
lean_ctor_set(x_155, 6, x_152);
lean_ctor_set(x_155, 7, x_153);
lean_ctor_set(x_155, 8, x_154);
x_156 = lean_st_ref_set(x_59, x_155, x_145);
lean_dec(x_59);
x_157 = !lean_is_exclusive(x_156);
if (x_157 == 0)
{
lean_object* x_158; lean_object* x_159; 
x_158 = lean_ctor_get(x_156, 0);
lean_dec(x_158);
x_159 = lean_box(0);
lean_ctor_set(x_156, 0, x_159);
return x_156;
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_160 = lean_ctor_get(x_156, 1);
lean_inc(x_160);
lean_dec(x_156);
x_161 = lean_box(0);
x_162 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_162, 1, x_160);
return x_162;
}
}
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; uint8_t x_189; 
x_163 = lean_ctor_get(x_81, 1);
lean_inc(x_163);
lean_dec(x_81);
x_164 = l_Lean_MessageLog_append(x_64, x_67);
x_165 = l_Lean_MessageLog_empty;
x_166 = l_Lean_MessageLog_toList(x_164);
x_167 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_167, 0, x_165);
lean_ctor_set(x_167, 1, x_165);
x_168 = l_List_forIn_x27_loop___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___redArg(x_58, x_166, x_167, x_163);
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_168, 1);
lean_inc(x_170);
lean_dec(x_168);
x_171 = lean_ctor_get(x_169, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_169, 1);
lean_inc(x_172);
lean_dec(x_169);
x_173 = l_Lean_MessageLog_toList(x_171);
lean_dec(x_171);
x_174 = lean_box(0);
x_175 = l_List_mapM_loop___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__4___redArg(x_173, x_174, x_170);
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_175, 1);
lean_inc(x_177);
lean_dec(x_175);
x_178 = l_Lean_Elab_Tactic_GuardMsgs_removeTrailingWhitespaceMarker(x_57);
lean_dec(x_57);
x_179 = lean_ctor_get(x_66, 1);
lean_inc(x_179);
lean_dec(x_66);
x_180 = l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply(x_63, x_176);
x_181 = lean_mk_string_unchecked("---\n", 4, 4);
x_182 = l_String_intercalate(x_181, x_180);
lean_dec(x_181);
x_183 = lean_string_utf8_byte_size(x_182);
lean_inc(x_1);
x_184 = l_Substring_takeWhileAux___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1(x_1, x_182, x_183, x_56);
x_185 = l_Substring_takeRightWhileAux___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2(x_1, x_182, x_184, x_183);
x_186 = lean_string_utf8_extract(x_182, x_184, x_185);
x_187 = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply(x_60, x_178);
x_188 = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply(x_60, x_186);
x_189 = lean_string_dec_eq(x_187, x_188);
lean_dec(x_188);
lean_dec(x_187);
if (x_189 == 0)
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; uint8_t x_215; 
lean_dec(x_172);
x_190 = lean_st_ref_take(x_59, x_177);
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_190, 1);
lean_inc(x_192);
lean_dec(x_190);
x_193 = lean_ctor_get(x_191, 0);
lean_inc(x_193);
x_194 = l_Lean_MessageLog_append(x_179, x_164);
x_195 = lean_ctor_get(x_191, 2);
lean_inc(x_195);
x_196 = lean_ctor_get(x_191, 3);
lean_inc(x_196);
x_197 = lean_ctor_get(x_191, 4);
lean_inc(x_197);
x_198 = lean_ctor_get(x_191, 5);
lean_inc(x_198);
x_199 = lean_ctor_get(x_191, 6);
lean_inc(x_199);
x_200 = lean_ctor_get(x_191, 7);
lean_inc(x_200);
x_201 = lean_ctor_get(x_191, 8);
lean_inc(x_201);
lean_dec(x_191);
x_202 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_202, 0, x_193);
lean_ctor_set(x_202, 1, x_194);
lean_ctor_set(x_202, 2, x_195);
lean_ctor_set(x_202, 3, x_196);
lean_ctor_set(x_202, 4, x_197);
lean_ctor_set(x_202, 5, x_198);
lean_ctor_set(x_202, 6, x_199);
lean_ctor_set(x_202, 7, x_200);
lean_ctor_set(x_202, 8, x_201);
x_203 = lean_st_ref_set(x_59, x_202, x_192);
x_204 = lean_ctor_get(x_203, 1);
lean_inc(x_204);
lean_dec(x_203);
x_205 = lean_st_ref_get(x_59, x_204);
x_206 = lean_ctor_get(x_205, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_205, 1);
lean_inc(x_207);
lean_dec(x_205);
x_208 = l_Lean_Elab_Command_instInhabitedScope;
x_209 = lean_ctor_get(x_206, 2);
lean_inc(x_209);
lean_dec(x_206);
x_210 = l_List_head_x21(lean_box(0), x_208, x_209);
lean_dec(x_209);
x_211 = lean_ctor_get(x_210, 1);
lean_inc(x_211);
lean_dec(x_210);
x_212 = lean_mk_string_unchecked("guard_msgs", 10, 10);
x_213 = lean_mk_string_unchecked("diff", 4, 4);
x_214 = l_Lean_Name_mkStr2(x_212, x_213);
x_215 = l_Lean_KVMap_getBool(x_211, x_214, x_189);
lean_dec(x_214);
lean_dec(x_211);
if (x_215 == 0)
{
lean_dec(x_178);
x_5 = x_59;
x_6 = x_185;
x_7 = x_62;
x_8 = x_184;
x_9 = x_182;
x_10 = x_65;
x_11 = x_207;
x_12 = x_186;
goto block_50;
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_216 = lean_mk_string_unchecked("", 0, 0);
x_217 = l_String_split___at___Lean_stringToMessageData_spec__0(x_178);
lean_dec(x_178);
x_218 = lean_array_mk(x_217);
x_219 = l_String_split___at___Lean_stringToMessageData_spec__0(x_186);
lean_dec(x_186);
x_220 = lean_array_mk(x_219);
x_221 = l_Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5(x_216, x_218, x_220);
x_222 = l_Lean_Diff_linesToString___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__32(x_221);
lean_dec(x_221);
x_5 = x_59;
x_6 = x_185;
x_7 = x_62;
x_8 = x_184;
x_9 = x_182;
x_10 = x_65;
x_11 = x_207;
x_12 = x_222;
goto block_50;
}
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
lean_dec(x_186);
lean_dec(x_185);
lean_dec(x_184);
lean_dec(x_182);
lean_dec(x_178);
lean_dec(x_164);
lean_dec(x_65);
lean_dec(x_62);
x_223 = lean_st_ref_take(x_59, x_177);
x_224 = lean_ctor_get(x_223, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_223, 1);
lean_inc(x_225);
lean_dec(x_223);
x_226 = lean_ctor_get(x_224, 0);
lean_inc(x_226);
x_227 = l_Lean_MessageLog_append(x_179, x_172);
x_228 = lean_ctor_get(x_224, 2);
lean_inc(x_228);
x_229 = lean_ctor_get(x_224, 3);
lean_inc(x_229);
x_230 = lean_ctor_get(x_224, 4);
lean_inc(x_230);
x_231 = lean_ctor_get(x_224, 5);
lean_inc(x_231);
x_232 = lean_ctor_get(x_224, 6);
lean_inc(x_232);
x_233 = lean_ctor_get(x_224, 7);
lean_inc(x_233);
x_234 = lean_ctor_get(x_224, 8);
lean_inc(x_234);
lean_dec(x_224);
x_235 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_235, 0, x_226);
lean_ctor_set(x_235, 1, x_227);
lean_ctor_set(x_235, 2, x_228);
lean_ctor_set(x_235, 3, x_229);
lean_ctor_set(x_235, 4, x_230);
lean_ctor_set(x_235, 5, x_231);
lean_ctor_set(x_235, 6, x_232);
lean_ctor_set(x_235, 7, x_233);
lean_ctor_set(x_235, 8, x_234);
x_236 = lean_st_ref_set(x_59, x_235, x_225);
lean_dec(x_59);
x_237 = lean_ctor_get(x_236, 1);
lean_inc(x_237);
if (lean_is_exclusive(x_236)) {
 lean_ctor_release(x_236, 0);
 lean_ctor_release(x_236, 1);
 x_238 = x_236;
} else {
 lean_dec_ref(x_236);
 x_238 = lean_box(0);
}
x_239 = lean_box(0);
if (lean_is_scalar(x_238)) {
 x_240 = lean_alloc_ctor(0, 2, 0);
} else {
 x_240 = x_238;
}
lean_ctor_set(x_240, 0, x_239);
lean_ctor_set(x_240, 1, x_237);
return x_240;
}
}
}
block_323:
{
lean_object* x_250; lean_object* x_251; 
x_250 = lean_string_utf8_byte_size(x_249);
x_251 = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec(x_247, x_248, x_245, x_244);
if (lean_obj_tag(x_251) == 0)
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; size_t x_263; lean_object* x_264; lean_object* x_265; size_t x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; uint8_t x_292; lean_object* x_293; lean_object* x_294; 
x_252 = lean_ctor_get(x_251, 0);
lean_inc(x_252);
x_253 = lean_ctor_get(x_252, 1);
lean_inc(x_253);
x_254 = lean_ctor_get(x_251, 1);
lean_inc(x_254);
lean_dec(x_251);
x_255 = lean_ctor_get(x_252, 0);
lean_inc(x_255);
lean_dec(x_252);
x_256 = lean_ctor_get(x_253, 0);
lean_inc(x_256);
x_257 = lean_ctor_get(x_253, 1);
lean_inc(x_257);
lean_dec(x_253);
x_258 = lean_st_ref_take(x_245, x_254);
x_259 = lean_ctor_get(x_258, 0);
lean_inc(x_259);
x_260 = lean_ctor_get(x_258, 1);
lean_inc(x_260);
lean_dec(x_258);
x_261 = lean_ctor_get(x_259, 0);
lean_inc(x_261);
x_262 = lean_unsigned_to_nat(5u);
x_263 = lean_usize_of_nat(x_262);
x_264 = lean_usize_to_nat(x_263);
x_265 = lean_nat_pow(x_242, x_264);
lean_dec(x_264);
x_266 = lean_usize_of_nat(x_265);
lean_dec(x_265);
x_267 = lean_usize_to_nat(x_266);
x_268 = lean_mk_empty_array_with_capacity(x_267);
lean_dec(x_267);
lean_inc(x_268);
x_269 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_269, 0, x_268);
x_270 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_270, 0, x_269);
lean_ctor_set(x_270, 1, x_268);
lean_ctor_set(x_270, 2, x_56);
lean_ctor_set(x_270, 3, x_56);
lean_ctor_set_usize(x_270, 4, x_263);
x_271 = lean_box(0);
lean_inc(x_270);
x_272 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_272, 0, x_270);
lean_ctor_set(x_272, 1, x_270);
lean_ctor_set(x_272, 2, x_271);
x_273 = lean_ctor_get(x_259, 2);
lean_inc(x_273);
x_274 = lean_ctor_get(x_259, 3);
lean_inc(x_274);
x_275 = lean_ctor_get(x_259, 4);
lean_inc(x_275);
x_276 = lean_ctor_get(x_259, 5);
lean_inc(x_276);
x_277 = lean_ctor_get(x_259, 6);
lean_inc(x_277);
x_278 = lean_ctor_get(x_259, 7);
lean_inc(x_278);
x_279 = lean_ctor_get(x_259, 8);
lean_inc(x_279);
lean_inc(x_272);
x_280 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_280, 0, x_261);
lean_ctor_set(x_280, 1, x_272);
lean_ctor_set(x_280, 2, x_273);
lean_ctor_set(x_280, 3, x_274);
lean_ctor_set(x_280, 4, x_275);
lean_ctor_set(x_280, 5, x_276);
lean_ctor_set(x_280, 6, x_277);
lean_ctor_set(x_280, 7, x_278);
lean_ctor_set(x_280, 8, x_279);
x_281 = lean_st_ref_set(x_245, x_280, x_260);
x_282 = lean_ctor_get(x_281, 1);
lean_inc(x_282);
lean_dec(x_281);
x_283 = lean_ctor_get(x_248, 0);
lean_inc(x_283);
x_284 = lean_ctor_get(x_248, 1);
lean_inc(x_284);
x_285 = lean_ctor_get(x_248, 2);
lean_inc(x_285);
x_286 = lean_ctor_get(x_248, 3);
lean_inc(x_286);
x_287 = lean_ctor_get(x_248, 4);
lean_inc(x_287);
x_288 = lean_ctor_get(x_248, 5);
lean_inc(x_288);
x_289 = lean_ctor_get(x_248, 6);
lean_inc(x_289);
x_290 = lean_box(0);
x_291 = lean_ctor_get(x_248, 8);
lean_inc(x_291);
x_292 = lean_ctor_get_uint8(x_248, sizeof(void*)*9);
x_293 = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(x_293, 0, x_283);
lean_ctor_set(x_293, 1, x_284);
lean_ctor_set(x_293, 2, x_285);
lean_ctor_set(x_293, 3, x_286);
lean_ctor_set(x_293, 4, x_287);
lean_ctor_set(x_293, 5, x_288);
lean_ctor_set(x_293, 6, x_289);
lean_ctor_set(x_293, 7, x_290);
lean_ctor_set(x_293, 8, x_291);
lean_ctor_set_uint8(x_293, sizeof(void*)*9, x_292);
lean_inc(x_245);
x_294 = l_Lean_Elab_Command_elabCommandTopLevel(x_243, x_293, x_245, x_282);
lean_dec(x_293);
if (lean_obj_tag(x_294) == 0)
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; uint8_t x_308; 
x_295 = lean_ctor_get(x_294, 1);
lean_inc(x_295);
lean_dec(x_294);
x_296 = lean_st_ref_get(x_245, x_295);
x_297 = lean_ctor_get(x_296, 0);
lean_inc(x_297);
x_298 = lean_ctor_get(x_296, 1);
lean_inc(x_298);
lean_dec(x_296);
x_299 = lean_st_ref_get(x_245, x_298);
x_300 = lean_ctor_get(x_299, 0);
lean_inc(x_300);
x_301 = lean_ctor_get(x_299, 1);
lean_inc(x_301);
lean_dec(x_299);
lean_inc(x_1);
x_302 = l_Substring_takeWhileAux___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1(x_1, x_249, x_250, x_56);
lean_inc(x_1);
x_303 = l_Substring_takeRightWhileAux___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2(x_1, x_249, x_302, x_250);
x_304 = lean_string_utf8_extract(x_249, x_302, x_303);
lean_dec(x_303);
lean_dec(x_302);
lean_dec(x_249);
x_305 = lean_ctor_get(x_297, 1);
lean_inc(x_305);
lean_dec(x_297);
x_306 = lean_ctor_get(x_300, 8);
lean_inc(x_306);
lean_dec(x_300);
x_307 = lean_array_get_size(x_306);
x_308 = lean_nat_dec_lt(x_56, x_307);
if (x_308 == 0)
{
uint8_t x_309; uint8_t x_310; 
lean_dec(x_307);
lean_dec(x_306);
x_309 = lean_unbox(x_255);
lean_dec(x_255);
x_310 = lean_unbox(x_256);
lean_dec(x_256);
x_57 = x_304;
x_58 = x_257;
x_59 = x_245;
x_60 = x_309;
x_61 = x_301;
x_62 = x_246;
x_63 = x_310;
x_64 = x_305;
x_65 = x_248;
x_66 = x_259;
x_67 = x_272;
goto block_241;
}
else
{
uint8_t x_311; 
x_311 = lean_nat_dec_le(x_307, x_307);
if (x_311 == 0)
{
uint8_t x_312; uint8_t x_313; 
lean_dec(x_307);
lean_dec(x_306);
x_312 = lean_unbox(x_255);
lean_dec(x_255);
x_313 = lean_unbox(x_256);
lean_dec(x_256);
x_57 = x_304;
x_58 = x_257;
x_59 = x_245;
x_60 = x_312;
x_61 = x_301;
x_62 = x_246;
x_63 = x_313;
x_64 = x_305;
x_65 = x_248;
x_66 = x_259;
x_67 = x_272;
goto block_241;
}
else
{
size_t x_314; size_t x_315; lean_object* x_316; uint8_t x_317; uint8_t x_318; 
x_314 = lean_usize_of_nat(x_56);
x_315 = lean_usize_of_nat(x_307);
lean_dec(x_307);
x_316 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__34(x_306, x_314, x_315, x_272);
lean_dec(x_306);
x_317 = lean_unbox(x_255);
lean_dec(x_255);
x_318 = lean_unbox(x_256);
lean_dec(x_256);
x_57 = x_304;
x_58 = x_257;
x_59 = x_245;
x_60 = x_317;
x_61 = x_301;
x_62 = x_246;
x_63 = x_318;
x_64 = x_305;
x_65 = x_248;
x_66 = x_259;
x_67 = x_316;
goto block_241;
}
}
}
else
{
lean_dec(x_272);
lean_dec(x_259);
lean_dec(x_257);
lean_dec(x_256);
lean_dec(x_255);
lean_dec(x_250);
lean_dec(x_249);
lean_dec(x_248);
lean_dec(x_246);
lean_dec(x_245);
lean_dec(x_1);
return x_294;
}
}
else
{
uint8_t x_319; 
lean_dec(x_250);
lean_dec(x_249);
lean_dec(x_248);
lean_dec(x_246);
lean_dec(x_245);
lean_dec(x_243);
lean_dec(x_1);
x_319 = !lean_is_exclusive(x_251);
if (x_319 == 0)
{
return x_251;
}
else
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; 
x_320 = lean_ctor_get(x_251, 0);
x_321 = lean_ctor_get(x_251, 1);
lean_inc(x_321);
lean_inc(x_320);
lean_dec(x_251);
x_322 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_322, 0, x_320);
lean_ctor_set(x_322, 1, x_321);
return x_322;
}
}
}
block_342:
{
lean_object* x_332; 
x_332 = l_Lean_Syntax_getArg(x_1, x_330);
if (lean_obj_tag(x_327) == 0)
{
lean_object* x_333; 
x_333 = lean_mk_string_unchecked("", 0, 0);
x_242 = x_324;
x_243 = x_325;
x_244 = x_328;
x_245 = x_326;
x_246 = x_332;
x_247 = x_331;
x_248 = x_329;
x_249 = x_333;
goto block_323;
}
else
{
lean_object* x_334; lean_object* x_335; 
x_334 = lean_ctor_get(x_327, 0);
lean_inc(x_334);
lean_dec(x_327);
x_335 = l_Lean_getDocStringText___at___Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0(x_334, x_329, x_326, x_328);
lean_dec(x_334);
if (lean_obj_tag(x_335) == 0)
{
lean_object* x_336; lean_object* x_337; 
x_336 = lean_ctor_get(x_335, 0);
lean_inc(x_336);
x_337 = lean_ctor_get(x_335, 1);
lean_inc(x_337);
lean_dec(x_335);
x_242 = x_324;
x_243 = x_325;
x_244 = x_337;
x_245 = x_326;
x_246 = x_332;
x_247 = x_331;
x_248 = x_329;
x_249 = x_336;
goto block_323;
}
else
{
uint8_t x_338; 
lean_dec(x_332);
lean_dec(x_331);
lean_dec(x_329);
lean_dec(x_326);
lean_dec(x_325);
lean_dec(x_1);
x_338 = !lean_is_exclusive(x_335);
if (x_338 == 0)
{
return x_335;
}
else
{
lean_object* x_339; lean_object* x_340; lean_object* x_341; 
x_339 = lean_ctor_get(x_335, 0);
x_340 = lean_ctor_get(x_335, 1);
lean_inc(x_340);
lean_inc(x_339);
lean_dec(x_335);
x_341 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_341, 0, x_339);
lean_ctor_set(x_341, 1, x_340);
return x_341;
}
}
}
}
block_357:
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; 
x_347 = lean_unsigned_to_nat(1u);
x_348 = lean_unsigned_to_nat(2u);
x_349 = l_Lean_Syntax_getArg(x_1, x_348);
x_350 = lean_unsigned_to_nat(4u);
x_351 = l_Lean_Syntax_getArg(x_1, x_350);
x_352 = l_Lean_Syntax_getOptional_x3f(x_349);
lean_dec(x_349);
if (lean_obj_tag(x_352) == 0)
{
lean_object* x_353; 
x_353 = lean_box(0);
x_324 = x_348;
x_325 = x_351;
x_326 = x_345;
x_327 = x_343;
x_328 = x_346;
x_329 = x_344;
x_330 = x_347;
x_331 = x_353;
goto block_342;
}
else
{
uint8_t x_354; 
x_354 = !lean_is_exclusive(x_352);
if (x_354 == 0)
{
x_324 = x_348;
x_325 = x_351;
x_326 = x_345;
x_327 = x_343;
x_328 = x_346;
x_329 = x_344;
x_330 = x_347;
x_331 = x_352;
goto block_342;
}
else
{
lean_object* x_355; lean_object* x_356; 
x_355 = lean_ctor_get(x_352, 0);
lean_inc(x_355);
lean_dec(x_352);
x_356 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_356, 0, x_355);
x_324 = x_348;
x_325 = x_351;
x_326 = x_345;
x_327 = x_343;
x_328 = x_346;
x_329 = x_344;
x_330 = x_347;
x_331 = x_356;
goto block_342;
}
}
}
}
block_50:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_13 = lean_mk_string_unchecked("❌️ Docstring on `#guard_msgs` does not match generated message:\n\n", 69, 65);
x_14 = l_Lean_stringToMessageData(x_13);
lean_dec(x_13);
x_15 = l_Lean_stringToMessageData(x_12);
lean_dec(x_12);
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_mk_string_unchecked("", 0, 0);
x_18 = l_Lean_stringToMessageData(x_17);
lean_dec(x_17);
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
lean_inc(x_10);
x_20 = l_Lean_logErrorAt___at___Lean_Elab_logException___at___Lean_Elab_Command_runLinters_spec__0_spec__0(x_7, x_19, x_10, x_5, x_11);
lean_dec(x_7);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_20, 1);
x_23 = lean_ctor_get(x_20, 0);
lean_dec(x_23);
x_24 = l_Lean_Elab_Command_getRef(x_10, x_5, x_22);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = lean_ctor_get(x_24, 1);
x_28 = l_Lean_Elab_Tactic_GuardMsgs_instImpl____x40_Lean_Elab_GuardMsgs___hyg_1820_;
x_29 = lean_string_utf8_extract(x_9, x_8, x_6);
lean_dec(x_6);
lean_dec(x_8);
lean_dec(x_9);
lean_ctor_set(x_24, 1, x_29);
lean_ctor_set(x_24, 0, x_28);
lean_ctor_set(x_20, 1, x_24);
lean_ctor_set(x_20, 0, x_26);
x_30 = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(x_30, 0, x_20);
x_31 = l_Lean_Elab_pushInfoLeaf___at___Lean_Elab_addCompletionInfo___at___Lean_Elab_elabSetOption___at___Lean_withSetOptionIn_spec__0_spec__0_spec__0(x_30, x_10, x_5, x_27);
lean_dec(x_5);
lean_dec(x_10);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_32 = lean_ctor_get(x_24, 0);
x_33 = lean_ctor_get(x_24, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_24);
x_34 = l_Lean_Elab_Tactic_GuardMsgs_instImpl____x40_Lean_Elab_GuardMsgs___hyg_1820_;
x_35 = lean_string_utf8_extract(x_9, x_8, x_6);
lean_dec(x_6);
lean_dec(x_8);
lean_dec(x_9);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
lean_ctor_set(x_20, 1, x_36);
lean_ctor_set(x_20, 0, x_32);
x_37 = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(x_37, 0, x_20);
x_38 = l_Lean_Elab_pushInfoLeaf___at___Lean_Elab_addCompletionInfo___at___Lean_Elab_elabSetOption___at___Lean_withSetOptionIn_spec__0_spec__0_spec__0(x_37, x_10, x_5, x_33);
lean_dec(x_5);
lean_dec(x_10);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_39 = lean_ctor_get(x_20, 1);
lean_inc(x_39);
lean_dec(x_20);
x_40 = l_Lean_Elab_Command_getRef(x_10, x_5, x_39);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_43 = x_40;
} else {
 lean_dec_ref(x_40);
 x_43 = lean_box(0);
}
x_44 = l_Lean_Elab_Tactic_GuardMsgs_instImpl____x40_Lean_Elab_GuardMsgs___hyg_1820_;
x_45 = lean_string_utf8_extract(x_9, x_8, x_6);
lean_dec(x_6);
lean_dec(x_8);
lean_dec(x_9);
if (lean_is_scalar(x_43)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_43;
}
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_41);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(x_48, 0, x_47);
x_49 = l_Lean_Elab_pushInfoLeaf___at___Lean_Elab_addCompletionInfo___at___Lean_Elab_elabSetOption___at___Lean_withSetOptionIn_spec__0_spec__0_spec__0(x_48, x_10, x_5, x_42);
lean_dec(x_5);
lean_dec(x_10);
return x_49;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Substring_takeWhileAux___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Substring_takeWhileAux___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Substring_takeRightWhileAux___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Substring_takeRightWhileAux___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_List_forIn_x27_loop___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_List_mapM_loop___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__4(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_matchPrefix_go___at___Lean_Diff_matchPrefix___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__5_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Diff_matchPrefix_go___at___Lean_Diff_matchPrefix___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__5_spec__5(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_matchPrefix___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__5___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Diff_matchPrefix___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__5(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_matchSuffix_go___at___Lean_Diff_matchSuffix___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__7_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Diff_matchSuffix_go___at___Lean_Diff_matchSuffix___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__7_spec__7(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_matchSuffix___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__7___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Diff_matchSuffix___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__7(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Diff_Histogram_addLeft___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__9_spec__9___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Diff_Histogram_addLeft___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__9_spec__9___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Diff_Histogram_addLeft___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__9_spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Diff_Histogram_addLeft___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__9_spec__9(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Diff_Histogram_addLeft___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__9_spec__10___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Diff_Histogram_addLeft___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__9_spec__10___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Diff_Histogram_addLeft___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__9_spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Diff_Histogram_addLeft___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__9_spec__10(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Diff_Histogram_addLeft___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__9(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__16___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_Range_forIn_x27_loop___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__16___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__16___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_Range_forIn_x27_loop___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__16(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__17___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Diff_Histogram_addRight___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__17(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__18___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_Range_forIn_x27_loop___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__18___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__18___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_Range_forIn_x27_loop___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__18(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__19___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_forIn_x27_loop___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__19(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__20___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_foldrM___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__20(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__21___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldrMUnsafe_fold___at___Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5_spec__21(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Diff_lcs___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__5(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__23___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Loop_forIn_loop___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__23(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__24___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Loop_forIn_loop___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__24(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__25_spec__25___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__25_spec__25(x_1, x_2, x_3, x_4, x_8, x_9, x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__25___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = l_Array_forIn_x27Unsafe_loop___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__25(x_1, x_2, x_3, x_4, x_8, x_9, x_7);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__27___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Loop_forIn_loop___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__27(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__28___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Loop_forIn_loop___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__28(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__29___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__29(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__30___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Lean_Diff_diff___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5_spec__30(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Diff_linesToString___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__32_spec__32___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_forIn_x27Unsafe_loop___at___Lean_Diff_linesToString___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__32_spec__32(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_linesToString___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__32___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Diff_linesToString___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__32(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__34_spec__34___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__34_spec__34(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__34___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__34(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = l_Lean_Elab_Command_commandElabAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("guardMsgsCmd", 12, 12);
lean_inc(x_3);
x_5 = l_Lean_Name_mkStr2(x_3, x_4);
x_6 = lean_mk_string_unchecked("Elab", 4, 4);
x_7 = lean_mk_string_unchecked("Tactic", 6, 6);
x_8 = lean_mk_string_unchecked("GuardMsgs", 9, 9);
x_9 = lean_mk_string_unchecked("elabGuardMsgs", 13, 13);
x_10 = l_Lean_Name_mkStr5(x_3, x_6, x_7, x_8, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs), 4, 0);
x_12 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_5, x_10, x_11, x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Elab", 4, 4);
x_4 = lean_mk_string_unchecked("Tactic", 6, 6);
x_5 = lean_mk_string_unchecked("GuardMsgs", 9, 9);
x_6 = lean_mk_string_unchecked("elabGuardMsgs", 13, 13);
x_7 = l_Lean_Name_mkStr5(x_2, x_3, x_4, x_5, x_6);
x_8 = lean_unsigned_to_nat(137u);
x_9 = lean_unsigned_to_nat(42u);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_unsigned_to_nat(168u);
x_12 = lean_unsigned_to_nat(31u);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_9);
lean_ctor_set(x_14, 2, x_13);
lean_ctor_set(x_14, 3, x_12);
x_15 = lean_unsigned_to_nat(46u);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_8);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_unsigned_to_nat(59u);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_8);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_15);
lean_ctor_set(x_19, 2, x_18);
lean_ctor_set(x_19, 3, x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_14);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_addBuiltinDeclarationRanges(x_7, x_20, x_1);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_findSomeMAux___at___Lean_PersistentArray_findSomeM_x3f___at___Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
x_6 = lean_box(0);
x_7 = lean_array_uget(x_1, x_3);
x_8 = l_Lean_PersistentArray_findSomeMAux___at___Lean_PersistentArray_findSomeM_x3f___at___Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0(x_7);
lean_dec(x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; 
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_6);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_usize_of_nat(x_11);
x_13 = lean_usize_add(x_3, x_12);
x_3 = x_13;
x_4 = x_10;
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_8);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_6);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_findSomeMAux___at___Lean_PersistentArray_findSomeM_x3f___at___Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0_spec__1_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_3, x_2);
if (x_11 == 0)
{
return x_4;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_4);
x_12 = lean_box(0);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_array_uget(x_1, x_3);
if (lean_obj_tag(x_15) == 1)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
lean_dec(x_18);
if (lean_obj_tag(x_17) == 9)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_17, 0);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
x_24 = l_Lean_Elab_Tactic_GuardMsgs_instImpl____x40_Lean_Elab_GuardMsgs___hyg_1820_;
x_25 = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(x_23, x_24);
lean_dec(x_23);
if (lean_obj_tag(x_25) == 0)
{
lean_free_object(x_20);
lean_dec(x_22);
lean_free_object(x_17);
lean_free_object(x_15);
x_5 = x_14;
goto block_10;
}
else
{
uint8_t x_26; 
lean_dec(x_14);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_25, 0);
lean_ctor_set(x_20, 1, x_27);
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 0, x_25);
lean_ctor_set_tag(x_15, 0);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_25, 0);
lean_inc(x_28);
lean_dec(x_25);
lean_ctor_set(x_20, 1, x_28);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_20);
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 0, x_29);
lean_ctor_set_tag(x_15, 0);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_20, 0);
x_31 = lean_ctor_get(x_20, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_20);
x_32 = l_Lean_Elab_Tactic_GuardMsgs_instImpl____x40_Lean_Elab_GuardMsgs___hyg_1820_;
x_33 = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(x_31, x_32);
lean_dec(x_31);
if (lean_obj_tag(x_33) == 0)
{
lean_dec(x_30);
lean_free_object(x_17);
lean_free_object(x_15);
x_5 = x_14;
goto block_10;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_14);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 x_35 = x_33;
} else {
 lean_dec_ref(x_33);
 x_35 = lean_box(0);
}
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_30);
lean_ctor_set(x_36, 1, x_34);
if (lean_is_scalar(x_35)) {
 x_37 = lean_alloc_ctor(1, 1, 0);
} else {
 x_37 = x_35;
}
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 0, x_37);
lean_ctor_set_tag(x_15, 0);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_38 = lean_ctor_get(x_17, 0);
lean_inc(x_38);
lean_dec(x_17);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_41 = x_38;
} else {
 lean_dec_ref(x_38);
 x_41 = lean_box(0);
}
x_42 = l_Lean_Elab_Tactic_GuardMsgs_instImpl____x40_Lean_Elab_GuardMsgs___hyg_1820_;
x_43 = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(x_40, x_42);
lean_dec(x_40);
if (lean_obj_tag(x_43) == 0)
{
lean_dec(x_41);
lean_dec(x_39);
lean_free_object(x_15);
x_5 = x_14;
goto block_10;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_14);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 x_45 = x_43;
} else {
 lean_dec_ref(x_43);
 x_45 = lean_box(0);
}
if (lean_is_scalar(x_41)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_41;
}
lean_ctor_set(x_46, 0, x_39);
lean_ctor_set(x_46, 1, x_44);
if (lean_is_scalar(x_45)) {
 x_47 = lean_alloc_ctor(1, 1, 0);
} else {
 x_47 = x_45;
}
lean_ctor_set(x_47, 0, x_46);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set_tag(x_15, 0);
lean_ctor_set(x_15, 1, x_13);
lean_ctor_set(x_15, 0, x_48);
return x_15;
}
}
}
else
{
lean_free_object(x_15);
lean_dec(x_17);
x_5 = x_14;
goto block_10;
}
}
else
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_15, 0);
lean_inc(x_49);
lean_dec(x_15);
if (lean_obj_tag(x_49) == 9)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 x_51 = x_49;
} else {
 lean_dec_ref(x_49);
 x_51 = lean_box(0);
}
x_52 = lean_ctor_get(x_50, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_54 = x_50;
} else {
 lean_dec_ref(x_50);
 x_54 = lean_box(0);
}
x_55 = l_Lean_Elab_Tactic_GuardMsgs_instImpl____x40_Lean_Elab_GuardMsgs___hyg_1820_;
x_56 = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(x_53, x_55);
lean_dec(x_53);
if (lean_obj_tag(x_56) == 0)
{
lean_dec(x_54);
lean_dec(x_52);
lean_dec(x_51);
x_5 = x_14;
goto block_10;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_14);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 x_58 = x_56;
} else {
 lean_dec_ref(x_56);
 x_58 = lean_box(0);
}
if (lean_is_scalar(x_54)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_54;
}
lean_ctor_set(x_59, 0, x_52);
lean_ctor_set(x_59, 1, x_57);
if (lean_is_scalar(x_58)) {
 x_60 = lean_alloc_ctor(1, 1, 0);
} else {
 x_60 = x_58;
}
lean_ctor_set(x_60, 0, x_59);
if (lean_is_scalar(x_51)) {
 x_61 = lean_alloc_ctor(1, 1, 0);
} else {
 x_61 = x_51;
 lean_ctor_set_tag(x_61, 1);
}
lean_ctor_set(x_61, 0, x_60);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_13);
return x_62;
}
}
else
{
lean_dec(x_49);
x_5 = x_14;
goto block_10;
}
}
}
else
{
lean_dec(x_15);
x_5 = x_14;
goto block_10;
}
}
block_10:
{
lean_object* x_6; size_t x_7; size_t x_8; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_usize_of_nat(x_6);
x_8 = lean_usize_add(x_3, x_7);
x_3 = x_8;
x_4 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_findSomeMAux___at___Lean_PersistentArray_findSomeM_x3f___at___Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_3, x_2);
if (x_11 == 0)
{
lean_inc(x_4);
return x_4;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_box(0);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_array_uget(x_1, x_3);
if (lean_obj_tag(x_15) == 1)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
lean_dec(x_18);
if (lean_obj_tag(x_17) == 9)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_17, 0);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
x_24 = l_Lean_Elab_Tactic_GuardMsgs_instImpl____x40_Lean_Elab_GuardMsgs___hyg_1820_;
x_25 = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(x_23, x_24);
lean_dec(x_23);
if (lean_obj_tag(x_25) == 0)
{
lean_free_object(x_20);
lean_dec(x_22);
lean_free_object(x_17);
lean_free_object(x_15);
x_5 = x_14;
goto block_10;
}
else
{
uint8_t x_26; 
lean_dec(x_14);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_25, 0);
lean_ctor_set(x_20, 1, x_27);
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 0, x_25);
lean_ctor_set_tag(x_15, 0);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_25, 0);
lean_inc(x_28);
lean_dec(x_25);
lean_ctor_set(x_20, 1, x_28);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_20);
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 0, x_29);
lean_ctor_set_tag(x_15, 0);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_20, 0);
x_31 = lean_ctor_get(x_20, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_20);
x_32 = l_Lean_Elab_Tactic_GuardMsgs_instImpl____x40_Lean_Elab_GuardMsgs___hyg_1820_;
x_33 = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(x_31, x_32);
lean_dec(x_31);
if (lean_obj_tag(x_33) == 0)
{
lean_dec(x_30);
lean_free_object(x_17);
lean_free_object(x_15);
x_5 = x_14;
goto block_10;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_14);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 x_35 = x_33;
} else {
 lean_dec_ref(x_33);
 x_35 = lean_box(0);
}
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_30);
lean_ctor_set(x_36, 1, x_34);
if (lean_is_scalar(x_35)) {
 x_37 = lean_alloc_ctor(1, 1, 0);
} else {
 x_37 = x_35;
}
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 0, x_37);
lean_ctor_set_tag(x_15, 0);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_38 = lean_ctor_get(x_17, 0);
lean_inc(x_38);
lean_dec(x_17);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_41 = x_38;
} else {
 lean_dec_ref(x_38);
 x_41 = lean_box(0);
}
x_42 = l_Lean_Elab_Tactic_GuardMsgs_instImpl____x40_Lean_Elab_GuardMsgs___hyg_1820_;
x_43 = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(x_40, x_42);
lean_dec(x_40);
if (lean_obj_tag(x_43) == 0)
{
lean_dec(x_41);
lean_dec(x_39);
lean_free_object(x_15);
x_5 = x_14;
goto block_10;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_14);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 x_45 = x_43;
} else {
 lean_dec_ref(x_43);
 x_45 = lean_box(0);
}
if (lean_is_scalar(x_41)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_41;
}
lean_ctor_set(x_46, 0, x_39);
lean_ctor_set(x_46, 1, x_44);
if (lean_is_scalar(x_45)) {
 x_47 = lean_alloc_ctor(1, 1, 0);
} else {
 x_47 = x_45;
}
lean_ctor_set(x_47, 0, x_46);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set_tag(x_15, 0);
lean_ctor_set(x_15, 1, x_13);
lean_ctor_set(x_15, 0, x_48);
return x_15;
}
}
}
else
{
lean_free_object(x_15);
lean_dec(x_17);
x_5 = x_14;
goto block_10;
}
}
else
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_15, 0);
lean_inc(x_49);
lean_dec(x_15);
if (lean_obj_tag(x_49) == 9)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 x_51 = x_49;
} else {
 lean_dec_ref(x_49);
 x_51 = lean_box(0);
}
x_52 = lean_ctor_get(x_50, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_54 = x_50;
} else {
 lean_dec_ref(x_50);
 x_54 = lean_box(0);
}
x_55 = l_Lean_Elab_Tactic_GuardMsgs_instImpl____x40_Lean_Elab_GuardMsgs___hyg_1820_;
x_56 = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(x_53, x_55);
lean_dec(x_53);
if (lean_obj_tag(x_56) == 0)
{
lean_dec(x_54);
lean_dec(x_52);
lean_dec(x_51);
x_5 = x_14;
goto block_10;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_14);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 x_58 = x_56;
} else {
 lean_dec_ref(x_56);
 x_58 = lean_box(0);
}
if (lean_is_scalar(x_54)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_54;
}
lean_ctor_set(x_59, 0, x_52);
lean_ctor_set(x_59, 1, x_57);
if (lean_is_scalar(x_58)) {
 x_60 = lean_alloc_ctor(1, 1, 0);
} else {
 x_60 = x_58;
}
lean_ctor_set(x_60, 0, x_59);
if (lean_is_scalar(x_51)) {
 x_61 = lean_alloc_ctor(1, 1, 0);
} else {
 x_61 = x_51;
 lean_ctor_set_tag(x_61, 1);
}
lean_ctor_set(x_61, 0, x_60);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_13);
return x_62;
}
}
else
{
lean_dec(x_49);
x_5 = x_14;
goto block_10;
}
}
}
else
{
lean_dec(x_15);
x_5 = x_14;
goto block_10;
}
}
block_10:
{
lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_usize_of_nat(x_6);
x_8 = lean_usize_add(x_3, x_7);
x_9 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_findSomeMAux___at___Lean_PersistentArray_findSomeM_x3f___at___Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0_spec__1_spec__1(x_1, x_2, x_8, x_5);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at___Lean_PersistentArray_findSomeM_x3f___at___Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; size_t x_6; lean_object* x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_box(0);
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
x_6 = lean_array_size(x_2);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_usize_of_nat(x_7);
x_9 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_findSomeMAux___at___Lean_PersistentArray_findSomeM_x3f___at___Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0_spec__0(x_2, x_6, x_8, x_5);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_box(0);
return x_11;
}
else
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
return x_12;
}
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; lean_object* x_18; size_t x_19; lean_object* x_20; lean_object* x_21; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_box(0);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_array_size(x_13);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_usize_of_nat(x_18);
x_20 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_findSomeMAux___at___Lean_PersistentArray_findSomeM_x3f___at___Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0_spec__1(x_13, x_17, x_19, x_16);
lean_dec(x_16);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec(x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = lean_box(0);
return x_22;
}
else
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
lean_dec(x_21);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___at___Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = l_Lean_PersistentArray_findSomeMAux___at___Lean_PersistentArray_findSomeM_x3f___at___Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0(x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; lean_object* x_9; size_t x_10; lean_object* x_11; lean_object* x_12; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_box(0);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_array_size(x_4);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_usize_of_nat(x_9);
x_11 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_findSomeMAux___at___Lean_PersistentArray_findSomeM_x3f___at___Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0_spec__1(x_4, x_8, x_10, x_7);
lean_dec(x_7);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
if (lean_obj_tag(x_12) == 0)
{
return x_3;
}
else
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
return x_13;
}
}
else
{
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_18; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_2);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_19 = lean_ctor_get(x_1, 0);
x_20 = lean_unsigned_to_nat(0u);
x_21 = l_Array_empty(lean_box(0));
x_22 = lean_mk_string_unchecked("null", 4, 4);
x_23 = l_Lean_Name_mkStr1(x_22);
x_24 = lean_box(2);
x_25 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
lean_ctor_set(x_25, 2, x_21);
x_26 = l_Lean_Syntax_setArg(x_3, x_20, x_25);
x_27 = l_Lean_Syntax_getPos_x3f(x_26, x_4);
lean_dec(x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_2);
lean_ctor_set(x_28, 1, x_17);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_45; uint8_t x_51; lean_object* x_57; uint8_t x_58; 
lean_dec(x_2);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 x_30 = x_27;
} else {
 lean_dec_ref(x_27);
 x_30 = lean_box(0);
}
x_45 = l_Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace(x_16);
x_57 = lean_string_utf8_byte_size(x_45);
x_58 = l_instDecidableEqPos(x_57, x_20);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_59 = lean_string_length(x_45);
x_60 = lean_unsigned_to_nat(93u);
x_61 = lean_nat_dec_le(x_59, x_60);
lean_dec(x_59);
if (x_61 == 0)
{
lean_dec(x_57);
x_51 = x_61;
goto block_56;
}
else
{
uint8_t x_62; 
x_62 = l_String_anyAux___at___Lean_Parser_checkTailLinebreak_spec__0(x_45, x_57, x_20);
lean_dec(x_57);
if (x_62 == 0)
{
x_51 = x_61;
goto block_56;
}
else
{
goto block_50;
}
}
}
else
{
lean_object* x_63; 
lean_dec(x_57);
lean_dec(x_45);
x_63 = lean_mk_string_unchecked("", 0, 0);
x_31 = x_63;
goto block_44;
}
block_44:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_32 = l_Lean_Server_FileWorker_EditableDocument_versionedIdentifier(x_5);
x_33 = lean_ctor_get(x_5, 0);
lean_inc(x_33);
lean_dec(x_5);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec(x_33);
x_35 = lean_ctor_get(x_34, 3);
lean_inc(x_35);
lean_dec(x_34);
lean_inc(x_19);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_19);
lean_ctor_set(x_36, 1, x_29);
x_37 = l_Lean_FileMap_utf8RangeToLspRange(x_35, x_36);
lean_dec(x_36);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_31);
lean_ctor_set(x_39, 2, x_38);
lean_ctor_set(x_39, 3, x_6);
x_40 = l_Lean_Lsp_WorkspaceEdit_ofTextEdit(x_32, x_39);
if (lean_is_scalar(x_30)) {
 x_41 = lean_alloc_ctor(1, 1, 0);
} else {
 x_41 = x_30;
}
lean_ctor_set(x_41, 0, x_40);
x_42 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_42, 0, x_7);
lean_ctor_set(x_42, 1, x_8);
lean_ctor_set(x_42, 2, x_9);
lean_ctor_set(x_42, 3, x_10);
lean_ctor_set(x_42, 4, x_11);
lean_ctor_set(x_42, 5, x_12);
lean_ctor_set(x_42, 6, x_13);
lean_ctor_set(x_42, 7, x_41);
lean_ctor_set(x_42, 8, x_14);
lean_ctor_set(x_42, 9, x_15);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_17);
return x_43;
}
block_50:
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_46 = lean_mk_string_unchecked("/--\n", 4, 4);
x_47 = lean_string_append(x_46, x_45);
lean_dec(x_45);
x_48 = lean_mk_string_unchecked("\n-/\n", 4, 4);
x_49 = lean_string_append(x_47, x_48);
lean_dec(x_48);
x_31 = x_49;
goto block_44;
}
block_56:
{
if (x_51 == 0)
{
goto block_50;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_mk_string_unchecked("/-- ", 4, 4);
x_53 = lean_string_append(x_52, x_45);
lean_dec(x_45);
x_54 = lean_mk_string_unchecked(" -/\n", 4, 4);
x_55 = lean_string_append(x_53, x_54);
lean_dec(x_54);
x_31 = x_55;
goto block_44;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 0);
lean_dec(x_6);
x_7 = l_Lean_PersistentArray_findSomeM_x3f___at___Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0(x_5);
lean_dec(x_5);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_mk_empty_array_with_capacity(x_8);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_3);
lean_ctor_set(x_1, 0, x_9);
return x_1;
}
else
{
uint8_t x_10; 
lean_free_object(x_1);
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_7, 0);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = l_Lean_Server_RequestM_readDoc___at___Lean_Server_RequestM_withWaitFindSnapAtPos_spec__0(x_2, x_3);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_box(0);
x_19 = lean_mk_string_unchecked("Update #guard_msgs with tactic output", 37, 37);
x_20 = lean_mk_string_unchecked("quickfix", 8, 8);
lean_ctor_set(x_7, 0, x_20);
x_21 = lean_box(0);
x_22 = lean_box(1);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_box(0);
x_25 = lean_box(0);
x_26 = lean_box(0);
lean_inc(x_23);
lean_inc(x_7);
lean_inc(x_19);
x_27 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_27, 0, x_18);
lean_ctor_set(x_27, 1, x_18);
lean_ctor_set(x_27, 2, x_19);
lean_ctor_set(x_27, 3, x_7);
lean_ctor_set(x_27, 4, x_21);
lean_ctor_set(x_27, 5, x_23);
lean_ctor_set(x_27, 6, x_18);
lean_ctor_set(x_27, 7, x_24);
lean_ctor_set(x_27, 8, x_25);
lean_ctor_set(x_27, 9, x_26);
x_28 = lean_unbox(x_22);
x_29 = l_Lean_Syntax_getPos_x3f(x_13, x_28);
lean_inc(x_27);
x_30 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___boxed), 17, 16);
lean_closure_set(x_30, 0, x_29);
lean_closure_set(x_30, 1, x_27);
lean_closure_set(x_30, 2, x_13);
lean_closure_set(x_30, 3, x_22);
lean_closure_set(x_30, 4, x_17);
lean_closure_set(x_30, 5, x_18);
lean_closure_set(x_30, 6, x_18);
lean_closure_set(x_30, 7, x_18);
lean_closure_set(x_30, 8, x_19);
lean_closure_set(x_30, 9, x_7);
lean_closure_set(x_30, 10, x_21);
lean_closure_set(x_30, 11, x_23);
lean_closure_set(x_30, 12, x_18);
lean_closure_set(x_30, 13, x_25);
lean_closure_set(x_30, 14, x_26);
lean_closure_set(x_30, 15, x_14);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_11, 1, x_31);
lean_ctor_set(x_11, 0, x_27);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_mk_empty_array_with_capacity(x_32);
x_34 = lean_array_push(x_33, x_11);
lean_ctor_set(x_15, 0, x_34);
return x_15;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_35 = lean_ctor_get(x_15, 0);
x_36 = lean_ctor_get(x_15, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_15);
x_37 = lean_box(0);
x_38 = lean_mk_string_unchecked("Update #guard_msgs with tactic output", 37, 37);
x_39 = lean_mk_string_unchecked("quickfix", 8, 8);
lean_ctor_set(x_7, 0, x_39);
x_40 = lean_box(0);
x_41 = lean_box(1);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
x_43 = lean_box(0);
x_44 = lean_box(0);
x_45 = lean_box(0);
lean_inc(x_42);
lean_inc(x_7);
lean_inc(x_38);
x_46 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_46, 0, x_37);
lean_ctor_set(x_46, 1, x_37);
lean_ctor_set(x_46, 2, x_38);
lean_ctor_set(x_46, 3, x_7);
lean_ctor_set(x_46, 4, x_40);
lean_ctor_set(x_46, 5, x_42);
lean_ctor_set(x_46, 6, x_37);
lean_ctor_set(x_46, 7, x_43);
lean_ctor_set(x_46, 8, x_44);
lean_ctor_set(x_46, 9, x_45);
x_47 = lean_unbox(x_41);
x_48 = l_Lean_Syntax_getPos_x3f(x_13, x_47);
lean_inc(x_46);
x_49 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___boxed), 17, 16);
lean_closure_set(x_49, 0, x_48);
lean_closure_set(x_49, 1, x_46);
lean_closure_set(x_49, 2, x_13);
lean_closure_set(x_49, 3, x_41);
lean_closure_set(x_49, 4, x_35);
lean_closure_set(x_49, 5, x_37);
lean_closure_set(x_49, 6, x_37);
lean_closure_set(x_49, 7, x_37);
lean_closure_set(x_49, 8, x_38);
lean_closure_set(x_49, 9, x_7);
lean_closure_set(x_49, 10, x_40);
lean_closure_set(x_49, 11, x_42);
lean_closure_set(x_49, 12, x_37);
lean_closure_set(x_49, 13, x_44);
lean_closure_set(x_49, 14, x_45);
lean_closure_set(x_49, 15, x_14);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_11, 1, x_50);
lean_ctor_set(x_11, 0, x_46);
x_51 = lean_unsigned_to_nat(1u);
x_52 = lean_mk_empty_array_with_capacity(x_51);
x_53 = lean_array_push(x_52, x_11);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_36);
return x_54;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_55 = lean_ctor_get(x_11, 0);
x_56 = lean_ctor_get(x_11, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_11);
x_57 = l_Lean_Server_RequestM_readDoc___at___Lean_Server_RequestM_withWaitFindSnapAtPos_spec__0(x_2, x_3);
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
x_61 = lean_box(0);
x_62 = lean_mk_string_unchecked("Update #guard_msgs with tactic output", 37, 37);
x_63 = lean_mk_string_unchecked("quickfix", 8, 8);
lean_ctor_set(x_7, 0, x_63);
x_64 = lean_box(0);
x_65 = lean_box(1);
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_65);
x_67 = lean_box(0);
x_68 = lean_box(0);
x_69 = lean_box(0);
lean_inc(x_66);
lean_inc(x_7);
lean_inc(x_62);
x_70 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_70, 0, x_61);
lean_ctor_set(x_70, 1, x_61);
lean_ctor_set(x_70, 2, x_62);
lean_ctor_set(x_70, 3, x_7);
lean_ctor_set(x_70, 4, x_64);
lean_ctor_set(x_70, 5, x_66);
lean_ctor_set(x_70, 6, x_61);
lean_ctor_set(x_70, 7, x_67);
lean_ctor_set(x_70, 8, x_68);
lean_ctor_set(x_70, 9, x_69);
x_71 = lean_unbox(x_65);
x_72 = l_Lean_Syntax_getPos_x3f(x_55, x_71);
lean_inc(x_70);
x_73 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___boxed), 17, 16);
lean_closure_set(x_73, 0, x_72);
lean_closure_set(x_73, 1, x_70);
lean_closure_set(x_73, 2, x_55);
lean_closure_set(x_73, 3, x_65);
lean_closure_set(x_73, 4, x_58);
lean_closure_set(x_73, 5, x_61);
lean_closure_set(x_73, 6, x_61);
lean_closure_set(x_73, 7, x_61);
lean_closure_set(x_73, 8, x_62);
lean_closure_set(x_73, 9, x_7);
lean_closure_set(x_73, 10, x_64);
lean_closure_set(x_73, 11, x_66);
lean_closure_set(x_73, 12, x_61);
lean_closure_set(x_73, 13, x_68);
lean_closure_set(x_73, 14, x_69);
lean_closure_set(x_73, 15, x_56);
x_74 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_74, 0, x_73);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_70);
lean_ctor_set(x_75, 1, x_74);
x_76 = lean_unsigned_to_nat(1u);
x_77 = lean_mk_empty_array_with_capacity(x_76);
x_78 = lean_array_push(x_77, x_75);
if (lean_is_scalar(x_60)) {
 x_79 = lean_alloc_ctor(0, 2, 0);
} else {
 x_79 = x_60;
}
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_59);
return x_79;
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_80 = lean_ctor_get(x_7, 0);
lean_inc(x_80);
lean_dec(x_7);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_83 = x_80;
} else {
 lean_dec_ref(x_80);
 x_83 = lean_box(0);
}
x_84 = l_Lean_Server_RequestM_readDoc___at___Lean_Server_RequestM_withWaitFindSnapAtPos_spec__0(x_2, x_3);
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
x_88 = lean_box(0);
x_89 = lean_mk_string_unchecked("Update #guard_msgs with tactic output", 37, 37);
x_90 = lean_mk_string_unchecked("quickfix", 8, 8);
x_91 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_91, 0, x_90);
x_92 = lean_box(0);
x_93 = lean_box(1);
x_94 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_94, 0, x_93);
x_95 = lean_box(0);
x_96 = lean_box(0);
x_97 = lean_box(0);
lean_inc(x_94);
lean_inc(x_91);
lean_inc(x_89);
x_98 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_98, 0, x_88);
lean_ctor_set(x_98, 1, x_88);
lean_ctor_set(x_98, 2, x_89);
lean_ctor_set(x_98, 3, x_91);
lean_ctor_set(x_98, 4, x_92);
lean_ctor_set(x_98, 5, x_94);
lean_ctor_set(x_98, 6, x_88);
lean_ctor_set(x_98, 7, x_95);
lean_ctor_set(x_98, 8, x_96);
lean_ctor_set(x_98, 9, x_97);
x_99 = lean_unbox(x_93);
x_100 = l_Lean_Syntax_getPos_x3f(x_81, x_99);
lean_inc(x_98);
x_101 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___boxed), 17, 16);
lean_closure_set(x_101, 0, x_100);
lean_closure_set(x_101, 1, x_98);
lean_closure_set(x_101, 2, x_81);
lean_closure_set(x_101, 3, x_93);
lean_closure_set(x_101, 4, x_85);
lean_closure_set(x_101, 5, x_88);
lean_closure_set(x_101, 6, x_88);
lean_closure_set(x_101, 7, x_88);
lean_closure_set(x_101, 8, x_89);
lean_closure_set(x_101, 9, x_91);
lean_closure_set(x_101, 10, x_92);
lean_closure_set(x_101, 11, x_94);
lean_closure_set(x_101, 12, x_88);
lean_closure_set(x_101, 13, x_96);
lean_closure_set(x_101, 14, x_97);
lean_closure_set(x_101, 15, x_82);
x_102 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_102, 0, x_101);
if (lean_is_scalar(x_83)) {
 x_103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_103 = x_83;
}
lean_ctor_set(x_103, 0, x_98);
lean_ctor_set(x_103, 1, x_102);
x_104 = lean_unsigned_to_nat(1u);
x_105 = lean_mk_empty_array_with_capacity(x_104);
x_106 = lean_array_push(x_105, x_103);
if (lean_is_scalar(x_87)) {
 x_107 = lean_alloc_ctor(0, 2, 0);
} else {
 x_107 = x_87;
}
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_86);
return x_107;
}
}
}
else
{
lean_object* x_108; lean_object* x_109; 
x_108 = lean_ctor_get(x_1, 1);
lean_inc(x_108);
lean_dec(x_1);
x_109 = l_Lean_PersistentArray_findSomeM_x3f___at___Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0(x_108);
lean_dec(x_108);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_unsigned_to_nat(0u);
x_111 = lean_mk_empty_array_with_capacity(x_110);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_3);
return x_112;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_113 = lean_ctor_get(x_109, 0);
lean_inc(x_113);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 x_114 = x_109;
} else {
 lean_dec_ref(x_109);
 x_114 = lean_box(0);
}
x_115 = lean_ctor_get(x_113, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_113, 1);
lean_inc(x_116);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 x_117 = x_113;
} else {
 lean_dec_ref(x_113);
 x_117 = lean_box(0);
}
x_118 = l_Lean_Server_RequestM_readDoc___at___Lean_Server_RequestM_withWaitFindSnapAtPos_spec__0(x_2, x_3);
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
x_122 = lean_box(0);
x_123 = lean_mk_string_unchecked("Update #guard_msgs with tactic output", 37, 37);
x_124 = lean_mk_string_unchecked("quickfix", 8, 8);
if (lean_is_scalar(x_114)) {
 x_125 = lean_alloc_ctor(1, 1, 0);
} else {
 x_125 = x_114;
}
lean_ctor_set(x_125, 0, x_124);
x_126 = lean_box(0);
x_127 = lean_box(1);
x_128 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_128, 0, x_127);
x_129 = lean_box(0);
x_130 = lean_box(0);
x_131 = lean_box(0);
lean_inc(x_128);
lean_inc(x_125);
lean_inc(x_123);
x_132 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_132, 0, x_122);
lean_ctor_set(x_132, 1, x_122);
lean_ctor_set(x_132, 2, x_123);
lean_ctor_set(x_132, 3, x_125);
lean_ctor_set(x_132, 4, x_126);
lean_ctor_set(x_132, 5, x_128);
lean_ctor_set(x_132, 6, x_122);
lean_ctor_set(x_132, 7, x_129);
lean_ctor_set(x_132, 8, x_130);
lean_ctor_set(x_132, 9, x_131);
x_133 = lean_unbox(x_127);
x_134 = l_Lean_Syntax_getPos_x3f(x_115, x_133);
lean_inc(x_132);
x_135 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___boxed), 17, 16);
lean_closure_set(x_135, 0, x_134);
lean_closure_set(x_135, 1, x_132);
lean_closure_set(x_135, 2, x_115);
lean_closure_set(x_135, 3, x_127);
lean_closure_set(x_135, 4, x_119);
lean_closure_set(x_135, 5, x_122);
lean_closure_set(x_135, 6, x_122);
lean_closure_set(x_135, 7, x_122);
lean_closure_set(x_135, 8, x_123);
lean_closure_set(x_135, 9, x_125);
lean_closure_set(x_135, 10, x_126);
lean_closure_set(x_135, 11, x_128);
lean_closure_set(x_135, 12, x_122);
lean_closure_set(x_135, 13, x_130);
lean_closure_set(x_135, 14, x_131);
lean_closure_set(x_135, 15, x_116);
x_136 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_136, 0, x_135);
if (lean_is_scalar(x_117)) {
 x_137 = lean_alloc_ctor(0, 2, 0);
} else {
 x_137 = x_117;
}
lean_ctor_set(x_137, 0, x_132);
lean_ctor_set(x_137, 1, x_136);
x_138 = lean_unsigned_to_nat(1u);
x_139 = lean_mk_empty_array_with_capacity(x_138);
x_140 = lean_array_push(x_139, x_137);
if (lean_is_scalar(x_121)) {
 x_141 = lean_alloc_ctor(0, 2, 0);
} else {
 x_141 = x_121;
}
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_120);
return x_141;
}
}
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
lean_dec(x_1);
x_142 = lean_unsigned_to_nat(0u);
x_143 = lean_mk_empty_array_with_capacity(x_142);
x_144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_3);
return x_144;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg(x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_findSomeMAux___at___Lean_PersistentArray_findSomeM_x3f___at___Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_findSomeMAux___at___Lean_PersistentArray_findSomeM_x3f___at___Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0_spec__0(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_findSomeMAux___at___Lean_PersistentArray_findSomeM_x3f___at___Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_findSomeMAux___at___Lean_PersistentArray_findSomeM_x3f___at___Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0_spec__1_spec__1(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_findSomeMAux___at___Lean_PersistentArray_findSomeM_x3f___at___Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_findSomeMAux___at___Lean_PersistentArray_findSomeM_x3f___at___Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0_spec__1(x_1, x_5, x_6, x_4);
lean_dec(x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at___Lean_PersistentArray_findSomeM_x3f___at___Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PersistentArray_findSomeMAux___at___Lean_PersistentArray_findSomeM_x3f___at___Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___at___Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PersistentArray_findSomeM_x3f___at___Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
uint8_t x_18; lean_object* x_19; 
x_18 = lean_unbox(x_4);
lean_dec(x_4);
x_19 = l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0(x_1, x_2, x_3, x_18, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_16);
lean_dec(x_1);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_declare__1____x40_Lean_Elab_GuardMsgs___hyg_3378_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("guardMsgsCmd", 12, 12);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_mk_empty_array_with_capacity(x_5);
x_7 = lean_array_push(x_6, x_4);
x_8 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___boxed), 6, 0);
x_9 = l_Lean_CodeAction_insertBuiltin(x_7, x_8, x_1);
lean_dec(x_7);
return x_9;
}
}
lean_object* initialize_Lean_Elab_Notation(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_Diff(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Server_CodeActions_Attr(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_GuardMsgs(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Notation(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_Diff(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_CodeActions_Attr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
if (builtin) {res = l_initFn____x40_Lean_Elab_GuardMsgs___hyg_6_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_guard__msgs_diff = lean_io_result_get_value(res);
lean_mark_persistent(l_guard__msgs_diff);
lean_dec_ref(res);
}l_Lean_Elab_Tactic_GuardMsgs_instImpl____x40_Lean_Elab_GuardMsgs___hyg_1820_ = _init_l_Lean_Elab_Tactic_GuardMsgs_instImpl____x40_Lean_Elab_GuardMsgs___hyg_1820_();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardMsgs_instImpl____x40_Lean_Elab_GuardMsgs___hyg_1820_);
l_Lean_Elab_Tactic_GuardMsgs_instTypeNameGuardMsgFailure = _init_l_Lean_Elab_Tactic_GuardMsgs_instTypeNameGuardMsgFailure();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardMsgs_instTypeNameGuardMsgFailure);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_declare__1____x40_Lean_Elab_GuardMsgs___hyg_3378_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
