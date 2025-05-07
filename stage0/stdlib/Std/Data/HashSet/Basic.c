// Lean compiler output
// Module: Std.Data.HashSet.Basic
// Imports: Std.Data.HashMap.Basic
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
lean_object* l_Std_DHashMap_Internal_AssocList_getKey_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_getKey___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Internal_numBuckets___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet___aux__Std__Data__HashSet__Basic______unexpand__Std__HashSet__Equiv__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_numBuckets___at___Std_HashSet_Internal_numBuckets_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_filter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_empty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_emptyWithCapacity___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_any___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_forM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_union___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet___aux__Std__Data__HashSet__Basic______unexpand__Std__HashSet__Equiv__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_ofArray(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_instInsert___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_HashSet_any___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_HashSet_all___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_partition___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_emptyWithCapacity___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_instRepr___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_instMembership(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_get_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_instRepr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_union___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_size(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_erase(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_foldM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_insertMany___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_getD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_toList(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldrMUnsafe_fold___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_forM___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_forM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_AssocList_contains(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_toArray___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_filter___redArg___lam__1(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_replace___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_instSingleton(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_foldM___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_all___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_get___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_toList___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_all___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_toList___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_ofList(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_Internal_numBuckets___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_filter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_filter___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_forIn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_instInhabited___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_all___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_HashSet_forIn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_forM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_instForM___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_numBuckets___at___Std_HashSet_Internal_numBuckets_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_HashSet_filter___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_filter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_getD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_instDecidableMem___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_get(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Internal_numBuckets(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_size___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_instUnion(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_all___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_forM___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_foldM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_getD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_instMembership___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_instForIn(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_instUnion___redArg(lean_object*, lean_object*);
lean_object* l_List_repr___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_filter___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_instRepr___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_size___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_instEmptyCollection___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_contains___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_erase___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_insert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_union___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_forM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_partition___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_partition(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_fold___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_instForM___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_get_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_HashSet_contains(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Internal_numBuckets___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_getKey_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_instDecidableMem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_any___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_union(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_HashSet_any(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_get___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_forIn___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_partition___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_length___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_empty___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_containsThenInsert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_instSingleton___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_foldM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_fold___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_insertMany___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forIn_x27_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_toArray___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_toList___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_foldM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forIn_x27Unsafe_loop___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_toList___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_term___x7em__;
LEAN_EXPORT lean_object* l_Std_HashSet_empty(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_HashSet_isEmpty(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DHashMap_instDecidableMem___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_forM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_instRepr___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_numBuckets___at___Std_HashSet_Internal_numBuckets_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_ofList___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_HashSet_instDecidableMem___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_isEmpty___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_instDecidableNot___redArg(uint8_t);
LEAN_EXPORT lean_object* l_Std_HashSet_any___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_toArray___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_contains___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_insertMany(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_size___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_instSingleton___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_instForM(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_instRepr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_foldM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_getD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_instForIn___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_union___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT lean_object* l_Std_HashSet_toArray(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_forIn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_instEmptyCollection(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_emptyWithCapacity___redArg(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Std_HashSet_emptyWithCapacity(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_get_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_get_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_getKeyD___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_all___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_ofList___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_instInsert(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_instForIn___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_any___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_toList___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_instInsert___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_get_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_get_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_HashSet_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_HashSet_instDecidableMem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_containsThenInsert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_fold___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_erase___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_forIn___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_empty___redArg___boxed(lean_object*);
lean_object* l_String_toSubstring_x27(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_toArray___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_forInStep_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_isEmpty___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_HashSet_all(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_filter(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_get_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_forIn___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_numBuckets___at___Std_HashSet_Internal_numBuckets_spec__0___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_HashSet_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_toArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Internal_numBuckets___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_instInhabited(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_ofArray___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_emptyWithCapacity___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_shiftl(x_1, x_3);
x_5 = lean_unsigned_to_nat(3u);
x_6 = lean_nat_div(x_4, x_5);
lean_dec(x_4);
x_7 = l_Nat_nextPowerOfTwo(x_6);
lean_dec(x_6);
x_8 = lean_box(0);
x_9 = lean_mk_array(x_7, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_emptyWithCapacity(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_unsigned_to_nat(2u);
x_7 = lean_nat_shiftl(x_4, x_6);
x_8 = lean_unsigned_to_nat(3u);
x_9 = lean_nat_div(x_7, x_8);
lean_dec(x_7);
x_10 = l_Nat_nextPowerOfTwo(x_9);
lean_dec(x_9);
x_11 = lean_box(0);
x_12 = lean_mk_array(x_10, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_emptyWithCapacity___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_HashSet_emptyWithCapacity___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_emptyWithCapacity___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_HashSet_emptyWithCapacity(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_empty___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_shiftl(x_1, x_3);
x_5 = lean_unsigned_to_nat(3u);
x_6 = lean_nat_div(x_4, x_5);
lean_dec(x_4);
x_7 = l_Nat_nextPowerOfTwo(x_6);
lean_dec(x_6);
x_8 = lean_box(0);
x_9 = lean_mk_array(x_7, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_empty(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_unsigned_to_nat(2u);
x_7 = lean_nat_shiftl(x_4, x_6);
x_8 = lean_unsigned_to_nat(3u);
x_9 = lean_nat_div(x_7, x_8);
lean_dec(x_7);
x_10 = l_Nat_nextPowerOfTwo(x_9);
lean_dec(x_9);
x_11 = lean_box(0);
x_12 = lean_mk_array(x_10, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_empty___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_HashSet_empty___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_empty___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_HashSet_empty(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instEmptyCollection(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_4 = lean_unsigned_to_nat(8u);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_unsigned_to_nat(2u);
x_7 = lean_nat_shiftl(x_4, x_6);
x_8 = lean_unsigned_to_nat(3u);
x_9 = lean_nat_div(x_7, x_8);
lean_dec(x_7);
x_10 = l_Nat_nextPowerOfTwo(x_9);
lean_dec(x_9);
x_11 = lean_box(0);
x_12 = lean_mk_array(x_10, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instEmptyCollection___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_HashSet_instEmptyCollection(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instInhabited(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_4 = lean_unsigned_to_nat(8u);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_unsigned_to_nat(2u);
x_7 = lean_nat_shiftl(x_4, x_6);
x_8 = lean_unsigned_to_nat(3u);
x_9 = lean_nat_div(x_7, x_8);
lean_dec(x_7);
x_10 = l_Nat_nextPowerOfTwo(x_9);
lean_dec(x_9);
x_11 = lean_box(0);
x_12 = lean_mk_array(x_10, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instInhabited___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_HashSet_instInhabited(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Std_HashSet_term___x7em__() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_1 = lean_mk_string_unchecked("Std", 3, 3);
x_2 = lean_mk_string_unchecked("HashSet", 7, 7);
x_3 = lean_mk_string_unchecked("term_~m_", 8, 8);
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
x_5 = lean_unsigned_to_nat(50u);
x_6 = lean_mk_string_unchecked("andthen", 7, 7);
x_7 = l_Lean_Name_mkStr1(x_6);
x_8 = lean_mk_string_unchecked(" ~m ", 4, 4);
x_9 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_mk_string_unchecked("term", 4, 4);
x_11 = l_Lean_Name_mkStr1(x_10);
x_12 = lean_unsigned_to_nat(51u);
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_9);
lean_ctor_set(x_14, 2, x_13);
x_15 = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_5);
lean_ctor_set(x_15, 2, x_5);
lean_ctor_set(x_15, 3, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_mk_string_unchecked("Std", 3, 3);
x_5 = lean_mk_string_unchecked("HashSet", 7, 7);
x_6 = lean_mk_string_unchecked("term_~m_", 8, 8);
lean_inc(x_5);
lean_inc(x_4);
x_7 = l_Lean_Name_mkStr3(x_4, x_5, x_6);
lean_inc(x_1);
x_8 = l_Lean_Syntax_isOfKind(x_1, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(1);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_3);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
x_13 = lean_unsigned_to_nat(2u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
lean_dec(x_1);
x_15 = lean_ctor_get(x_2, 5);
lean_inc(x_15);
x_16 = lean_box(0);
x_17 = lean_unbox(x_16);
x_18 = l_Lean_SourceInfo_fromRef(x_15, x_17);
lean_dec(x_15);
x_19 = lean_ctor_get(x_2, 2);
lean_inc(x_19);
x_20 = lean_ctor_get(x_2, 1);
lean_inc(x_20);
lean_dec(x_2);
x_21 = lean_mk_string_unchecked("Lean", 4, 4);
x_22 = lean_mk_string_unchecked("Parser", 6, 6);
x_23 = lean_mk_string_unchecked("Term", 4, 4);
x_24 = lean_mk_string_unchecked("app", 3, 3);
x_25 = l_Lean_Name_mkStr4(x_21, x_22, x_23, x_24);
x_26 = lean_mk_string_unchecked("Equiv", 5, 5);
lean_inc(x_26);
x_27 = l_String_toSubstring_x27(x_26);
lean_inc(x_26);
x_28 = l_Lean_Name_mkStr1(x_26);
x_29 = l_Lean_addMacroScope(x_20, x_28, x_19);
x_30 = l_Lean_Name_mkStr3(x_4, x_5, x_26);
x_31 = lean_box(0);
lean_inc(x_30);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_30);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_32);
lean_ctor_set(x_36, 1, x_35);
lean_inc(x_18);
x_37 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_37, 0, x_18);
lean_ctor_set(x_37, 1, x_27);
lean_ctor_set(x_37, 2, x_29);
lean_ctor_set(x_37, 3, x_36);
x_38 = lean_mk_string_unchecked("null", 4, 4);
x_39 = l_Lean_Name_mkStr1(x_38);
lean_inc(x_18);
x_40 = l_Lean_Syntax_node2(x_18, x_39, x_12, x_14);
x_41 = l_Lean_Syntax_node2(x_18, x_25, x_37, x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_3);
return x_42;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet___aux__Std__Data__HashSet__Basic______unexpand__Std__HashSet__Equiv__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Term", 4, 4);
x_7 = lean_mk_string_unchecked("app", 3, 3);
x_8 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_7);
lean_inc(x_1);
x_9 = l_Lean_Syntax_isOfKind(x_1, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_1);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Lean_Syntax_getArg(x_1, x_12);
x_14 = lean_mk_string_unchecked("ident", 5, 5);
x_15 = l_Lean_Name_mkStr1(x_14);
lean_inc(x_13);
x_16 = l_Lean_Syntax_isOfKind(x_13, x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_13);
lean_dec(x_1);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_3);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = l_Lean_Syntax_getArg(x_1, x_19);
lean_dec(x_1);
x_21 = lean_unsigned_to_nat(2u);
lean_inc(x_20);
x_22 = l_Lean_Syntax_matchesNull(x_20, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_20);
lean_dec(x_13);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_3);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_25 = l_Lean_Syntax_getArg(x_20, x_12);
x_26 = l_Lean_Syntax_getArg(x_20, x_19);
lean_dec(x_20);
x_27 = l_Lean_replaceRef(x_13, x_2);
lean_dec(x_13);
x_28 = lean_box(0);
x_29 = lean_unbox(x_28);
x_30 = l_Lean_SourceInfo_fromRef(x_27, x_29);
lean_dec(x_27);
x_31 = lean_mk_string_unchecked("Std", 3, 3);
x_32 = lean_mk_string_unchecked("HashSet", 7, 7);
x_33 = lean_mk_string_unchecked("term_~m_", 8, 8);
x_34 = l_Lean_Name_mkStr3(x_31, x_32, x_33);
x_35 = lean_mk_string_unchecked(" ~m ", 4, 4);
lean_inc(x_30);
x_36 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_36, 0, x_30);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_Lean_Syntax_node3(x_30, x_34, x_25, x_36, x_26);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_3);
return x_38;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet___aux__Std__Data__HashSet__Basic______unexpand__Std__HashSet__Equiv__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_HashSet___aux__Std__Data__HashSet__Basic______unexpand__Std__HashSet__Equiv__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_insert___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint64_t x_9; lean_object* x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; lean_object* x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; size_t x_18; size_t x_19; lean_object* x_20; size_t x_21; size_t x_22; size_t x_23; lean_object* x_24; uint8_t x_25; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
x_7 = lean_array_get_size(x_6);
lean_inc(x_2);
lean_inc(x_4);
x_8 = lean_apply_1(x_2, x_4);
x_9 = lean_unbox_uint64(x_8);
lean_dec(x_8);
x_10 = lean_unsigned_to_nat(32u);
x_11 = lean_uint64_of_nat(x_10);
x_12 = lean_uint64_shift_right(x_9, x_11);
x_13 = lean_uint64_xor(x_9, x_12);
x_14 = lean_unsigned_to_nat(16u);
x_15 = lean_uint64_of_nat(x_14);
x_16 = lean_uint64_shift_right(x_13, x_15);
x_17 = lean_uint64_xor(x_13, x_16);
x_18 = lean_uint64_to_usize(x_17);
x_19 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_usize_of_nat(x_20);
x_22 = lean_usize_sub(x_19, x_21);
x_23 = lean_usize_land(x_18, x_22);
x_24 = lean_array_uget(x_6, x_23);
lean_inc(x_24);
lean_inc(x_4);
x_25 = l_Std_DHashMap_Internal_AssocList_contains(lean_box(0), lean_box(0), x_1, x_4, x_24);
if (x_25 == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_3);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_27 = lean_ctor_get(x_3, 1);
lean_dec(x_27);
x_28 = lean_ctor_get(x_3, 0);
lean_dec(x_28);
x_29 = lean_box(0);
x_30 = lean_nat_add(x_5, x_20);
lean_dec(x_5);
x_31 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_31, 0, x_4);
lean_ctor_set(x_31, 1, x_29);
lean_ctor_set(x_31, 2, x_24);
x_32 = lean_array_uset(x_6, x_23, x_31);
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
x_39 = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(x_2, x_32);
lean_ctor_set(x_3, 1, x_39);
lean_ctor_set(x_3, 0, x_30);
return x_3;
}
else
{
lean_dec(x_2);
lean_ctor_set(x_3, 1, x_32);
lean_ctor_set(x_3, 0, x_30);
return x_3;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
lean_dec(x_3);
x_40 = lean_box(0);
x_41 = lean_nat_add(x_5, x_20);
lean_dec(x_5);
x_42 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_42, 0, x_4);
lean_ctor_set(x_42, 1, x_40);
lean_ctor_set(x_42, 2, x_24);
x_43 = lean_array_uset(x_6, x_23, x_42);
x_44 = lean_unsigned_to_nat(2u);
x_45 = lean_nat_shiftl(x_41, x_44);
x_46 = lean_unsigned_to_nat(3u);
x_47 = lean_nat_div(x_45, x_46);
lean_dec(x_45);
x_48 = lean_array_get_size(x_43);
x_49 = lean_nat_dec_le(x_47, x_48);
lean_dec(x_48);
lean_dec(x_47);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(x_2, x_43);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_41);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
else
{
lean_object* x_52; 
lean_dec(x_2);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_41);
lean_ctor_set(x_52, 1, x_43);
return x_52;
}
}
}
else
{
lean_dec(x_24);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_insert(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint64_t x_10; lean_object* x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; lean_object* x_15; uint64_t x_16; uint64_t x_17; uint64_t x_18; size_t x_19; size_t x_20; lean_object* x_21; size_t x_22; size_t x_23; size_t x_24; lean_object* x_25; uint8_t x_26; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
x_8 = lean_array_get_size(x_7);
lean_inc(x_3);
lean_inc(x_5);
x_9 = lean_apply_1(x_3, x_5);
x_10 = lean_unbox_uint64(x_9);
lean_dec(x_9);
x_11 = lean_unsigned_to_nat(32u);
x_12 = lean_uint64_of_nat(x_11);
x_13 = lean_uint64_shift_right(x_10, x_12);
x_14 = lean_uint64_xor(x_10, x_13);
x_15 = lean_unsigned_to_nat(16u);
x_16 = lean_uint64_of_nat(x_15);
x_17 = lean_uint64_shift_right(x_14, x_16);
x_18 = lean_uint64_xor(x_14, x_17);
x_19 = lean_uint64_to_usize(x_18);
x_20 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_usize_of_nat(x_21);
x_23 = lean_usize_sub(x_20, x_22);
x_24 = lean_usize_land(x_19, x_23);
x_25 = lean_array_uget(x_7, x_24);
lean_inc(x_25);
lean_inc(x_5);
x_26 = l_Std_DHashMap_Internal_AssocList_contains(lean_box(0), lean_box(0), x_2, x_5, x_25);
if (x_26 == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_4);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_28 = lean_ctor_get(x_4, 1);
lean_dec(x_28);
x_29 = lean_ctor_get(x_4, 0);
lean_dec(x_29);
x_30 = lean_box(0);
x_31 = lean_nat_add(x_6, x_21);
lean_dec(x_6);
x_32 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_32, 0, x_5);
lean_ctor_set(x_32, 1, x_30);
lean_ctor_set(x_32, 2, x_25);
x_33 = lean_array_uset(x_7, x_24, x_32);
x_34 = lean_unsigned_to_nat(2u);
x_35 = lean_nat_shiftl(x_31, x_34);
x_36 = lean_unsigned_to_nat(3u);
x_37 = lean_nat_div(x_35, x_36);
lean_dec(x_35);
x_38 = lean_array_get_size(x_33);
x_39 = lean_nat_dec_le(x_37, x_38);
lean_dec(x_38);
lean_dec(x_37);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(x_3, x_33);
lean_ctor_set(x_4, 1, x_40);
lean_ctor_set(x_4, 0, x_31);
return x_4;
}
else
{
lean_dec(x_3);
lean_ctor_set(x_4, 1, x_33);
lean_ctor_set(x_4, 0, x_31);
return x_4;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
lean_dec(x_4);
x_41 = lean_box(0);
x_42 = lean_nat_add(x_6, x_21);
lean_dec(x_6);
x_43 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_43, 0, x_5);
lean_ctor_set(x_43, 1, x_41);
lean_ctor_set(x_43, 2, x_25);
x_44 = lean_array_uset(x_7, x_24, x_43);
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
lean_object* x_51; lean_object* x_52; 
x_51 = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(x_3, x_44);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_42);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
else
{
lean_object* x_53; 
lean_dec(x_3);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_42);
lean_ctor_set(x_53, 1, x_44);
return x_53;
}
}
}
else
{
lean_dec(x_25);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instSingleton___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint64_t x_14; lean_object* x_15; uint64_t x_16; uint64_t x_17; uint64_t x_18; lean_object* x_19; uint64_t x_20; uint64_t x_21; uint64_t x_22; size_t x_23; size_t x_24; lean_object* x_25; size_t x_26; size_t x_27; size_t x_28; lean_object* x_29; uint8_t x_30; 
x_4 = lean_unsigned_to_nat(8u);
x_5 = lean_unsigned_to_nat(2u);
x_6 = lean_nat_shiftl(x_4, x_5);
x_7 = lean_unsigned_to_nat(3u);
x_8 = lean_nat_div(x_6, x_7);
lean_dec(x_6);
x_9 = l_Nat_nextPowerOfTwo(x_8);
lean_dec(x_8);
x_10 = lean_box(0);
x_11 = lean_mk_array(x_9, x_10);
x_12 = lean_array_get_size(x_11);
lean_inc(x_1);
lean_inc(x_3);
x_13 = lean_apply_1(x_1, x_3);
x_14 = lean_unbox_uint64(x_13);
lean_dec(x_13);
x_15 = lean_unsigned_to_nat(32u);
x_16 = lean_uint64_of_nat(x_15);
x_17 = lean_uint64_shift_right(x_14, x_16);
x_18 = lean_uint64_xor(x_14, x_17);
x_19 = lean_unsigned_to_nat(16u);
x_20 = lean_uint64_of_nat(x_19);
x_21 = lean_uint64_shift_right(x_18, x_20);
x_22 = lean_uint64_xor(x_18, x_21);
x_23 = lean_uint64_to_usize(x_22);
x_24 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_usize_of_nat(x_25);
x_27 = lean_usize_sub(x_24, x_26);
x_28 = lean_usize_land(x_23, x_27);
x_29 = lean_array_uget(x_11, x_28);
lean_inc(x_29);
lean_inc(x_3);
x_30 = l_Std_DHashMap_Internal_AssocList_contains(lean_box(0), lean_box(0), x_2, x_3, x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_32, 0, x_3);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set(x_32, 2, x_29);
x_33 = lean_array_uset(x_11, x_28, x_32);
x_34 = lean_nat_shiftl(x_25, x_5);
x_35 = lean_nat_div(x_34, x_7);
lean_dec(x_34);
x_36 = lean_array_get_size(x_33);
x_37 = lean_nat_dec_le(x_35, x_36);
lean_dec(x_36);
lean_dec(x_35);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(x_1, x_33);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_25);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
else
{
lean_object* x_40; 
lean_dec(x_1);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_25);
lean_ctor_set(x_40, 1, x_33);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_29);
lean_dec(x_3);
lean_dec(x_1);
x_41 = lean_unsigned_to_nat(0u);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_11);
return x_42;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instSingleton___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_HashSet_instSingleton___redArg___lam__0), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instSingleton(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_HashSet_instSingleton___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instInsert___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint64_t x_9; lean_object* x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; lean_object* x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; size_t x_18; size_t x_19; lean_object* x_20; size_t x_21; size_t x_22; size_t x_23; lean_object* x_24; uint8_t x_25; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
x_7 = lean_array_get_size(x_6);
lean_inc(x_1);
lean_inc(x_3);
x_8 = lean_apply_1(x_1, x_3);
x_9 = lean_unbox_uint64(x_8);
lean_dec(x_8);
x_10 = lean_unsigned_to_nat(32u);
x_11 = lean_uint64_of_nat(x_10);
x_12 = lean_uint64_shift_right(x_9, x_11);
x_13 = lean_uint64_xor(x_9, x_12);
x_14 = lean_unsigned_to_nat(16u);
x_15 = lean_uint64_of_nat(x_14);
x_16 = lean_uint64_shift_right(x_13, x_15);
x_17 = lean_uint64_xor(x_13, x_16);
x_18 = lean_uint64_to_usize(x_17);
x_19 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_usize_of_nat(x_20);
x_22 = lean_usize_sub(x_19, x_21);
x_23 = lean_usize_land(x_18, x_22);
x_24 = lean_array_uget(x_6, x_23);
lean_inc(x_24);
lean_inc(x_3);
x_25 = l_Std_DHashMap_Internal_AssocList_contains(lean_box(0), lean_box(0), x_2, x_3, x_24);
if (x_25 == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_4);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_27 = lean_ctor_get(x_4, 1);
lean_dec(x_27);
x_28 = lean_ctor_get(x_4, 0);
lean_dec(x_28);
x_29 = lean_box(0);
x_30 = lean_nat_add(x_5, x_20);
lean_dec(x_5);
x_31 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_31, 0, x_3);
lean_ctor_set(x_31, 1, x_29);
lean_ctor_set(x_31, 2, x_24);
x_32 = lean_array_uset(x_6, x_23, x_31);
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
x_39 = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(x_1, x_32);
lean_ctor_set(x_4, 1, x_39);
lean_ctor_set(x_4, 0, x_30);
return x_4;
}
else
{
lean_dec(x_1);
lean_ctor_set(x_4, 1, x_32);
lean_ctor_set(x_4, 0, x_30);
return x_4;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
lean_dec(x_4);
x_40 = lean_box(0);
x_41 = lean_nat_add(x_5, x_20);
lean_dec(x_5);
x_42 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_42, 0, x_3);
lean_ctor_set(x_42, 1, x_40);
lean_ctor_set(x_42, 2, x_24);
x_43 = lean_array_uset(x_6, x_23, x_42);
x_44 = lean_unsigned_to_nat(2u);
x_45 = lean_nat_shiftl(x_41, x_44);
x_46 = lean_unsigned_to_nat(3u);
x_47 = lean_nat_div(x_45, x_46);
lean_dec(x_45);
x_48 = lean_array_get_size(x_43);
x_49 = lean_nat_dec_le(x_47, x_48);
lean_dec(x_48);
lean_dec(x_47);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(x_1, x_43);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_41);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
else
{
lean_object* x_52; 
lean_dec(x_1);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_41);
lean_ctor_set(x_52, 1, x_43);
return x_52;
}
}
}
else
{
lean_dec(x_24);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instInsert___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_HashSet_instInsert___redArg___lam__0), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instInsert(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_HashSet_instInsert___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_containsThenInsert___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint64_t x_14; lean_object* x_15; uint64_t x_16; uint64_t x_17; uint64_t x_18; lean_object* x_19; uint64_t x_20; uint64_t x_21; uint64_t x_22; size_t x_23; size_t x_24; lean_object* x_25; size_t x_26; size_t x_27; size_t x_28; lean_object* x_29; uint8_t x_30; 
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
x_12 = lean_array_get_size(x_11);
lean_inc(x_2);
lean_inc(x_4);
x_13 = lean_apply_1(x_2, x_4);
x_14 = lean_unbox_uint64(x_13);
lean_dec(x_13);
x_15 = lean_unsigned_to_nat(32u);
x_16 = lean_uint64_of_nat(x_15);
x_17 = lean_uint64_shift_right(x_14, x_16);
x_18 = lean_uint64_xor(x_14, x_17);
x_19 = lean_unsigned_to_nat(16u);
x_20 = lean_uint64_of_nat(x_19);
x_21 = lean_uint64_shift_right(x_18, x_20);
x_22 = lean_uint64_xor(x_18, x_21);
x_23 = lean_uint64_to_usize(x_22);
x_24 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_usize_of_nat(x_25);
x_27 = lean_usize_sub(x_24, x_26);
x_28 = lean_usize_land(x_23, x_27);
x_29 = lean_array_uget(x_11, x_28);
lean_inc(x_29);
lean_inc(x_4);
x_30 = l_Std_DHashMap_Internal_AssocList_contains(lean_box(0), lean_box(0), x_1, x_4, x_29);
if (x_30 == 0)
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_3);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_32 = lean_ctor_get(x_3, 1);
lean_dec(x_32);
x_33 = lean_ctor_get(x_3, 0);
lean_dec(x_33);
x_34 = lean_box(0);
x_35 = lean_nat_add(x_10, x_25);
lean_dec(x_10);
x_36 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_36, 0, x_4);
lean_ctor_set(x_36, 1, x_34);
lean_ctor_set(x_36, 2, x_29);
x_37 = lean_array_uset(x_11, x_28, x_36);
x_38 = lean_unsigned_to_nat(2u);
x_39 = lean_nat_shiftl(x_35, x_38);
x_40 = lean_unsigned_to_nat(3u);
x_41 = lean_nat_div(x_39, x_40);
lean_dec(x_39);
x_42 = lean_array_get_size(x_37);
x_43 = lean_nat_dec_le(x_41, x_42);
lean_dec(x_42);
lean_dec(x_41);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(x_2, x_37);
lean_ctor_set(x_3, 1, x_44);
lean_ctor_set(x_3, 0, x_35);
x_45 = lean_box(x_30);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_3);
x_5 = x_46;
goto block_9;
}
else
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_2);
lean_ctor_set(x_3, 1, x_37);
lean_ctor_set(x_3, 0, x_35);
x_47 = lean_box(x_30);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_3);
x_5 = x_48;
goto block_9;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
lean_dec(x_3);
x_49 = lean_box(0);
x_50 = lean_nat_add(x_10, x_25);
lean_dec(x_10);
x_51 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_51, 0, x_4);
lean_ctor_set(x_51, 1, x_49);
lean_ctor_set(x_51, 2, x_29);
x_52 = lean_array_uset(x_11, x_28, x_51);
x_53 = lean_unsigned_to_nat(2u);
x_54 = lean_nat_shiftl(x_50, x_53);
x_55 = lean_unsigned_to_nat(3u);
x_56 = lean_nat_div(x_54, x_55);
lean_dec(x_54);
x_57 = lean_array_get_size(x_52);
x_58 = lean_nat_dec_le(x_56, x_57);
lean_dec(x_57);
lean_dec(x_56);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_59 = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(x_2, x_52);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_50);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_box(x_30);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_60);
x_5 = x_62;
goto block_9;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_2);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_50);
lean_ctor_set(x_63, 1, x_52);
x_64 = lean_box(x_30);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_63);
x_5 = x_65;
goto block_9;
}
}
}
else
{
lean_object* x_66; lean_object* x_67; 
lean_dec(x_29);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_2);
x_66 = lean_box(x_30);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_3);
x_5 = x_67;
goto block_9;
}
block_9:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_containsThenInsert(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint64_t x_15; lean_object* x_16; uint64_t x_17; uint64_t x_18; uint64_t x_19; lean_object* x_20; uint64_t x_21; uint64_t x_22; uint64_t x_23; size_t x_24; size_t x_25; lean_object* x_26; size_t x_27; size_t x_28; size_t x_29; lean_object* x_30; uint8_t x_31; 
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_4, 1);
lean_inc(x_12);
x_13 = lean_array_get_size(x_12);
lean_inc(x_3);
lean_inc(x_5);
x_14 = lean_apply_1(x_3, x_5);
x_15 = lean_unbox_uint64(x_14);
lean_dec(x_14);
x_16 = lean_unsigned_to_nat(32u);
x_17 = lean_uint64_of_nat(x_16);
x_18 = lean_uint64_shift_right(x_15, x_17);
x_19 = lean_uint64_xor(x_15, x_18);
x_20 = lean_unsigned_to_nat(16u);
x_21 = lean_uint64_of_nat(x_20);
x_22 = lean_uint64_shift_right(x_19, x_21);
x_23 = lean_uint64_xor(x_19, x_22);
x_24 = lean_uint64_to_usize(x_23);
x_25 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_usize_of_nat(x_26);
x_28 = lean_usize_sub(x_25, x_27);
x_29 = lean_usize_land(x_24, x_28);
x_30 = lean_array_uget(x_12, x_29);
lean_inc(x_30);
lean_inc(x_5);
x_31 = l_Std_DHashMap_Internal_AssocList_contains(lean_box(0), lean_box(0), x_2, x_5, x_30);
if (x_31 == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_4);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_33 = lean_ctor_get(x_4, 1);
lean_dec(x_33);
x_34 = lean_ctor_get(x_4, 0);
lean_dec(x_34);
x_35 = lean_box(0);
x_36 = lean_nat_add(x_11, x_26);
lean_dec(x_11);
x_37 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_37, 0, x_5);
lean_ctor_set(x_37, 1, x_35);
lean_ctor_set(x_37, 2, x_30);
x_38 = lean_array_uset(x_12, x_29, x_37);
x_39 = lean_unsigned_to_nat(2u);
x_40 = lean_nat_shiftl(x_36, x_39);
x_41 = lean_unsigned_to_nat(3u);
x_42 = lean_nat_div(x_40, x_41);
lean_dec(x_40);
x_43 = lean_array_get_size(x_38);
x_44 = lean_nat_dec_le(x_42, x_43);
lean_dec(x_43);
lean_dec(x_42);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(x_3, x_38);
lean_ctor_set(x_4, 1, x_45);
lean_ctor_set(x_4, 0, x_36);
x_46 = lean_box(x_31);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_4);
x_6 = x_47;
goto block_10;
}
else
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_3);
lean_ctor_set(x_4, 1, x_38);
lean_ctor_set(x_4, 0, x_36);
x_48 = lean_box(x_31);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_4);
x_6 = x_49;
goto block_10;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
lean_dec(x_4);
x_50 = lean_box(0);
x_51 = lean_nat_add(x_11, x_26);
lean_dec(x_11);
x_52 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_52, 0, x_5);
lean_ctor_set(x_52, 1, x_50);
lean_ctor_set(x_52, 2, x_30);
x_53 = lean_array_uset(x_12, x_29, x_52);
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
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_60 = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(x_3, x_53);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_51);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_box(x_31);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_61);
x_6 = x_63;
goto block_10;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_3);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_51);
lean_ctor_set(x_64, 1, x_53);
x_65 = lean_box(x_31);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_64);
x_6 = x_66;
goto block_10;
}
}
}
else
{
lean_object* x_67; lean_object* x_68; 
lean_dec(x_30);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_3);
x_67 = lean_box(x_31);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_4);
x_6 = x_68;
goto block_10;
}
block_10:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_contains___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; lean_object* x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; lean_object* x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; size_t x_17; size_t x_18; lean_object* x_19; size_t x_20; size_t x_21; size_t x_22; lean_object* x_23; uint8_t x_24; 
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_array_get_size(x_5);
lean_inc(x_4);
x_7 = lean_apply_1(x_2, x_4);
x_8 = lean_unbox_uint64(x_7);
lean_dec(x_7);
x_9 = lean_unsigned_to_nat(32u);
x_10 = lean_uint64_of_nat(x_9);
x_11 = lean_uint64_shift_right(x_8, x_10);
x_12 = lean_uint64_xor(x_8, x_11);
x_13 = lean_unsigned_to_nat(16u);
x_14 = lean_uint64_of_nat(x_13);
x_15 = lean_uint64_shift_right(x_12, x_14);
x_16 = lean_uint64_xor(x_12, x_15);
x_17 = lean_uint64_to_usize(x_16);
x_18 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_usize_of_nat(x_19);
x_21 = lean_usize_sub(x_18, x_20);
x_22 = lean_usize_land(x_17, x_21);
x_23 = lean_array_uget(x_5, x_22);
x_24 = l_Std_DHashMap_Internal_AssocList_contains(lean_box(0), lean_box(0), x_1, x_4, x_23);
return x_24;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_contains(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint64_t x_9; lean_object* x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; lean_object* x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; size_t x_18; size_t x_19; lean_object* x_20; size_t x_21; size_t x_22; size_t x_23; lean_object* x_24; uint8_t x_25; 
x_6 = lean_ctor_get(x_4, 1);
x_7 = lean_array_get_size(x_6);
lean_inc(x_5);
x_8 = lean_apply_1(x_3, x_5);
x_9 = lean_unbox_uint64(x_8);
lean_dec(x_8);
x_10 = lean_unsigned_to_nat(32u);
x_11 = lean_uint64_of_nat(x_10);
x_12 = lean_uint64_shift_right(x_9, x_11);
x_13 = lean_uint64_xor(x_9, x_12);
x_14 = lean_unsigned_to_nat(16u);
x_15 = lean_uint64_of_nat(x_14);
x_16 = lean_uint64_shift_right(x_13, x_15);
x_17 = lean_uint64_xor(x_13, x_16);
x_18 = lean_uint64_to_usize(x_17);
x_19 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_usize_of_nat(x_20);
x_22 = lean_usize_sub(x_19, x_21);
x_23 = lean_usize_land(x_18, x_22);
x_24 = lean_array_uget(x_6, x_23);
x_25 = l_Std_DHashMap_Internal_AssocList_contains(lean_box(0), lean_box(0), x_2, x_5, x_24);
return x_25;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_contains___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Std_HashSet_contains___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_contains___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Std_HashSet_contains(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instMembership(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instMembership___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_HashSet_instMembership(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_instDecidableMem___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Std_DHashMap_instDecidableMem___redArg(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_instDecidableMem(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = l_Std_DHashMap_instDecidableMem___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instDecidableMem___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Std_HashSet_instDecidableMem___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instDecidableMem___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Std_HashSet_instDecidableMem(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_erase___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint64_t x_9; lean_object* x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; lean_object* x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; size_t x_18; size_t x_19; lean_object* x_20; size_t x_21; size_t x_22; size_t x_23; lean_object* x_24; uint8_t x_25; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
x_7 = lean_array_get_size(x_6);
lean_inc(x_4);
x_8 = lean_apply_1(x_2, x_4);
x_9 = lean_unbox_uint64(x_8);
lean_dec(x_8);
x_10 = lean_unsigned_to_nat(32u);
x_11 = lean_uint64_of_nat(x_10);
x_12 = lean_uint64_shift_right(x_9, x_11);
x_13 = lean_uint64_xor(x_9, x_12);
x_14 = lean_unsigned_to_nat(16u);
x_15 = lean_uint64_of_nat(x_14);
x_16 = lean_uint64_shift_right(x_13, x_15);
x_17 = lean_uint64_xor(x_13, x_16);
x_18 = lean_uint64_to_usize(x_17);
x_19 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_usize_of_nat(x_20);
x_22 = lean_usize_sub(x_19, x_21);
x_23 = lean_usize_land(x_18, x_22);
x_24 = lean_array_uget(x_6, x_23);
lean_inc(x_24);
lean_inc(x_4);
lean_inc(x_1);
x_25 = l_Std_DHashMap_Internal_AssocList_contains(lean_box(0), lean_box(0), x_1, x_4, x_24);
if (x_25 == 0)
{
lean_dec(x_24);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_3;
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_3);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_27 = lean_ctor_get(x_3, 1);
lean_dec(x_27);
x_28 = lean_ctor_get(x_3, 0);
lean_dec(x_28);
x_29 = lean_box(0);
x_30 = lean_array_uset(x_6, x_23, x_29);
x_31 = lean_nat_sub(x_5, x_20);
lean_dec(x_5);
x_32 = l_Std_DHashMap_Internal_AssocList_erase___redArg(x_1, x_4, x_24);
x_33 = lean_array_uset(x_30, x_23, x_32);
lean_ctor_set(x_3, 1, x_33);
lean_ctor_set(x_3, 0, x_31);
return x_3;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_3);
x_34 = lean_box(0);
x_35 = lean_array_uset(x_6, x_23, x_34);
x_36 = lean_nat_sub(x_5, x_20);
lean_dec(x_5);
x_37 = l_Std_DHashMap_Internal_AssocList_erase___redArg(x_1, x_4, x_24);
x_38 = lean_array_uset(x_35, x_23, x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_erase(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint64_t x_10; lean_object* x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; lean_object* x_15; uint64_t x_16; uint64_t x_17; uint64_t x_18; size_t x_19; size_t x_20; lean_object* x_21; size_t x_22; size_t x_23; size_t x_24; lean_object* x_25; uint8_t x_26; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
x_8 = lean_array_get_size(x_7);
lean_inc(x_5);
x_9 = lean_apply_1(x_3, x_5);
x_10 = lean_unbox_uint64(x_9);
lean_dec(x_9);
x_11 = lean_unsigned_to_nat(32u);
x_12 = lean_uint64_of_nat(x_11);
x_13 = lean_uint64_shift_right(x_10, x_12);
x_14 = lean_uint64_xor(x_10, x_13);
x_15 = lean_unsigned_to_nat(16u);
x_16 = lean_uint64_of_nat(x_15);
x_17 = lean_uint64_shift_right(x_14, x_16);
x_18 = lean_uint64_xor(x_14, x_17);
x_19 = lean_uint64_to_usize(x_18);
x_20 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_usize_of_nat(x_21);
x_23 = lean_usize_sub(x_20, x_22);
x_24 = lean_usize_land(x_19, x_23);
x_25 = lean_array_uget(x_7, x_24);
lean_inc(x_25);
lean_inc(x_5);
lean_inc(x_2);
x_26 = l_Std_DHashMap_Internal_AssocList_contains(lean_box(0), lean_box(0), x_2, x_5, x_25);
if (x_26 == 0)
{
lean_dec(x_25);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
return x_4;
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_4);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_28 = lean_ctor_get(x_4, 1);
lean_dec(x_28);
x_29 = lean_ctor_get(x_4, 0);
lean_dec(x_29);
x_30 = lean_box(0);
x_31 = lean_array_uset(x_7, x_24, x_30);
x_32 = lean_nat_sub(x_6, x_21);
lean_dec(x_6);
x_33 = l_Std_DHashMap_Internal_AssocList_erase___redArg(x_2, x_5, x_25);
x_34 = lean_array_uset(x_31, x_24, x_33);
lean_ctor_set(x_4, 1, x_34);
lean_ctor_set(x_4, 0, x_32);
return x_4;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_4);
x_35 = lean_box(0);
x_36 = lean_array_uset(x_7, x_24, x_35);
x_37 = lean_nat_sub(x_6, x_21);
lean_dec(x_6);
x_38 = l_Std_DHashMap_Internal_AssocList_erase___redArg(x_2, x_5, x_25);
x_39 = lean_array_uset(x_36, x_24, x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_size___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_size(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_size___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_HashSet_size___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_size___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_HashSet_size(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_get_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; lean_object* x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; lean_object* x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; size_t x_17; size_t x_18; lean_object* x_19; size_t x_20; size_t x_21; size_t x_22; lean_object* x_23; lean_object* x_24; 
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_array_get_size(x_5);
lean_inc(x_4);
x_7 = lean_apply_1(x_2, x_4);
x_8 = lean_unbox_uint64(x_7);
lean_dec(x_7);
x_9 = lean_unsigned_to_nat(32u);
x_10 = lean_uint64_of_nat(x_9);
x_11 = lean_uint64_shift_right(x_8, x_10);
x_12 = lean_uint64_xor(x_8, x_11);
x_13 = lean_unsigned_to_nat(16u);
x_14 = lean_uint64_of_nat(x_13);
x_15 = lean_uint64_shift_right(x_12, x_14);
x_16 = lean_uint64_xor(x_12, x_15);
x_17 = lean_uint64_to_usize(x_16);
x_18 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_usize_of_nat(x_19);
x_21 = lean_usize_sub(x_18, x_20);
x_22 = lean_usize_land(x_17, x_21);
x_23 = lean_array_uget(x_5, x_22);
x_24 = l_Std_DHashMap_Internal_AssocList_getKey_x3f(lean_box(0), lean_box(0), x_1, x_4, x_23);
return x_24;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_get_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint64_t x_9; lean_object* x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; lean_object* x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; size_t x_18; size_t x_19; lean_object* x_20; size_t x_21; size_t x_22; size_t x_23; lean_object* x_24; lean_object* x_25; 
x_6 = lean_ctor_get(x_4, 1);
x_7 = lean_array_get_size(x_6);
lean_inc(x_5);
x_8 = lean_apply_1(x_3, x_5);
x_9 = lean_unbox_uint64(x_8);
lean_dec(x_8);
x_10 = lean_unsigned_to_nat(32u);
x_11 = lean_uint64_of_nat(x_10);
x_12 = lean_uint64_shift_right(x_9, x_11);
x_13 = lean_uint64_xor(x_9, x_12);
x_14 = lean_unsigned_to_nat(16u);
x_15 = lean_uint64_of_nat(x_14);
x_16 = lean_uint64_shift_right(x_13, x_15);
x_17 = lean_uint64_xor(x_13, x_16);
x_18 = lean_uint64_to_usize(x_17);
x_19 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_usize_of_nat(x_20);
x_22 = lean_usize_sub(x_19, x_21);
x_23 = lean_usize_land(x_18, x_22);
x_24 = lean_array_uget(x_6, x_23);
x_25 = l_Std_DHashMap_Internal_AssocList_getKey_x3f(lean_box(0), lean_box(0), x_2, x_5, x_24);
return x_25;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_get_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_HashSet_get_x3f___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_get_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_HashSet_get_x3f(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_get___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; lean_object* x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; lean_object* x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; size_t x_17; size_t x_18; lean_object* x_19; size_t x_20; size_t x_21; size_t x_22; lean_object* x_23; lean_object* x_24; 
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_array_get_size(x_5);
lean_inc(x_4);
x_7 = lean_apply_1(x_2, x_4);
x_8 = lean_unbox_uint64(x_7);
lean_dec(x_7);
x_9 = lean_unsigned_to_nat(32u);
x_10 = lean_uint64_of_nat(x_9);
x_11 = lean_uint64_shift_right(x_8, x_10);
x_12 = lean_uint64_xor(x_8, x_11);
x_13 = lean_unsigned_to_nat(16u);
x_14 = lean_uint64_of_nat(x_13);
x_15 = lean_uint64_shift_right(x_12, x_14);
x_16 = lean_uint64_xor(x_12, x_15);
x_17 = lean_uint64_to_usize(x_16);
x_18 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_usize_of_nat(x_19);
x_21 = lean_usize_sub(x_18, x_20);
x_22 = lean_usize_land(x_17, x_21);
x_23 = lean_array_uget(x_5, x_22);
x_24 = l_Std_DHashMap_Internal_AssocList_getKey___redArg(x_1, x_4, x_23);
return x_24;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_get(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint64_t x_10; lean_object* x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; lean_object* x_15; uint64_t x_16; uint64_t x_17; uint64_t x_18; size_t x_19; size_t x_20; lean_object* x_21; size_t x_22; size_t x_23; size_t x_24; lean_object* x_25; lean_object* x_26; 
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_array_get_size(x_7);
lean_inc(x_5);
x_9 = lean_apply_1(x_3, x_5);
x_10 = lean_unbox_uint64(x_9);
lean_dec(x_9);
x_11 = lean_unsigned_to_nat(32u);
x_12 = lean_uint64_of_nat(x_11);
x_13 = lean_uint64_shift_right(x_10, x_12);
x_14 = lean_uint64_xor(x_10, x_13);
x_15 = lean_unsigned_to_nat(16u);
x_16 = lean_uint64_of_nat(x_15);
x_17 = lean_uint64_shift_right(x_14, x_16);
x_18 = lean_uint64_xor(x_14, x_17);
x_19 = lean_uint64_to_usize(x_18);
x_20 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_usize_of_nat(x_21);
x_23 = lean_usize_sub(x_20, x_22);
x_24 = lean_usize_land(x_19, x_23);
x_25 = lean_array_uget(x_7, x_24);
x_26 = l_Std_DHashMap_Internal_AssocList_getKey___redArg(x_2, x_5, x_25);
return x_26;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_get___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_HashSet_get___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_get___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_HashSet_get(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_getD___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint64_t x_9; lean_object* x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; lean_object* x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; size_t x_18; size_t x_19; lean_object* x_20; size_t x_21; size_t x_22; size_t x_23; lean_object* x_24; lean_object* x_25; 
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_array_get_size(x_6);
lean_inc(x_4);
x_8 = lean_apply_1(x_2, x_4);
x_9 = lean_unbox_uint64(x_8);
lean_dec(x_8);
x_10 = lean_unsigned_to_nat(32u);
x_11 = lean_uint64_of_nat(x_10);
x_12 = lean_uint64_shift_right(x_9, x_11);
x_13 = lean_uint64_xor(x_9, x_12);
x_14 = lean_unsigned_to_nat(16u);
x_15 = lean_uint64_of_nat(x_14);
x_16 = lean_uint64_shift_right(x_13, x_15);
x_17 = lean_uint64_xor(x_13, x_16);
x_18 = lean_uint64_to_usize(x_17);
x_19 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_usize_of_nat(x_20);
x_22 = lean_usize_sub(x_19, x_21);
x_23 = lean_usize_land(x_18, x_22);
x_24 = lean_array_uget(x_6, x_23);
x_25 = l_Std_DHashMap_Internal_AssocList_getKeyD___redArg(x_1, x_4, x_5, x_24);
return x_25;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_getD(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint64_t x_10; lean_object* x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; lean_object* x_15; uint64_t x_16; uint64_t x_17; uint64_t x_18; size_t x_19; size_t x_20; lean_object* x_21; size_t x_22; size_t x_23; size_t x_24; lean_object* x_25; lean_object* x_26; 
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_array_get_size(x_7);
lean_inc(x_5);
x_9 = lean_apply_1(x_3, x_5);
x_10 = lean_unbox_uint64(x_9);
lean_dec(x_9);
x_11 = lean_unsigned_to_nat(32u);
x_12 = lean_uint64_of_nat(x_11);
x_13 = lean_uint64_shift_right(x_10, x_12);
x_14 = lean_uint64_xor(x_10, x_13);
x_15 = lean_unsigned_to_nat(16u);
x_16 = lean_uint64_of_nat(x_15);
x_17 = lean_uint64_shift_right(x_14, x_16);
x_18 = lean_uint64_xor(x_14, x_17);
x_19 = lean_uint64_to_usize(x_18);
x_20 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_usize_of_nat(x_21);
x_23 = lean_usize_sub(x_20, x_22);
x_24 = lean_usize_land(x_19, x_23);
x_25 = lean_array_uget(x_7, x_24);
x_26 = l_Std_DHashMap_Internal_AssocList_getKeyD___redArg(x_2, x_5, x_6, x_25);
return x_26;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_getD___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_HashSet_getD___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_getD___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_HashSet_getD(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_get_x21___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint64_t x_9; lean_object* x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; lean_object* x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; size_t x_18; size_t x_19; lean_object* x_20; size_t x_21; size_t x_22; size_t x_23; lean_object* x_24; lean_object* x_25; 
x_6 = lean_ctor_get(x_4, 1);
x_7 = lean_array_get_size(x_6);
lean_inc(x_5);
x_8 = lean_apply_1(x_2, x_5);
x_9 = lean_unbox_uint64(x_8);
lean_dec(x_8);
x_10 = lean_unsigned_to_nat(32u);
x_11 = lean_uint64_of_nat(x_10);
x_12 = lean_uint64_shift_right(x_9, x_11);
x_13 = lean_uint64_xor(x_9, x_12);
x_14 = lean_unsigned_to_nat(16u);
x_15 = lean_uint64_of_nat(x_14);
x_16 = lean_uint64_shift_right(x_13, x_15);
x_17 = lean_uint64_xor(x_13, x_16);
x_18 = lean_uint64_to_usize(x_17);
x_19 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_usize_of_nat(x_20);
x_22 = lean_usize_sub(x_19, x_21);
x_23 = lean_usize_land(x_18, x_22);
x_24 = lean_array_uget(x_6, x_23);
x_25 = l_Std_DHashMap_Internal_AssocList_getKey_x21___redArg(x_1, x_3, x_5, x_24);
return x_25;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_get_x21(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint64_t x_10; lean_object* x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; lean_object* x_15; uint64_t x_16; uint64_t x_17; uint64_t x_18; size_t x_19; size_t x_20; lean_object* x_21; size_t x_22; size_t x_23; size_t x_24; lean_object* x_25; lean_object* x_26; 
x_7 = lean_ctor_get(x_5, 1);
x_8 = lean_array_get_size(x_7);
lean_inc(x_6);
x_9 = lean_apply_1(x_3, x_6);
x_10 = lean_unbox_uint64(x_9);
lean_dec(x_9);
x_11 = lean_unsigned_to_nat(32u);
x_12 = lean_uint64_of_nat(x_11);
x_13 = lean_uint64_shift_right(x_10, x_12);
x_14 = lean_uint64_xor(x_10, x_13);
x_15 = lean_unsigned_to_nat(16u);
x_16 = lean_uint64_of_nat(x_15);
x_17 = lean_uint64_shift_right(x_14, x_16);
x_18 = lean_uint64_xor(x_14, x_17);
x_19 = lean_uint64_to_usize(x_18);
x_20 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_usize_of_nat(x_21);
x_23 = lean_usize_sub(x_20, x_22);
x_24 = lean_usize_land(x_19, x_23);
x_25 = lean_array_uget(x_7, x_24);
x_26 = l_Std_DHashMap_Internal_AssocList_getKey_x21___redArg(x_2, x_4, x_6, x_25);
return x_26;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_get_x21___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_HashSet_get_x21___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_get_x21___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_HashSet_get_x21(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_isEmpty___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_isEmpty(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_isEmpty___redArg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Std_HashSet_isEmpty___redArg(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_isEmpty___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Std_HashSet_isEmpty(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_toList___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_toList___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_foldrM___redArg(x_1, x_2, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_toList___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_2 = lean_box(0);
x_3 = lean_alloc_closure((void*)(l_Id_instMonad___lam__0), 4, 0);
x_4 = lean_alloc_closure((void*)(l_Id_instMonad___lam__1___boxed), 4, 0);
x_5 = lean_alloc_closure((void*)(l_Id_instMonad___lam__2___boxed), 2, 0);
x_6 = lean_alloc_closure((void*)(l_Id_instMonad___lam__3), 4, 0);
x_7 = lean_alloc_closure((void*)(l_Id_instMonad___lam__4___boxed), 4, 0);
x_8 = lean_alloc_closure((void*)(l_Id_instMonad___lam__5___boxed), 4, 0);
x_9 = lean_alloc_closure((void*)(l_Id_instMonad___lam__6), 4, 0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_4);
x_11 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_5);
lean_ctor_set(x_11, 2, x_6);
lean_ctor_set(x_11, 3, x_7);
lean_ctor_set(x_11, 4, x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_array_get_size(x_13);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_nat_dec_lt(x_15, x_14);
if (x_16 == 0)
{
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
return x_2;
}
else
{
lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; 
x_17 = lean_alloc_closure((void*)(l_Std_HashSet_toList___redArg___lam__0___boxed), 3, 0);
lean_inc(x_12);
x_18 = lean_alloc_closure((void*)(l_Std_HashSet_toList___redArg___lam__1), 4, 2);
lean_closure_set(x_18, 0, x_12);
lean_closure_set(x_18, 1, x_17);
x_19 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_20 = lean_usize_of_nat(x_15);
x_21 = l_Array_foldrMUnsafe_fold___redArg(x_12, x_18, x_13, x_19, x_20, x_2);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_toList(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_5 = lean_box(0);
x_6 = lean_alloc_closure((void*)(l_Id_instMonad___lam__0), 4, 0);
x_7 = lean_alloc_closure((void*)(l_Id_instMonad___lam__1___boxed), 4, 0);
x_8 = lean_alloc_closure((void*)(l_Id_instMonad___lam__2___boxed), 2, 0);
x_9 = lean_alloc_closure((void*)(l_Id_instMonad___lam__3), 4, 0);
x_10 = lean_alloc_closure((void*)(l_Id_instMonad___lam__4___boxed), 4, 0);
x_11 = lean_alloc_closure((void*)(l_Id_instMonad___lam__5___boxed), 4, 0);
x_12 = lean_alloc_closure((void*)(l_Id_instMonad___lam__6), 4, 0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_7);
x_14 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_8);
lean_ctor_set(x_14, 2, x_9);
lean_ctor_set(x_14, 3, x_10);
lean_ctor_set(x_14, 4, x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_12);
x_16 = lean_ctor_get(x_4, 1);
lean_inc(x_16);
lean_dec(x_4);
x_17 = lean_array_get_size(x_16);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_nat_dec_lt(x_18, x_17);
if (x_19 == 0)
{
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
return x_5;
}
else
{
lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; lean_object* x_24; 
x_20 = lean_alloc_closure((void*)(l_Std_HashSet_toList___redArg___lam__0___boxed), 3, 0);
lean_inc(x_15);
x_21 = lean_alloc_closure((void*)(l_Std_HashSet_toList___redArg___lam__1), 4, 2);
lean_closure_set(x_21, 0, x_15);
lean_closure_set(x_21, 1, x_20);
x_22 = lean_usize_of_nat(x_17);
lean_dec(x_17);
x_23 = lean_usize_of_nat(x_18);
x_24 = l_Array_foldrMUnsafe_fold___redArg(x_15, x_21, x_16, x_22, x_23, x_5);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_toList___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_HashSet_toList___redArg___lam__0(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_toList___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_HashSet_toList(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_ofList___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint64_t x_10; lean_object* x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; lean_object* x_15; uint64_t x_16; uint64_t x_17; uint64_t x_18; size_t x_19; size_t x_20; lean_object* x_21; size_t x_22; size_t x_23; size_t x_24; lean_object* x_25; uint8_t x_26; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
x_8 = lean_array_get_size(x_7);
lean_inc(x_1);
lean_inc(x_3);
x_9 = lean_apply_1(x_1, x_3);
x_10 = lean_unbox_uint64(x_9);
lean_dec(x_9);
x_11 = lean_unsigned_to_nat(32u);
x_12 = lean_uint64_of_nat(x_11);
x_13 = lean_uint64_shift_right(x_10, x_12);
x_14 = lean_uint64_xor(x_10, x_13);
x_15 = lean_unsigned_to_nat(16u);
x_16 = lean_uint64_of_nat(x_15);
x_17 = lean_uint64_shift_right(x_14, x_16);
x_18 = lean_uint64_xor(x_14, x_17);
x_19 = lean_uint64_to_usize(x_18);
x_20 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_usize_of_nat(x_21);
x_23 = lean_usize_sub(x_20, x_22);
x_24 = lean_usize_land(x_19, x_23);
x_25 = lean_array_uget(x_7, x_24);
lean_inc(x_25);
lean_inc(x_3);
x_26 = l_Std_DHashMap_Internal_AssocList_contains(lean_box(0), lean_box(0), x_2, x_3, x_25);
if (x_26 == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_5);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_28 = lean_ctor_get(x_5, 1);
lean_dec(x_28);
x_29 = lean_ctor_get(x_5, 0);
lean_dec(x_29);
x_30 = lean_box(0);
x_31 = lean_nat_add(x_6, x_21);
lean_dec(x_6);
x_32 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_32, 0, x_3);
lean_ctor_set(x_32, 1, x_30);
lean_ctor_set(x_32, 2, x_25);
x_33 = lean_array_uset(x_7, x_24, x_32);
x_34 = lean_unsigned_to_nat(2u);
x_35 = lean_nat_shiftl(x_31, x_34);
x_36 = lean_unsigned_to_nat(3u);
x_37 = lean_nat_div(x_35, x_36);
lean_dec(x_35);
x_38 = lean_array_get_size(x_33);
x_39 = lean_nat_dec_le(x_37, x_38);
lean_dec(x_38);
lean_dec(x_37);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(x_1, x_33);
lean_ctor_set(x_5, 1, x_40);
lean_ctor_set(x_5, 0, x_31);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_5);
return x_41;
}
else
{
lean_object* x_42; 
lean_dec(x_1);
lean_ctor_set(x_5, 1, x_33);
lean_ctor_set(x_5, 0, x_31);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_5);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
lean_dec(x_5);
x_43 = lean_box(0);
x_44 = lean_nat_add(x_6, x_21);
lean_dec(x_6);
x_45 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_45, 0, x_3);
lean_ctor_set(x_45, 1, x_43);
lean_ctor_set(x_45, 2, x_25);
x_46 = lean_array_uset(x_7, x_24, x_45);
x_47 = lean_unsigned_to_nat(2u);
x_48 = lean_nat_shiftl(x_44, x_47);
x_49 = lean_unsigned_to_nat(3u);
x_50 = lean_nat_div(x_48, x_49);
lean_dec(x_48);
x_51 = lean_array_get_size(x_46);
x_52 = lean_nat_dec_le(x_50, x_51);
lean_dec(x_51);
lean_dec(x_50);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(x_1, x_46);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_44);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_54);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; 
lean_dec(x_1);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_44);
lean_ctor_set(x_56, 1, x_46);
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_56);
return x_57;
}
}
}
else
{
lean_object* x_58; 
lean_dec(x_25);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_5);
return x_58;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_ofList___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_4 = lean_alloc_closure((void*)(l_Std_HashSet_ofList___redArg___lam__0), 5, 2);
lean_closure_set(x_4, 0, x_2);
lean_closure_set(x_4, 1, x_1);
x_5 = lean_unsigned_to_nat(8u);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_unsigned_to_nat(2u);
x_8 = lean_nat_shiftl(x_5, x_7);
x_9 = lean_unsigned_to_nat(3u);
x_10 = lean_nat_div(x_8, x_9);
lean_dec(x_8);
x_11 = l_Nat_nextPowerOfTwo(x_10);
lean_dec(x_10);
x_12 = lean_box(0);
x_13 = lean_mk_array(x_11, x_12);
x_14 = lean_alloc_closure((void*)(l_Id_instMonad___lam__0), 4, 0);
x_15 = lean_alloc_closure((void*)(l_Id_instMonad___lam__1___boxed), 4, 0);
x_16 = lean_alloc_closure((void*)(l_Id_instMonad___lam__2___boxed), 2, 0);
x_17 = lean_alloc_closure((void*)(l_Id_instMonad___lam__3), 4, 0);
x_18 = lean_alloc_closure((void*)(l_Id_instMonad___lam__4___boxed), 4, 0);
x_19 = lean_alloc_closure((void*)(l_Id_instMonad___lam__5___boxed), 4, 0);
x_20 = lean_alloc_closure((void*)(l_Id_instMonad___lam__6), 4, 0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_14);
lean_ctor_set(x_21, 1, x_15);
x_22 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_16);
lean_ctor_set(x_22, 2, x_17);
lean_ctor_set(x_22, 3, x_18);
lean_ctor_set(x_22, 4, x_19);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_20);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_6);
lean_ctor_set(x_24, 1, x_13);
lean_inc(x_3);
x_25 = l_List_forIn_x27_loop(lean_box(0), lean_box(0), lean_box(0), x_23, x_3, x_4, x_3, x_24, lean_box(0));
lean_dec(x_3);
return x_25;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_ofList(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_5 = lean_alloc_closure((void*)(l_Std_HashSet_ofList___redArg___lam__0), 5, 2);
lean_closure_set(x_5, 0, x_3);
lean_closure_set(x_5, 1, x_2);
x_6 = lean_unsigned_to_nat(8u);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_unsigned_to_nat(2u);
x_9 = lean_nat_shiftl(x_6, x_8);
x_10 = lean_unsigned_to_nat(3u);
x_11 = lean_nat_div(x_9, x_10);
lean_dec(x_9);
x_12 = l_Nat_nextPowerOfTwo(x_11);
lean_dec(x_11);
x_13 = lean_box(0);
x_14 = lean_mk_array(x_12, x_13);
x_15 = lean_alloc_closure((void*)(l_Id_instMonad___lam__0), 4, 0);
x_16 = lean_alloc_closure((void*)(l_Id_instMonad___lam__1___boxed), 4, 0);
x_17 = lean_alloc_closure((void*)(l_Id_instMonad___lam__2___boxed), 2, 0);
x_18 = lean_alloc_closure((void*)(l_Id_instMonad___lam__3), 4, 0);
x_19 = lean_alloc_closure((void*)(l_Id_instMonad___lam__4___boxed), 4, 0);
x_20 = lean_alloc_closure((void*)(l_Id_instMonad___lam__5___boxed), 4, 0);
x_21 = lean_alloc_closure((void*)(l_Id_instMonad___lam__6), 4, 0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_15);
lean_ctor_set(x_22, 1, x_16);
x_23 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_17);
lean_ctor_set(x_23, 2, x_18);
lean_ctor_set(x_23, 3, x_19);
lean_ctor_set(x_23, 4, x_20);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_21);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_7);
lean_ctor_set(x_25, 1, x_14);
lean_inc(x_4);
x_26 = l_List_forIn_x27_loop(lean_box(0), lean_box(0), lean_box(0), x_24, x_4, x_5, x_4, x_25, lean_box(0));
lean_dec(x_4);
return x_26;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_foldM___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_2(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_foldM___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_foldM___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_get_size(x_5);
x_8 = lean_nat_dec_lt(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_apply_2(x_10, lean_box(0), x_3);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = lean_nat_dec_le(x_7, x_7);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_apply_2(x_14, lean_box(0), x_3);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; 
x_16 = lean_alloc_closure((void*)(l_Std_HashSet_foldM___redArg___lam__0___boxed), 4, 1);
lean_closure_set(x_16, 0, x_2);
lean_inc(x_1);
x_17 = lean_alloc_closure((void*)(l_Std_HashSet_foldM___redArg___lam__1), 4, 2);
lean_closure_set(x_17, 0, x_1);
lean_closure_set(x_17, 1, x_16);
x_18 = lean_usize_of_nat(x_6);
x_19 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_20 = l_Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_1, x_17, x_5, x_18, x_19, x_3);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_foldM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_array_get_size(x_10);
x_13 = lean_nat_dec_lt(x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_7);
x_14 = lean_ctor_get(x_5, 0);
lean_inc(x_14);
lean_dec(x_5);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_apply_2(x_15, lean_box(0), x_8);
return x_16;
}
else
{
uint8_t x_17; 
x_17 = lean_nat_dec_le(x_12, x_12);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_7);
x_18 = lean_ctor_get(x_5, 0);
lean_inc(x_18);
lean_dec(x_5);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_apply_2(x_19, lean_box(0), x_8);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; 
x_21 = lean_alloc_closure((void*)(l_Std_HashSet_foldM___redArg___lam__0___boxed), 4, 1);
lean_closure_set(x_21, 0, x_7);
lean_inc(x_5);
x_22 = lean_alloc_closure((void*)(l_Std_HashSet_foldM___redArg___lam__1), 4, 2);
lean_closure_set(x_22, 0, x_5);
lean_closure_set(x_22, 1, x_21);
x_23 = lean_usize_of_nat(x_11);
x_24 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_25 = l_Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_5, x_22, x_10, x_23, x_24, x_8);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_foldM___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_HashSet_foldM___redArg___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_foldM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Std_HashSet_foldM(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_fold___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_fold___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_4 = lean_alloc_closure((void*)(l_Id_instMonad___lam__0), 4, 0);
x_5 = lean_alloc_closure((void*)(l_Id_instMonad___lam__1___boxed), 4, 0);
x_6 = lean_alloc_closure((void*)(l_Id_instMonad___lam__2___boxed), 2, 0);
x_7 = lean_alloc_closure((void*)(l_Id_instMonad___lam__3), 4, 0);
x_8 = lean_alloc_closure((void*)(l_Id_instMonad___lam__4___boxed), 4, 0);
x_9 = lean_alloc_closure((void*)(l_Id_instMonad___lam__5___boxed), 4, 0);
x_10 = lean_alloc_closure((void*)(l_Id_instMonad___lam__6), 4, 0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_5);
x_12 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_6);
lean_ctor_set(x_12, 2, x_7);
lean_ctor_set(x_12, 3, x_8);
lean_ctor_set(x_12, 4, x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
x_14 = lean_ctor_get(x_3, 1);
lean_inc(x_14);
lean_dec(x_3);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_get_size(x_14);
x_17 = lean_nat_dec_lt(x_15, x_16);
if (x_17 == 0)
{
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_1);
return x_2;
}
else
{
uint8_t x_18; 
x_18 = lean_nat_dec_le(x_16, x_16);
if (x_18 == 0)
{
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; 
x_19 = lean_alloc_closure((void*)(l_Std_HashSet_foldM___redArg___lam__0___boxed), 4, 1);
lean_closure_set(x_19, 0, x_1);
lean_inc(x_13);
x_20 = lean_alloc_closure((void*)(l_Std_HashSet_fold___redArg___lam__1), 4, 2);
lean_closure_set(x_20, 0, x_13);
lean_closure_set(x_20, 1, x_19);
x_21 = lean_usize_of_nat(x_15);
x_22 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_23 = l_Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_13, x_20, x_14, x_21, x_22, x_2);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_fold(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_8 = lean_alloc_closure((void*)(l_Id_instMonad___lam__0), 4, 0);
x_9 = lean_alloc_closure((void*)(l_Id_instMonad___lam__1___boxed), 4, 0);
x_10 = lean_alloc_closure((void*)(l_Id_instMonad___lam__2___boxed), 2, 0);
x_11 = lean_alloc_closure((void*)(l_Id_instMonad___lam__3), 4, 0);
x_12 = lean_alloc_closure((void*)(l_Id_instMonad___lam__4___boxed), 4, 0);
x_13 = lean_alloc_closure((void*)(l_Id_instMonad___lam__5___boxed), 4, 0);
x_14 = lean_alloc_closure((void*)(l_Id_instMonad___lam__6), 4, 0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_9);
x_16 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_10);
lean_ctor_set(x_16, 2, x_11);
lean_ctor_set(x_16, 3, x_12);
lean_ctor_set(x_16, 4, x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_14);
x_18 = lean_ctor_get(x_7, 1);
lean_inc(x_18);
lean_dec(x_7);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_array_get_size(x_18);
x_21 = lean_nat_dec_lt(x_19, x_20);
if (x_21 == 0)
{
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_5);
return x_6;
}
else
{
uint8_t x_22; 
x_22 = lean_nat_dec_le(x_20, x_20);
if (x_22 == 0)
{
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_5);
return x_6;
}
else
{
lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; lean_object* x_27; 
x_23 = lean_alloc_closure((void*)(l_Std_HashSet_foldM___redArg___lam__0___boxed), 4, 1);
lean_closure_set(x_23, 0, x_5);
lean_inc(x_17);
x_24 = lean_alloc_closure((void*)(l_Std_HashSet_fold___redArg___lam__1), 4, 2);
lean_closure_set(x_24, 0, x_17);
lean_closure_set(x_24, 1, x_23);
x_25 = lean_usize_of_nat(x_19);
x_26 = lean_usize_of_nat(x_20);
lean_dec(x_20);
x_27 = l_Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_17, x_24, x_18, x_25, x_26, x_6);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_fold___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_HashSet_fold(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_forM___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_1(x_1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_forM___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
x_6 = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(x_1, x_2, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_forM___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_array_get_size(x_4);
x_7 = lean_box(0);
x_8 = lean_nat_dec_lt(x_5, x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_apply_2(x_10, lean_box(0), x_7);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = lean_nat_dec_le(x_6, x_6);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_apply_2(x_14, lean_box(0), x_7);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; 
x_16 = lean_alloc_closure((void*)(l_Std_HashSet_forM___redArg___lam__0___boxed), 4, 1);
lean_closure_set(x_16, 0, x_2);
lean_inc(x_1);
x_17 = lean_alloc_closure((void*)(l_Std_HashSet_forM___redArg___lam__1___boxed), 4, 2);
lean_closure_set(x_17, 0, x_1);
lean_closure_set(x_17, 1, x_16);
x_18 = lean_usize_of_nat(x_5);
x_19 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_20 = l_Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_1, x_17, x_4, x_18, x_19, x_7);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_forM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_array_get_size(x_8);
x_11 = lean_box(0);
x_12 = lean_nat_dec_lt(x_9, x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
x_13 = lean_ctor_get(x_5, 0);
lean_inc(x_13);
lean_dec(x_5);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_apply_2(x_14, lean_box(0), x_11);
return x_15;
}
else
{
uint8_t x_16; 
x_16 = lean_nat_dec_le(x_10, x_10);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
x_17 = lean_ctor_get(x_5, 0);
lean_inc(x_17);
lean_dec(x_5);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_apply_2(x_18, lean_box(0), x_11);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; lean_object* x_24; 
x_20 = lean_alloc_closure((void*)(l_Std_HashSet_forM___redArg___lam__0___boxed), 4, 1);
lean_closure_set(x_20, 0, x_6);
lean_inc(x_5);
x_21 = lean_alloc_closure((void*)(l_Std_HashSet_forM___redArg___lam__1___boxed), 4, 2);
lean_closure_set(x_21, 0, x_5);
lean_closure_set(x_21, 1, x_20);
x_22 = lean_usize_of_nat(x_9);
x_23 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_24 = l_Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_5, x_21, x_8, x_22, x_23, x_11);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_forM___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_HashSet_forM___redArg___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_forM___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_HashSet_forM___redArg___lam__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_forM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_HashSet_forM(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_forIn___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_2(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_forIn___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_DHashMap_Internal_AssocList_forInStep_go___redArg(x_1, x_2, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_forIn___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; lean_object* x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_alloc_closure((void*)(l_Std_HashSet_forIn___redArg___lam__0___boxed), 4, 1);
lean_closure_set(x_5, 0, x_2);
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(l_Std_HashSet_forIn___redArg___lam__1), 5, 2);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_5);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec(x_4);
x_8 = lean_array_size(x_7);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_usize_of_nat(x_9);
x_11 = l_Array_forIn_x27Unsafe_loop___redArg(x_1, x_7, x_6, x_8, x_10, x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_forIn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; lean_object* x_14; size_t x_15; lean_object* x_16; 
x_10 = lean_alloc_closure((void*)(l_Std_HashSet_forIn___redArg___lam__0___boxed), 4, 1);
lean_closure_set(x_10, 0, x_7);
lean_inc(x_5);
x_11 = lean_alloc_closure((void*)(l_Std_HashSet_forIn___redArg___lam__1), 5, 2);
lean_closure_set(x_11, 0, x_5);
lean_closure_set(x_11, 1, x_10);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_array_size(x_12);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_usize_of_nat(x_14);
x_16 = l_Array_forIn_x27Unsafe_loop___redArg(x_5, x_12, x_11, x_13, x_15, x_8);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_forIn___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_HashSet_forIn___redArg___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_forIn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Std_HashSet_forIn(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instForM___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_array_get_size(x_4);
x_7 = lean_box(0);
x_8 = lean_nat_dec_lt(x_5, x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_apply_2(x_10, lean_box(0), x_7);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = lean_nat_dec_le(x_6, x_6);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_apply_2(x_14, lean_box(0), x_7);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; 
x_16 = lean_alloc_closure((void*)(l_Std_HashSet_forM___redArg___lam__0___boxed), 4, 1);
lean_closure_set(x_16, 0, x_3);
lean_inc(x_1);
x_17 = lean_alloc_closure((void*)(l_Std_HashSet_forM___redArg___lam__1___boxed), 4, 2);
lean_closure_set(x_17, 0, x_1);
lean_closure_set(x_17, 1, x_16);
x_18 = lean_usize_of_nat(x_5);
x_19 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_20 = l_Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_1, x_17, x_4, x_18, x_19, x_7);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instForM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Std_HashSet_instForM___lam__2), 3, 0);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instForM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_HashSet_instForM(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instForIn___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; lean_object* x_10; size_t x_11; lean_object* x_12; 
x_6 = lean_alloc_closure((void*)(l_Std_HashSet_forIn___redArg___lam__0___boxed), 4, 1);
lean_closure_set(x_6, 0, x_5);
lean_inc(x_2);
x_7 = lean_alloc_closure((void*)(l_Std_HashSet_forIn___redArg___lam__1), 5, 2);
lean_closure_set(x_7, 0, x_2);
lean_closure_set(x_7, 1, x_6);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_dec(x_3);
x_9 = lean_array_size(x_8);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_usize_of_nat(x_10);
x_12 = l_Array_forIn_x27Unsafe_loop___redArg(x_2, x_8, x_7, x_9, x_11, x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instForIn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Std_HashSet_instForIn___lam__2), 5, 0);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instForIn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_HashSet_instForIn(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_filter___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_apply_1(x_1, x_2);
x_5 = lean_unbox(x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_filter___redArg___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_length___redArg(x_2);
x_4 = lean_nat_add(x_1, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_filter___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; lean_object* x_19; size_t x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 0);
lean_dec(x_5);
x_6 = lean_alloc_closure((void*)(l_Std_HashSet_filter___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_6, 0, x_1);
x_7 = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_AssocList_filter), 4, 3);
lean_closure_set(x_7, 0, lean_box(0));
lean_closure_set(x_7, 1, lean_box(0));
lean_closure_set(x_7, 2, x_6);
x_8 = lean_alloc_closure((void*)(l_Id_instMonad___lam__0), 4, 0);
x_9 = lean_alloc_closure((void*)(l_Id_instMonad___lam__1___boxed), 4, 0);
x_10 = lean_alloc_closure((void*)(l_Id_instMonad___lam__2___boxed), 2, 0);
x_11 = lean_alloc_closure((void*)(l_Id_instMonad___lam__3), 4, 0);
x_12 = lean_alloc_closure((void*)(l_Id_instMonad___lam__4___boxed), 4, 0);
x_13 = lean_alloc_closure((void*)(l_Id_instMonad___lam__5___boxed), 4, 0);
x_14 = lean_alloc_closure((void*)(l_Id_instMonad___lam__6), 4, 0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_9);
x_16 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_10);
lean_ctor_set(x_16, 2, x_11);
lean_ctor_set(x_16, 3, x_12);
lean_ctor_set(x_16, 4, x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_14);
x_18 = lean_array_size(x_4);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_usize_of_nat(x_19);
lean_inc(x_17);
x_21 = l_Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), x_17, x_7, x_18, x_20, x_4);
x_22 = lean_array_get_size(x_21);
x_23 = lean_nat_dec_lt(x_19, x_22);
if (x_23 == 0)
{
lean_dec(x_22);
lean_dec(x_17);
lean_ctor_set(x_2, 1, x_21);
lean_ctor_set(x_2, 0, x_19);
return x_2;
}
else
{
uint8_t x_24; 
x_24 = lean_nat_dec_le(x_22, x_22);
if (x_24 == 0)
{
lean_dec(x_22);
lean_dec(x_17);
lean_ctor_set(x_2, 1, x_21);
lean_ctor_set(x_2, 0, x_19);
return x_2;
}
else
{
lean_object* x_25; size_t x_26; lean_object* x_27; 
x_25 = lean_alloc_closure((void*)(l_Std_HashSet_filter___redArg___lam__1___boxed), 2, 0);
x_26 = lean_usize_of_nat(x_22);
lean_dec(x_22);
lean_inc(x_21);
x_27 = l_Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_17, x_25, x_21, x_20, x_26, x_19);
lean_ctor_set(x_2, 1, x_21);
lean_ctor_set(x_2, 0, x_27);
return x_2;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; size_t x_41; lean_object* x_42; size_t x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_28 = lean_ctor_get(x_2, 1);
lean_inc(x_28);
lean_dec(x_2);
x_29 = lean_alloc_closure((void*)(l_Std_HashSet_filter___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_29, 0, x_1);
x_30 = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_AssocList_filter), 4, 3);
lean_closure_set(x_30, 0, lean_box(0));
lean_closure_set(x_30, 1, lean_box(0));
lean_closure_set(x_30, 2, x_29);
x_31 = lean_alloc_closure((void*)(l_Id_instMonad___lam__0), 4, 0);
x_32 = lean_alloc_closure((void*)(l_Id_instMonad___lam__1___boxed), 4, 0);
x_33 = lean_alloc_closure((void*)(l_Id_instMonad___lam__2___boxed), 2, 0);
x_34 = lean_alloc_closure((void*)(l_Id_instMonad___lam__3), 4, 0);
x_35 = lean_alloc_closure((void*)(l_Id_instMonad___lam__4___boxed), 4, 0);
x_36 = lean_alloc_closure((void*)(l_Id_instMonad___lam__5___boxed), 4, 0);
x_37 = lean_alloc_closure((void*)(l_Id_instMonad___lam__6), 4, 0);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_31);
lean_ctor_set(x_38, 1, x_32);
x_39 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_33);
lean_ctor_set(x_39, 2, x_34);
lean_ctor_set(x_39, 3, x_35);
lean_ctor_set(x_39, 4, x_36);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_37);
x_41 = lean_array_size(x_28);
x_42 = lean_unsigned_to_nat(0u);
x_43 = lean_usize_of_nat(x_42);
lean_inc(x_40);
x_44 = l_Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), x_40, x_30, x_41, x_43, x_28);
x_45 = lean_array_get_size(x_44);
x_46 = lean_nat_dec_lt(x_42, x_45);
if (x_46 == 0)
{
lean_object* x_47; 
lean_dec(x_45);
lean_dec(x_40);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_42);
lean_ctor_set(x_47, 1, x_44);
return x_47;
}
else
{
uint8_t x_48; 
x_48 = lean_nat_dec_le(x_45, x_45);
if (x_48 == 0)
{
lean_object* x_49; 
lean_dec(x_45);
lean_dec(x_40);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_42);
lean_ctor_set(x_49, 1, x_44);
return x_49;
}
else
{
lean_object* x_50; size_t x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_alloc_closure((void*)(l_Std_HashSet_filter___redArg___lam__1___boxed), 2, 0);
x_51 = lean_usize_of_nat(x_45);
lean_dec(x_45);
lean_inc(x_44);
x_52 = l_Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_40, x_50, x_44, x_43, x_51, x_42);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_44);
return x_53;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_filter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; lean_object* x_22; size_t x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_7 = lean_ctor_get(x_5, 1);
x_8 = lean_ctor_get(x_5, 0);
lean_dec(x_8);
x_9 = lean_alloc_closure((void*)(l_Std_HashSet_filter___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_9, 0, x_4);
x_10 = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_AssocList_filter), 4, 3);
lean_closure_set(x_10, 0, lean_box(0));
lean_closure_set(x_10, 1, lean_box(0));
lean_closure_set(x_10, 2, x_9);
x_11 = lean_alloc_closure((void*)(l_Id_instMonad___lam__0), 4, 0);
x_12 = lean_alloc_closure((void*)(l_Id_instMonad___lam__1___boxed), 4, 0);
x_13 = lean_alloc_closure((void*)(l_Id_instMonad___lam__2___boxed), 2, 0);
x_14 = lean_alloc_closure((void*)(l_Id_instMonad___lam__3), 4, 0);
x_15 = lean_alloc_closure((void*)(l_Id_instMonad___lam__4___boxed), 4, 0);
x_16 = lean_alloc_closure((void*)(l_Id_instMonad___lam__5___boxed), 4, 0);
x_17 = lean_alloc_closure((void*)(l_Id_instMonad___lam__6), 4, 0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_12);
x_19 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_13);
lean_ctor_set(x_19, 2, x_14);
lean_ctor_set(x_19, 3, x_15);
lean_ctor_set(x_19, 4, x_16);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_17);
x_21 = lean_array_size(x_7);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_usize_of_nat(x_22);
lean_inc(x_20);
x_24 = l_Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), x_20, x_10, x_21, x_23, x_7);
x_25 = lean_array_get_size(x_24);
x_26 = lean_nat_dec_lt(x_22, x_25);
if (x_26 == 0)
{
lean_dec(x_25);
lean_dec(x_20);
lean_ctor_set(x_5, 1, x_24);
lean_ctor_set(x_5, 0, x_22);
return x_5;
}
else
{
uint8_t x_27; 
x_27 = lean_nat_dec_le(x_25, x_25);
if (x_27 == 0)
{
lean_dec(x_25);
lean_dec(x_20);
lean_ctor_set(x_5, 1, x_24);
lean_ctor_set(x_5, 0, x_22);
return x_5;
}
else
{
lean_object* x_28; size_t x_29; lean_object* x_30; 
x_28 = lean_alloc_closure((void*)(l_Std_HashSet_filter___redArg___lam__1___boxed), 2, 0);
x_29 = lean_usize_of_nat(x_25);
lean_dec(x_25);
lean_inc(x_24);
x_30 = l_Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_20, x_28, x_24, x_23, x_29, x_22);
lean_ctor_set(x_5, 1, x_24);
lean_ctor_set(x_5, 0, x_30);
return x_5;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; size_t x_44; lean_object* x_45; size_t x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_31 = lean_ctor_get(x_5, 1);
lean_inc(x_31);
lean_dec(x_5);
x_32 = lean_alloc_closure((void*)(l_Std_HashSet_filter___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_32, 0, x_4);
x_33 = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_AssocList_filter), 4, 3);
lean_closure_set(x_33, 0, lean_box(0));
lean_closure_set(x_33, 1, lean_box(0));
lean_closure_set(x_33, 2, x_32);
x_34 = lean_alloc_closure((void*)(l_Id_instMonad___lam__0), 4, 0);
x_35 = lean_alloc_closure((void*)(l_Id_instMonad___lam__1___boxed), 4, 0);
x_36 = lean_alloc_closure((void*)(l_Id_instMonad___lam__2___boxed), 2, 0);
x_37 = lean_alloc_closure((void*)(l_Id_instMonad___lam__3), 4, 0);
x_38 = lean_alloc_closure((void*)(l_Id_instMonad___lam__4___boxed), 4, 0);
x_39 = lean_alloc_closure((void*)(l_Id_instMonad___lam__5___boxed), 4, 0);
x_40 = lean_alloc_closure((void*)(l_Id_instMonad___lam__6), 4, 0);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_34);
lean_ctor_set(x_41, 1, x_35);
x_42 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_36);
lean_ctor_set(x_42, 2, x_37);
lean_ctor_set(x_42, 3, x_38);
lean_ctor_set(x_42, 4, x_39);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_40);
x_44 = lean_array_size(x_31);
x_45 = lean_unsigned_to_nat(0u);
x_46 = lean_usize_of_nat(x_45);
lean_inc(x_43);
x_47 = l_Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), x_43, x_33, x_44, x_46, x_31);
x_48 = lean_array_get_size(x_47);
x_49 = lean_nat_dec_lt(x_45, x_48);
if (x_49 == 0)
{
lean_object* x_50; 
lean_dec(x_48);
lean_dec(x_43);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_45);
lean_ctor_set(x_50, 1, x_47);
return x_50;
}
else
{
uint8_t x_51; 
x_51 = lean_nat_dec_le(x_48, x_48);
if (x_51 == 0)
{
lean_object* x_52; 
lean_dec(x_48);
lean_dec(x_43);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_45);
lean_ctor_set(x_52, 1, x_47);
return x_52;
}
else
{
lean_object* x_53; size_t x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_alloc_closure((void*)(l_Std_HashSet_filter___redArg___lam__1___boxed), 2, 0);
x_54 = lean_usize_of_nat(x_48);
lean_dec(x_48);
lean_inc(x_47);
x_55 = l_Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_43, x_53, x_47, x_46, x_54, x_45);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_47);
return x_56;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_filter___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_HashSet_filter___redArg___lam__0(x_1, x_2, x_3);
lean_dec(x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_filter___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_HashSet_filter___redArg___lam__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_filter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_HashSet_filter(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_insertMany___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint64_t x_9; lean_object* x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; lean_object* x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; size_t x_18; size_t x_19; lean_object* x_20; size_t x_21; size_t x_22; size_t x_23; lean_object* x_24; uint8_t x_25; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
x_7 = lean_array_get_size(x_6);
lean_inc(x_1);
lean_inc(x_3);
x_8 = lean_apply_1(x_1, x_3);
x_9 = lean_unbox_uint64(x_8);
lean_dec(x_8);
x_10 = lean_unsigned_to_nat(32u);
x_11 = lean_uint64_of_nat(x_10);
x_12 = lean_uint64_shift_right(x_9, x_11);
x_13 = lean_uint64_xor(x_9, x_12);
x_14 = lean_unsigned_to_nat(16u);
x_15 = lean_uint64_of_nat(x_14);
x_16 = lean_uint64_shift_right(x_13, x_15);
x_17 = lean_uint64_xor(x_13, x_16);
x_18 = lean_uint64_to_usize(x_17);
x_19 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_usize_of_nat(x_20);
x_22 = lean_usize_sub(x_19, x_21);
x_23 = lean_usize_land(x_18, x_22);
x_24 = lean_array_uget(x_6, x_23);
lean_inc(x_24);
lean_inc(x_3);
x_25 = l_Std_DHashMap_Internal_AssocList_contains(lean_box(0), lean_box(0), x_2, x_3, x_24);
if (x_25 == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_4);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_27 = lean_ctor_get(x_4, 1);
lean_dec(x_27);
x_28 = lean_ctor_get(x_4, 0);
lean_dec(x_28);
x_29 = lean_box(0);
x_30 = lean_nat_add(x_5, x_20);
lean_dec(x_5);
x_31 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_31, 0, x_3);
lean_ctor_set(x_31, 1, x_29);
lean_ctor_set(x_31, 2, x_24);
x_32 = lean_array_uset(x_6, x_23, x_31);
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
lean_object* x_39; lean_object* x_40; 
x_39 = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(x_1, x_32);
lean_ctor_set(x_4, 1, x_39);
lean_ctor_set(x_4, 0, x_30);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_4);
return x_40;
}
else
{
lean_object* x_41; 
lean_dec(x_1);
lean_ctor_set(x_4, 1, x_32);
lean_ctor_set(x_4, 0, x_30);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_4);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
lean_dec(x_4);
x_42 = lean_box(0);
x_43 = lean_nat_add(x_5, x_20);
lean_dec(x_5);
x_44 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_44, 0, x_3);
lean_ctor_set(x_44, 1, x_42);
lean_ctor_set(x_44, 2, x_24);
x_45 = lean_array_uset(x_6, x_23, x_44);
x_46 = lean_unsigned_to_nat(2u);
x_47 = lean_nat_shiftl(x_43, x_46);
x_48 = lean_unsigned_to_nat(3u);
x_49 = lean_nat_div(x_47, x_48);
lean_dec(x_47);
x_50 = lean_array_get_size(x_45);
x_51 = lean_nat_dec_le(x_49, x_50);
lean_dec(x_50);
lean_dec(x_49);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(x_1, x_45);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_43);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; 
lean_dec(x_1);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_43);
lean_ctor_set(x_55, 1, x_45);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
return x_56;
}
}
}
else
{
lean_object* x_57; 
lean_dec(x_24);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_4);
return x_57;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_insertMany___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_6 = lean_alloc_closure((void*)(l_Std_HashSet_insertMany___redArg___lam__0), 4, 2);
lean_closure_set(x_6, 0, x_2);
lean_closure_set(x_6, 1, x_1);
x_7 = lean_alloc_closure((void*)(l_Id_instMonad___lam__0), 4, 0);
x_8 = lean_alloc_closure((void*)(l_Id_instMonad___lam__1___boxed), 4, 0);
x_9 = lean_alloc_closure((void*)(l_Id_instMonad___lam__2___boxed), 2, 0);
x_10 = lean_alloc_closure((void*)(l_Id_instMonad___lam__3), 4, 0);
x_11 = lean_alloc_closure((void*)(l_Id_instMonad___lam__4___boxed), 4, 0);
x_12 = lean_alloc_closure((void*)(l_Id_instMonad___lam__5___boxed), 4, 0);
x_13 = lean_alloc_closure((void*)(l_Id_instMonad___lam__6), 4, 0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_8);
x_15 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_9);
lean_ctor_set(x_15, 2, x_10);
lean_ctor_set(x_15, 3, x_11);
lean_ctor_set(x_15, 4, x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
x_17 = lean_apply_5(x_3, lean_box(0), x_16, x_5, x_4, x_6);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_insertMany(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_8 = lean_alloc_closure((void*)(l_Std_HashSet_insertMany___redArg___lam__0), 4, 2);
lean_closure_set(x_8, 0, x_3);
lean_closure_set(x_8, 1, x_2);
x_9 = lean_alloc_closure((void*)(l_Id_instMonad___lam__0), 4, 0);
x_10 = lean_alloc_closure((void*)(l_Id_instMonad___lam__1___boxed), 4, 0);
x_11 = lean_alloc_closure((void*)(l_Id_instMonad___lam__2___boxed), 2, 0);
x_12 = lean_alloc_closure((void*)(l_Id_instMonad___lam__3), 4, 0);
x_13 = lean_alloc_closure((void*)(l_Id_instMonad___lam__4___boxed), 4, 0);
x_14 = lean_alloc_closure((void*)(l_Id_instMonad___lam__5___boxed), 4, 0);
x_15 = lean_alloc_closure((void*)(l_Id_instMonad___lam__6), 4, 0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_9);
lean_ctor_set(x_16, 1, x_10);
x_17 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_11);
lean_ctor_set(x_17, 2, x_12);
lean_ctor_set(x_17, 3, x_13);
lean_ctor_set(x_17, 4, x_14);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_15);
x_19 = lean_apply_5(x_5, lean_box(0), x_18, x_7, x_6, x_8);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_partition___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_4, 0);
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
x_10 = lean_apply_1(x_1, x_5);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint64_t x_17; lean_object* x_18; uint64_t x_19; uint64_t x_20; uint64_t x_21; lean_object* x_22; uint64_t x_23; uint64_t x_24; uint64_t x_25; size_t x_26; size_t x_27; lean_object* x_28; size_t x_29; size_t x_30; size_t x_31; lean_object* x_32; uint8_t x_33; 
x_13 = lean_ctor_get(x_9, 0);
x_14 = lean_ctor_get(x_9, 1);
x_15 = lean_array_get_size(x_14);
lean_inc(x_2);
lean_inc(x_5);
x_16 = lean_apply_1(x_2, x_5);
x_17 = lean_unbox_uint64(x_16);
lean_dec(x_16);
x_18 = lean_unsigned_to_nat(32u);
x_19 = lean_uint64_of_nat(x_18);
x_20 = lean_uint64_shift_right(x_17, x_19);
x_21 = lean_uint64_xor(x_17, x_20);
x_22 = lean_unsigned_to_nat(16u);
x_23 = lean_uint64_of_nat(x_22);
x_24 = lean_uint64_shift_right(x_21, x_23);
x_25 = lean_uint64_xor(x_21, x_24);
x_26 = lean_uint64_to_usize(x_25);
x_27 = lean_usize_of_nat(x_15);
lean_dec(x_15);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_usize_of_nat(x_28);
x_30 = lean_usize_sub(x_27, x_29);
x_31 = lean_usize_land(x_26, x_30);
x_32 = lean_array_uget(x_14, x_31);
lean_inc(x_32);
lean_inc(x_5);
lean_inc(x_3);
x_33 = l_Std_DHashMap_Internal_AssocList_contains(lean_box(0), lean_box(0), x_3, x_5, x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
lean_dec(x_3);
x_34 = lean_nat_add(x_13, x_28);
lean_dec(x_13);
x_35 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_35, 0, x_5);
lean_ctor_set(x_35, 1, x_6);
lean_ctor_set(x_35, 2, x_32);
x_36 = lean_array_uset(x_14, x_31, x_35);
x_37 = lean_unsigned_to_nat(2u);
x_38 = lean_nat_shiftl(x_34, x_37);
x_39 = lean_unsigned_to_nat(3u);
x_40 = lean_nat_div(x_38, x_39);
lean_dec(x_38);
x_41 = lean_array_get_size(x_36);
x_42 = lean_nat_dec_le(x_40, x_41);
lean_dec(x_41);
lean_dec(x_40);
if (x_42 == 0)
{
lean_object* x_43; 
x_43 = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(x_2, x_36);
lean_ctor_set(x_9, 1, x_43);
lean_ctor_set(x_9, 0, x_34);
return x_4;
}
else
{
lean_dec(x_2);
lean_ctor_set(x_9, 1, x_36);
lean_ctor_set(x_9, 0, x_34);
return x_4;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_2);
x_44 = lean_box(0);
x_45 = lean_array_uset(x_14, x_31, x_44);
x_46 = l_Std_DHashMap_Internal_AssocList_replace___redArg(x_3, x_5, x_6, x_32);
x_47 = lean_array_uset(x_45, x_31, x_46);
lean_ctor_set(x_9, 1, x_47);
return x_4;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint64_t x_52; lean_object* x_53; uint64_t x_54; uint64_t x_55; uint64_t x_56; lean_object* x_57; uint64_t x_58; uint64_t x_59; uint64_t x_60; size_t x_61; size_t x_62; lean_object* x_63; size_t x_64; size_t x_65; size_t x_66; lean_object* x_67; uint8_t x_68; 
x_48 = lean_ctor_get(x_9, 0);
x_49 = lean_ctor_get(x_9, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_9);
x_50 = lean_array_get_size(x_49);
lean_inc(x_2);
lean_inc(x_5);
x_51 = lean_apply_1(x_2, x_5);
x_52 = lean_unbox_uint64(x_51);
lean_dec(x_51);
x_53 = lean_unsigned_to_nat(32u);
x_54 = lean_uint64_of_nat(x_53);
x_55 = lean_uint64_shift_right(x_52, x_54);
x_56 = lean_uint64_xor(x_52, x_55);
x_57 = lean_unsigned_to_nat(16u);
x_58 = lean_uint64_of_nat(x_57);
x_59 = lean_uint64_shift_right(x_56, x_58);
x_60 = lean_uint64_xor(x_56, x_59);
x_61 = lean_uint64_to_usize(x_60);
x_62 = lean_usize_of_nat(x_50);
lean_dec(x_50);
x_63 = lean_unsigned_to_nat(1u);
x_64 = lean_usize_of_nat(x_63);
x_65 = lean_usize_sub(x_62, x_64);
x_66 = lean_usize_land(x_61, x_65);
x_67 = lean_array_uget(x_49, x_66);
lean_inc(x_67);
lean_inc(x_5);
lean_inc(x_3);
x_68 = l_Std_DHashMap_Internal_AssocList_contains(lean_box(0), lean_box(0), x_3, x_5, x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
lean_dec(x_3);
x_69 = lean_nat_add(x_48, x_63);
lean_dec(x_48);
x_70 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_70, 0, x_5);
lean_ctor_set(x_70, 1, x_6);
lean_ctor_set(x_70, 2, x_67);
x_71 = lean_array_uset(x_49, x_66, x_70);
x_72 = lean_unsigned_to_nat(2u);
x_73 = lean_nat_shiftl(x_69, x_72);
x_74 = lean_unsigned_to_nat(3u);
x_75 = lean_nat_div(x_73, x_74);
lean_dec(x_73);
x_76 = lean_array_get_size(x_71);
x_77 = lean_nat_dec_le(x_75, x_76);
lean_dec(x_76);
lean_dec(x_75);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; 
x_78 = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(x_2, x_71);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_69);
lean_ctor_set(x_79, 1, x_78);
lean_ctor_set(x_4, 1, x_79);
return x_4;
}
else
{
lean_object* x_80; 
lean_dec(x_2);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_69);
lean_ctor_set(x_80, 1, x_71);
lean_ctor_set(x_4, 1, x_80);
return x_4;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_2);
x_81 = lean_box(0);
x_82 = lean_array_uset(x_49, x_66, x_81);
x_83 = l_Std_DHashMap_Internal_AssocList_replace___redArg(x_3, x_5, x_6, x_67);
x_84 = lean_array_uset(x_82, x_66, x_83);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_48);
lean_ctor_set(x_85, 1, x_84);
lean_ctor_set(x_4, 1, x_85);
return x_4;
}
}
}
else
{
uint8_t x_86; 
x_86 = !lean_is_exclusive(x_8);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint64_t x_91; lean_object* x_92; uint64_t x_93; uint64_t x_94; uint64_t x_95; lean_object* x_96; uint64_t x_97; uint64_t x_98; uint64_t x_99; size_t x_100; size_t x_101; lean_object* x_102; size_t x_103; size_t x_104; size_t x_105; lean_object* x_106; uint8_t x_107; 
x_87 = lean_ctor_get(x_8, 0);
x_88 = lean_ctor_get(x_8, 1);
x_89 = lean_array_get_size(x_88);
lean_inc(x_2);
lean_inc(x_5);
x_90 = lean_apply_1(x_2, x_5);
x_91 = lean_unbox_uint64(x_90);
lean_dec(x_90);
x_92 = lean_unsigned_to_nat(32u);
x_93 = lean_uint64_of_nat(x_92);
x_94 = lean_uint64_shift_right(x_91, x_93);
x_95 = lean_uint64_xor(x_91, x_94);
x_96 = lean_unsigned_to_nat(16u);
x_97 = lean_uint64_of_nat(x_96);
x_98 = lean_uint64_shift_right(x_95, x_97);
x_99 = lean_uint64_xor(x_95, x_98);
x_100 = lean_uint64_to_usize(x_99);
x_101 = lean_usize_of_nat(x_89);
lean_dec(x_89);
x_102 = lean_unsigned_to_nat(1u);
x_103 = lean_usize_of_nat(x_102);
x_104 = lean_usize_sub(x_101, x_103);
x_105 = lean_usize_land(x_100, x_104);
x_106 = lean_array_uget(x_88, x_105);
lean_inc(x_106);
lean_inc(x_5);
lean_inc(x_3);
x_107 = l_Std_DHashMap_Internal_AssocList_contains(lean_box(0), lean_box(0), x_3, x_5, x_106);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; 
lean_dec(x_3);
x_108 = lean_nat_add(x_87, x_102);
lean_dec(x_87);
x_109 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_109, 0, x_5);
lean_ctor_set(x_109, 1, x_6);
lean_ctor_set(x_109, 2, x_106);
x_110 = lean_array_uset(x_88, x_105, x_109);
x_111 = lean_unsigned_to_nat(2u);
x_112 = lean_nat_shiftl(x_108, x_111);
x_113 = lean_unsigned_to_nat(3u);
x_114 = lean_nat_div(x_112, x_113);
lean_dec(x_112);
x_115 = lean_array_get_size(x_110);
x_116 = lean_nat_dec_le(x_114, x_115);
lean_dec(x_115);
lean_dec(x_114);
if (x_116 == 0)
{
lean_object* x_117; 
x_117 = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(x_2, x_110);
lean_ctor_set(x_8, 1, x_117);
lean_ctor_set(x_8, 0, x_108);
return x_4;
}
else
{
lean_dec(x_2);
lean_ctor_set(x_8, 1, x_110);
lean_ctor_set(x_8, 0, x_108);
return x_4;
}
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec(x_2);
x_118 = lean_box(0);
x_119 = lean_array_uset(x_88, x_105, x_118);
x_120 = l_Std_DHashMap_Internal_AssocList_replace___redArg(x_3, x_5, x_6, x_106);
x_121 = lean_array_uset(x_119, x_105, x_120);
lean_ctor_set(x_8, 1, x_121);
return x_4;
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint64_t x_126; lean_object* x_127; uint64_t x_128; uint64_t x_129; uint64_t x_130; lean_object* x_131; uint64_t x_132; uint64_t x_133; uint64_t x_134; size_t x_135; size_t x_136; lean_object* x_137; size_t x_138; size_t x_139; size_t x_140; lean_object* x_141; uint8_t x_142; 
x_122 = lean_ctor_get(x_8, 0);
x_123 = lean_ctor_get(x_8, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_8);
x_124 = lean_array_get_size(x_123);
lean_inc(x_2);
lean_inc(x_5);
x_125 = lean_apply_1(x_2, x_5);
x_126 = lean_unbox_uint64(x_125);
lean_dec(x_125);
x_127 = lean_unsigned_to_nat(32u);
x_128 = lean_uint64_of_nat(x_127);
x_129 = lean_uint64_shift_right(x_126, x_128);
x_130 = lean_uint64_xor(x_126, x_129);
x_131 = lean_unsigned_to_nat(16u);
x_132 = lean_uint64_of_nat(x_131);
x_133 = lean_uint64_shift_right(x_130, x_132);
x_134 = lean_uint64_xor(x_130, x_133);
x_135 = lean_uint64_to_usize(x_134);
x_136 = lean_usize_of_nat(x_124);
lean_dec(x_124);
x_137 = lean_unsigned_to_nat(1u);
x_138 = lean_usize_of_nat(x_137);
x_139 = lean_usize_sub(x_136, x_138);
x_140 = lean_usize_land(x_135, x_139);
x_141 = lean_array_uget(x_123, x_140);
lean_inc(x_141);
lean_inc(x_5);
lean_inc(x_3);
x_142 = l_Std_DHashMap_Internal_AssocList_contains(lean_box(0), lean_box(0), x_3, x_5, x_141);
if (x_142 == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; 
lean_dec(x_3);
x_143 = lean_nat_add(x_122, x_137);
lean_dec(x_122);
x_144 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_144, 0, x_5);
lean_ctor_set(x_144, 1, x_6);
lean_ctor_set(x_144, 2, x_141);
x_145 = lean_array_uset(x_123, x_140, x_144);
x_146 = lean_unsigned_to_nat(2u);
x_147 = lean_nat_shiftl(x_143, x_146);
x_148 = lean_unsigned_to_nat(3u);
x_149 = lean_nat_div(x_147, x_148);
lean_dec(x_147);
x_150 = lean_array_get_size(x_145);
x_151 = lean_nat_dec_le(x_149, x_150);
lean_dec(x_150);
lean_dec(x_149);
if (x_151 == 0)
{
lean_object* x_152; lean_object* x_153; 
x_152 = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(x_2, x_145);
x_153 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_153, 0, x_143);
lean_ctor_set(x_153, 1, x_152);
lean_ctor_set(x_4, 0, x_153);
return x_4;
}
else
{
lean_object* x_154; 
lean_dec(x_2);
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_143);
lean_ctor_set(x_154, 1, x_145);
lean_ctor_set(x_4, 0, x_154);
return x_4;
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
lean_dec(x_2);
x_155 = lean_box(0);
x_156 = lean_array_uset(x_123, x_140, x_155);
x_157 = l_Std_DHashMap_Internal_AssocList_replace___redArg(x_3, x_5, x_6, x_141);
x_158 = lean_array_uset(x_156, x_140, x_157);
x_159 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_159, 0, x_122);
lean_ctor_set(x_159, 1, x_158);
lean_ctor_set(x_4, 0, x_159);
return x_4;
}
}
}
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; uint8_t x_163; 
x_160 = lean_ctor_get(x_4, 0);
x_161 = lean_ctor_get(x_4, 1);
lean_inc(x_161);
lean_inc(x_160);
lean_dec(x_4);
lean_inc(x_5);
x_162 = lean_apply_1(x_1, x_5);
x_163 = lean_unbox(x_162);
lean_dec(x_162);
if (x_163 == 0)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; uint64_t x_169; lean_object* x_170; uint64_t x_171; uint64_t x_172; uint64_t x_173; lean_object* x_174; uint64_t x_175; uint64_t x_176; uint64_t x_177; size_t x_178; size_t x_179; lean_object* x_180; size_t x_181; size_t x_182; size_t x_183; lean_object* x_184; uint8_t x_185; 
x_164 = lean_ctor_get(x_161, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_161, 1);
lean_inc(x_165);
if (lean_is_exclusive(x_161)) {
 lean_ctor_release(x_161, 0);
 lean_ctor_release(x_161, 1);
 x_166 = x_161;
} else {
 lean_dec_ref(x_161);
 x_166 = lean_box(0);
}
x_167 = lean_array_get_size(x_165);
lean_inc(x_2);
lean_inc(x_5);
x_168 = lean_apply_1(x_2, x_5);
x_169 = lean_unbox_uint64(x_168);
lean_dec(x_168);
x_170 = lean_unsigned_to_nat(32u);
x_171 = lean_uint64_of_nat(x_170);
x_172 = lean_uint64_shift_right(x_169, x_171);
x_173 = lean_uint64_xor(x_169, x_172);
x_174 = lean_unsigned_to_nat(16u);
x_175 = lean_uint64_of_nat(x_174);
x_176 = lean_uint64_shift_right(x_173, x_175);
x_177 = lean_uint64_xor(x_173, x_176);
x_178 = lean_uint64_to_usize(x_177);
x_179 = lean_usize_of_nat(x_167);
lean_dec(x_167);
x_180 = lean_unsigned_to_nat(1u);
x_181 = lean_usize_of_nat(x_180);
x_182 = lean_usize_sub(x_179, x_181);
x_183 = lean_usize_land(x_178, x_182);
x_184 = lean_array_uget(x_165, x_183);
lean_inc(x_184);
lean_inc(x_5);
lean_inc(x_3);
x_185 = l_Std_DHashMap_Internal_AssocList_contains(lean_box(0), lean_box(0), x_3, x_5, x_184);
if (x_185 == 0)
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; uint8_t x_194; 
lean_dec(x_3);
x_186 = lean_nat_add(x_164, x_180);
lean_dec(x_164);
x_187 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_187, 0, x_5);
lean_ctor_set(x_187, 1, x_6);
lean_ctor_set(x_187, 2, x_184);
x_188 = lean_array_uset(x_165, x_183, x_187);
x_189 = lean_unsigned_to_nat(2u);
x_190 = lean_nat_shiftl(x_186, x_189);
x_191 = lean_unsigned_to_nat(3u);
x_192 = lean_nat_div(x_190, x_191);
lean_dec(x_190);
x_193 = lean_array_get_size(x_188);
x_194 = lean_nat_dec_le(x_192, x_193);
lean_dec(x_193);
lean_dec(x_192);
if (x_194 == 0)
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_195 = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(x_2, x_188);
if (lean_is_scalar(x_166)) {
 x_196 = lean_alloc_ctor(0, 2, 0);
} else {
 x_196 = x_166;
}
lean_ctor_set(x_196, 0, x_186);
lean_ctor_set(x_196, 1, x_195);
x_197 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_197, 0, x_160);
lean_ctor_set(x_197, 1, x_196);
return x_197;
}
else
{
lean_object* x_198; lean_object* x_199; 
lean_dec(x_2);
if (lean_is_scalar(x_166)) {
 x_198 = lean_alloc_ctor(0, 2, 0);
} else {
 x_198 = x_166;
}
lean_ctor_set(x_198, 0, x_186);
lean_ctor_set(x_198, 1, x_188);
x_199 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_199, 0, x_160);
lean_ctor_set(x_199, 1, x_198);
return x_199;
}
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
lean_dec(x_2);
x_200 = lean_box(0);
x_201 = lean_array_uset(x_165, x_183, x_200);
x_202 = l_Std_DHashMap_Internal_AssocList_replace___redArg(x_3, x_5, x_6, x_184);
x_203 = lean_array_uset(x_201, x_183, x_202);
if (lean_is_scalar(x_166)) {
 x_204 = lean_alloc_ctor(0, 2, 0);
} else {
 x_204 = x_166;
}
lean_ctor_set(x_204, 0, x_164);
lean_ctor_set(x_204, 1, x_203);
x_205 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_205, 0, x_160);
lean_ctor_set(x_205, 1, x_204);
return x_205;
}
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; uint64_t x_211; lean_object* x_212; uint64_t x_213; uint64_t x_214; uint64_t x_215; lean_object* x_216; uint64_t x_217; uint64_t x_218; uint64_t x_219; size_t x_220; size_t x_221; lean_object* x_222; size_t x_223; size_t x_224; size_t x_225; lean_object* x_226; uint8_t x_227; 
x_206 = lean_ctor_get(x_160, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_160, 1);
lean_inc(x_207);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 lean_ctor_release(x_160, 1);
 x_208 = x_160;
} else {
 lean_dec_ref(x_160);
 x_208 = lean_box(0);
}
x_209 = lean_array_get_size(x_207);
lean_inc(x_2);
lean_inc(x_5);
x_210 = lean_apply_1(x_2, x_5);
x_211 = lean_unbox_uint64(x_210);
lean_dec(x_210);
x_212 = lean_unsigned_to_nat(32u);
x_213 = lean_uint64_of_nat(x_212);
x_214 = lean_uint64_shift_right(x_211, x_213);
x_215 = lean_uint64_xor(x_211, x_214);
x_216 = lean_unsigned_to_nat(16u);
x_217 = lean_uint64_of_nat(x_216);
x_218 = lean_uint64_shift_right(x_215, x_217);
x_219 = lean_uint64_xor(x_215, x_218);
x_220 = lean_uint64_to_usize(x_219);
x_221 = lean_usize_of_nat(x_209);
lean_dec(x_209);
x_222 = lean_unsigned_to_nat(1u);
x_223 = lean_usize_of_nat(x_222);
x_224 = lean_usize_sub(x_221, x_223);
x_225 = lean_usize_land(x_220, x_224);
x_226 = lean_array_uget(x_207, x_225);
lean_inc(x_226);
lean_inc(x_5);
lean_inc(x_3);
x_227 = l_Std_DHashMap_Internal_AssocList_contains(lean_box(0), lean_box(0), x_3, x_5, x_226);
if (x_227 == 0)
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; uint8_t x_236; 
lean_dec(x_3);
x_228 = lean_nat_add(x_206, x_222);
lean_dec(x_206);
x_229 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_229, 0, x_5);
lean_ctor_set(x_229, 1, x_6);
lean_ctor_set(x_229, 2, x_226);
x_230 = lean_array_uset(x_207, x_225, x_229);
x_231 = lean_unsigned_to_nat(2u);
x_232 = lean_nat_shiftl(x_228, x_231);
x_233 = lean_unsigned_to_nat(3u);
x_234 = lean_nat_div(x_232, x_233);
lean_dec(x_232);
x_235 = lean_array_get_size(x_230);
x_236 = lean_nat_dec_le(x_234, x_235);
lean_dec(x_235);
lean_dec(x_234);
if (x_236 == 0)
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_237 = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(x_2, x_230);
if (lean_is_scalar(x_208)) {
 x_238 = lean_alloc_ctor(0, 2, 0);
} else {
 x_238 = x_208;
}
lean_ctor_set(x_238, 0, x_228);
lean_ctor_set(x_238, 1, x_237);
x_239 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_239, 0, x_238);
lean_ctor_set(x_239, 1, x_161);
return x_239;
}
else
{
lean_object* x_240; lean_object* x_241; 
lean_dec(x_2);
if (lean_is_scalar(x_208)) {
 x_240 = lean_alloc_ctor(0, 2, 0);
} else {
 x_240 = x_208;
}
lean_ctor_set(x_240, 0, x_228);
lean_ctor_set(x_240, 1, x_230);
x_241 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_241, 0, x_240);
lean_ctor_set(x_241, 1, x_161);
return x_241;
}
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; 
lean_dec(x_2);
x_242 = lean_box(0);
x_243 = lean_array_uset(x_207, x_225, x_242);
x_244 = l_Std_DHashMap_Internal_AssocList_replace___redArg(x_3, x_5, x_6, x_226);
x_245 = lean_array_uset(x_243, x_225, x_244);
if (lean_is_scalar(x_208)) {
 x_246 = lean_alloc_ctor(0, 2, 0);
} else {
 x_246 = x_208;
}
lean_ctor_set(x_246, 0, x_206);
lean_ctor_set(x_246, 1, x_245);
x_247 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_247, 0, x_246);
lean_ctor_set(x_247, 1, x_161);
return x_247;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_partition___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_partition___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_5 = lean_unsigned_to_nat(8u);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_unsigned_to_nat(2u);
x_8 = lean_nat_shiftl(x_5, x_7);
x_9 = lean_unsigned_to_nat(3u);
x_10 = lean_nat_div(x_8, x_9);
lean_dec(x_8);
x_11 = l_Nat_nextPowerOfTwo(x_10);
lean_dec(x_10);
x_12 = lean_box(0);
x_13 = lean_mk_array(x_11, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_6);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_alloc_closure((void*)(l_Id_instMonad___lam__0), 4, 0);
x_16 = lean_alloc_closure((void*)(l_Id_instMonad___lam__1___boxed), 4, 0);
x_17 = lean_alloc_closure((void*)(l_Id_instMonad___lam__2___boxed), 2, 0);
x_18 = lean_alloc_closure((void*)(l_Id_instMonad___lam__3), 4, 0);
x_19 = lean_alloc_closure((void*)(l_Id_instMonad___lam__4___boxed), 4, 0);
x_20 = lean_alloc_closure((void*)(l_Id_instMonad___lam__5___boxed), 4, 0);
x_21 = lean_alloc_closure((void*)(l_Id_instMonad___lam__6), 4, 0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_15);
lean_ctor_set(x_22, 1, x_16);
x_23 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_17);
lean_ctor_set(x_23, 2, x_18);
lean_ctor_set(x_23, 3, x_19);
lean_ctor_set(x_23, 4, x_20);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_21);
x_25 = lean_ctor_get(x_4, 1);
lean_inc(x_25);
lean_dec(x_4);
x_26 = lean_array_get_size(x_25);
x_27 = lean_nat_dec_lt(x_6, x_26);
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
lean_inc(x_14);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_14);
lean_ctor_set(x_28, 1, x_14);
return x_28;
}
else
{
uint8_t x_29; 
x_29 = lean_nat_dec_le(x_26, x_26);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
lean_inc(x_14);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_14);
lean_ctor_set(x_30, 1, x_14);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; size_t x_34; size_t x_35; lean_object* x_36; uint8_t x_37; 
x_31 = lean_alloc_closure((void*)(l_Std_HashSet_partition___redArg___lam__0), 6, 3);
lean_closure_set(x_31, 0, x_3);
lean_closure_set(x_31, 1, x_2);
lean_closure_set(x_31, 2, x_1);
lean_inc(x_24);
x_32 = lean_alloc_closure((void*)(l_Std_HashSet_partition___redArg___lam__1), 4, 2);
lean_closure_set(x_32, 0, x_24);
lean_closure_set(x_32, 1, x_31);
lean_inc(x_14);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_14);
lean_ctor_set(x_33, 1, x_14);
x_34 = lean_usize_of_nat(x_6);
x_35 = lean_usize_of_nat(x_26);
lean_dec(x_26);
x_36 = l_Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_24, x_32, x_25, x_34, x_35, x_33);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
return x_36;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_36, 0);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_36);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_partition(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_6 = lean_unsigned_to_nat(8u);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_unsigned_to_nat(2u);
x_9 = lean_nat_shiftl(x_6, x_8);
x_10 = lean_unsigned_to_nat(3u);
x_11 = lean_nat_div(x_9, x_10);
lean_dec(x_9);
x_12 = l_Nat_nextPowerOfTwo(x_11);
lean_dec(x_11);
x_13 = lean_box(0);
x_14 = lean_mk_array(x_12, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_closure((void*)(l_Id_instMonad___lam__0), 4, 0);
x_17 = lean_alloc_closure((void*)(l_Id_instMonad___lam__1___boxed), 4, 0);
x_18 = lean_alloc_closure((void*)(l_Id_instMonad___lam__2___boxed), 2, 0);
x_19 = lean_alloc_closure((void*)(l_Id_instMonad___lam__3), 4, 0);
x_20 = lean_alloc_closure((void*)(l_Id_instMonad___lam__4___boxed), 4, 0);
x_21 = lean_alloc_closure((void*)(l_Id_instMonad___lam__5___boxed), 4, 0);
x_22 = lean_alloc_closure((void*)(l_Id_instMonad___lam__6), 4, 0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_16);
lean_ctor_set(x_23, 1, x_17);
x_24 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_18);
lean_ctor_set(x_24, 2, x_19);
lean_ctor_set(x_24, 3, x_20);
lean_ctor_set(x_24, 4, x_21);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_22);
x_26 = lean_ctor_get(x_5, 1);
lean_inc(x_26);
lean_dec(x_5);
x_27 = lean_array_get_size(x_26);
x_28 = lean_nat_dec_lt(x_7, x_27);
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_inc(x_15);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_15);
lean_ctor_set(x_29, 1, x_15);
return x_29;
}
else
{
uint8_t x_30; 
x_30 = lean_nat_dec_le(x_27, x_27);
if (x_30 == 0)
{
lean_object* x_31; 
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_inc(x_15);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_15);
lean_ctor_set(x_31, 1, x_15);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; size_t x_35; size_t x_36; lean_object* x_37; uint8_t x_38; 
x_32 = lean_alloc_closure((void*)(l_Std_HashSet_partition___redArg___lam__0), 6, 3);
lean_closure_set(x_32, 0, x_4);
lean_closure_set(x_32, 1, x_3);
lean_closure_set(x_32, 2, x_2);
lean_inc(x_25);
x_33 = lean_alloc_closure((void*)(l_Std_HashSet_partition___redArg___lam__1), 4, 2);
lean_closure_set(x_33, 0, x_25);
lean_closure_set(x_33, 1, x_32);
lean_inc(x_15);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_15);
lean_ctor_set(x_34, 1, x_15);
x_35 = lean_usize_of_nat(x_7);
x_36 = lean_usize_of_nat(x_27);
lean_dec(x_27);
x_37 = l_Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_25, x_33, x_26, x_35, x_36, x_34);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
return x_37;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_37, 0);
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_37);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_all___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; uint8_t x_9; 
x_7 = lean_apply_1(x_1, x_4);
x_8 = lean_unbox(x_7);
lean_dec(x_7);
x_9 = l_instDecidableNot___redArg(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_3);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_2);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_2);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_all___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_DHashMap_Internal_AssocList_forInStep_go___redArg(x_1, x_2, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_all___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; lean_object* x_20; size_t x_21; lean_object* x_22; lean_object* x_23; 
x_3 = lean_alloc_closure((void*)(l_Id_instMonad___lam__0), 4, 0);
x_4 = lean_alloc_closure((void*)(l_Id_instMonad___lam__1___boxed), 4, 0);
x_5 = lean_alloc_closure((void*)(l_Id_instMonad___lam__2___boxed), 2, 0);
x_6 = lean_alloc_closure((void*)(l_Id_instMonad___lam__3), 4, 0);
x_7 = lean_alloc_closure((void*)(l_Id_instMonad___lam__4___boxed), 4, 0);
x_8 = lean_alloc_closure((void*)(l_Id_instMonad___lam__5___boxed), 4, 0);
x_9 = lean_alloc_closure((void*)(l_Id_instMonad___lam__6), 4, 0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_4);
x_11 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_5);
lean_ctor_set(x_11, 2, x_6);
lean_ctor_set(x_11, 3, x_7);
lean_ctor_set(x_11, 4, x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
x_13 = lean_box(0);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
lean_inc(x_15);
x_16 = lean_alloc_closure((void*)(l_Std_HashSet_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(x_16, 0, x_2);
lean_closure_set(x_16, 1, x_15);
lean_closure_set(x_16, 2, x_14);
lean_inc(x_12);
x_17 = lean_alloc_closure((void*)(l_Std_HashSet_all___redArg___lam__1), 5, 2);
lean_closure_set(x_17, 0, x_12);
lean_closure_set(x_17, 1, x_16);
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
lean_dec(x_1);
x_19 = lean_array_size(x_18);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_usize_of_nat(x_20);
x_22 = l_Array_forIn_x27Unsafe_loop___redArg(x_12, x_18, x_17, x_19, x_21, x_15);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec(x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_box(1);
x_25 = lean_unbox(x_24);
return x_25;
}
else
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_23, 0);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_unbox(x_26);
lean_dec(x_26);
return x_27;
}
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_all(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; size_t x_22; lean_object* x_23; size_t x_24; lean_object* x_25; lean_object* x_26; 
x_6 = lean_alloc_closure((void*)(l_Id_instMonad___lam__0), 4, 0);
x_7 = lean_alloc_closure((void*)(l_Id_instMonad___lam__1___boxed), 4, 0);
x_8 = lean_alloc_closure((void*)(l_Id_instMonad___lam__2___boxed), 2, 0);
x_9 = lean_alloc_closure((void*)(l_Id_instMonad___lam__3), 4, 0);
x_10 = lean_alloc_closure((void*)(l_Id_instMonad___lam__4___boxed), 4, 0);
x_11 = lean_alloc_closure((void*)(l_Id_instMonad___lam__5___boxed), 4, 0);
x_12 = lean_alloc_closure((void*)(l_Id_instMonad___lam__6), 4, 0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_7);
x_14 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_8);
lean_ctor_set(x_14, 2, x_9);
lean_ctor_set(x_14, 3, x_10);
lean_ctor_set(x_14, 4, x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_12);
x_16 = lean_box(0);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
lean_inc(x_18);
x_19 = lean_alloc_closure((void*)(l_Std_HashSet_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(x_19, 0, x_5);
lean_closure_set(x_19, 1, x_18);
lean_closure_set(x_19, 2, x_17);
lean_inc(x_15);
x_20 = lean_alloc_closure((void*)(l_Std_HashSet_all___redArg___lam__1), 5, 2);
lean_closure_set(x_20, 0, x_15);
lean_closure_set(x_20, 1, x_19);
x_21 = lean_ctor_get(x_4, 1);
lean_inc(x_21);
lean_dec(x_4);
x_22 = lean_array_size(x_21);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_usize_of_nat(x_23);
x_25 = l_Array_forIn_x27Unsafe_loop___redArg(x_15, x_21, x_20, x_22, x_24, x_18);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec(x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_box(1);
x_28 = lean_unbox(x_27);
return x_28;
}
else
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_26, 0);
lean_inc(x_29);
lean_dec(x_26);
x_30 = lean_unbox(x_29);
lean_dec(x_29);
return x_30;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_all___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_HashSet_all___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_all___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_HashSet_all___redArg(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_all___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Std_HashSet_all(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_any___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_apply_1(x_1, x_4);
x_8 = lean_unbox(x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_3);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_2);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_2);
x_10 = lean_box(x_8);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_3);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_any___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; lean_object* x_20; size_t x_21; lean_object* x_22; lean_object* x_23; 
x_3 = lean_alloc_closure((void*)(l_Id_instMonad___lam__0), 4, 0);
x_4 = lean_alloc_closure((void*)(l_Id_instMonad___lam__1___boxed), 4, 0);
x_5 = lean_alloc_closure((void*)(l_Id_instMonad___lam__2___boxed), 2, 0);
x_6 = lean_alloc_closure((void*)(l_Id_instMonad___lam__3), 4, 0);
x_7 = lean_alloc_closure((void*)(l_Id_instMonad___lam__4___boxed), 4, 0);
x_8 = lean_alloc_closure((void*)(l_Id_instMonad___lam__5___boxed), 4, 0);
x_9 = lean_alloc_closure((void*)(l_Id_instMonad___lam__6), 4, 0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_4);
x_11 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_5);
lean_ctor_set(x_11, 2, x_6);
lean_ctor_set(x_11, 3, x_7);
lean_ctor_set(x_11, 4, x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
x_13 = lean_box(0);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
lean_inc(x_15);
x_16 = lean_alloc_closure((void*)(l_Std_HashSet_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(x_16, 0, x_2);
lean_closure_set(x_16, 1, x_15);
lean_closure_set(x_16, 2, x_14);
lean_inc(x_12);
x_17 = lean_alloc_closure((void*)(l_Std_HashSet_all___redArg___lam__1), 5, 2);
lean_closure_set(x_17, 0, x_12);
lean_closure_set(x_17, 1, x_16);
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
lean_dec(x_1);
x_19 = lean_array_size(x_18);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_usize_of_nat(x_20);
x_22 = l_Array_forIn_x27Unsafe_loop___redArg(x_12, x_18, x_17, x_19, x_21, x_15);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec(x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_box(0);
x_25 = lean_unbox(x_24);
return x_25;
}
else
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_23, 0);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_unbox(x_26);
lean_dec(x_26);
return x_27;
}
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_any(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; size_t x_22; lean_object* x_23; size_t x_24; lean_object* x_25; lean_object* x_26; 
x_6 = lean_alloc_closure((void*)(l_Id_instMonad___lam__0), 4, 0);
x_7 = lean_alloc_closure((void*)(l_Id_instMonad___lam__1___boxed), 4, 0);
x_8 = lean_alloc_closure((void*)(l_Id_instMonad___lam__2___boxed), 2, 0);
x_9 = lean_alloc_closure((void*)(l_Id_instMonad___lam__3), 4, 0);
x_10 = lean_alloc_closure((void*)(l_Id_instMonad___lam__4___boxed), 4, 0);
x_11 = lean_alloc_closure((void*)(l_Id_instMonad___lam__5___boxed), 4, 0);
x_12 = lean_alloc_closure((void*)(l_Id_instMonad___lam__6), 4, 0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_7);
x_14 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_8);
lean_ctor_set(x_14, 2, x_9);
lean_ctor_set(x_14, 3, x_10);
lean_ctor_set(x_14, 4, x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_12);
x_16 = lean_box(0);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
lean_inc(x_18);
x_19 = lean_alloc_closure((void*)(l_Std_HashSet_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(x_19, 0, x_5);
lean_closure_set(x_19, 1, x_18);
lean_closure_set(x_19, 2, x_17);
lean_inc(x_15);
x_20 = lean_alloc_closure((void*)(l_Std_HashSet_all___redArg___lam__1), 5, 2);
lean_closure_set(x_20, 0, x_15);
lean_closure_set(x_20, 1, x_19);
x_21 = lean_ctor_get(x_4, 1);
lean_inc(x_21);
lean_dec(x_4);
x_22 = lean_array_size(x_21);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_usize_of_nat(x_23);
x_25 = l_Array_forIn_x27Unsafe_loop___redArg(x_15, x_21, x_20, x_22, x_24, x_18);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec(x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_box(0);
x_28 = lean_unbox(x_27);
return x_28;
}
else
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_26, 0);
lean_inc(x_29);
lean_dec(x_26);
x_30 = lean_unbox(x_29);
lean_dec(x_29);
return x_30;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_any___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_HashSet_any___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_any___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_HashSet_any___redArg(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_any___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Std_HashSet_any(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_toArray___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_array_push(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_toArray___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_toArray___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_mk_empty_array_with_capacity(x_2);
lean_dec(x_2);
x_4 = lean_alloc_closure((void*)(l_Id_instMonad___lam__0), 4, 0);
x_5 = lean_alloc_closure((void*)(l_Id_instMonad___lam__1___boxed), 4, 0);
x_6 = lean_alloc_closure((void*)(l_Id_instMonad___lam__2___boxed), 2, 0);
x_7 = lean_alloc_closure((void*)(l_Id_instMonad___lam__3), 4, 0);
x_8 = lean_alloc_closure((void*)(l_Id_instMonad___lam__4___boxed), 4, 0);
x_9 = lean_alloc_closure((void*)(l_Id_instMonad___lam__5___boxed), 4, 0);
x_10 = lean_alloc_closure((void*)(l_Id_instMonad___lam__6), 4, 0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_5);
x_12 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_6);
lean_ctor_set(x_12, 2, x_7);
lean_ctor_set(x_12, 3, x_8);
lean_ctor_set(x_12, 4, x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_get_size(x_14);
x_17 = lean_nat_dec_lt(x_15, x_16);
if (x_17 == 0)
{
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
return x_3;
}
else
{
uint8_t x_18; 
x_18 = lean_nat_dec_le(x_16, x_16);
if (x_18 == 0)
{
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
return x_3;
}
else
{
lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; 
x_19 = lean_alloc_closure((void*)(l_Std_HashSet_toArray___redArg___lam__0___boxed), 3, 0);
lean_inc(x_13);
x_20 = lean_alloc_closure((void*)(l_Std_HashSet_toArray___redArg___lam__1), 4, 2);
lean_closure_set(x_20, 0, x_13);
lean_closure_set(x_20, 1, x_19);
x_21 = lean_usize_of_nat(x_15);
x_22 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_23 = l_Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_13, x_20, x_14, x_21, x_22, x_3);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_toArray(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_mk_empty_array_with_capacity(x_5);
lean_dec(x_5);
x_7 = lean_alloc_closure((void*)(l_Id_instMonad___lam__0), 4, 0);
x_8 = lean_alloc_closure((void*)(l_Id_instMonad___lam__1___boxed), 4, 0);
x_9 = lean_alloc_closure((void*)(l_Id_instMonad___lam__2___boxed), 2, 0);
x_10 = lean_alloc_closure((void*)(l_Id_instMonad___lam__3), 4, 0);
x_11 = lean_alloc_closure((void*)(l_Id_instMonad___lam__4___boxed), 4, 0);
x_12 = lean_alloc_closure((void*)(l_Id_instMonad___lam__5___boxed), 4, 0);
x_13 = lean_alloc_closure((void*)(l_Id_instMonad___lam__6), 4, 0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_8);
x_15 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_9);
lean_ctor_set(x_15, 2, x_10);
lean_ctor_set(x_15, 3, x_11);
lean_ctor_set(x_15, 4, x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
x_17 = lean_ctor_get(x_4, 1);
lean_inc(x_17);
lean_dec(x_4);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_array_get_size(x_17);
x_20 = lean_nat_dec_lt(x_18, x_19);
if (x_20 == 0)
{
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
return x_6;
}
else
{
uint8_t x_21; 
x_21 = lean_nat_dec_le(x_19, x_19);
if (x_21 == 0)
{
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
return x_6;
}
else
{
lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; lean_object* x_26; 
x_22 = lean_alloc_closure((void*)(l_Std_HashSet_toArray___redArg___lam__0___boxed), 3, 0);
lean_inc(x_16);
x_23 = lean_alloc_closure((void*)(l_Std_HashSet_toArray___redArg___lam__1), 4, 2);
lean_closure_set(x_23, 0, x_16);
lean_closure_set(x_23, 1, x_22);
x_24 = lean_usize_of_nat(x_18);
x_25 = lean_usize_of_nat(x_19);
lean_dec(x_19);
x_26 = l_Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_16, x_23, x_17, x_24, x_25, x_6);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_toArray___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_HashSet_toArray___redArg___lam__0(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_toArray___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_HashSet_toArray(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_ofArray___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; lean_object* x_27; 
x_4 = lean_alloc_closure((void*)(l_Std_HashSet_ofList___redArg___lam__0), 5, 2);
lean_closure_set(x_4, 0, x_2);
lean_closure_set(x_4, 1, x_1);
x_5 = lean_unsigned_to_nat(8u);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_unsigned_to_nat(2u);
x_8 = lean_nat_shiftl(x_5, x_7);
x_9 = lean_unsigned_to_nat(3u);
x_10 = lean_nat_div(x_8, x_9);
lean_dec(x_8);
x_11 = l_Nat_nextPowerOfTwo(x_10);
lean_dec(x_10);
x_12 = lean_box(0);
x_13 = lean_mk_array(x_11, x_12);
x_14 = lean_alloc_closure((void*)(l_Id_instMonad___lam__0), 4, 0);
x_15 = lean_alloc_closure((void*)(l_Id_instMonad___lam__1___boxed), 4, 0);
x_16 = lean_alloc_closure((void*)(l_Id_instMonad___lam__2___boxed), 2, 0);
x_17 = lean_alloc_closure((void*)(l_Id_instMonad___lam__3), 4, 0);
x_18 = lean_alloc_closure((void*)(l_Id_instMonad___lam__4___boxed), 4, 0);
x_19 = lean_alloc_closure((void*)(l_Id_instMonad___lam__5___boxed), 4, 0);
x_20 = lean_alloc_closure((void*)(l_Id_instMonad___lam__6), 4, 0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_14);
lean_ctor_set(x_21, 1, x_15);
x_22 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_16);
lean_ctor_set(x_22, 2, x_17);
lean_ctor_set(x_22, 3, x_18);
lean_ctor_set(x_22, 4, x_19);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_20);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_6);
lean_ctor_set(x_24, 1, x_13);
x_25 = lean_array_size(x_3);
x_26 = lean_usize_of_nat(x_6);
x_27 = l_Array_forIn_x27Unsafe_loop___redArg(x_23, x_3, x_4, x_25, x_26, x_24);
return x_27;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_ofArray(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; lean_object* x_28; 
x_5 = lean_alloc_closure((void*)(l_Std_HashSet_ofList___redArg___lam__0), 5, 2);
lean_closure_set(x_5, 0, x_3);
lean_closure_set(x_5, 1, x_2);
x_6 = lean_unsigned_to_nat(8u);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_unsigned_to_nat(2u);
x_9 = lean_nat_shiftl(x_6, x_8);
x_10 = lean_unsigned_to_nat(3u);
x_11 = lean_nat_div(x_9, x_10);
lean_dec(x_9);
x_12 = l_Nat_nextPowerOfTwo(x_11);
lean_dec(x_11);
x_13 = lean_box(0);
x_14 = lean_mk_array(x_12, x_13);
x_15 = lean_alloc_closure((void*)(l_Id_instMonad___lam__0), 4, 0);
x_16 = lean_alloc_closure((void*)(l_Id_instMonad___lam__1___boxed), 4, 0);
x_17 = lean_alloc_closure((void*)(l_Id_instMonad___lam__2___boxed), 2, 0);
x_18 = lean_alloc_closure((void*)(l_Id_instMonad___lam__3), 4, 0);
x_19 = lean_alloc_closure((void*)(l_Id_instMonad___lam__4___boxed), 4, 0);
x_20 = lean_alloc_closure((void*)(l_Id_instMonad___lam__5___boxed), 4, 0);
x_21 = lean_alloc_closure((void*)(l_Id_instMonad___lam__6), 4, 0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_15);
lean_ctor_set(x_22, 1, x_16);
x_23 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_17);
lean_ctor_set(x_23, 2, x_18);
lean_ctor_set(x_23, 3, x_19);
lean_ctor_set(x_23, 4, x_20);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_21);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_7);
lean_ctor_set(x_25, 1, x_14);
x_26 = lean_array_size(x_4);
x_27 = lean_usize_of_nat(x_7);
x_28 = l_Array_forIn_x27Unsafe_loop___redArg(x_24, x_4, x_5, x_26, x_27, x_25);
return x_28;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_union___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint64_t x_10; lean_object* x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; lean_object* x_15; uint64_t x_16; uint64_t x_17; uint64_t x_18; size_t x_19; size_t x_20; lean_object* x_21; size_t x_22; size_t x_23; size_t x_24; lean_object* x_25; uint8_t x_26; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
x_8 = lean_array_get_size(x_7);
lean_inc(x_1);
lean_inc(x_4);
x_9 = lean_apply_1(x_1, x_4);
x_10 = lean_unbox_uint64(x_9);
lean_dec(x_9);
x_11 = lean_unsigned_to_nat(32u);
x_12 = lean_uint64_of_nat(x_11);
x_13 = lean_uint64_shift_right(x_10, x_12);
x_14 = lean_uint64_xor(x_10, x_13);
x_15 = lean_unsigned_to_nat(16u);
x_16 = lean_uint64_of_nat(x_15);
x_17 = lean_uint64_shift_right(x_14, x_16);
x_18 = lean_uint64_xor(x_14, x_17);
x_19 = lean_uint64_to_usize(x_18);
x_20 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_usize_of_nat(x_21);
x_23 = lean_usize_sub(x_20, x_22);
x_24 = lean_usize_land(x_19, x_23);
x_25 = lean_array_uget(x_7, x_24);
lean_inc(x_25);
lean_inc(x_4);
x_26 = l_Std_DHashMap_Internal_AssocList_contains(lean_box(0), lean_box(0), x_2, x_4, x_25);
if (x_26 == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_3);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_28 = lean_ctor_get(x_3, 1);
lean_dec(x_28);
x_29 = lean_ctor_get(x_3, 0);
lean_dec(x_29);
x_30 = lean_box(0);
x_31 = lean_nat_add(x_6, x_21);
lean_dec(x_6);
x_32 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_32, 0, x_4);
lean_ctor_set(x_32, 1, x_30);
lean_ctor_set(x_32, 2, x_25);
x_33 = lean_array_uset(x_7, x_24, x_32);
x_34 = lean_unsigned_to_nat(2u);
x_35 = lean_nat_shiftl(x_31, x_34);
x_36 = lean_unsigned_to_nat(3u);
x_37 = lean_nat_div(x_35, x_36);
lean_dec(x_35);
x_38 = lean_array_get_size(x_33);
x_39 = lean_nat_dec_le(x_37, x_38);
lean_dec(x_38);
lean_dec(x_37);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(x_1, x_33);
lean_ctor_set(x_3, 1, x_40);
lean_ctor_set(x_3, 0, x_31);
return x_3;
}
else
{
lean_dec(x_1);
lean_ctor_set(x_3, 1, x_33);
lean_ctor_set(x_3, 0, x_31);
return x_3;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
lean_dec(x_3);
x_41 = lean_box(0);
x_42 = lean_nat_add(x_6, x_21);
lean_dec(x_6);
x_43 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_43, 0, x_4);
lean_ctor_set(x_43, 1, x_41);
lean_ctor_set(x_43, 2, x_25);
x_44 = lean_array_uset(x_7, x_24, x_43);
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
lean_object* x_51; lean_object* x_52; 
x_51 = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(x_1, x_44);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_42);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
else
{
lean_object* x_53; 
lean_dec(x_1);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_42);
lean_ctor_set(x_53, 1, x_44);
return x_53;
}
}
}
else
{
lean_dec(x_25);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_union___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_union___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_5 = lean_alloc_closure((void*)(l_Id_instMonad___lam__0), 4, 0);
x_6 = lean_alloc_closure((void*)(l_Id_instMonad___lam__1___boxed), 4, 0);
x_7 = lean_alloc_closure((void*)(l_Id_instMonad___lam__2___boxed), 2, 0);
x_8 = lean_alloc_closure((void*)(l_Id_instMonad___lam__3), 4, 0);
x_9 = lean_alloc_closure((void*)(l_Id_instMonad___lam__4___boxed), 4, 0);
x_10 = lean_alloc_closure((void*)(l_Id_instMonad___lam__5___boxed), 4, 0);
x_11 = lean_alloc_closure((void*)(l_Id_instMonad___lam__6), 4, 0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_6);
x_13 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_7);
lean_ctor_set(x_13, 2, x_8);
lean_ctor_set(x_13, 3, x_9);
lean_ctor_set(x_13, 4, x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
x_15 = lean_ctor_get(x_4, 1);
lean_inc(x_15);
lean_dec(x_4);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_get_size(x_15);
x_18 = lean_nat_dec_lt(x_16, x_17);
if (x_18 == 0)
{
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
uint8_t x_19; 
x_19 = lean_nat_dec_le(x_17, x_17);
if (x_19 == 0)
{
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; lean_object* x_24; 
x_20 = lean_alloc_closure((void*)(l_Std_HashSet_union___redArg___lam__0___boxed), 5, 2);
lean_closure_set(x_20, 0, x_2);
lean_closure_set(x_20, 1, x_1);
lean_inc(x_14);
x_21 = lean_alloc_closure((void*)(l_Std_HashSet_union___redArg___lam__1), 4, 2);
lean_closure_set(x_21, 0, x_14);
lean_closure_set(x_21, 1, x_20);
x_22 = lean_usize_of_nat(x_16);
x_23 = lean_usize_of_nat(x_17);
lean_dec(x_17);
x_24 = l_Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_14, x_21, x_15, x_22, x_23, x_3);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_union(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_6 = lean_alloc_closure((void*)(l_Id_instMonad___lam__0), 4, 0);
x_7 = lean_alloc_closure((void*)(l_Id_instMonad___lam__1___boxed), 4, 0);
x_8 = lean_alloc_closure((void*)(l_Id_instMonad___lam__2___boxed), 2, 0);
x_9 = lean_alloc_closure((void*)(l_Id_instMonad___lam__3), 4, 0);
x_10 = lean_alloc_closure((void*)(l_Id_instMonad___lam__4___boxed), 4, 0);
x_11 = lean_alloc_closure((void*)(l_Id_instMonad___lam__5___boxed), 4, 0);
x_12 = lean_alloc_closure((void*)(l_Id_instMonad___lam__6), 4, 0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_7);
x_14 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_8);
lean_ctor_set(x_14, 2, x_9);
lean_ctor_set(x_14, 3, x_10);
lean_ctor_set(x_14, 4, x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_12);
x_16 = lean_ctor_get(x_5, 1);
lean_inc(x_16);
lean_dec(x_5);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_array_get_size(x_16);
x_19 = lean_nat_dec_lt(x_17, x_18);
if (x_19 == 0)
{
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
else
{
uint8_t x_20; 
x_20 = lean_nat_dec_le(x_18, x_18);
if (x_20 == 0)
{
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
else
{
lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; 
x_21 = lean_alloc_closure((void*)(l_Std_HashSet_union___redArg___lam__0___boxed), 5, 2);
lean_closure_set(x_21, 0, x_3);
lean_closure_set(x_21, 1, x_2);
lean_inc(x_15);
x_22 = lean_alloc_closure((void*)(l_Std_HashSet_union___redArg___lam__1), 4, 2);
lean_closure_set(x_22, 0, x_15);
lean_closure_set(x_22, 1, x_21);
x_23 = lean_usize_of_nat(x_17);
x_24 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_25 = l_Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_15, x_22, x_16, x_23, x_24, x_4);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_union___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_HashSet_union___redArg___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instUnion___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_HashSet_union), 5, 3);
lean_closure_set(x_3, 0, lean_box(0));
lean_closure_set(x_3, 1, x_1);
lean_closure_set(x_3, 2, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instUnion(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Std_HashSet_union), 5, 3);
lean_closure_set(x_4, 0, lean_box(0));
lean_closure_set(x_4, 1, x_2);
lean_closure_set(x_4, 2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_numBuckets___at___Std_HashSet_Internal_numBuckets_spec__0___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_DHashMap_Raw_Internal_numBuckets___redArg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_numBuckets___at___Std_HashSet_Internal_numBuckets_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_DHashMap_Raw_Internal_numBuckets___redArg(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Internal_numBuckets___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Raw_Internal_numBuckets___redArg(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Internal_numBuckets(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Raw_Internal_numBuckets___redArg(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_numBuckets___at___Std_HashSet_Internal_numBuckets_spec__0___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_DHashMap_Internal_numBuckets___at___Std_HashSet_Internal_numBuckets_spec__0___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_numBuckets___at___Std_HashSet_Internal_numBuckets_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_DHashMap_Internal_numBuckets___at___Std_HashSet_Internal_numBuckets_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Internal_numBuckets___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_HashSet_Internal_numBuckets___redArg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Internal_numBuckets___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_HashSet_Internal_numBuckets(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instRepr___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_5 = lean_mk_string_unchecked("Std.HashSet.ofList ", 19, 19);
x_6 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_12 = lean_box(0);
x_13 = lean_alloc_closure((void*)(l_Id_instMonad___lam__0), 4, 0);
x_14 = lean_alloc_closure((void*)(l_Id_instMonad___lam__1___boxed), 4, 0);
x_15 = lean_alloc_closure((void*)(l_Id_instMonad___lam__2___boxed), 2, 0);
x_16 = lean_alloc_closure((void*)(l_Id_instMonad___lam__3), 4, 0);
x_17 = lean_alloc_closure((void*)(l_Id_instMonad___lam__4___boxed), 4, 0);
x_18 = lean_alloc_closure((void*)(l_Id_instMonad___lam__5___boxed), 4, 0);
x_19 = lean_alloc_closure((void*)(l_Id_instMonad___lam__6), 4, 0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_13);
lean_ctor_set(x_20, 1, x_14);
x_21 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_15);
lean_ctor_set(x_21, 2, x_16);
lean_ctor_set(x_21, 3, x_17);
lean_ctor_set(x_21, 4, x_18);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_19);
x_23 = lean_ctor_get(x_3, 1);
lean_inc(x_23);
lean_dec(x_3);
x_24 = lean_array_get_size(x_23);
x_25 = lean_unsigned_to_nat(0u);
x_26 = lean_nat_dec_lt(x_25, x_24);
if (x_26 == 0)
{
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_2);
x_7 = x_12;
goto block_11;
}
else
{
lean_object* x_27; size_t x_28; size_t x_29; lean_object* x_30; 
lean_inc(x_22);
x_27 = lean_alloc_closure((void*)(l_Std_HashSet_toList___redArg___lam__1), 4, 2);
lean_closure_set(x_27, 0, x_22);
lean_closure_set(x_27, 1, x_2);
x_28 = lean_usize_of_nat(x_24);
lean_dec(x_24);
x_29 = lean_usize_of_nat(x_25);
x_30 = l_Array_foldrMUnsafe_fold___redArg(x_22, x_27, x_23, x_28, x_29, x_12);
x_7 = x_30;
goto block_11;
}
block_11:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_List_repr___redArg(x_1, x_7);
x_9 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Repr_addAppParen(x_9, x_4);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instRepr___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_alloc_closure((void*)(l_Std_HashSet_toList___redArg___lam__0___boxed), 3, 0);
x_3 = lean_alloc_closure((void*)(l_Std_HashSet_instRepr___redArg___lam__2___boxed), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instRepr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_HashSet_instRepr___redArg(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instRepr___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_HashSet_instRepr___redArg___lam__2(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instRepr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_HashSet_instRepr(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* initialize_Std_Data_HashMap_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_HashSet_Basic(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_HashMap_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_HashSet_term___x7em__ = _init_l_Std_HashSet_term___x7em__();
lean_mark_persistent(l_Std_HashSet_term___x7em__);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
