// Lean compiler output
// Module: Std.Sat.AIG.Basic
// Imports: Std.Data.HashSet Init.Data.Vector.Basic
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
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instInhabitedFanin;
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_hashFanin____x40_Std_Sat_AIG_Basic___hyg_36____boxed(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Ref_cast(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Fanin_gate(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Ref_flip___redArg(lean_object*, uint8_t);
uint8_t l_Lean_Syntax_matchesIdent(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_denote___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_hashDecl____x40_Std_Sat_AIG_Basic___hyg_533____boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_reprDecl____x40_Std_Sat_AIG_Basic___hyg_620____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_BinaryInput_cast(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_TernaryInput_cast___redArg___boxed(lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_unexpandDenote___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGate___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_BinaryInput_cast___redArg___boxed(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Ref_not___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_get_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_noUpdate___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Ref_flip___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instMembership___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_BinaryInput_invert___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_decEqFanin____x40_Std_Sat_AIG_Basic___hyg_134_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_decEqDecl___redArg____x40_Std_Sat_AIG_Basic___hyg_793____boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instDecidableEqDecl___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_reprFanin____x40_Std_Sat_AIG_Basic___hyg_82____boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_decEqDecl___redArg____x40_Std_Sat_AIG_Basic___hyg_793_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_isConstant___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_get_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Bool_toNat(uint8_t);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Fanin_mk(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_reprFanin____x40_Std_Sat_AIG_Basic___hyg_82_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instHashableDecl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instDecidableEqDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_AssocList_contains(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_getConstant___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instInhabitedDecl(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Fanin_flip(lean_object*, uint8_t);
LEAN_EXPORT uint8_t l_Std_Sat_AIG_instDecidableEqDecl(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_AIG_Cache_insert___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_AIG_Fanin_invert(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_TernaryInput_cast___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_getConstant___redArg(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_replace___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_unexpandDenote(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_BinaryInput_cast___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Ref_cast___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instReprDecl___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_hashDecl____x40_Std_Sat_AIG_Basic___hyg_533_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_AIG_isConstant(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_getConstant___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instDecidableEqFanin___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_denote_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_BinaryInput_invert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT uint64_t l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_hashDecl___redArg____x40_Std_Sat_AIG_Basic___hyg_533_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_noUpdate___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_noUpdate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGate___redArg___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_noUpdate___redArg(lean_object*);
LEAN_EXPORT uint64_t l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_hashFanin____x40_Std_Sat_AIG_Basic___hyg_36_(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_decEqFanin____x40_Std_Sat_AIG_Basic___hyg_134____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Ref_cast___redArg___boxed(lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_empty___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_term_u27e6___x2c___u27e7;
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Ref_not___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_insert___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkAtom___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_get_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_insert___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkConst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_isConstant___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_reprFanin___redArg____x40_Std_Sat_AIG_Basic___hyg_82_(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_land(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_getConstant(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instHashableFin(lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Fanin_gate___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_AIG_denote___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_AIG_isConstant___redArg(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT uint8_t l_Std_Sat_AIG_denote_go___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Ref_not(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Ref_not___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_term_u27e6___x2c___x2c___u27e7;
LEAN_EXPORT lean_object* l_Std_Sat_AIG_empty(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Ref_flip(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_empty(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_reprDecl____x40_Std_Sat_AIG_Basic___hyg_620_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Fanin_mk___boxed(lean_object*, lean_object*);
lean_object* lean_nat_lxor(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Fanin_invert___boxed(lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_BinaryInput_invert___redArg(lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_invEdgeStyle___boxed(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGate___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_insert___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_reprDecl___redArg____x40_Std_Sat_AIG_Basic___hyg_620_(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_AIG_denote_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Ref_flip___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Ref_cast___redArg(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_decEqDecl____x40_Std_Sat_AIG_Basic___hyg_793_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkAtom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_decEqDecl____x40_Std_Sat_AIG_Basic___hyg_793____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkConst(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_denote_go___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_empty___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_insert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_TernaryInput_cast(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Fanin_flip___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_BinaryInput_invert___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_BinaryInput_cast___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instReprFanin;
lean_object* l_instDecidableEqFin___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_denote___redArg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_AIG_instDecidableEqDecl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_AIG_instDecidableEqFanin(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkConst___redArg(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_TernaryInput_cast___redArg(lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_AIG_denote(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instHashableFanin;
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instReprDecl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_reprDecl___redArg____x40_Std_Sat_AIG_Basic___hyg_620____boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_String_toSubstring_x27(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkAtom___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instMembership(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instHashableDecl___redArg(lean_object*);
lean_object* lean_nat_lor(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_hashDecl___redArg____x40_Std_Sat_AIG_Basic___hyg_533____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_invEdgeStyle(uint8_t);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkConst___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_hashFanin____x40_Std_Sat_AIG_Basic___hyg_36_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint64_t x_3; uint64_t x_4; uint64_t x_5; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_uint64_of_nat(x_2);
x_4 = lean_uint64_of_nat(x_1);
x_5 = lean_uint64_mix_hash(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_hashFanin____x40_Std_Sat_AIG_Basic___hyg_36____boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_hashFanin____x40_Std_Sat_AIG_Basic___hyg_36_(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
static lean_object* _init_l_Std_Sat_AIG_instHashableFanin() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_hashFanin____x40_Std_Sat_AIG_Basic___hyg_36____boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_reprFanin___redArg____x40_Std_Sat_AIG_Basic___hyg_82_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_2 = lean_mk_string_unchecked("{ ", 2, 2);
x_3 = lean_box(0);
x_4 = lean_mk_string_unchecked("val", 3, 3);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_mk_string_unchecked(" := ", 4, 4);
x_8 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(7u);
x_11 = lean_nat_to_int(x_10);
x_12 = l___private_Init_Data_Repr_0__Nat_reprFast(x_1);
x_13 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_16, 0, x_14);
x_17 = lean_unbox(x_15);
lean_ctor_set_uint8(x_16, sizeof(void*)*1, x_17);
x_18 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_18, 0, x_9);
lean_ctor_set(x_18, 1, x_16);
x_19 = lean_mk_string_unchecked(" }", 2, 2);
x_20 = lean_unsigned_to_nat(2u);
x_21 = lean_nat_to_int(x_20);
x_22 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_22, 0, x_2);
x_23 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_18);
x_24 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_24, 0, x_19);
x_25 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_26, 0, x_21);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_unbox(x_15);
lean_ctor_set_uint8(x_27, sizeof(void*)*1, x_28);
return x_27;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_reprFanin____x40_Std_Sat_AIG_Basic___hyg_82_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_reprFanin___redArg____x40_Std_Sat_AIG_Basic___hyg_82_(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_reprFanin____x40_Std_Sat_AIG_Basic___hyg_82____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_reprFanin____x40_Std_Sat_AIG_Basic___hyg_82_(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Std_Sat_AIG_instReprFanin() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_reprFanin____x40_Std_Sat_AIG_Basic___hyg_82____boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_decEqFanin____x40_Std_Sat_AIG_Basic___hyg_134_(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_nat_dec_eq(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_decEqFanin____x40_Std_Sat_AIG_Basic___hyg_134____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_decEqFanin____x40_Std_Sat_AIG_Basic___hyg_134_(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_AIG_instDecidableEqFanin(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_nat_dec_eq(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instDecidableEqFanin___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_Sat_AIG_instDecidableEqFanin(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Std_Sat_AIG_instInhabitedFanin() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Fanin_mk(lean_object* x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_shiftl(x_1, x_3);
x_5 = l_Bool_toNat(x_2);
x_6 = lean_nat_lor(x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Fanin_mk___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
lean_dec(x_2);
x_4 = l_Std_Sat_AIG_Fanin_mk(x_1, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Fanin_gate(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_shiftr(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Fanin_gate___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Sat_AIG_Fanin_gate(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_AIG_Fanin_invert(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_land(x_2, x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
lean_dec(x_3);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_box(1);
x_7 = lean_unbox(x_6);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_box(0);
x_9 = lean_unbox(x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Fanin_invert___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Std_Sat_AIG_Fanin_invert(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Fanin_flip(lean_object* x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Bool_toNat(x_2);
x_4 = lean_nat_lxor(x_1, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Fanin_flip___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
lean_dec(x_2);
x_4 = l_Std_Sat_AIG_Fanin_flip(x_1, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT uint64_t l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_hashDecl___redArg____x40_Std_Sat_AIG_Basic___hyg_533_(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_3; uint64_t x_4; 
lean_dec(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_uint64_of_nat(x_3);
return x_4;
}
case 1:
{
lean_object* x_5; lean_object* x_6; uint64_t x_7; lean_object* x_8; uint64_t x_9; uint64_t x_10; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_uint64_of_nat(x_6);
x_8 = lean_apply_1(x_1, x_5);
x_9 = lean_unbox_uint64(x_8);
lean_dec(x_8);
x_10 = lean_uint64_mix_hash(x_7, x_9);
return x_10;
}
default: 
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; uint64_t x_18; 
lean_dec(x_1);
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_dec(x_2);
x_13 = lean_unsigned_to_nat(2u);
x_14 = lean_uint64_of_nat(x_13);
x_15 = l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_hashFanin____x40_Std_Sat_AIG_Basic___hyg_36_(x_11);
lean_dec(x_11);
x_16 = lean_uint64_mix_hash(x_14, x_15);
x_17 = l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_hashFanin____x40_Std_Sat_AIG_Basic___hyg_36_(x_12);
lean_dec(x_12);
x_18 = lean_uint64_mix_hash(x_16, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT uint64_t l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_hashDecl____x40_Std_Sat_AIG_Basic___hyg_533_(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; 
x_4 = l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_hashDecl___redArg____x40_Std_Sat_AIG_Basic___hyg_533_(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_hashDecl___redArg____x40_Std_Sat_AIG_Basic___hyg_533____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; lean_object* x_4; 
x_3 = l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_hashDecl___redArg____x40_Std_Sat_AIG_Basic___hyg_533_(x_1, x_2);
x_4 = lean_box_uint64(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_hashDecl____x40_Std_Sat_AIG_Basic___hyg_533____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; lean_object* x_5; 
x_4 = l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_hashDecl____x40_Std_Sat_AIG_Basic___hyg_533_(x_1, x_2, x_3);
x_5 = lean_box_uint64(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instHashableDecl___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_hashDecl____x40_Std_Sat_AIG_Basic___hyg_533____boxed), 3, 2);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instHashableDecl(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_hashDecl____x40_Std_Sat_AIG_Basic___hyg_533____boxed), 3, 2);
lean_closure_set(x_3, 0, lean_box(0));
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_reprDecl___redArg____x40_Std_Sat_AIG_Basic___hyg_620_(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_13; uint8_t x_14; 
lean_dec(x_1);
x_13 = lean_unsigned_to_nat(1024u);
x_14 = lean_nat_dec_le(x_13, x_3);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_unsigned_to_nat(2u);
x_16 = lean_nat_to_int(x_15);
x_4 = x_16;
goto block_12;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_to_int(x_17);
x_4 = x_18;
goto block_12;
}
}
case 1:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_35; uint8_t x_36; 
x_19 = lean_ctor_get(x_2, 0);
lean_inc(x_19);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 x_20 = x_2;
} else {
 lean_dec_ref(x_2);
 x_20 = lean_box(0);
}
x_35 = lean_unsigned_to_nat(1024u);
x_36 = lean_nat_dec_le(x_35, x_3);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_unsigned_to_nat(2u);
x_38 = lean_nat_to_int(x_37);
x_21 = x_38;
goto block_34;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_nat_to_int(x_39);
x_21 = x_40;
goto block_34;
}
block_34:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_22 = lean_mk_string_unchecked("Std.Sat.AIG.Decl.atom", 21, 21);
if (lean_is_scalar(x_20)) {
 x_23 = lean_alloc_ctor(3, 1, 0);
} else {
 x_23 = x_20;
 lean_ctor_set_tag(x_23, 3);
}
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_box(1);
x_25 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_unsigned_to_nat(1024u);
x_27 = lean_apply_2(x_1, x_19, x_26);
x_28 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_29, 0, x_21);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_31, 0, x_29);
x_32 = lean_unbox(x_30);
lean_ctor_set_uint8(x_31, sizeof(void*)*1, x_32);
x_33 = l_Repr_addAppParen(x_31, x_3);
return x_33;
}
}
default: 
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_60; uint8_t x_61; 
lean_dec(x_1);
x_41 = lean_ctor_get(x_2, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_2, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_43 = x_2;
} else {
 lean_dec_ref(x_2);
 x_43 = lean_box(0);
}
x_60 = lean_unsigned_to_nat(1024u);
x_61 = lean_nat_dec_le(x_60, x_3);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_unsigned_to_nat(2u);
x_63 = lean_nat_to_int(x_62);
x_44 = x_63;
goto block_59;
}
else
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_unsigned_to_nat(1u);
x_65 = lean_nat_to_int(x_64);
x_44 = x_65;
goto block_59;
}
block_59:
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; 
x_45 = lean_mk_string_unchecked("Std.Sat.AIG.Decl.gate", 21, 21);
x_46 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_46, 0, x_45);
x_47 = lean_box(1);
if (lean_is_scalar(x_43)) {
 x_48 = lean_alloc_ctor(5, 2, 0);
} else {
 x_48 = x_43;
 lean_ctor_set_tag(x_48, 5);
}
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
x_49 = l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_reprFanin___redArg____x40_Std_Sat_AIG_Basic___hyg_82_(x_41);
x_50 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_47);
x_52 = l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_reprFanin___redArg____x40_Std_Sat_AIG_Basic___hyg_82_(x_42);
x_53 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_54, 0, x_44);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_box(0);
x_56 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_56, 0, x_54);
x_57 = lean_unbox(x_55);
lean_ctor_set_uint8(x_56, sizeof(void*)*1, x_57);
x_58 = l_Repr_addAppParen(x_56, x_3);
return x_58;
}
}
}
block_12:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_5 = lean_mk_string_unchecked("Std.Sat.AIG.Decl.false", 22, 22);
x_6 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_9, 0, x_7);
x_10 = lean_unbox(x_8);
lean_ctor_set_uint8(x_9, sizeof(void*)*1, x_10);
x_11 = l_Repr_addAppParen(x_9, x_3);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_reprDecl____x40_Std_Sat_AIG_Basic___hyg_620_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_reprDecl___redArg____x40_Std_Sat_AIG_Basic___hyg_620_(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_reprDecl___redArg____x40_Std_Sat_AIG_Basic___hyg_620____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_reprDecl___redArg____x40_Std_Sat_AIG_Basic___hyg_620_(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_reprDecl____x40_Std_Sat_AIG_Basic___hyg_620____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_reprDecl____x40_Std_Sat_AIG_Basic___hyg_620_(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instReprDecl___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_reprDecl____x40_Std_Sat_AIG_Basic___hyg_620____boxed), 4, 2);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instReprDecl(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_reprDecl____x40_Std_Sat_AIG_Basic___hyg_620____boxed), 4, 2);
lean_closure_set(x_3, 0, lean_box(0));
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_decEqDecl___redArg____x40_Std_Sat_AIG_Basic___hyg_793_(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(1);
x_5 = lean_box(0);
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_dec(x_1);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_6; 
x_6 = lean_unbox(x_4);
return x_6;
}
else
{
uint8_t x_7; 
lean_dec(x_3);
x_7 = lean_unbox(x_5);
return x_7;
}
}
case 1:
{
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
lean_dec(x_3);
x_10 = lean_apply_2(x_1, x_8, x_9);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = lean_unbox(x_5);
return x_12;
}
else
{
uint8_t x_13; 
x_13 = lean_unbox(x_4);
return x_13;
}
}
else
{
uint8_t x_14; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_unbox(x_5);
return x_14;
}
}
default: 
{
lean_dec(x_1);
if (lean_obj_tag(x_3) == 2)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_15 = lean_ctor_get(x_2, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_2, 1);
lean_inc(x_16);
lean_dec(x_2);
x_17 = lean_ctor_get(x_3, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_3, 1);
lean_inc(x_18);
lean_dec(x_3);
x_19 = lean_nat_dec_eq(x_15, x_17);
lean_dec(x_17);
lean_dec(x_15);
if (x_19 == 0)
{
uint8_t x_20; 
lean_dec(x_18);
lean_dec(x_16);
x_20 = lean_unbox(x_5);
return x_20;
}
else
{
uint8_t x_21; 
x_21 = lean_nat_dec_eq(x_16, x_18);
lean_dec(x_18);
lean_dec(x_16);
if (x_21 == 0)
{
uint8_t x_22; 
x_22 = lean_unbox(x_5);
return x_22;
}
else
{
uint8_t x_23; 
x_23 = lean_unbox(x_4);
return x_23;
}
}
}
else
{
uint8_t x_24; 
lean_dec(x_3);
lean_dec(x_2);
x_24 = lean_unbox(x_5);
return x_24;
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_decEqDecl____x40_Std_Sat_AIG_Basic___hyg_793_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_decEqDecl___redArg____x40_Std_Sat_AIG_Basic___hyg_793_(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_decEqDecl___redArg____x40_Std_Sat_AIG_Basic___hyg_793____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_decEqDecl___redArg____x40_Std_Sat_AIG_Basic___hyg_793_(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_decEqDecl____x40_Std_Sat_AIG_Basic___hyg_793____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_decEqDecl____x40_Std_Sat_AIG_Basic___hyg_793_(x_1, x_2, x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_AIG_instDecidableEqDecl___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_decEqDecl___redArg____x40_Std_Sat_AIG_Basic___hyg_793_(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_AIG_instDecidableEqDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_decEqDecl___redArg____x40_Std_Sat_AIG_Basic___hyg_793_(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instDecidableEqDecl___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_Sat_AIG_instDecidableEqDecl___redArg(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instDecidableEqDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Std_Sat_AIG_instDecidableEqDecl(x_1, x_2, x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instInhabitedDecl(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_empty(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
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
return x_14;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_empty___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Sat_AIG_Cache_empty(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_noUpdate___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_noUpdate(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_inc(x_6);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_noUpdate___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Sat_AIG_Cache_noUpdate___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_noUpdate___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_Sat_AIG_Cache_noUpdate(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_AIG_Cache_insert___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_decEqDecl___redArg____x40_Std_Sat_AIG_Basic___hyg_793_(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_insert___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint64_t x_13; lean_object* x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; lean_object* x_18; uint64_t x_19; uint64_t x_20; uint64_t x_21; size_t x_22; size_t x_23; lean_object* x_24; size_t x_25; size_t x_26; size_t x_27; lean_object* x_28; uint8_t x_29; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_ctor_get(x_4, 1);
x_9 = lean_alloc_closure((void*)(l_Std_Sat_AIG_Cache_insert___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_9, 0, x_2);
x_10 = l_instBEqOfDecidableEq___redArg(x_9);
x_11 = lean_array_get_size(x_3);
x_12 = lean_array_get_size(x_8);
lean_inc(x_5);
lean_inc(x_1);
x_13 = l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_hashDecl___redArg____x40_Std_Sat_AIG_Basic___hyg_533_(x_1, x_5);
x_14 = lean_unsigned_to_nat(32u);
x_15 = lean_uint64_of_nat(x_14);
x_16 = lean_uint64_shift_right(x_13, x_15);
x_17 = lean_uint64_xor(x_13, x_16);
x_18 = lean_unsigned_to_nat(16u);
x_19 = lean_uint64_of_nat(x_18);
x_20 = lean_uint64_shift_right(x_17, x_19);
x_21 = lean_uint64_xor(x_17, x_20);
x_22 = lean_uint64_to_usize(x_21);
x_23 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_usize_of_nat(x_24);
x_26 = lean_usize_sub(x_23, x_25);
x_27 = lean_usize_land(x_22, x_26);
x_28 = lean_array_uget(x_8, x_27);
lean_inc(x_28);
lean_inc(x_5);
lean_inc(x_10);
x_29 = l_Std_DHashMap_Internal_AssocList_contains(lean_box(0), lean_box(0), x_10, x_5, x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
lean_dec(x_10);
x_30 = lean_nat_add(x_7, x_24);
lean_dec(x_7);
x_31 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_31, 0, x_5);
lean_ctor_set(x_31, 1, x_11);
lean_ctor_set(x_31, 2, x_28);
x_32 = lean_array_uset(x_8, x_27, x_31);
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
x_39 = lean_alloc_closure((void*)(l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_hashDecl____x40_Std_Sat_AIG_Basic___hyg_533____boxed), 3, 2);
lean_closure_set(x_39, 0, lean_box(0));
lean_closure_set(x_39, 1, x_1);
x_40 = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(x_39, x_32);
lean_ctor_set(x_4, 1, x_40);
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
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_1);
x_41 = lean_box(0);
x_42 = lean_array_uset(x_8, x_27, x_41);
x_43 = l_Std_DHashMap_Internal_AssocList_replace___redArg(x_10, x_5, x_11, x_28);
x_44 = lean_array_uset(x_42, x_27, x_43);
lean_ctor_set(x_4, 1, x_44);
return x_4;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint64_t x_51; lean_object* x_52; uint64_t x_53; uint64_t x_54; uint64_t x_55; lean_object* x_56; uint64_t x_57; uint64_t x_58; uint64_t x_59; size_t x_60; size_t x_61; lean_object* x_62; size_t x_63; size_t x_64; size_t x_65; lean_object* x_66; uint8_t x_67; 
x_45 = lean_ctor_get(x_4, 0);
x_46 = lean_ctor_get(x_4, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_4);
x_47 = lean_alloc_closure((void*)(l_Std_Sat_AIG_Cache_insert___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_47, 0, x_2);
x_48 = l_instBEqOfDecidableEq___redArg(x_47);
x_49 = lean_array_get_size(x_3);
x_50 = lean_array_get_size(x_46);
lean_inc(x_5);
lean_inc(x_1);
x_51 = l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_hashDecl___redArg____x40_Std_Sat_AIG_Basic___hyg_533_(x_1, x_5);
x_52 = lean_unsigned_to_nat(32u);
x_53 = lean_uint64_of_nat(x_52);
x_54 = lean_uint64_shift_right(x_51, x_53);
x_55 = lean_uint64_xor(x_51, x_54);
x_56 = lean_unsigned_to_nat(16u);
x_57 = lean_uint64_of_nat(x_56);
x_58 = lean_uint64_shift_right(x_55, x_57);
x_59 = lean_uint64_xor(x_55, x_58);
x_60 = lean_uint64_to_usize(x_59);
x_61 = lean_usize_of_nat(x_50);
lean_dec(x_50);
x_62 = lean_unsigned_to_nat(1u);
x_63 = lean_usize_of_nat(x_62);
x_64 = lean_usize_sub(x_61, x_63);
x_65 = lean_usize_land(x_60, x_64);
x_66 = lean_array_uget(x_46, x_65);
lean_inc(x_66);
lean_inc(x_5);
lean_inc(x_48);
x_67 = l_Std_DHashMap_Internal_AssocList_contains(lean_box(0), lean_box(0), x_48, x_5, x_66);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
lean_dec(x_48);
x_68 = lean_nat_add(x_45, x_62);
lean_dec(x_45);
x_69 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_69, 0, x_5);
lean_ctor_set(x_69, 1, x_49);
lean_ctor_set(x_69, 2, x_66);
x_70 = lean_array_uset(x_46, x_65, x_69);
x_71 = lean_unsigned_to_nat(2u);
x_72 = lean_nat_shiftl(x_68, x_71);
x_73 = lean_unsigned_to_nat(3u);
x_74 = lean_nat_div(x_72, x_73);
lean_dec(x_72);
x_75 = lean_array_get_size(x_70);
x_76 = lean_nat_dec_le(x_74, x_75);
lean_dec(x_75);
lean_dec(x_74);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_alloc_closure((void*)(l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_hashDecl____x40_Std_Sat_AIG_Basic___hyg_533____boxed), 3, 2);
lean_closure_set(x_77, 0, lean_box(0));
lean_closure_set(x_77, 1, x_1);
x_78 = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(x_77, x_70);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_68);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
else
{
lean_object* x_80; 
lean_dec(x_1);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_68);
lean_ctor_set(x_80, 1, x_70);
return x_80;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_1);
x_81 = lean_box(0);
x_82 = lean_array_uset(x_46, x_65, x_81);
x_83 = l_Std_DHashMap_Internal_AssocList_replace___redArg(x_48, x_5, x_49, x_66);
x_84 = lean_array_uset(x_82, x_65, x_83);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_45);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_insert(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint64_t x_14; lean_object* x_15; uint64_t x_16; uint64_t x_17; uint64_t x_18; lean_object* x_19; uint64_t x_20; uint64_t x_21; uint64_t x_22; size_t x_23; size_t x_24; lean_object* x_25; size_t x_26; size_t x_27; size_t x_28; lean_object* x_29; uint8_t x_30; 
x_8 = lean_ctor_get(x_5, 0);
x_9 = lean_ctor_get(x_5, 1);
x_10 = lean_alloc_closure((void*)(l_Std_Sat_AIG_Cache_insert___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_10, 0, x_3);
x_11 = l_instBEqOfDecidableEq___redArg(x_10);
x_12 = lean_array_get_size(x_4);
x_13 = lean_array_get_size(x_9);
lean_inc(x_6);
lean_inc(x_2);
x_14 = l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_hashDecl___redArg____x40_Std_Sat_AIG_Basic___hyg_533_(x_2, x_6);
x_15 = lean_unsigned_to_nat(32u);
x_16 = lean_uint64_of_nat(x_15);
x_17 = lean_uint64_shift_right(x_14, x_16);
x_18 = lean_uint64_xor(x_14, x_17);
x_19 = lean_unsigned_to_nat(16u);
x_20 = lean_uint64_of_nat(x_19);
x_21 = lean_uint64_shift_right(x_18, x_20);
x_22 = lean_uint64_xor(x_18, x_21);
x_23 = lean_uint64_to_usize(x_22);
x_24 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_usize_of_nat(x_25);
x_27 = lean_usize_sub(x_24, x_26);
x_28 = lean_usize_land(x_23, x_27);
x_29 = lean_array_uget(x_9, x_28);
lean_inc(x_29);
lean_inc(x_6);
lean_inc(x_11);
x_30 = l_Std_DHashMap_Internal_AssocList_contains(lean_box(0), lean_box(0), x_11, x_6, x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
lean_dec(x_11);
x_31 = lean_nat_add(x_8, x_25);
lean_dec(x_8);
x_32 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_32, 0, x_6);
lean_ctor_set(x_32, 1, x_12);
lean_ctor_set(x_32, 2, x_29);
x_33 = lean_array_uset(x_9, x_28, x_32);
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
x_40 = lean_alloc_closure((void*)(l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_hashDecl____x40_Std_Sat_AIG_Basic___hyg_533____boxed), 3, 2);
lean_closure_set(x_40, 0, lean_box(0));
lean_closure_set(x_40, 1, x_2);
x_41 = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(x_40, x_33);
lean_ctor_set(x_5, 1, x_41);
lean_ctor_set(x_5, 0, x_31);
return x_5;
}
else
{
lean_dec(x_2);
lean_ctor_set(x_5, 1, x_33);
lean_ctor_set(x_5, 0, x_31);
return x_5;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_2);
x_42 = lean_box(0);
x_43 = lean_array_uset(x_9, x_28, x_42);
x_44 = l_Std_DHashMap_Internal_AssocList_replace___redArg(x_11, x_6, x_12, x_29);
x_45 = lean_array_uset(x_43, x_28, x_44);
lean_ctor_set(x_5, 1, x_45);
return x_5;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint64_t x_52; lean_object* x_53; uint64_t x_54; uint64_t x_55; uint64_t x_56; lean_object* x_57; uint64_t x_58; uint64_t x_59; uint64_t x_60; size_t x_61; size_t x_62; lean_object* x_63; size_t x_64; size_t x_65; size_t x_66; lean_object* x_67; uint8_t x_68; 
x_46 = lean_ctor_get(x_5, 0);
x_47 = lean_ctor_get(x_5, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_5);
x_48 = lean_alloc_closure((void*)(l_Std_Sat_AIG_Cache_insert___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_48, 0, x_3);
x_49 = l_instBEqOfDecidableEq___redArg(x_48);
x_50 = lean_array_get_size(x_4);
x_51 = lean_array_get_size(x_47);
lean_inc(x_6);
lean_inc(x_2);
x_52 = l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_hashDecl___redArg____x40_Std_Sat_AIG_Basic___hyg_533_(x_2, x_6);
x_53 = lean_unsigned_to_nat(32u);
x_54 = lean_uint64_of_nat(x_53);
x_55 = lean_uint64_shift_right(x_52, x_54);
x_56 = lean_uint64_xor(x_52, x_55);
x_57 = lean_unsigned_to_nat(16u);
x_58 = lean_uint64_of_nat(x_57);
x_59 = lean_uint64_shift_right(x_56, x_58);
x_60 = lean_uint64_xor(x_56, x_59);
x_61 = lean_uint64_to_usize(x_60);
x_62 = lean_usize_of_nat(x_51);
lean_dec(x_51);
x_63 = lean_unsigned_to_nat(1u);
x_64 = lean_usize_of_nat(x_63);
x_65 = lean_usize_sub(x_62, x_64);
x_66 = lean_usize_land(x_61, x_65);
x_67 = lean_array_uget(x_47, x_66);
lean_inc(x_67);
lean_inc(x_6);
lean_inc(x_49);
x_68 = l_Std_DHashMap_Internal_AssocList_contains(lean_box(0), lean_box(0), x_49, x_6, x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
lean_dec(x_49);
x_69 = lean_nat_add(x_46, x_63);
lean_dec(x_46);
x_70 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_70, 0, x_6);
lean_ctor_set(x_70, 1, x_50);
lean_ctor_set(x_70, 2, x_67);
x_71 = lean_array_uset(x_47, x_66, x_70);
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
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_alloc_closure((void*)(l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_hashDecl____x40_Std_Sat_AIG_Basic___hyg_533____boxed), 3, 2);
lean_closure_set(x_78, 0, lean_box(0));
lean_closure_set(x_78, 1, x_2);
x_79 = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(x_78, x_71);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_69);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
else
{
lean_object* x_81; 
lean_dec(x_2);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_69);
lean_ctor_set(x_81, 1, x_71);
return x_81;
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_2);
x_82 = lean_box(0);
x_83 = lean_array_uset(x_47, x_66, x_82);
x_84 = l_Std_DHashMap_Internal_AssocList_replace___redArg(x_49, x_6, x_50, x_67);
x_85 = lean_array_uset(x_83, x_66, x_84);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_46);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_insert___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_Sat_AIG_Cache_insert___redArg___lam__0(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_insert___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Sat_AIG_Cache_insert___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_insert___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_Sat_AIG_Cache_insert(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_get_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint64_t x_9; lean_object* x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; lean_object* x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; size_t x_18; size_t x_19; lean_object* x_20; size_t x_21; size_t x_22; size_t x_23; lean_object* x_24; lean_object* x_25; 
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_alloc_closure((void*)(l_Std_Sat_AIG_Cache_insert___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_6, 0, x_2);
x_7 = l_instBEqOfDecidableEq___redArg(x_6);
x_8 = lean_array_get_size(x_5);
lean_inc(x_4);
x_9 = l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_hashDecl___redArg____x40_Std_Sat_AIG_Basic___hyg_533_(x_1, x_4);
x_10 = lean_unsigned_to_nat(32u);
x_11 = lean_uint64_of_nat(x_10);
x_12 = lean_uint64_shift_right(x_9, x_11);
x_13 = lean_uint64_xor(x_9, x_12);
x_14 = lean_unsigned_to_nat(16u);
x_15 = lean_uint64_of_nat(x_14);
x_16 = lean_uint64_shift_right(x_13, x_15);
x_17 = lean_uint64_xor(x_13, x_16);
x_18 = lean_uint64_to_usize(x_17);
x_19 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_usize_of_nat(x_20);
x_22 = lean_usize_sub(x_19, x_21);
x_23 = lean_usize_land(x_18, x_22);
x_24 = lean_array_uget(x_5, x_23);
x_25 = l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(x_7, x_4, x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
x_26 = lean_box(0);
return x_26;
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_25);
if (x_27 == 0)
{
return x_25;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_25, 0);
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_get_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint64_t x_11; lean_object* x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; lean_object* x_16; uint64_t x_17; uint64_t x_18; uint64_t x_19; size_t x_20; size_t x_21; lean_object* x_22; size_t x_23; size_t x_24; size_t x_25; lean_object* x_26; lean_object* x_27; 
x_7 = lean_ctor_get(x_5, 1);
x_8 = lean_alloc_closure((void*)(l_Std_Sat_AIG_Cache_insert___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_8, 0, x_3);
x_9 = l_instBEqOfDecidableEq___redArg(x_8);
x_10 = lean_array_get_size(x_7);
lean_inc(x_6);
x_11 = l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_hashDecl___redArg____x40_Std_Sat_AIG_Basic___hyg_533_(x_2, x_6);
x_12 = lean_unsigned_to_nat(32u);
x_13 = lean_uint64_of_nat(x_12);
x_14 = lean_uint64_shift_right(x_11, x_13);
x_15 = lean_uint64_xor(x_11, x_14);
x_16 = lean_unsigned_to_nat(16u);
x_17 = lean_uint64_of_nat(x_16);
x_18 = lean_uint64_shift_right(x_15, x_17);
x_19 = lean_uint64_xor(x_15, x_18);
x_20 = lean_uint64_to_usize(x_19);
x_21 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_usize_of_nat(x_22);
x_24 = lean_usize_sub(x_21, x_23);
x_25 = lean_usize_land(x_20, x_24);
x_26 = lean_array_uget(x_7, x_25);
x_27 = l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(x_9, x_6, x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; 
x_28 = lean_box(0);
return x_28;
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_27);
if (x_29 == 0)
{
return x_27;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_27, 0);
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_get_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Sat_AIG_Cache_get_x3f___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_get_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_Sat_AIG_Cache_get_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_empty(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_4 = lean_box(0);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_mk_empty_array_with_capacity(x_5);
x_7 = lean_array_push(x_6, x_4);
x_8 = lean_unsigned_to_nat(8u);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_unsigned_to_nat(2u);
x_11 = lean_nat_shiftl(x_8, x_10);
x_12 = lean_unsigned_to_nat(3u);
x_13 = lean_nat_div(x_11, x_12);
lean_dec(x_11);
x_14 = l_Nat_nextPowerOfTwo(x_13);
lean_dec(x_13);
x_15 = lean_box(0);
x_16 = lean_mk_array(x_14, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_9);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_7);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_empty___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Sat_AIG_empty(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instMembership(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instMembership___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Sat_AIG_instMembership(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Ref_cast___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
lean_inc(x_2);
x_4 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Ref_cast(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get_uint8(x_6, sizeof(void*)*1);
lean_inc(x_8);
x_10 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set_uint8(x_10, sizeof(void*)*1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Ref_cast___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Sat_AIG_Ref_cast___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Ref_cast___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_Sat_AIG_Ref_cast(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Ref_flip___redArg(lean_object* x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 0);
if (x_2 == 0)
{
uint8_t x_12; 
x_12 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
if (x_12 == 0)
{
goto block_11;
}
else
{
goto block_7;
}
}
else
{
uint8_t x_13; 
x_13 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
if (x_13 == 0)
{
goto block_7;
}
else
{
goto block_11;
}
}
block_7:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_box(1);
lean_inc(x_3);
x_5 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_5, 0, x_3);
x_6 = lean_unbox(x_4);
lean_ctor_set_uint8(x_5, sizeof(void*)*1, x_6);
return x_5;
}
block_11:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_box(0);
lean_inc(x_3);
x_9 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_9, 0, x_3);
x_10 = lean_unbox(x_8);
lean_ctor_set_uint8(x_9, sizeof(void*)*1, x_10);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Ref_flip(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_5, 0);
if (x_6 == 0)
{
uint8_t x_16; 
x_16 = lean_ctor_get_uint8(x_5, sizeof(void*)*1);
if (x_16 == 0)
{
goto block_15;
}
else
{
goto block_11;
}
}
else
{
uint8_t x_17; 
x_17 = lean_ctor_get_uint8(x_5, sizeof(void*)*1);
if (x_17 == 0)
{
goto block_11;
}
else
{
goto block_15;
}
}
block_11:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_box(1);
lean_inc(x_7);
x_9 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_9, 0, x_7);
x_10 = lean_unbox(x_8);
lean_ctor_set_uint8(x_9, sizeof(void*)*1, x_10);
return x_9;
}
block_15:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_box(0);
lean_inc(x_7);
x_13 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_13, 0, x_7);
x_14 = lean_unbox(x_12);
lean_ctor_set_uint8(x_13, sizeof(void*)*1, x_14);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Ref_flip___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
lean_dec(x_2);
x_4 = l_Std_Sat_AIG_Ref_flip___redArg(x_1, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Ref_flip___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_6);
lean_dec(x_6);
x_8 = l_Std_Sat_AIG_Ref_flip(x_1, x_2, x_3, x_4, x_5, x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Ref_not___redArg(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_box(1);
lean_inc(x_3);
x_5 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_5, 0, x_3);
x_6 = lean_unbox(x_4);
lean_ctor_set_uint8(x_5, sizeof(void*)*1, x_6);
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_box(0);
lean_inc(x_7);
x_9 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_9, 0, x_7);
x_10 = lean_unbox(x_8);
lean_ctor_set_uint8(x_9, sizeof(void*)*1, x_10);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Ref_not(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_ctor_get_uint8(x_5, sizeof(void*)*1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_box(1);
lean_inc(x_7);
x_9 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_9, 0, x_7);
x_10 = lean_unbox(x_8);
lean_ctor_set_uint8(x_9, sizeof(void*)*1, x_10);
return x_9;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_5, 0);
x_12 = lean_box(0);
lean_inc(x_11);
x_13 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_13, 0, x_11);
x_14 = lean_unbox(x_12);
lean_ctor_set_uint8(x_13, sizeof(void*)*1, x_14);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Ref_not___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Sat_AIG_Ref_not___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Ref_not___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Sat_AIG_Ref_not(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_BinaryInput_cast___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
lean_inc(x_3);
x_5 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set_uint8(x_5, sizeof(void*)*1, x_4);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_6, 0);
x_8 = lean_ctor_get_uint8(x_6, sizeof(void*)*1);
lean_inc(x_7);
x_9 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set_uint8(x_9, sizeof(void*)*1, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_BinaryInput_cast(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_8, 0);
x_10 = lean_ctor_get_uint8(x_8, sizeof(void*)*1);
lean_inc(x_9);
x_11 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_10);
x_12 = lean_ctor_get(x_6, 1);
x_13 = lean_ctor_get(x_12, 0);
x_14 = lean_ctor_get_uint8(x_12, sizeof(void*)*1);
lean_inc(x_13);
x_15 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set_uint8(x_15, sizeof(void*)*1, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_BinaryInput_cast___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Sat_AIG_BinaryInput_cast___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_BinaryInput_cast___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_Sat_AIG_BinaryInput_cast(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_BinaryInput_invert___redArg(lean_object* x_1, uint8_t x_2, uint8_t x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_11; lean_object* x_12; lean_object* x_18; lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_1, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
if (x_2 == 0)
{
uint8_t x_38; 
x_38 = lean_ctor_get_uint8(x_28, sizeof(void*)*1);
lean_dec(x_28);
if (x_38 == 0)
{
goto block_37;
}
else
{
goto block_33;
}
}
else
{
uint8_t x_39; 
x_39 = lean_ctor_get_uint8(x_28, sizeof(void*)*1);
lean_dec(x_28);
if (x_39 == 0)
{
goto block_33;
}
else
{
goto block_37;
}
}
block_10:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_7, 0, x_4);
x_8 = lean_unbox(x_6);
lean_ctor_set_uint8(x_7, sizeof(void*)*1, x_8);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
block_17:
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_14, 0, x_11);
x_15 = lean_unbox(x_13);
lean_ctor_set_uint8(x_14, sizeof(void*)*1, x_15);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
block_27:
{
if (x_3 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_1, 1);
lean_inc(x_19);
lean_dec(x_1);
x_20 = lean_ctor_get_uint8(x_19, sizeof(void*)*1);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec(x_19);
x_11 = x_21;
x_12 = x_18;
goto block_17;
}
else
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_19, 0);
lean_inc(x_22);
lean_dec(x_19);
x_4 = x_22;
x_5 = x_18;
goto block_10;
}
}
else
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_1, 1);
lean_inc(x_23);
lean_dec(x_1);
x_24 = lean_ctor_get_uint8(x_23, sizeof(void*)*1);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
lean_dec(x_23);
x_4 = x_25;
x_5 = x_18;
goto block_10;
}
else
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_23, 0);
lean_inc(x_26);
lean_dec(x_23);
x_11 = x_26;
x_12 = x_18;
goto block_17;
}
}
}
block_33:
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = lean_box(1);
x_31 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_31, 0, x_29);
x_32 = lean_unbox(x_30);
lean_ctor_set_uint8(x_31, sizeof(void*)*1, x_32);
x_18 = x_31;
goto block_27;
}
block_37:
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_35, 0, x_29);
x_36 = lean_unbox(x_34);
lean_ctor_set_uint8(x_35, sizeof(void*)*1, x_36);
x_18 = x_35;
goto block_27;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_BinaryInput_invert(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, uint8_t x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_15; lean_object* x_16; lean_object* x_22; lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_5, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
if (x_6 == 0)
{
uint8_t x_42; 
x_42 = lean_ctor_get_uint8(x_32, sizeof(void*)*1);
lean_dec(x_32);
if (x_42 == 0)
{
goto block_41;
}
else
{
goto block_37;
}
}
else
{
uint8_t x_43; 
x_43 = lean_ctor_get_uint8(x_32, sizeof(void*)*1);
lean_dec(x_32);
if (x_43 == 0)
{
goto block_37;
}
else
{
goto block_41;
}
}
block_14:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_10 = lean_box(1);
x_11 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_11, 0, x_8);
x_12 = lean_unbox(x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_12);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
block_21:
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_18, 0, x_15);
x_19 = lean_unbox(x_17);
lean_ctor_set_uint8(x_18, sizeof(void*)*1, x_19);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_16);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
block_31:
{
if (x_7 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_5, 1);
lean_inc(x_23);
lean_dec(x_5);
x_24 = lean_ctor_get_uint8(x_23, sizeof(void*)*1);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
lean_dec(x_23);
x_15 = x_25;
x_16 = x_22;
goto block_21;
}
else
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_23, 0);
lean_inc(x_26);
lean_dec(x_23);
x_8 = x_26;
x_9 = x_22;
goto block_14;
}
}
else
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_5, 1);
lean_inc(x_27);
lean_dec(x_5);
x_28 = lean_ctor_get_uint8(x_27, sizeof(void*)*1);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
lean_dec(x_27);
x_8 = x_29;
x_9 = x_22;
goto block_14;
}
else
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_27, 0);
lean_inc(x_30);
lean_dec(x_27);
x_15 = x_30;
x_16 = x_22;
goto block_21;
}
}
}
block_37:
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_34 = lean_box(1);
x_35 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_35, 0, x_33);
x_36 = lean_unbox(x_34);
lean_ctor_set_uint8(x_35, sizeof(void*)*1, x_36);
x_22 = x_35;
goto block_31;
}
block_41:
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_39, 0, x_33);
x_40 = lean_unbox(x_38);
lean_ctor_set_uint8(x_39, sizeof(void*)*1, x_40);
x_22 = x_39;
goto block_31;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_BinaryInput_invert___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = lean_unbox(x_3);
lean_dec(x_3);
x_6 = l_Std_Sat_AIG_BinaryInput_invert___redArg(x_1, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_BinaryInput_invert___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_unbox(x_6);
lean_dec(x_6);
x_9 = lean_unbox(x_7);
lean_dec(x_7);
x_10 = l_Std_Sat_AIG_BinaryInput_invert(x_1, x_2, x_3, x_4, x_5, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_TernaryInput_cast___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
lean_inc(x_3);
x_5 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set_uint8(x_5, sizeof(void*)*1, x_4);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_6, 0);
x_8 = lean_ctor_get_uint8(x_6, sizeof(void*)*1);
lean_inc(x_7);
x_9 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set_uint8(x_9, sizeof(void*)*1, x_8);
x_10 = lean_ctor_get(x_1, 2);
x_11 = lean_ctor_get(x_10, 0);
x_12 = lean_ctor_get_uint8(x_10, sizeof(void*)*1);
lean_inc(x_11);
x_13 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set_uint8(x_13, sizeof(void*)*1, x_12);
x_14 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_14, 0, x_5);
lean_ctor_set(x_14, 1, x_9);
lean_ctor_set(x_14, 2, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_TernaryInput_cast(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_8, 0);
x_10 = lean_ctor_get_uint8(x_8, sizeof(void*)*1);
lean_inc(x_9);
x_11 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_10);
x_12 = lean_ctor_get(x_6, 1);
x_13 = lean_ctor_get(x_12, 0);
x_14 = lean_ctor_get_uint8(x_12, sizeof(void*)*1);
lean_inc(x_13);
x_15 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set_uint8(x_15, sizeof(void*)*1, x_14);
x_16 = lean_ctor_get(x_6, 2);
x_17 = lean_ctor_get(x_16, 0);
x_18 = lean_ctor_get_uint8(x_16, sizeof(void*)*1);
lean_inc(x_17);
x_19 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*1, x_18);
x_20 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_20, 0, x_11);
lean_ctor_set(x_20, 1, x_15);
lean_ctor_set(x_20, 2, x_19);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_TernaryInput_cast___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Sat_AIG_TernaryInput_cast___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_TernaryInput_cast___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_Sat_AIG_TernaryInput_cast(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_invEdgeStyle(uint8_t x_1) {
_start:
{
if (x_1 == 0)
{
lean_object* x_2; 
x_2 = lean_mk_string_unchecked(" [color=blue]", 13, 13);
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_mk_string_unchecked(" [color=red]", 12, 12);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_invEdgeStyle___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Std_Sat_AIG_toGraphviz_invEdgeStyle(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; uint8_t x_9; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint64_t x_39; lean_object* x_40; uint64_t x_41; uint64_t x_42; uint64_t x_43; lean_object* x_44; uint64_t x_45; uint64_t x_46; uint64_t x_47; size_t x_48; size_t x_49; lean_object* x_50; size_t x_51; size_t x_52; size_t x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_67; 
x_33 = lean_ctor_get(x_4, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_4, 1);
lean_inc(x_34);
x_35 = lean_array_get_size(x_2);
lean_inc(x_35);
x_36 = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(x_36, 0, x_35);
x_37 = l_instBEqOfDecidableEq___redArg(x_36);
x_38 = lean_array_get_size(x_34);
x_39 = lean_uint64_of_nat(x_3);
x_40 = lean_unsigned_to_nat(32u);
x_41 = lean_uint64_of_nat(x_40);
x_42 = lean_uint64_shift_right(x_39, x_41);
x_43 = lean_uint64_xor(x_39, x_42);
x_44 = lean_unsigned_to_nat(16u);
x_45 = lean_uint64_of_nat(x_44);
x_46 = lean_uint64_shift_right(x_43, x_45);
x_47 = lean_uint64_xor(x_43, x_46);
x_48 = lean_uint64_to_usize(x_47);
x_49 = lean_usize_of_nat(x_38);
lean_dec(x_38);
x_50 = lean_unsigned_to_nat(1u);
x_51 = lean_usize_of_nat(x_50);
x_52 = lean_usize_sub(x_49, x_51);
x_53 = lean_usize_land(x_48, x_52);
x_54 = lean_array_uget(x_34, x_53);
lean_inc(x_54);
lean_inc(x_3);
x_55 = l_Std_DHashMap_Internal_AssocList_contains(lean_box(0), lean_box(0), x_37, x_3, x_54);
if (x_55 == 0)
{
if (x_55 == 0)
{
uint8_t x_79; 
x_79 = !lean_is_exclusive(x_4);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_80 = lean_ctor_get(x_4, 1);
lean_dec(x_80);
x_81 = lean_ctor_get(x_4, 0);
lean_dec(x_81);
x_82 = lean_box(0);
x_83 = lean_nat_add(x_33, x_50);
lean_dec(x_33);
lean_inc(x_3);
x_84 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_84, 0, x_3);
lean_ctor_set(x_84, 1, x_82);
lean_ctor_set(x_84, 2, x_54);
x_85 = lean_array_uset(x_34, x_53, x_84);
x_86 = lean_unsigned_to_nat(2u);
x_87 = lean_nat_shiftl(x_83, x_86);
x_88 = lean_unsigned_to_nat(3u);
x_89 = lean_nat_div(x_87, x_88);
lean_dec(x_87);
x_90 = lean_array_get_size(x_85);
x_91 = lean_nat_dec_le(x_89, x_90);
lean_dec(x_90);
lean_dec(x_89);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; 
x_92 = l_instHashableFin(x_35);
lean_dec(x_35);
x_93 = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(x_92, x_85);
lean_ctor_set(x_4, 1, x_93);
lean_ctor_set(x_4, 0, x_83);
x_67 = x_4;
goto block_78;
}
else
{
lean_dec(x_35);
lean_ctor_set(x_4, 1, x_85);
lean_ctor_set(x_4, 0, x_83);
x_67 = x_4;
goto block_78;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; 
lean_dec(x_4);
x_94 = lean_box(0);
x_95 = lean_nat_add(x_33, x_50);
lean_dec(x_33);
lean_inc(x_3);
x_96 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_96, 0, x_3);
lean_ctor_set(x_96, 1, x_94);
lean_ctor_set(x_96, 2, x_54);
x_97 = lean_array_uset(x_34, x_53, x_96);
x_98 = lean_unsigned_to_nat(2u);
x_99 = lean_nat_shiftl(x_95, x_98);
x_100 = lean_unsigned_to_nat(3u);
x_101 = lean_nat_div(x_99, x_100);
lean_dec(x_99);
x_102 = lean_array_get_size(x_97);
x_103 = lean_nat_dec_le(x_101, x_102);
lean_dec(x_102);
lean_dec(x_101);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = l_instHashableFin(x_35);
lean_dec(x_35);
x_105 = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(x_104, x_97);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_95);
lean_ctor_set(x_106, 1, x_105);
x_67 = x_106;
goto block_78;
}
else
{
lean_object* x_107; 
lean_dec(x_35);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_95);
lean_ctor_set(x_107, 1, x_97);
x_67 = x_107;
goto block_78;
}
}
}
else
{
lean_dec(x_54);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
x_67 = x_4;
goto block_78;
}
}
else
{
lean_object* x_108; 
lean_dec(x_54);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_3);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_1);
lean_ctor_set(x_108, 1, x_4);
return x_108;
}
block_32:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_10 = l___private_Init_Data_Repr_0__Nat_reprFast(x_3);
x_11 = lean_mk_string_unchecked(" -> ", 4, 4);
lean_inc(x_10);
x_12 = lean_string_append(x_10, x_11);
lean_inc(x_8);
x_13 = l___private_Init_Data_Repr_0__Nat_reprFast(x_8);
x_14 = lean_string_append(x_12, x_13);
lean_dec(x_13);
x_15 = l_Std_Sat_AIG_toGraphviz_invEdgeStyle(x_7);
x_16 = lean_string_append(x_14, x_15);
lean_dec(x_15);
x_17 = lean_mk_string_unchecked("; ", 2, 2);
x_18 = lean_string_append(x_16, x_17);
lean_dec(x_17);
x_19 = lean_string_append(x_18, x_10);
lean_dec(x_10);
x_20 = lean_string_append(x_19, x_11);
lean_dec(x_11);
lean_inc(x_5);
x_21 = l___private_Init_Data_Repr_0__Nat_reprFast(x_5);
x_22 = lean_string_append(x_20, x_21);
lean_dec(x_21);
x_23 = l_Std_Sat_AIG_toGraphviz_invEdgeStyle(x_9);
x_24 = lean_string_append(x_22, x_23);
lean_dec(x_23);
x_25 = lean_mk_string_unchecked(";", 1, 1);
x_26 = lean_string_append(x_24, x_25);
lean_dec(x_25);
x_27 = lean_string_append(x_1, x_26);
lean_dec(x_26);
x_28 = l_Std_Sat_AIG_toGraphviz_go___redArg(x_27, x_2, x_8, x_6);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_1 = x_29;
x_3 = x_5;
x_4 = x_30;
goto _start;
}
block_66:
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_60 = lean_nat_shiftr(x_57, x_50);
x_61 = lean_nat_land(x_50, x_57);
lean_dec(x_57);
x_62 = lean_unsigned_to_nat(0u);
x_63 = lean_nat_dec_eq(x_61, x_62);
lean_dec(x_61);
if (x_63 == 0)
{
lean_object* x_64; uint8_t x_65; 
x_64 = lean_box(1);
x_65 = lean_unbox(x_64);
x_5 = x_60;
x_6 = x_56;
x_7 = x_59;
x_8 = x_58;
x_9 = x_65;
goto block_32;
}
else
{
x_5 = x_60;
x_6 = x_56;
x_7 = x_59;
x_8 = x_58;
x_9 = x_55;
goto block_32;
}
}
block_78:
{
lean_object* x_68; 
x_68 = lean_array_fget(x_2, x_3);
if (lean_obj_tag(x_68) == 2)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = lean_nat_shiftr(x_69, x_50);
x_72 = lean_nat_land(x_50, x_69);
lean_dec(x_69);
x_73 = lean_unsigned_to_nat(0u);
x_74 = lean_nat_dec_eq(x_72, x_73);
lean_dec(x_72);
if (x_74 == 0)
{
lean_object* x_75; uint8_t x_76; 
x_75 = lean_box(1);
x_76 = lean_unbox(x_75);
x_56 = x_67;
x_57 = x_70;
x_58 = x_71;
x_59 = x_76;
goto block_66;
}
else
{
x_56 = x_67;
x_57 = x_70;
x_58 = x_71;
x_59 = x_55;
goto block_66;
}
}
else
{
lean_object* x_77; 
lean_dec(x_68);
lean_dec(x_3);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_1);
lean_ctor_set(x_77, 1, x_67);
return x_77;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Std_Sat_AIG_toGraphviz_go___redArg(x_5, x_6, x_8, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Sat_AIG_toGraphviz_go___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Std_Sat_AIG_toGraphviz_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_array_fget(x_2, x_3);
switch (lean_obj_tag(x_4)) {
case 0:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_1);
x_5 = l___private_Init_Data_Repr_0__Nat_reprFast(x_3);
x_6 = lean_mk_string_unchecked(" [label=\"", 9, 9);
x_7 = lean_string_append(x_5, x_6);
lean_dec(x_6);
x_8 = lean_mk_string_unchecked("false", 5, 5);
x_9 = lean_string_append(x_7, x_8);
lean_dec(x_8);
x_10 = lean_mk_string_unchecked("\", shape=box];", 14, 14);
x_11 = lean_string_append(x_9, x_10);
lean_dec(x_10);
return x_11;
}
case 1:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_4, 0);
lean_inc(x_12);
lean_dec(x_4);
x_13 = l___private_Init_Data_Repr_0__Nat_reprFast(x_3);
x_14 = lean_mk_string_unchecked(" [label=\"", 9, 9);
x_15 = lean_string_append(x_13, x_14);
lean_dec(x_14);
x_16 = lean_apply_1(x_1, x_12);
x_17 = lean_string_append(x_15, x_16);
lean_dec(x_16);
x_18 = lean_mk_string_unchecked("\", shape=doublecircle];", 23, 23);
x_19 = lean_string_append(x_17, x_18);
lean_dec(x_18);
return x_19;
}
default: 
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_4);
lean_dec(x_1);
x_20 = l___private_Init_Data_Repr_0__Nat_reprFast(x_3);
x_21 = lean_mk_string_unchecked(" [label=\"", 9, 9);
lean_inc(x_20);
x_22 = lean_string_append(x_20, x_21);
lean_dec(x_21);
x_23 = lean_string_append(x_22, x_20);
lean_dec(x_20);
x_24 = lean_mk_string_unchecked(" ∧\",shape=trapezium];", 23, 21);
x_25 = lean_string_append(x_23, x_24);
lean_dec(x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg(x_3, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_Sat_AIG_toGraphviz_toGraphvizString(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg(x_1, x_2, x_4);
x_7 = lean_string_append(x_3, x_6);
lean_dec(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_ctor_get(x_4, 1);
lean_dec(x_8);
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_mk_string_unchecked("", 0, 0);
x_11 = lean_unsigned_to_nat(8u);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_unsigned_to_nat(2u);
x_14 = lean_nat_shiftl(x_11, x_13);
x_15 = lean_unsigned_to_nat(3u);
x_16 = lean_nat_div(x_14, x_15);
lean_dec(x_14);
x_17 = l_Nat_nextPowerOfTwo(x_16);
lean_dec(x_16);
x_18 = lean_box(0);
x_19 = lean_mk_array(x_17, x_18);
lean_ctor_set(x_4, 1, x_19);
lean_ctor_set(x_4, 0, x_12);
lean_inc(x_10);
x_20 = l_Std_Sat_AIG_toGraphviz_go___redArg(x_10, x_7, x_9, x_4);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
x_31 = lean_alloc_closure((void*)(l_Id_instMonad___lam__0), 4, 0);
x_32 = lean_alloc_closure((void*)(l_Id_instMonad___lam__1___boxed), 4, 0);
x_33 = lean_alloc_closure((void*)(l_Id_instMonad___lam__2___boxed), 2, 0);
x_34 = lean_alloc_closure((void*)(l_Id_instMonad___lam__3), 4, 0);
x_35 = lean_alloc_closure((void*)(l_Id_instMonad___lam__4___boxed), 4, 0);
x_36 = lean_alloc_closure((void*)(l_Id_instMonad___lam__5___boxed), 4, 0);
x_37 = lean_alloc_closure((void*)(l_Id_instMonad___lam__6), 4, 0);
lean_ctor_set(x_20, 1, x_32);
lean_ctor_set(x_20, 0, x_31);
x_38 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_38, 0, x_20);
lean_ctor_set(x_38, 1, x_33);
lean_ctor_set(x_38, 2, x_34);
lean_ctor_set(x_38, 3, x_35);
lean_ctor_set(x_38, 4, x_36);
lean_ctor_set(x_2, 1, x_37);
lean_ctor_set(x_2, 0, x_38);
x_39 = lean_ctor_get(x_23, 1);
lean_inc(x_39);
lean_dec(x_23);
x_40 = lean_array_get_size(x_39);
x_41 = lean_nat_dec_lt(x_12, x_40);
if (x_41 == 0)
{
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_2);
lean_dec(x_7);
lean_dec(x_1);
x_24 = x_10;
goto block_30;
}
else
{
uint8_t x_42; 
x_42 = lean_nat_dec_le(x_40, x_40);
if (x_42 == 0)
{
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_2);
lean_dec(x_7);
lean_dec(x_1);
x_24 = x_10;
goto block_30;
}
else
{
lean_object* x_43; lean_object* x_44; size_t x_45; size_t x_46; lean_object* x_47; 
x_43 = lean_alloc_closure((void*)(l_Std_Sat_AIG_toGraphviz___redArg___lam__0___boxed), 5, 2);
lean_closure_set(x_43, 0, x_1);
lean_closure_set(x_43, 1, x_7);
lean_inc(x_2);
x_44 = lean_alloc_closure((void*)(l_Std_Sat_AIG_toGraphviz___redArg___lam__1), 4, 2);
lean_closure_set(x_44, 0, x_2);
lean_closure_set(x_44, 1, x_43);
x_45 = lean_usize_of_nat(x_12);
x_46 = lean_usize_of_nat(x_40);
lean_dec(x_40);
x_47 = l_Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_2, x_44, x_39, x_45, x_46, x_10);
x_24 = x_47;
goto block_30;
}
}
block_30:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_mk_string_unchecked("Digraph AIG {", 13, 13);
x_26 = lean_string_append(x_25, x_24);
lean_dec(x_24);
x_27 = lean_string_append(x_26, x_22);
lean_dec(x_22);
x_28 = lean_mk_string_unchecked("}", 1, 1);
x_29 = lean_string_append(x_27, x_28);
lean_dec(x_28);
return x_29;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_48 = lean_ctor_get(x_20, 0);
x_49 = lean_ctor_get(x_20, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_20);
x_57 = lean_alloc_closure((void*)(l_Id_instMonad___lam__0), 4, 0);
x_58 = lean_alloc_closure((void*)(l_Id_instMonad___lam__1___boxed), 4, 0);
x_59 = lean_alloc_closure((void*)(l_Id_instMonad___lam__2___boxed), 2, 0);
x_60 = lean_alloc_closure((void*)(l_Id_instMonad___lam__3), 4, 0);
x_61 = lean_alloc_closure((void*)(l_Id_instMonad___lam__4___boxed), 4, 0);
x_62 = lean_alloc_closure((void*)(l_Id_instMonad___lam__5___boxed), 4, 0);
x_63 = lean_alloc_closure((void*)(l_Id_instMonad___lam__6), 4, 0);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_57);
lean_ctor_set(x_64, 1, x_58);
x_65 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_59);
lean_ctor_set(x_65, 2, x_60);
lean_ctor_set(x_65, 3, x_61);
lean_ctor_set(x_65, 4, x_62);
lean_ctor_set(x_2, 1, x_63);
lean_ctor_set(x_2, 0, x_65);
x_66 = lean_ctor_get(x_49, 1);
lean_inc(x_66);
lean_dec(x_49);
x_67 = lean_array_get_size(x_66);
x_68 = lean_nat_dec_lt(x_12, x_67);
if (x_68 == 0)
{
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_2);
lean_dec(x_7);
lean_dec(x_1);
x_50 = x_10;
goto block_56;
}
else
{
uint8_t x_69; 
x_69 = lean_nat_dec_le(x_67, x_67);
if (x_69 == 0)
{
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_2);
lean_dec(x_7);
lean_dec(x_1);
x_50 = x_10;
goto block_56;
}
else
{
lean_object* x_70; lean_object* x_71; size_t x_72; size_t x_73; lean_object* x_74; 
x_70 = lean_alloc_closure((void*)(l_Std_Sat_AIG_toGraphviz___redArg___lam__0___boxed), 5, 2);
lean_closure_set(x_70, 0, x_1);
lean_closure_set(x_70, 1, x_7);
lean_inc(x_2);
x_71 = lean_alloc_closure((void*)(l_Std_Sat_AIG_toGraphviz___redArg___lam__1), 4, 2);
lean_closure_set(x_71, 0, x_2);
lean_closure_set(x_71, 1, x_70);
x_72 = lean_usize_of_nat(x_12);
x_73 = lean_usize_of_nat(x_67);
lean_dec(x_67);
x_74 = l_Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_2, x_71, x_66, x_72, x_73, x_10);
x_50 = x_74;
goto block_56;
}
}
block_56:
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_51 = lean_mk_string_unchecked("Digraph AIG {", 13, 13);
x_52 = lean_string_append(x_51, x_50);
lean_dec(x_50);
x_53 = lean_string_append(x_52, x_48);
lean_dec(x_48);
x_54 = lean_mk_string_unchecked("}", 1, 1);
x_55 = lean_string_append(x_53, x_54);
lean_dec(x_54);
return x_55;
}
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; 
x_75 = lean_ctor_get(x_2, 1);
x_76 = lean_ctor_get(x_4, 0);
lean_inc(x_76);
lean_dec(x_4);
x_77 = lean_ctor_get(x_75, 0);
lean_inc(x_77);
lean_dec(x_75);
x_78 = lean_mk_string_unchecked("", 0, 0);
x_79 = lean_unsigned_to_nat(8u);
x_80 = lean_unsigned_to_nat(0u);
x_81 = lean_unsigned_to_nat(2u);
x_82 = lean_nat_shiftl(x_79, x_81);
x_83 = lean_unsigned_to_nat(3u);
x_84 = lean_nat_div(x_82, x_83);
lean_dec(x_82);
x_85 = l_Nat_nextPowerOfTwo(x_84);
lean_dec(x_84);
x_86 = lean_box(0);
x_87 = lean_mk_array(x_85, x_86);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_80);
lean_ctor_set(x_88, 1, x_87);
lean_inc(x_78);
x_89 = l_Std_Sat_AIG_toGraphviz_go___redArg(x_78, x_76, x_77, x_88);
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_92 = x_89;
} else {
 lean_dec_ref(x_89);
 x_92 = lean_box(0);
}
x_100 = lean_alloc_closure((void*)(l_Id_instMonad___lam__0), 4, 0);
x_101 = lean_alloc_closure((void*)(l_Id_instMonad___lam__1___boxed), 4, 0);
x_102 = lean_alloc_closure((void*)(l_Id_instMonad___lam__2___boxed), 2, 0);
x_103 = lean_alloc_closure((void*)(l_Id_instMonad___lam__3), 4, 0);
x_104 = lean_alloc_closure((void*)(l_Id_instMonad___lam__4___boxed), 4, 0);
x_105 = lean_alloc_closure((void*)(l_Id_instMonad___lam__5___boxed), 4, 0);
x_106 = lean_alloc_closure((void*)(l_Id_instMonad___lam__6), 4, 0);
if (lean_is_scalar(x_92)) {
 x_107 = lean_alloc_ctor(0, 2, 0);
} else {
 x_107 = x_92;
}
lean_ctor_set(x_107, 0, x_100);
lean_ctor_set(x_107, 1, x_101);
x_108 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_102);
lean_ctor_set(x_108, 2, x_103);
lean_ctor_set(x_108, 3, x_104);
lean_ctor_set(x_108, 4, x_105);
lean_ctor_set(x_2, 1, x_106);
lean_ctor_set(x_2, 0, x_108);
x_109 = lean_ctor_get(x_91, 1);
lean_inc(x_109);
lean_dec(x_91);
x_110 = lean_array_get_size(x_109);
x_111 = lean_nat_dec_lt(x_80, x_110);
if (x_111 == 0)
{
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_2);
lean_dec(x_76);
lean_dec(x_1);
x_93 = x_78;
goto block_99;
}
else
{
uint8_t x_112; 
x_112 = lean_nat_dec_le(x_110, x_110);
if (x_112 == 0)
{
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_2);
lean_dec(x_76);
lean_dec(x_1);
x_93 = x_78;
goto block_99;
}
else
{
lean_object* x_113; lean_object* x_114; size_t x_115; size_t x_116; lean_object* x_117; 
x_113 = lean_alloc_closure((void*)(l_Std_Sat_AIG_toGraphviz___redArg___lam__0___boxed), 5, 2);
lean_closure_set(x_113, 0, x_1);
lean_closure_set(x_113, 1, x_76);
lean_inc(x_2);
x_114 = lean_alloc_closure((void*)(l_Std_Sat_AIG_toGraphviz___redArg___lam__1), 4, 2);
lean_closure_set(x_114, 0, x_2);
lean_closure_set(x_114, 1, x_113);
x_115 = lean_usize_of_nat(x_80);
x_116 = lean_usize_of_nat(x_110);
lean_dec(x_110);
x_117 = l_Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_2, x_114, x_109, x_115, x_116, x_78);
x_93 = x_117;
goto block_99;
}
}
block_99:
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_94 = lean_mk_string_unchecked("Digraph AIG {", 13, 13);
x_95 = lean_string_append(x_94, x_93);
lean_dec(x_93);
x_96 = lean_string_append(x_95, x_90);
lean_dec(x_90);
x_97 = lean_mk_string_unchecked("}", 1, 1);
x_98 = lean_string_append(x_96, x_97);
lean_dec(x_97);
return x_98;
}
}
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; uint8_t x_157; 
x_118 = lean_ctor_get(x_2, 0);
x_119 = lean_ctor_get(x_2, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_2);
x_120 = lean_ctor_get(x_118, 0);
lean_inc(x_120);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 x_121 = x_118;
} else {
 lean_dec_ref(x_118);
 x_121 = lean_box(0);
}
x_122 = lean_ctor_get(x_119, 0);
lean_inc(x_122);
lean_dec(x_119);
x_123 = lean_mk_string_unchecked("", 0, 0);
x_124 = lean_unsigned_to_nat(8u);
x_125 = lean_unsigned_to_nat(0u);
x_126 = lean_unsigned_to_nat(2u);
x_127 = lean_nat_shiftl(x_124, x_126);
x_128 = lean_unsigned_to_nat(3u);
x_129 = lean_nat_div(x_127, x_128);
lean_dec(x_127);
x_130 = l_Nat_nextPowerOfTwo(x_129);
lean_dec(x_129);
x_131 = lean_box(0);
x_132 = lean_mk_array(x_130, x_131);
if (lean_is_scalar(x_121)) {
 x_133 = lean_alloc_ctor(0, 2, 0);
} else {
 x_133 = x_121;
}
lean_ctor_set(x_133, 0, x_125);
lean_ctor_set(x_133, 1, x_132);
lean_inc(x_123);
x_134 = l_Std_Sat_AIG_toGraphviz_go___redArg(x_123, x_120, x_122, x_133);
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_134, 1);
lean_inc(x_136);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_137 = x_134;
} else {
 lean_dec_ref(x_134);
 x_137 = lean_box(0);
}
x_145 = lean_alloc_closure((void*)(l_Id_instMonad___lam__0), 4, 0);
x_146 = lean_alloc_closure((void*)(l_Id_instMonad___lam__1___boxed), 4, 0);
x_147 = lean_alloc_closure((void*)(l_Id_instMonad___lam__2___boxed), 2, 0);
x_148 = lean_alloc_closure((void*)(l_Id_instMonad___lam__3), 4, 0);
x_149 = lean_alloc_closure((void*)(l_Id_instMonad___lam__4___boxed), 4, 0);
x_150 = lean_alloc_closure((void*)(l_Id_instMonad___lam__5___boxed), 4, 0);
x_151 = lean_alloc_closure((void*)(l_Id_instMonad___lam__6), 4, 0);
if (lean_is_scalar(x_137)) {
 x_152 = lean_alloc_ctor(0, 2, 0);
} else {
 x_152 = x_137;
}
lean_ctor_set(x_152, 0, x_145);
lean_ctor_set(x_152, 1, x_146);
x_153 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_153, 1, x_147);
lean_ctor_set(x_153, 2, x_148);
lean_ctor_set(x_153, 3, x_149);
lean_ctor_set(x_153, 4, x_150);
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_151);
x_155 = lean_ctor_get(x_136, 1);
lean_inc(x_155);
lean_dec(x_136);
x_156 = lean_array_get_size(x_155);
x_157 = lean_nat_dec_lt(x_125, x_156);
if (x_157 == 0)
{
lean_dec(x_156);
lean_dec(x_155);
lean_dec(x_154);
lean_dec(x_120);
lean_dec(x_1);
x_138 = x_123;
goto block_144;
}
else
{
uint8_t x_158; 
x_158 = lean_nat_dec_le(x_156, x_156);
if (x_158 == 0)
{
lean_dec(x_156);
lean_dec(x_155);
lean_dec(x_154);
lean_dec(x_120);
lean_dec(x_1);
x_138 = x_123;
goto block_144;
}
else
{
lean_object* x_159; lean_object* x_160; size_t x_161; size_t x_162; lean_object* x_163; 
x_159 = lean_alloc_closure((void*)(l_Std_Sat_AIG_toGraphviz___redArg___lam__0___boxed), 5, 2);
lean_closure_set(x_159, 0, x_1);
lean_closure_set(x_159, 1, x_120);
lean_inc(x_154);
x_160 = lean_alloc_closure((void*)(l_Std_Sat_AIG_toGraphviz___redArg___lam__1), 4, 2);
lean_closure_set(x_160, 0, x_154);
lean_closure_set(x_160, 1, x_159);
x_161 = lean_usize_of_nat(x_125);
x_162 = lean_usize_of_nat(x_156);
lean_dec(x_156);
x_163 = l_Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_154, x_160, x_155, x_161, x_162, x_123);
x_138 = x_163;
goto block_144;
}
}
block_144:
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_139 = lean_mk_string_unchecked("Digraph AIG {", 13, 13);
x_140 = lean_string_append(x_139, x_138);
lean_dec(x_138);
x_141 = lean_string_append(x_140, x_135);
lean_dec(x_135);
x_142 = lean_mk_string_unchecked("}", 1, 1);
x_143 = lean_string_append(x_141, x_142);
lean_dec(x_142);
return x_143;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Sat_AIG_toGraphviz___redArg(x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Sat_AIG_toGraphviz___redArg___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Sat_AIG_toGraphviz(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_AIG_denote_go___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_array_fget(x_2, x_1);
switch (lean_obj_tag(x_4)) {
case 0:
{
lean_object* x_5; uint8_t x_6; 
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = lean_unbox(x_5);
return x_6;
}
case 1:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
lean_dec(x_4);
x_8 = lean_apply_1(x_3, x_7);
x_9 = lean_unbox(x_8);
lean_dec(x_8);
return x_9;
}
default: 
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; uint8_t x_20; uint8_t x_27; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_10 = lean_ctor_get(x_4, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_dec(x_4);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_shiftr(x_10, x_12);
lean_inc(x_3);
x_14 = l_Std_Sat_AIG_denote_go___redArg(x_13, x_2, x_3);
lean_dec(x_13);
x_15 = lean_nat_shiftr(x_11, x_12);
x_16 = l_Std_Sat_AIG_denote_go___redArg(x_15, x_2, x_3);
lean_dec(x_15);
x_33 = lean_nat_land(x_12, x_10);
lean_dec(x_10);
x_34 = lean_unsigned_to_nat(0u);
x_35 = lean_nat_dec_eq(x_33, x_34);
lean_dec(x_33);
if (x_35 == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_box(1);
x_37 = lean_unbox(x_36);
x_27 = x_37;
goto block_32;
}
else
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_box(0);
x_39 = lean_unbox(x_38);
x_27 = x_39;
goto block_32;
}
block_19:
{
if (x_16 == 0)
{
if (x_18 == 0)
{
return x_17;
}
else
{
return x_18;
}
}
else
{
if (x_18 == 0)
{
return x_16;
}
else
{
return x_17;
}
}
}
block_26:
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_nat_land(x_12, x_11);
lean_dec(x_11);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_nat_dec_eq(x_21, x_22);
lean_dec(x_21);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_box(1);
x_25 = lean_unbox(x_24);
x_17 = x_20;
x_18 = x_25;
goto block_19;
}
else
{
x_17 = x_20;
x_18 = x_20;
goto block_19;
}
}
block_32:
{
lean_object* x_28; 
x_28 = lean_box(0);
if (x_14 == 0)
{
if (x_27 == 0)
{
lean_dec(x_11);
return x_27;
}
else
{
uint8_t x_29; 
x_29 = lean_unbox(x_28);
x_20 = x_29;
goto block_26;
}
}
else
{
if (x_27 == 0)
{
uint8_t x_30; 
x_30 = lean_unbox(x_28);
x_20 = x_30;
goto block_26;
}
else
{
uint8_t x_31; 
lean_dec(x_11);
x_31 = lean_unbox(x_28);
return x_31;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_Sat_AIG_denote_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = l_Std_Sat_AIG_denote_go___redArg(x_2, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_denote_go___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_Sat_AIG_denote_go___redArg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_denote_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = l_Std_Sat_AIG_denote_go(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_AIG_denote___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_5, 0);
x_7 = l_Std_Sat_AIG_denote_go___redArg(x_4, x_6, x_1);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = lean_ctor_get_uint8(x_3, sizeof(void*)*1);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = lean_ctor_get_uint8(x_3, sizeof(void*)*1);
if (x_9 == 0)
{
return x_7;
}
else
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_box(0);
x_11 = lean_unbox(x_10);
return x_11;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_Sat_AIG_denote(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = l_Std_Sat_AIG_denote___redArg(x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_denote___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_Sat_AIG_denote___redArg(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_denote___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Std_Sat_AIG_denote(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_7 = lean_box(x_6);
return x_7;
}
}
static lean_object* _init_l_Std_Sat_AIG_term_u27e6___x2c___u27e7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_1 = lean_mk_string_unchecked("Std", 3, 3);
x_2 = lean_mk_string_unchecked("Sat", 3, 3);
x_3 = lean_mk_string_unchecked("AIG", 3, 3);
x_4 = lean_mk_string_unchecked("term⟦_,_⟧", 13, 9);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1024u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("⟦", 3, 1);
x_10 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_mk_string_unchecked("term", 4, 4);
x_12 = l_Lean_Name_mkStr1(x_11);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
lean_inc(x_14);
lean_inc(x_8);
x_15 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_10);
lean_ctor_set(x_15, 2, x_14);
x_16 = lean_mk_string_unchecked(", ", 2, 2);
x_17 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_17, 0, x_16);
lean_inc(x_8);
x_18 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_18, 0, x_8);
lean_ctor_set(x_18, 1, x_15);
lean_ctor_set(x_18, 2, x_17);
lean_inc(x_8);
x_19 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_19, 0, x_8);
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set(x_19, 2, x_14);
x_20 = lean_mk_string_unchecked("⟧", 3, 1);
x_21 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_22, 0, x_8);
lean_ctor_set(x_22, 1, x_19);
lean_ctor_set(x_22, 2, x_21);
x_23 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_23, 0, x_5);
lean_ctor_set(x_23, 1, x_6);
lean_ctor_set(x_23, 2, x_22);
return x_23;
}
}
static lean_object* _init_l_Std_Sat_AIG_term_u27e6___x2c___x2c___u27e7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_1 = lean_mk_string_unchecked("Std", 3, 3);
x_2 = lean_mk_string_unchecked("Sat", 3, 3);
x_3 = lean_mk_string_unchecked("AIG", 3, 3);
x_4 = lean_mk_string_unchecked("term⟦_,_,_⟧", 15, 11);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1024u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("⟦", 3, 1);
x_10 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_mk_string_unchecked("term", 4, 4);
x_12 = l_Lean_Name_mkStr1(x_11);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
lean_inc(x_14);
lean_inc(x_8);
x_15 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_10);
lean_ctor_set(x_15, 2, x_14);
x_16 = lean_mk_string_unchecked(", ", 2, 2);
x_17 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_17, 0, x_16);
lean_inc(x_17);
lean_inc(x_8);
x_18 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_18, 0, x_8);
lean_ctor_set(x_18, 1, x_15);
lean_ctor_set(x_18, 2, x_17);
lean_inc(x_14);
lean_inc(x_8);
x_19 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_19, 0, x_8);
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set(x_19, 2, x_14);
lean_inc(x_8);
x_20 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_20, 0, x_8);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_20, 2, x_17);
lean_inc(x_8);
x_21 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_21, 0, x_8);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set(x_21, 2, x_14);
x_22 = lean_mk_string_unchecked("⟧", 3, 1);
x_23 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_24, 0, x_8);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 2, x_23);
x_25 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_25, 0, x_5);
lean_ctor_set(x_25, 1, x_6);
lean_ctor_set(x_25, 2, x_24);
return x_25;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_mk_string_unchecked("Std", 3, 3);
x_5 = lean_mk_string_unchecked("Sat", 3, 3);
x_6 = lean_mk_string_unchecked("AIG", 3, 3);
x_7 = lean_mk_string_unchecked("term⟦_,_⟧", 13, 9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_8 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_7);
lean_inc(x_1);
x_9 = l_Lean_Syntax_isOfKind(x_1, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_10 = lean_box(1);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = l_Lean_Syntax_getArg(x_1, x_12);
x_14 = lean_unsigned_to_nat(3u);
x_15 = l_Lean_Syntax_getArg(x_1, x_14);
lean_dec(x_1);
x_16 = lean_ctor_get(x_2, 5);
lean_inc(x_16);
x_17 = lean_box(0);
x_18 = lean_unbox(x_17);
x_19 = l_Lean_SourceInfo_fromRef(x_16, x_18);
lean_dec(x_16);
x_20 = lean_ctor_get(x_2, 2);
lean_inc(x_20);
x_21 = lean_ctor_get(x_2, 1);
lean_inc(x_21);
lean_dec(x_2);
x_22 = lean_mk_string_unchecked("Lean", 4, 4);
x_23 = lean_mk_string_unchecked("Parser", 6, 6);
x_24 = lean_mk_string_unchecked("Term", 4, 4);
x_25 = lean_mk_string_unchecked("app", 3, 3);
x_26 = l_Lean_Name_mkStr4(x_22, x_23, x_24, x_25);
x_27 = lean_mk_string_unchecked("denote", 6, 6);
lean_inc(x_27);
x_28 = l_String_toSubstring_x27(x_27);
lean_inc(x_27);
x_29 = l_Lean_Name_mkStr1(x_27);
x_30 = l_Lean_addMacroScope(x_21, x_29, x_20);
x_31 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_27);
x_32 = lean_box(0);
lean_inc(x_31);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_31);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_33);
lean_ctor_set(x_37, 1, x_36);
lean_inc(x_19);
x_38 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_38, 0, x_19);
lean_ctor_set(x_38, 1, x_28);
lean_ctor_set(x_38, 2, x_30);
lean_ctor_set(x_38, 3, x_37);
x_39 = lean_mk_string_unchecked("null", 4, 4);
x_40 = l_Lean_Name_mkStr1(x_39);
lean_inc(x_19);
x_41 = l_Lean_Syntax_node2(x_19, x_40, x_15, x_13);
x_42 = l_Lean_Syntax_node2(x_19, x_26, x_38, x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_3);
return x_43;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_mk_string_unchecked("Std", 3, 3);
x_5 = lean_mk_string_unchecked("Sat", 3, 3);
x_6 = lean_mk_string_unchecked("AIG", 3, 3);
x_7 = lean_mk_string_unchecked("term⟦_,_,_⟧", 15, 11);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_8 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_7);
lean_inc(x_1);
x_9 = l_Lean_Syntax_isOfKind(x_1, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_10 = lean_box(1);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = l_Lean_Syntax_getArg(x_1, x_12);
x_14 = lean_unsigned_to_nat(3u);
x_15 = l_Lean_Syntax_getArg(x_1, x_14);
x_16 = lean_unsigned_to_nat(5u);
x_17 = l_Lean_Syntax_getArg(x_1, x_16);
lean_dec(x_1);
x_18 = lean_ctor_get(x_2, 5);
lean_inc(x_18);
x_19 = lean_box(0);
x_20 = lean_unbox(x_19);
x_21 = l_Lean_SourceInfo_fromRef(x_18, x_20);
lean_dec(x_18);
x_22 = lean_ctor_get(x_2, 2);
lean_inc(x_22);
x_23 = lean_ctor_get(x_2, 1);
lean_inc(x_23);
lean_dec(x_2);
x_24 = lean_mk_string_unchecked("Lean", 4, 4);
x_25 = lean_mk_string_unchecked("Parser", 6, 6);
x_26 = lean_mk_string_unchecked("Term", 4, 4);
x_27 = lean_mk_string_unchecked("app", 3, 3);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
x_28 = l_Lean_Name_mkStr4(x_24, x_25, x_26, x_27);
x_29 = lean_mk_string_unchecked("denote", 6, 6);
lean_inc(x_29);
x_30 = l_String_toSubstring_x27(x_29);
lean_inc(x_29);
x_31 = l_Lean_Name_mkStr1(x_29);
lean_inc(x_22);
lean_inc(x_23);
x_32 = l_Lean_addMacroScope(x_23, x_31, x_22);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_33 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_29);
x_34 = lean_box(0);
lean_inc(x_33);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_36, 0, x_33);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_35);
lean_ctor_set(x_39, 1, x_38);
lean_inc(x_21);
x_40 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_40, 0, x_21);
lean_ctor_set(x_40, 1, x_30);
lean_ctor_set(x_40, 2, x_32);
lean_ctor_set(x_40, 3, x_39);
x_41 = lean_mk_string_unchecked("null", 4, 4);
x_42 = l_Lean_Name_mkStr1(x_41);
x_43 = lean_mk_string_unchecked("paren", 5, 5);
x_44 = l_Lean_Name_mkStr4(x_24, x_25, x_26, x_43);
x_45 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_21);
x_46 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_46, 0, x_21);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_mk_string_unchecked("Entrypoint.mk", 13, 13);
x_48 = l_String_toSubstring_x27(x_47);
x_49 = lean_mk_string_unchecked("Entrypoint", 10, 10);
x_50 = lean_mk_string_unchecked("mk", 2, 2);
lean_inc(x_50);
lean_inc(x_49);
x_51 = l_Lean_Name_mkStr2(x_49, x_50);
x_52 = l_Lean_addMacroScope(x_23, x_51, x_22);
x_53 = l_Lean_Name_mkStr5(x_4, x_5, x_6, x_49, x_50);
lean_inc(x_53);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_34);
x_55 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_55, 0, x_53);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_37);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_56);
lean_inc(x_21);
x_58 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_58, 0, x_21);
lean_ctor_set(x_58, 1, x_48);
lean_ctor_set(x_58, 2, x_52);
lean_ctor_set(x_58, 3, x_57);
lean_inc(x_42);
lean_inc(x_21);
x_59 = l_Lean_Syntax_node2(x_21, x_42, x_13, x_15);
lean_inc(x_28);
lean_inc(x_21);
x_60 = l_Lean_Syntax_node2(x_21, x_28, x_58, x_59);
x_61 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_21);
x_62 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_62, 0, x_21);
lean_ctor_set(x_62, 1, x_61);
lean_inc(x_21);
x_63 = l_Lean_Syntax_node3(x_21, x_44, x_46, x_60, x_62);
lean_inc(x_21);
x_64 = l_Lean_Syntax_node2(x_21, x_42, x_17, x_63);
x_65 = l_Lean_Syntax_node2(x_21, x_28, x_40, x_64);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_3);
return x_66;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_unexpandDenote(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Term", 4, 4);
x_7 = lean_mk_string_unchecked("app", 3, 3);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_8 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_7);
lean_inc(x_1);
x_9 = l_Lean_Syntax_isOfKind(x_1, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = l_Lean_Syntax_getArg(x_1, x_12);
lean_dec(x_1);
x_14 = lean_unsigned_to_nat(2u);
lean_inc(x_13);
x_15 = l_Lean_Syntax_matchesNull(x_13, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_3);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_Lean_Syntax_getArg(x_13, x_18);
x_20 = lean_mk_string_unchecked("structInst", 10, 10);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_21 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_20);
lean_inc(x_19);
x_22 = l_Lean_Syntax_isOfKind(x_19, x_21);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_23 = l_Lean_Syntax_getArg(x_13, x_12);
lean_dec(x_13);
x_24 = l_Lean_SourceInfo_fromRef(x_2, x_22);
x_25 = lean_mk_string_unchecked("Std", 3, 3);
x_26 = lean_mk_string_unchecked("Sat", 3, 3);
x_27 = lean_mk_string_unchecked("AIG", 3, 3);
x_28 = lean_mk_string_unchecked("term⟦_,_⟧", 13, 9);
x_29 = l_Lean_Name_mkStr4(x_25, x_26, x_27, x_28);
x_30 = lean_mk_string_unchecked("⟦", 3, 1);
lean_inc(x_24);
x_31 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_31, 0, x_24);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_mk_string_unchecked(",", 1, 1);
lean_inc(x_24);
x_33 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_33, 0, x_24);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_mk_string_unchecked("⟧", 3, 1);
lean_inc(x_24);
x_35 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_35, 0, x_24);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_Syntax_node5(x_24, x_29, x_31, x_19, x_33, x_23, x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_3);
return x_37;
}
else
{
lean_object* x_38; uint8_t x_39; 
x_38 = l_Lean_Syntax_getArg(x_19, x_12);
x_39 = l_Lean_Syntax_matchesNull(x_38, x_18);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_40 = l_Lean_Syntax_getArg(x_13, x_12);
lean_dec(x_13);
x_41 = l_Lean_SourceInfo_fromRef(x_2, x_39);
x_42 = lean_mk_string_unchecked("Std", 3, 3);
x_43 = lean_mk_string_unchecked("Sat", 3, 3);
x_44 = lean_mk_string_unchecked("AIG", 3, 3);
x_45 = lean_mk_string_unchecked("term⟦_,_⟧", 13, 9);
x_46 = l_Lean_Name_mkStr4(x_42, x_43, x_44, x_45);
x_47 = lean_mk_string_unchecked("⟦", 3, 1);
lean_inc(x_41);
x_48 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_48, 0, x_41);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_mk_string_unchecked(",", 1, 1);
lean_inc(x_41);
x_50 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_50, 0, x_41);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_mk_string_unchecked("⟧", 3, 1);
lean_inc(x_41);
x_52 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_52, 0, x_41);
lean_ctor_set(x_52, 1, x_51);
x_53 = l_Lean_Syntax_node5(x_41, x_46, x_48, x_19, x_50, x_40, x_52);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_3);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_55 = l_Lean_Syntax_getArg(x_19, x_14);
x_56 = lean_mk_string_unchecked("structInstFields", 16, 16);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_57 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_56);
lean_inc(x_55);
x_58 = l_Lean_Syntax_isOfKind(x_55, x_57);
lean_dec(x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_55);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_59 = l_Lean_Syntax_getArg(x_13, x_12);
lean_dec(x_13);
x_60 = l_Lean_SourceInfo_fromRef(x_2, x_58);
x_61 = lean_mk_string_unchecked("Std", 3, 3);
x_62 = lean_mk_string_unchecked("Sat", 3, 3);
x_63 = lean_mk_string_unchecked("AIG", 3, 3);
x_64 = lean_mk_string_unchecked("term⟦_,_⟧", 13, 9);
x_65 = l_Lean_Name_mkStr4(x_61, x_62, x_63, x_64);
x_66 = lean_mk_string_unchecked("⟦", 3, 1);
lean_inc(x_60);
x_67 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_67, 0, x_60);
lean_ctor_set(x_67, 1, x_66);
x_68 = lean_mk_string_unchecked(",", 1, 1);
lean_inc(x_60);
x_69 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_69, 0, x_60);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_mk_string_unchecked("⟧", 3, 1);
lean_inc(x_60);
x_71 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_71, 0, x_60);
lean_ctor_set(x_71, 1, x_70);
x_72 = l_Lean_Syntax_node5(x_60, x_65, x_67, x_19, x_69, x_59, x_71);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_3);
return x_73;
}
else
{
lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_74 = l_Lean_Syntax_getArg(x_55, x_18);
lean_dec(x_55);
x_75 = lean_unsigned_to_nat(5u);
lean_inc(x_74);
x_76 = l_Lean_Syntax_matchesNull(x_74, x_75);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_74);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_77 = l_Lean_Syntax_getArg(x_13, x_12);
lean_dec(x_13);
x_78 = l_Lean_SourceInfo_fromRef(x_2, x_76);
x_79 = lean_mk_string_unchecked("Std", 3, 3);
x_80 = lean_mk_string_unchecked("Sat", 3, 3);
x_81 = lean_mk_string_unchecked("AIG", 3, 3);
x_82 = lean_mk_string_unchecked("term⟦_,_⟧", 13, 9);
x_83 = l_Lean_Name_mkStr4(x_79, x_80, x_81, x_82);
x_84 = lean_mk_string_unchecked("⟦", 3, 1);
lean_inc(x_78);
x_85 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_85, 0, x_78);
lean_ctor_set(x_85, 1, x_84);
x_86 = lean_mk_string_unchecked(",", 1, 1);
lean_inc(x_78);
x_87 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_87, 0, x_78);
lean_ctor_set(x_87, 1, x_86);
x_88 = lean_mk_string_unchecked("⟧", 3, 1);
lean_inc(x_78);
x_89 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_89, 0, x_78);
lean_ctor_set(x_89, 1, x_88);
x_90 = l_Lean_Syntax_node5(x_78, x_83, x_85, x_19, x_87, x_77, x_89);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_3);
return x_91;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_92 = l_Lean_Syntax_getArg(x_74, x_18);
x_93 = lean_mk_string_unchecked("structInstField", 15, 15);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_94 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_93);
lean_inc(x_92);
x_95 = l_Lean_Syntax_isOfKind(x_92, x_94);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_dec(x_94);
lean_dec(x_92);
lean_dec(x_74);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_96 = l_Lean_Syntax_getArg(x_13, x_12);
lean_dec(x_13);
x_97 = l_Lean_SourceInfo_fromRef(x_2, x_95);
x_98 = lean_mk_string_unchecked("Std", 3, 3);
x_99 = lean_mk_string_unchecked("Sat", 3, 3);
x_100 = lean_mk_string_unchecked("AIG", 3, 3);
x_101 = lean_mk_string_unchecked("term⟦_,_⟧", 13, 9);
x_102 = l_Lean_Name_mkStr4(x_98, x_99, x_100, x_101);
x_103 = lean_mk_string_unchecked("⟦", 3, 1);
lean_inc(x_97);
x_104 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_104, 0, x_97);
lean_ctor_set(x_104, 1, x_103);
x_105 = lean_mk_string_unchecked(",", 1, 1);
lean_inc(x_97);
x_106 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_106, 0, x_97);
lean_ctor_set(x_106, 1, x_105);
x_107 = lean_mk_string_unchecked("⟧", 3, 1);
lean_inc(x_97);
x_108 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_108, 0, x_97);
lean_ctor_set(x_108, 1, x_107);
x_109 = l_Lean_Syntax_node5(x_97, x_102, x_104, x_19, x_106, x_96, x_108);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_3);
return x_110;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; 
x_111 = l_Lean_Syntax_getArg(x_92, x_18);
x_112 = lean_mk_string_unchecked("structInstLVal", 14, 14);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_113 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_112);
lean_inc(x_111);
x_114 = l_Lean_Syntax_isOfKind(x_111, x_113);
if (x_114 == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_dec(x_113);
lean_dec(x_111);
lean_dec(x_94);
lean_dec(x_92);
lean_dec(x_74);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_115 = l_Lean_Syntax_getArg(x_13, x_12);
lean_dec(x_13);
x_116 = l_Lean_SourceInfo_fromRef(x_2, x_114);
x_117 = lean_mk_string_unchecked("Std", 3, 3);
x_118 = lean_mk_string_unchecked("Sat", 3, 3);
x_119 = lean_mk_string_unchecked("AIG", 3, 3);
x_120 = lean_mk_string_unchecked("term⟦_,_⟧", 13, 9);
x_121 = l_Lean_Name_mkStr4(x_117, x_118, x_119, x_120);
x_122 = lean_mk_string_unchecked("⟦", 3, 1);
lean_inc(x_116);
x_123 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_123, 0, x_116);
lean_ctor_set(x_123, 1, x_122);
x_124 = lean_mk_string_unchecked(",", 1, 1);
lean_inc(x_116);
x_125 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_125, 0, x_116);
lean_ctor_set(x_125, 1, x_124);
x_126 = lean_mk_string_unchecked("⟧", 3, 1);
lean_inc(x_116);
x_127 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_127, 0, x_116);
lean_ctor_set(x_127, 1, x_126);
x_128 = l_Lean_Syntax_node5(x_116, x_121, x_123, x_19, x_125, x_115, x_127);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_3);
return x_129;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; 
x_130 = l_Lean_Syntax_getArg(x_111, x_18);
x_131 = lean_mk_string_unchecked("aig", 3, 3);
x_132 = l_Lean_Name_mkStr1(x_131);
x_133 = l_Lean_Syntax_matchesIdent(x_130, x_132);
lean_dec(x_130);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
lean_dec(x_113);
lean_dec(x_111);
lean_dec(x_94);
lean_dec(x_92);
lean_dec(x_74);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_134 = l_Lean_Syntax_getArg(x_13, x_12);
lean_dec(x_13);
x_135 = l_Lean_SourceInfo_fromRef(x_2, x_133);
x_136 = lean_mk_string_unchecked("Std", 3, 3);
x_137 = lean_mk_string_unchecked("Sat", 3, 3);
x_138 = lean_mk_string_unchecked("AIG", 3, 3);
x_139 = lean_mk_string_unchecked("term⟦_,_⟧", 13, 9);
x_140 = l_Lean_Name_mkStr4(x_136, x_137, x_138, x_139);
x_141 = lean_mk_string_unchecked("⟦", 3, 1);
lean_inc(x_135);
x_142 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_142, 0, x_135);
lean_ctor_set(x_142, 1, x_141);
x_143 = lean_mk_string_unchecked(",", 1, 1);
lean_inc(x_135);
x_144 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_144, 0, x_135);
lean_ctor_set(x_144, 1, x_143);
x_145 = lean_mk_string_unchecked("⟧", 3, 1);
lean_inc(x_135);
x_146 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_146, 0, x_135);
lean_ctor_set(x_146, 1, x_145);
x_147 = l_Lean_Syntax_node5(x_135, x_140, x_142, x_19, x_144, x_134, x_146);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_3);
return x_148;
}
else
{
lean_object* x_149; uint8_t x_150; 
x_149 = l_Lean_Syntax_getArg(x_111, x_12);
lean_dec(x_111);
x_150 = l_Lean_Syntax_matchesNull(x_149, x_18);
if (x_150 == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
lean_dec(x_113);
lean_dec(x_94);
lean_dec(x_92);
lean_dec(x_74);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_151 = l_Lean_Syntax_getArg(x_13, x_12);
lean_dec(x_13);
x_152 = l_Lean_SourceInfo_fromRef(x_2, x_150);
x_153 = lean_mk_string_unchecked("Std", 3, 3);
x_154 = lean_mk_string_unchecked("Sat", 3, 3);
x_155 = lean_mk_string_unchecked("AIG", 3, 3);
x_156 = lean_mk_string_unchecked("term⟦_,_⟧", 13, 9);
x_157 = l_Lean_Name_mkStr4(x_153, x_154, x_155, x_156);
x_158 = lean_mk_string_unchecked("⟦", 3, 1);
lean_inc(x_152);
x_159 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_159, 0, x_152);
lean_ctor_set(x_159, 1, x_158);
x_160 = lean_mk_string_unchecked(",", 1, 1);
lean_inc(x_152);
x_161 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_161, 0, x_152);
lean_ctor_set(x_161, 1, x_160);
x_162 = lean_mk_string_unchecked("⟧", 3, 1);
lean_inc(x_152);
x_163 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_163, 0, x_152);
lean_ctor_set(x_163, 1, x_162);
x_164 = l_Lean_Syntax_node5(x_152, x_157, x_159, x_19, x_161, x_151, x_163);
x_165 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_165, 0, x_164);
lean_ctor_set(x_165, 1, x_3);
return x_165;
}
else
{
lean_object* x_166; lean_object* x_167; uint8_t x_168; 
x_166 = l_Lean_Syntax_getArg(x_92, x_12);
lean_dec(x_92);
x_167 = lean_unsigned_to_nat(3u);
lean_inc(x_166);
x_168 = l_Lean_Syntax_matchesNull(x_166, x_167);
if (x_168 == 0)
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
lean_dec(x_166);
lean_dec(x_113);
lean_dec(x_94);
lean_dec(x_74);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_169 = l_Lean_Syntax_getArg(x_13, x_12);
lean_dec(x_13);
x_170 = l_Lean_SourceInfo_fromRef(x_2, x_168);
x_171 = lean_mk_string_unchecked("Std", 3, 3);
x_172 = lean_mk_string_unchecked("Sat", 3, 3);
x_173 = lean_mk_string_unchecked("AIG", 3, 3);
x_174 = lean_mk_string_unchecked("term⟦_,_⟧", 13, 9);
x_175 = l_Lean_Name_mkStr4(x_171, x_172, x_173, x_174);
x_176 = lean_mk_string_unchecked("⟦", 3, 1);
lean_inc(x_170);
x_177 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_177, 0, x_170);
lean_ctor_set(x_177, 1, x_176);
x_178 = lean_mk_string_unchecked(",", 1, 1);
lean_inc(x_170);
x_179 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_179, 0, x_170);
lean_ctor_set(x_179, 1, x_178);
x_180 = lean_mk_string_unchecked("⟧", 3, 1);
lean_inc(x_170);
x_181 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_181, 0, x_170);
lean_ctor_set(x_181, 1, x_180);
x_182 = l_Lean_Syntax_node5(x_170, x_175, x_177, x_19, x_179, x_169, x_181);
x_183 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_3);
return x_183;
}
else
{
lean_object* x_184; uint8_t x_185; 
x_184 = l_Lean_Syntax_getArg(x_166, x_18);
x_185 = l_Lean_Syntax_matchesNull(x_184, x_18);
if (x_185 == 0)
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
lean_dec(x_166);
lean_dec(x_113);
lean_dec(x_94);
lean_dec(x_74);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_186 = l_Lean_Syntax_getArg(x_13, x_12);
lean_dec(x_13);
x_187 = l_Lean_SourceInfo_fromRef(x_2, x_185);
x_188 = lean_mk_string_unchecked("Std", 3, 3);
x_189 = lean_mk_string_unchecked("Sat", 3, 3);
x_190 = lean_mk_string_unchecked("AIG", 3, 3);
x_191 = lean_mk_string_unchecked("term⟦_,_⟧", 13, 9);
x_192 = l_Lean_Name_mkStr4(x_188, x_189, x_190, x_191);
x_193 = lean_mk_string_unchecked("⟦", 3, 1);
lean_inc(x_187);
x_194 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_194, 0, x_187);
lean_ctor_set(x_194, 1, x_193);
x_195 = lean_mk_string_unchecked(",", 1, 1);
lean_inc(x_187);
x_196 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_196, 0, x_187);
lean_ctor_set(x_196, 1, x_195);
x_197 = lean_mk_string_unchecked("⟧", 3, 1);
lean_inc(x_187);
x_198 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_198, 0, x_187);
lean_ctor_set(x_198, 1, x_197);
x_199 = l_Lean_Syntax_node5(x_187, x_192, x_194, x_19, x_196, x_186, x_198);
x_200 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_200, 0, x_199);
lean_ctor_set(x_200, 1, x_3);
return x_200;
}
else
{
lean_object* x_201; uint8_t x_202; 
x_201 = l_Lean_Syntax_getArg(x_166, x_12);
x_202 = l_Lean_Syntax_matchesNull(x_201, x_18);
if (x_202 == 0)
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
lean_dec(x_166);
lean_dec(x_113);
lean_dec(x_94);
lean_dec(x_74);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_203 = l_Lean_Syntax_getArg(x_13, x_12);
lean_dec(x_13);
x_204 = l_Lean_SourceInfo_fromRef(x_2, x_202);
x_205 = lean_mk_string_unchecked("Std", 3, 3);
x_206 = lean_mk_string_unchecked("Sat", 3, 3);
x_207 = lean_mk_string_unchecked("AIG", 3, 3);
x_208 = lean_mk_string_unchecked("term⟦_,_⟧", 13, 9);
x_209 = l_Lean_Name_mkStr4(x_205, x_206, x_207, x_208);
x_210 = lean_mk_string_unchecked("⟦", 3, 1);
lean_inc(x_204);
x_211 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_211, 0, x_204);
lean_ctor_set(x_211, 1, x_210);
x_212 = lean_mk_string_unchecked(",", 1, 1);
lean_inc(x_204);
x_213 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_213, 0, x_204);
lean_ctor_set(x_213, 1, x_212);
x_214 = lean_mk_string_unchecked("⟧", 3, 1);
lean_inc(x_204);
x_215 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_215, 0, x_204);
lean_ctor_set(x_215, 1, x_214);
x_216 = l_Lean_Syntax_node5(x_204, x_209, x_211, x_19, x_213, x_203, x_215);
x_217 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_217, 0, x_216);
lean_ctor_set(x_217, 1, x_3);
return x_217;
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; uint8_t x_221; 
x_218 = l_Lean_Syntax_getArg(x_166, x_14);
lean_dec(x_166);
x_219 = lean_mk_string_unchecked("structInstFieldDef", 18, 18);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_220 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_219);
lean_inc(x_218);
x_221 = l_Lean_Syntax_isOfKind(x_218, x_220);
if (x_221 == 0)
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; 
lean_dec(x_220);
lean_dec(x_218);
lean_dec(x_113);
lean_dec(x_94);
lean_dec(x_74);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_222 = l_Lean_Syntax_getArg(x_13, x_12);
lean_dec(x_13);
x_223 = l_Lean_SourceInfo_fromRef(x_2, x_221);
x_224 = lean_mk_string_unchecked("Std", 3, 3);
x_225 = lean_mk_string_unchecked("Sat", 3, 3);
x_226 = lean_mk_string_unchecked("AIG", 3, 3);
x_227 = lean_mk_string_unchecked("term⟦_,_⟧", 13, 9);
x_228 = l_Lean_Name_mkStr4(x_224, x_225, x_226, x_227);
x_229 = lean_mk_string_unchecked("⟦", 3, 1);
lean_inc(x_223);
x_230 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_230, 0, x_223);
lean_ctor_set(x_230, 1, x_229);
x_231 = lean_mk_string_unchecked(",", 1, 1);
lean_inc(x_223);
x_232 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_232, 0, x_223);
lean_ctor_set(x_232, 1, x_231);
x_233 = lean_mk_string_unchecked("⟧", 3, 1);
lean_inc(x_223);
x_234 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_234, 0, x_223);
lean_ctor_set(x_234, 1, x_233);
x_235 = l_Lean_Syntax_node5(x_223, x_228, x_230, x_19, x_232, x_222, x_234);
x_236 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_236, 0, x_235);
lean_ctor_set(x_236, 1, x_3);
return x_236;
}
else
{
lean_object* x_237; uint8_t x_238; 
x_237 = l_Lean_Syntax_getArg(x_74, x_14);
lean_inc(x_237);
x_238 = l_Lean_Syntax_isOfKind(x_237, x_94);
if (x_238 == 0)
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; 
lean_dec(x_237);
lean_dec(x_220);
lean_dec(x_218);
lean_dec(x_113);
lean_dec(x_94);
lean_dec(x_74);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_239 = l_Lean_Syntax_getArg(x_13, x_12);
lean_dec(x_13);
x_240 = l_Lean_SourceInfo_fromRef(x_2, x_238);
x_241 = lean_mk_string_unchecked("Std", 3, 3);
x_242 = lean_mk_string_unchecked("Sat", 3, 3);
x_243 = lean_mk_string_unchecked("AIG", 3, 3);
x_244 = lean_mk_string_unchecked("term⟦_,_⟧", 13, 9);
x_245 = l_Lean_Name_mkStr4(x_241, x_242, x_243, x_244);
x_246 = lean_mk_string_unchecked("⟦", 3, 1);
lean_inc(x_240);
x_247 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_247, 0, x_240);
lean_ctor_set(x_247, 1, x_246);
x_248 = lean_mk_string_unchecked(",", 1, 1);
lean_inc(x_240);
x_249 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_249, 0, x_240);
lean_ctor_set(x_249, 1, x_248);
x_250 = lean_mk_string_unchecked("⟧", 3, 1);
lean_inc(x_240);
x_251 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_251, 0, x_240);
lean_ctor_set(x_251, 1, x_250);
x_252 = l_Lean_Syntax_node5(x_240, x_245, x_247, x_19, x_249, x_239, x_251);
x_253 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_253, 0, x_252);
lean_ctor_set(x_253, 1, x_3);
return x_253;
}
else
{
lean_object* x_254; uint8_t x_255; 
x_254 = l_Lean_Syntax_getArg(x_237, x_18);
lean_inc(x_254);
x_255 = l_Lean_Syntax_isOfKind(x_254, x_113);
if (x_255 == 0)
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; 
lean_dec(x_254);
lean_dec(x_237);
lean_dec(x_220);
lean_dec(x_218);
lean_dec(x_113);
lean_dec(x_94);
lean_dec(x_74);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_256 = l_Lean_Syntax_getArg(x_13, x_12);
lean_dec(x_13);
x_257 = l_Lean_SourceInfo_fromRef(x_2, x_255);
x_258 = lean_mk_string_unchecked("Std", 3, 3);
x_259 = lean_mk_string_unchecked("Sat", 3, 3);
x_260 = lean_mk_string_unchecked("AIG", 3, 3);
x_261 = lean_mk_string_unchecked("term⟦_,_⟧", 13, 9);
x_262 = l_Lean_Name_mkStr4(x_258, x_259, x_260, x_261);
x_263 = lean_mk_string_unchecked("⟦", 3, 1);
lean_inc(x_257);
x_264 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_264, 0, x_257);
lean_ctor_set(x_264, 1, x_263);
x_265 = lean_mk_string_unchecked(",", 1, 1);
lean_inc(x_257);
x_266 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_266, 0, x_257);
lean_ctor_set(x_266, 1, x_265);
x_267 = lean_mk_string_unchecked("⟧", 3, 1);
lean_inc(x_257);
x_268 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_268, 0, x_257);
lean_ctor_set(x_268, 1, x_267);
x_269 = l_Lean_Syntax_node5(x_257, x_262, x_264, x_19, x_266, x_256, x_268);
x_270 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_270, 0, x_269);
lean_ctor_set(x_270, 1, x_3);
return x_270;
}
else
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; uint8_t x_274; 
x_271 = l_Lean_Syntax_getArg(x_254, x_18);
x_272 = lean_mk_string_unchecked("start", 5, 5);
x_273 = l_Lean_Name_mkStr1(x_272);
x_274 = l_Lean_Syntax_matchesIdent(x_271, x_273);
lean_dec(x_271);
if (x_274 == 0)
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; 
lean_dec(x_254);
lean_dec(x_237);
lean_dec(x_220);
lean_dec(x_218);
lean_dec(x_113);
lean_dec(x_94);
lean_dec(x_74);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_275 = l_Lean_Syntax_getArg(x_13, x_12);
lean_dec(x_13);
x_276 = l_Lean_SourceInfo_fromRef(x_2, x_274);
x_277 = lean_mk_string_unchecked("Std", 3, 3);
x_278 = lean_mk_string_unchecked("Sat", 3, 3);
x_279 = lean_mk_string_unchecked("AIG", 3, 3);
x_280 = lean_mk_string_unchecked("term⟦_,_⟧", 13, 9);
x_281 = l_Lean_Name_mkStr4(x_277, x_278, x_279, x_280);
x_282 = lean_mk_string_unchecked("⟦", 3, 1);
lean_inc(x_276);
x_283 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_283, 0, x_276);
lean_ctor_set(x_283, 1, x_282);
x_284 = lean_mk_string_unchecked(",", 1, 1);
lean_inc(x_276);
x_285 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_285, 0, x_276);
lean_ctor_set(x_285, 1, x_284);
x_286 = lean_mk_string_unchecked("⟧", 3, 1);
lean_inc(x_276);
x_287 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_287, 0, x_276);
lean_ctor_set(x_287, 1, x_286);
x_288 = l_Lean_Syntax_node5(x_276, x_281, x_283, x_19, x_285, x_275, x_287);
x_289 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_289, 0, x_288);
lean_ctor_set(x_289, 1, x_3);
return x_289;
}
else
{
lean_object* x_290; uint8_t x_291; 
x_290 = l_Lean_Syntax_getArg(x_254, x_12);
lean_dec(x_254);
x_291 = l_Lean_Syntax_matchesNull(x_290, x_18);
if (x_291 == 0)
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; 
lean_dec(x_237);
lean_dec(x_220);
lean_dec(x_218);
lean_dec(x_113);
lean_dec(x_94);
lean_dec(x_74);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_292 = l_Lean_Syntax_getArg(x_13, x_12);
lean_dec(x_13);
x_293 = l_Lean_SourceInfo_fromRef(x_2, x_291);
x_294 = lean_mk_string_unchecked("Std", 3, 3);
x_295 = lean_mk_string_unchecked("Sat", 3, 3);
x_296 = lean_mk_string_unchecked("AIG", 3, 3);
x_297 = lean_mk_string_unchecked("term⟦_,_⟧", 13, 9);
x_298 = l_Lean_Name_mkStr4(x_294, x_295, x_296, x_297);
x_299 = lean_mk_string_unchecked("⟦", 3, 1);
lean_inc(x_293);
x_300 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_300, 0, x_293);
lean_ctor_set(x_300, 1, x_299);
x_301 = lean_mk_string_unchecked(",", 1, 1);
lean_inc(x_293);
x_302 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_302, 0, x_293);
lean_ctor_set(x_302, 1, x_301);
x_303 = lean_mk_string_unchecked("⟧", 3, 1);
lean_inc(x_293);
x_304 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_304, 0, x_293);
lean_ctor_set(x_304, 1, x_303);
x_305 = l_Lean_Syntax_node5(x_293, x_298, x_300, x_19, x_302, x_292, x_304);
x_306 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_306, 0, x_305);
lean_ctor_set(x_306, 1, x_3);
return x_306;
}
else
{
lean_object* x_307; uint8_t x_308; 
x_307 = l_Lean_Syntax_getArg(x_237, x_12);
lean_dec(x_237);
lean_inc(x_307);
x_308 = l_Lean_Syntax_matchesNull(x_307, x_167);
if (x_308 == 0)
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; 
lean_dec(x_307);
lean_dec(x_220);
lean_dec(x_218);
lean_dec(x_113);
lean_dec(x_94);
lean_dec(x_74);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_309 = l_Lean_Syntax_getArg(x_13, x_12);
lean_dec(x_13);
x_310 = l_Lean_SourceInfo_fromRef(x_2, x_308);
x_311 = lean_mk_string_unchecked("Std", 3, 3);
x_312 = lean_mk_string_unchecked("Sat", 3, 3);
x_313 = lean_mk_string_unchecked("AIG", 3, 3);
x_314 = lean_mk_string_unchecked("term⟦_,_⟧", 13, 9);
x_315 = l_Lean_Name_mkStr4(x_311, x_312, x_313, x_314);
x_316 = lean_mk_string_unchecked("⟦", 3, 1);
lean_inc(x_310);
x_317 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_317, 0, x_310);
lean_ctor_set(x_317, 1, x_316);
x_318 = lean_mk_string_unchecked(",", 1, 1);
lean_inc(x_310);
x_319 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_319, 0, x_310);
lean_ctor_set(x_319, 1, x_318);
x_320 = lean_mk_string_unchecked("⟧", 3, 1);
lean_inc(x_310);
x_321 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_321, 0, x_310);
lean_ctor_set(x_321, 1, x_320);
x_322 = l_Lean_Syntax_node5(x_310, x_315, x_317, x_19, x_319, x_309, x_321);
x_323 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_323, 0, x_322);
lean_ctor_set(x_323, 1, x_3);
return x_323;
}
else
{
lean_object* x_324; uint8_t x_325; 
x_324 = l_Lean_Syntax_getArg(x_307, x_18);
x_325 = l_Lean_Syntax_matchesNull(x_324, x_18);
if (x_325 == 0)
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; 
lean_dec(x_307);
lean_dec(x_220);
lean_dec(x_218);
lean_dec(x_113);
lean_dec(x_94);
lean_dec(x_74);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_326 = l_Lean_Syntax_getArg(x_13, x_12);
lean_dec(x_13);
x_327 = l_Lean_SourceInfo_fromRef(x_2, x_325);
x_328 = lean_mk_string_unchecked("Std", 3, 3);
x_329 = lean_mk_string_unchecked("Sat", 3, 3);
x_330 = lean_mk_string_unchecked("AIG", 3, 3);
x_331 = lean_mk_string_unchecked("term⟦_,_⟧", 13, 9);
x_332 = l_Lean_Name_mkStr4(x_328, x_329, x_330, x_331);
x_333 = lean_mk_string_unchecked("⟦", 3, 1);
lean_inc(x_327);
x_334 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_334, 0, x_327);
lean_ctor_set(x_334, 1, x_333);
x_335 = lean_mk_string_unchecked(",", 1, 1);
lean_inc(x_327);
x_336 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_336, 0, x_327);
lean_ctor_set(x_336, 1, x_335);
x_337 = lean_mk_string_unchecked("⟧", 3, 1);
lean_inc(x_327);
x_338 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_338, 0, x_327);
lean_ctor_set(x_338, 1, x_337);
x_339 = l_Lean_Syntax_node5(x_327, x_332, x_334, x_19, x_336, x_326, x_338);
x_340 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_340, 0, x_339);
lean_ctor_set(x_340, 1, x_3);
return x_340;
}
else
{
lean_object* x_341; uint8_t x_342; 
x_341 = l_Lean_Syntax_getArg(x_307, x_12);
x_342 = l_Lean_Syntax_matchesNull(x_341, x_18);
if (x_342 == 0)
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; 
lean_dec(x_307);
lean_dec(x_220);
lean_dec(x_218);
lean_dec(x_113);
lean_dec(x_94);
lean_dec(x_74);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_343 = l_Lean_Syntax_getArg(x_13, x_12);
lean_dec(x_13);
x_344 = l_Lean_SourceInfo_fromRef(x_2, x_342);
x_345 = lean_mk_string_unchecked("Std", 3, 3);
x_346 = lean_mk_string_unchecked("Sat", 3, 3);
x_347 = lean_mk_string_unchecked("AIG", 3, 3);
x_348 = lean_mk_string_unchecked("term⟦_,_⟧", 13, 9);
x_349 = l_Lean_Name_mkStr4(x_345, x_346, x_347, x_348);
x_350 = lean_mk_string_unchecked("⟦", 3, 1);
lean_inc(x_344);
x_351 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_351, 0, x_344);
lean_ctor_set(x_351, 1, x_350);
x_352 = lean_mk_string_unchecked(",", 1, 1);
lean_inc(x_344);
x_353 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_353, 0, x_344);
lean_ctor_set(x_353, 1, x_352);
x_354 = lean_mk_string_unchecked("⟧", 3, 1);
lean_inc(x_344);
x_355 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_355, 0, x_344);
lean_ctor_set(x_355, 1, x_354);
x_356 = l_Lean_Syntax_node5(x_344, x_349, x_351, x_19, x_353, x_343, x_355);
x_357 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_357, 0, x_356);
lean_ctor_set(x_357, 1, x_3);
return x_357;
}
else
{
lean_object* x_358; uint8_t x_359; 
x_358 = l_Lean_Syntax_getArg(x_307, x_14);
lean_dec(x_307);
lean_inc(x_358);
x_359 = l_Lean_Syntax_isOfKind(x_358, x_220);
if (x_359 == 0)
{
lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; 
lean_dec(x_358);
lean_dec(x_220);
lean_dec(x_218);
lean_dec(x_113);
lean_dec(x_94);
lean_dec(x_74);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_360 = l_Lean_Syntax_getArg(x_13, x_12);
lean_dec(x_13);
x_361 = l_Lean_SourceInfo_fromRef(x_2, x_359);
x_362 = lean_mk_string_unchecked("Std", 3, 3);
x_363 = lean_mk_string_unchecked("Sat", 3, 3);
x_364 = lean_mk_string_unchecked("AIG", 3, 3);
x_365 = lean_mk_string_unchecked("term⟦_,_⟧", 13, 9);
x_366 = l_Lean_Name_mkStr4(x_362, x_363, x_364, x_365);
x_367 = lean_mk_string_unchecked("⟦", 3, 1);
lean_inc(x_361);
x_368 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_368, 0, x_361);
lean_ctor_set(x_368, 1, x_367);
x_369 = lean_mk_string_unchecked(",", 1, 1);
lean_inc(x_361);
x_370 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_370, 0, x_361);
lean_ctor_set(x_370, 1, x_369);
x_371 = lean_mk_string_unchecked("⟧", 3, 1);
lean_inc(x_361);
x_372 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_372, 0, x_361);
lean_ctor_set(x_372, 1, x_371);
x_373 = l_Lean_Syntax_node5(x_361, x_366, x_368, x_19, x_370, x_360, x_372);
x_374 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_374, 0, x_373);
lean_ctor_set(x_374, 1, x_3);
return x_374;
}
else
{
lean_object* x_375; lean_object* x_376; uint8_t x_377; 
x_375 = lean_unsigned_to_nat(4u);
x_376 = l_Lean_Syntax_getArg(x_74, x_375);
lean_dec(x_74);
lean_inc(x_376);
x_377 = l_Lean_Syntax_isOfKind(x_376, x_94);
lean_dec(x_94);
if (x_377 == 0)
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; 
lean_dec(x_376);
lean_dec(x_358);
lean_dec(x_220);
lean_dec(x_218);
lean_dec(x_113);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_378 = l_Lean_Syntax_getArg(x_13, x_12);
lean_dec(x_13);
x_379 = l_Lean_SourceInfo_fromRef(x_2, x_377);
x_380 = lean_mk_string_unchecked("Std", 3, 3);
x_381 = lean_mk_string_unchecked("Sat", 3, 3);
x_382 = lean_mk_string_unchecked("AIG", 3, 3);
x_383 = lean_mk_string_unchecked("term⟦_,_⟧", 13, 9);
x_384 = l_Lean_Name_mkStr4(x_380, x_381, x_382, x_383);
x_385 = lean_mk_string_unchecked("⟦", 3, 1);
lean_inc(x_379);
x_386 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_386, 0, x_379);
lean_ctor_set(x_386, 1, x_385);
x_387 = lean_mk_string_unchecked(",", 1, 1);
lean_inc(x_379);
x_388 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_388, 0, x_379);
lean_ctor_set(x_388, 1, x_387);
x_389 = lean_mk_string_unchecked("⟧", 3, 1);
lean_inc(x_379);
x_390 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_390, 0, x_379);
lean_ctor_set(x_390, 1, x_389);
x_391 = l_Lean_Syntax_node5(x_379, x_384, x_386, x_19, x_388, x_378, x_390);
x_392 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_392, 0, x_391);
lean_ctor_set(x_392, 1, x_3);
return x_392;
}
else
{
lean_object* x_393; uint8_t x_394; 
x_393 = l_Lean_Syntax_getArg(x_376, x_18);
lean_inc(x_393);
x_394 = l_Lean_Syntax_isOfKind(x_393, x_113);
lean_dec(x_113);
if (x_394 == 0)
{
lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; 
lean_dec(x_393);
lean_dec(x_376);
lean_dec(x_358);
lean_dec(x_220);
lean_dec(x_218);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_395 = l_Lean_Syntax_getArg(x_13, x_12);
lean_dec(x_13);
x_396 = l_Lean_SourceInfo_fromRef(x_2, x_394);
x_397 = lean_mk_string_unchecked("Std", 3, 3);
x_398 = lean_mk_string_unchecked("Sat", 3, 3);
x_399 = lean_mk_string_unchecked("AIG", 3, 3);
x_400 = lean_mk_string_unchecked("term⟦_,_⟧", 13, 9);
x_401 = l_Lean_Name_mkStr4(x_397, x_398, x_399, x_400);
x_402 = lean_mk_string_unchecked("⟦", 3, 1);
lean_inc(x_396);
x_403 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_403, 0, x_396);
lean_ctor_set(x_403, 1, x_402);
x_404 = lean_mk_string_unchecked(",", 1, 1);
lean_inc(x_396);
x_405 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_405, 0, x_396);
lean_ctor_set(x_405, 1, x_404);
x_406 = lean_mk_string_unchecked("⟧", 3, 1);
lean_inc(x_396);
x_407 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_407, 0, x_396);
lean_ctor_set(x_407, 1, x_406);
x_408 = l_Lean_Syntax_node5(x_396, x_401, x_403, x_19, x_405, x_395, x_407);
x_409 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_409, 0, x_408);
lean_ctor_set(x_409, 1, x_3);
return x_409;
}
else
{
lean_object* x_410; lean_object* x_411; lean_object* x_412; uint8_t x_413; 
x_410 = l_Lean_Syntax_getArg(x_393, x_18);
x_411 = lean_mk_string_unchecked("inv", 3, 3);
x_412 = l_Lean_Name_mkStr1(x_411);
x_413 = l_Lean_Syntax_matchesIdent(x_410, x_412);
lean_dec(x_410);
if (x_413 == 0)
{
lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; 
lean_dec(x_393);
lean_dec(x_376);
lean_dec(x_358);
lean_dec(x_220);
lean_dec(x_218);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_414 = l_Lean_Syntax_getArg(x_13, x_12);
lean_dec(x_13);
x_415 = l_Lean_SourceInfo_fromRef(x_2, x_413);
x_416 = lean_mk_string_unchecked("Std", 3, 3);
x_417 = lean_mk_string_unchecked("Sat", 3, 3);
x_418 = lean_mk_string_unchecked("AIG", 3, 3);
x_419 = lean_mk_string_unchecked("term⟦_,_⟧", 13, 9);
x_420 = l_Lean_Name_mkStr4(x_416, x_417, x_418, x_419);
x_421 = lean_mk_string_unchecked("⟦", 3, 1);
lean_inc(x_415);
x_422 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_422, 0, x_415);
lean_ctor_set(x_422, 1, x_421);
x_423 = lean_mk_string_unchecked(",", 1, 1);
lean_inc(x_415);
x_424 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_424, 0, x_415);
lean_ctor_set(x_424, 1, x_423);
x_425 = lean_mk_string_unchecked("⟧", 3, 1);
lean_inc(x_415);
x_426 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_426, 0, x_415);
lean_ctor_set(x_426, 1, x_425);
x_427 = l_Lean_Syntax_node5(x_415, x_420, x_422, x_19, x_424, x_414, x_426);
x_428 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_428, 0, x_427);
lean_ctor_set(x_428, 1, x_3);
return x_428;
}
else
{
lean_object* x_429; uint8_t x_430; 
x_429 = l_Lean_Syntax_getArg(x_393, x_12);
lean_dec(x_393);
x_430 = l_Lean_Syntax_matchesNull(x_429, x_18);
if (x_430 == 0)
{
lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; 
lean_dec(x_376);
lean_dec(x_358);
lean_dec(x_220);
lean_dec(x_218);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_431 = l_Lean_Syntax_getArg(x_13, x_12);
lean_dec(x_13);
x_432 = l_Lean_SourceInfo_fromRef(x_2, x_430);
x_433 = lean_mk_string_unchecked("Std", 3, 3);
x_434 = lean_mk_string_unchecked("Sat", 3, 3);
x_435 = lean_mk_string_unchecked("AIG", 3, 3);
x_436 = lean_mk_string_unchecked("term⟦_,_⟧", 13, 9);
x_437 = l_Lean_Name_mkStr4(x_433, x_434, x_435, x_436);
x_438 = lean_mk_string_unchecked("⟦", 3, 1);
lean_inc(x_432);
x_439 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_439, 0, x_432);
lean_ctor_set(x_439, 1, x_438);
x_440 = lean_mk_string_unchecked(",", 1, 1);
lean_inc(x_432);
x_441 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_441, 0, x_432);
lean_ctor_set(x_441, 1, x_440);
x_442 = lean_mk_string_unchecked("⟧", 3, 1);
lean_inc(x_432);
x_443 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_443, 0, x_432);
lean_ctor_set(x_443, 1, x_442);
x_444 = l_Lean_Syntax_node5(x_432, x_437, x_439, x_19, x_441, x_431, x_443);
x_445 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_445, 0, x_444);
lean_ctor_set(x_445, 1, x_3);
return x_445;
}
else
{
lean_object* x_446; uint8_t x_447; 
x_446 = l_Lean_Syntax_getArg(x_376, x_12);
lean_dec(x_376);
lean_inc(x_446);
x_447 = l_Lean_Syntax_matchesNull(x_446, x_167);
if (x_447 == 0)
{
lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; 
lean_dec(x_446);
lean_dec(x_358);
lean_dec(x_220);
lean_dec(x_218);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_448 = l_Lean_Syntax_getArg(x_13, x_12);
lean_dec(x_13);
x_449 = l_Lean_SourceInfo_fromRef(x_2, x_447);
x_450 = lean_mk_string_unchecked("Std", 3, 3);
x_451 = lean_mk_string_unchecked("Sat", 3, 3);
x_452 = lean_mk_string_unchecked("AIG", 3, 3);
x_453 = lean_mk_string_unchecked("term⟦_,_⟧", 13, 9);
x_454 = l_Lean_Name_mkStr4(x_450, x_451, x_452, x_453);
x_455 = lean_mk_string_unchecked("⟦", 3, 1);
lean_inc(x_449);
x_456 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_456, 0, x_449);
lean_ctor_set(x_456, 1, x_455);
x_457 = lean_mk_string_unchecked(",", 1, 1);
lean_inc(x_449);
x_458 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_458, 0, x_449);
lean_ctor_set(x_458, 1, x_457);
x_459 = lean_mk_string_unchecked("⟧", 3, 1);
lean_inc(x_449);
x_460 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_460, 0, x_449);
lean_ctor_set(x_460, 1, x_459);
x_461 = l_Lean_Syntax_node5(x_449, x_454, x_456, x_19, x_458, x_448, x_460);
x_462 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_462, 0, x_461);
lean_ctor_set(x_462, 1, x_3);
return x_462;
}
else
{
lean_object* x_463; uint8_t x_464; 
x_463 = l_Lean_Syntax_getArg(x_446, x_18);
x_464 = l_Lean_Syntax_matchesNull(x_463, x_18);
if (x_464 == 0)
{
lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; 
lean_dec(x_446);
lean_dec(x_358);
lean_dec(x_220);
lean_dec(x_218);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_465 = l_Lean_Syntax_getArg(x_13, x_12);
lean_dec(x_13);
x_466 = l_Lean_SourceInfo_fromRef(x_2, x_464);
x_467 = lean_mk_string_unchecked("Std", 3, 3);
x_468 = lean_mk_string_unchecked("Sat", 3, 3);
x_469 = lean_mk_string_unchecked("AIG", 3, 3);
x_470 = lean_mk_string_unchecked("term⟦_,_⟧", 13, 9);
x_471 = l_Lean_Name_mkStr4(x_467, x_468, x_469, x_470);
x_472 = lean_mk_string_unchecked("⟦", 3, 1);
lean_inc(x_466);
x_473 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_473, 0, x_466);
lean_ctor_set(x_473, 1, x_472);
x_474 = lean_mk_string_unchecked(",", 1, 1);
lean_inc(x_466);
x_475 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_475, 0, x_466);
lean_ctor_set(x_475, 1, x_474);
x_476 = lean_mk_string_unchecked("⟧", 3, 1);
lean_inc(x_466);
x_477 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_477, 0, x_466);
lean_ctor_set(x_477, 1, x_476);
x_478 = l_Lean_Syntax_node5(x_466, x_471, x_473, x_19, x_475, x_465, x_477);
x_479 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_479, 0, x_478);
lean_ctor_set(x_479, 1, x_3);
return x_479;
}
else
{
lean_object* x_480; uint8_t x_481; 
x_480 = l_Lean_Syntax_getArg(x_446, x_12);
x_481 = l_Lean_Syntax_matchesNull(x_480, x_18);
if (x_481 == 0)
{
lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; 
lean_dec(x_446);
lean_dec(x_358);
lean_dec(x_220);
lean_dec(x_218);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_482 = l_Lean_Syntax_getArg(x_13, x_12);
lean_dec(x_13);
x_483 = l_Lean_SourceInfo_fromRef(x_2, x_481);
x_484 = lean_mk_string_unchecked("Std", 3, 3);
x_485 = lean_mk_string_unchecked("Sat", 3, 3);
x_486 = lean_mk_string_unchecked("AIG", 3, 3);
x_487 = lean_mk_string_unchecked("term⟦_,_⟧", 13, 9);
x_488 = l_Lean_Name_mkStr4(x_484, x_485, x_486, x_487);
x_489 = lean_mk_string_unchecked("⟦", 3, 1);
lean_inc(x_483);
x_490 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_490, 0, x_483);
lean_ctor_set(x_490, 1, x_489);
x_491 = lean_mk_string_unchecked(",", 1, 1);
lean_inc(x_483);
x_492 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_492, 0, x_483);
lean_ctor_set(x_492, 1, x_491);
x_493 = lean_mk_string_unchecked("⟧", 3, 1);
lean_inc(x_483);
x_494 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_494, 0, x_483);
lean_ctor_set(x_494, 1, x_493);
x_495 = l_Lean_Syntax_node5(x_483, x_488, x_490, x_19, x_492, x_482, x_494);
x_496 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_496, 0, x_495);
lean_ctor_set(x_496, 1, x_3);
return x_496;
}
else
{
lean_object* x_497; uint8_t x_498; 
x_497 = l_Lean_Syntax_getArg(x_446, x_14);
lean_dec(x_446);
lean_inc(x_497);
x_498 = l_Lean_Syntax_isOfKind(x_497, x_220);
lean_dec(x_220);
if (x_498 == 0)
{
lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; 
lean_dec(x_497);
lean_dec(x_358);
lean_dec(x_218);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_499 = l_Lean_Syntax_getArg(x_13, x_12);
lean_dec(x_13);
x_500 = l_Lean_SourceInfo_fromRef(x_2, x_498);
x_501 = lean_mk_string_unchecked("Std", 3, 3);
x_502 = lean_mk_string_unchecked("Sat", 3, 3);
x_503 = lean_mk_string_unchecked("AIG", 3, 3);
x_504 = lean_mk_string_unchecked("term⟦_,_⟧", 13, 9);
x_505 = l_Lean_Name_mkStr4(x_501, x_502, x_503, x_504);
x_506 = lean_mk_string_unchecked("⟦", 3, 1);
lean_inc(x_500);
x_507 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_507, 0, x_500);
lean_ctor_set(x_507, 1, x_506);
x_508 = lean_mk_string_unchecked(",", 1, 1);
lean_inc(x_500);
x_509 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_509, 0, x_500);
lean_ctor_set(x_509, 1, x_508);
x_510 = lean_mk_string_unchecked("⟧", 3, 1);
lean_inc(x_500);
x_511 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_511, 0, x_500);
lean_ctor_set(x_511, 1, x_510);
x_512 = l_Lean_Syntax_node5(x_500, x_505, x_507, x_19, x_509, x_499, x_511);
x_513 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_513, 0, x_512);
lean_ctor_set(x_513, 1, x_3);
return x_513;
}
else
{
lean_object* x_514; lean_object* x_515; lean_object* x_516; uint8_t x_517; 
x_514 = l_Lean_Syntax_getArg(x_19, x_167);
x_515 = lean_mk_string_unchecked("optEllipsis", 11, 11);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_516 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_515);
lean_inc(x_514);
x_517 = l_Lean_Syntax_isOfKind(x_514, x_516);
lean_dec(x_516);
if (x_517 == 0)
{
lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; 
lean_dec(x_514);
lean_dec(x_497);
lean_dec(x_358);
lean_dec(x_218);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_518 = l_Lean_Syntax_getArg(x_13, x_12);
lean_dec(x_13);
x_519 = l_Lean_SourceInfo_fromRef(x_2, x_517);
x_520 = lean_mk_string_unchecked("Std", 3, 3);
x_521 = lean_mk_string_unchecked("Sat", 3, 3);
x_522 = lean_mk_string_unchecked("AIG", 3, 3);
x_523 = lean_mk_string_unchecked("term⟦_,_⟧", 13, 9);
x_524 = l_Lean_Name_mkStr4(x_520, x_521, x_522, x_523);
x_525 = lean_mk_string_unchecked("⟦", 3, 1);
lean_inc(x_519);
x_526 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_526, 0, x_519);
lean_ctor_set(x_526, 1, x_525);
x_527 = lean_mk_string_unchecked(",", 1, 1);
lean_inc(x_519);
x_528 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_528, 0, x_519);
lean_ctor_set(x_528, 1, x_527);
x_529 = lean_mk_string_unchecked("⟧", 3, 1);
lean_inc(x_519);
x_530 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_530, 0, x_519);
lean_ctor_set(x_530, 1, x_529);
x_531 = l_Lean_Syntax_node5(x_519, x_524, x_526, x_19, x_528, x_518, x_530);
x_532 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_532, 0, x_531);
lean_ctor_set(x_532, 1, x_3);
return x_532;
}
else
{
lean_object* x_533; uint8_t x_534; 
x_533 = l_Lean_Syntax_getArg(x_514, x_18);
lean_dec(x_514);
x_534 = l_Lean_Syntax_matchesNull(x_533, x_18);
if (x_534 == 0)
{
lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; 
lean_dec(x_497);
lean_dec(x_358);
lean_dec(x_218);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_535 = l_Lean_Syntax_getArg(x_13, x_12);
lean_dec(x_13);
x_536 = l_Lean_SourceInfo_fromRef(x_2, x_534);
x_537 = lean_mk_string_unchecked("Std", 3, 3);
x_538 = lean_mk_string_unchecked("Sat", 3, 3);
x_539 = lean_mk_string_unchecked("AIG", 3, 3);
x_540 = lean_mk_string_unchecked("term⟦_,_⟧", 13, 9);
x_541 = l_Lean_Name_mkStr4(x_537, x_538, x_539, x_540);
x_542 = lean_mk_string_unchecked("⟦", 3, 1);
lean_inc(x_536);
x_543 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_543, 0, x_536);
lean_ctor_set(x_543, 1, x_542);
x_544 = lean_mk_string_unchecked(",", 1, 1);
lean_inc(x_536);
x_545 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_545, 0, x_536);
lean_ctor_set(x_545, 1, x_544);
x_546 = lean_mk_string_unchecked("⟧", 3, 1);
lean_inc(x_536);
x_547 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_547, 0, x_536);
lean_ctor_set(x_547, 1, x_546);
x_548 = l_Lean_Syntax_node5(x_536, x_541, x_543, x_19, x_545, x_535, x_547);
x_549 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_549, 0, x_548);
lean_ctor_set(x_549, 1, x_3);
return x_549;
}
else
{
lean_object* x_550; uint8_t x_551; 
x_550 = l_Lean_Syntax_getArg(x_19, x_375);
x_551 = l_Lean_Syntax_matchesNull(x_550, x_18);
if (x_551 == 0)
{
lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; 
lean_dec(x_497);
lean_dec(x_358);
lean_dec(x_218);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_552 = l_Lean_Syntax_getArg(x_13, x_12);
lean_dec(x_13);
x_553 = l_Lean_SourceInfo_fromRef(x_2, x_551);
x_554 = lean_mk_string_unchecked("Std", 3, 3);
x_555 = lean_mk_string_unchecked("Sat", 3, 3);
x_556 = lean_mk_string_unchecked("AIG", 3, 3);
x_557 = lean_mk_string_unchecked("term⟦_,_⟧", 13, 9);
x_558 = l_Lean_Name_mkStr4(x_554, x_555, x_556, x_557);
x_559 = lean_mk_string_unchecked("⟦", 3, 1);
lean_inc(x_553);
x_560 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_560, 0, x_553);
lean_ctor_set(x_560, 1, x_559);
x_561 = lean_mk_string_unchecked(",", 1, 1);
lean_inc(x_553);
x_562 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_562, 0, x_553);
lean_ctor_set(x_562, 1, x_561);
x_563 = lean_mk_string_unchecked("⟧", 3, 1);
lean_inc(x_553);
x_564 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_564, 0, x_553);
lean_ctor_set(x_564, 1, x_563);
x_565 = l_Lean_Syntax_node5(x_553, x_558, x_560, x_19, x_562, x_552, x_564);
x_566 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_566, 0, x_565);
lean_ctor_set(x_566, 1, x_3);
return x_566;
}
else
{
lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; uint8_t x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; 
lean_dec(x_19);
x_567 = l_Lean_Syntax_getArg(x_218, x_12);
lean_dec(x_218);
x_568 = l_Lean_Syntax_getArg(x_358, x_12);
lean_dec(x_358);
x_569 = l_Lean_Syntax_getArg(x_497, x_12);
lean_dec(x_497);
x_570 = l_Lean_Syntax_getArg(x_13, x_12);
lean_dec(x_13);
x_571 = lean_box(0);
x_572 = lean_unbox(x_571);
x_573 = l_Lean_SourceInfo_fromRef(x_2, x_572);
x_574 = lean_mk_string_unchecked("Std", 3, 3);
x_575 = lean_mk_string_unchecked("Sat", 3, 3);
x_576 = lean_mk_string_unchecked("AIG", 3, 3);
x_577 = lean_mk_string_unchecked("term⟦_,_,_⟧", 15, 11);
x_578 = l_Lean_Name_mkStr4(x_574, x_575, x_576, x_577);
x_579 = lean_mk_string_unchecked("⟦", 3, 1);
lean_inc(x_573);
x_580 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_580, 0, x_573);
lean_ctor_set(x_580, 1, x_579);
x_581 = lean_mk_string_unchecked(",", 1, 1);
lean_inc(x_573);
x_582 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_582, 0, x_573);
lean_ctor_set(x_582, 1, x_581);
x_583 = lean_mk_string_unchecked("anonymousCtor", 13, 13);
x_584 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_583);
x_585 = lean_mk_string_unchecked("⟨", 3, 1);
lean_inc(x_573);
x_586 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_586, 0, x_573);
lean_ctor_set(x_586, 1, x_585);
x_587 = lean_mk_string_unchecked("null", 4, 4);
x_588 = l_Lean_Name_mkStr1(x_587);
lean_inc(x_582);
lean_inc(x_573);
x_589 = l_Lean_Syntax_node3(x_573, x_588, x_568, x_582, x_569);
x_590 = lean_mk_string_unchecked("⟩", 3, 1);
lean_inc(x_573);
x_591 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_591, 0, x_573);
lean_ctor_set(x_591, 1, x_590);
lean_inc(x_573);
x_592 = l_Lean_Syntax_node3(x_573, x_584, x_586, x_589, x_591);
x_593 = lean_mk_string_unchecked("⟧", 3, 1);
lean_inc(x_573);
x_594 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_594, 0, x_573);
lean_ctor_set(x_594, 1, x_593);
lean_inc(x_582);
x_595 = l_Lean_Syntax_node7(x_573, x_578, x_580, x_567, x_582, x_592, x_582, x_570, x_594);
x_596 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_596, 0, x_595);
lean_ctor_set(x_596, 1, x_3);
return x_596;
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_unexpandDenote___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Sat_AIG_unexpandDenote(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGate___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_array_get_size(x_3);
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_5, 0);
x_7 = lean_ctor_get_uint8(x_5, sizeof(void*)*1);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_shiftl(x_6, x_8);
x_10 = l_Bool_toNat(x_7);
x_11 = lean_nat_lor(x_9, x_10);
lean_dec(x_10);
lean_dec(x_9);
x_12 = lean_ctor_get(x_2, 1);
x_13 = lean_ctor_get(x_12, 0);
x_14 = lean_ctor_get_uint8(x_12, sizeof(void*)*1);
x_15 = lean_nat_shiftl(x_13, x_8);
x_16 = l_Bool_toNat(x_14);
x_17 = lean_nat_lor(x_15, x_16);
lean_dec(x_16);
lean_dec(x_15);
x_18 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_array_push(x_3, x_18);
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
lean_dec(x_1);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_23, 0, x_4);
x_24 = lean_unbox(x_22);
lean_ctor_set_uint8(x_23, sizeof(void*)*1, x_24);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_21);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGate(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Sat_AIG_mkGate___redArg(x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGate___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Sat_AIG_mkGate___redArg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGate___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Sat_AIG_mkGate(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkAtom___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_array_get_size(x_3);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_2);
x_6 = lean_array_push(x_3, x_5);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_10, 0, x_4);
x_11 = lean_unbox(x_9);
lean_ctor_set_uint8(x_10, sizeof(void*)*1, x_11);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkAtom(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Sat_AIG_mkAtom___redArg(x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkAtom___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Sat_AIG_mkAtom(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkConst___redArg(lean_object* x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_array_get_size(x_3);
x_5 = lean_box(0);
x_6 = lean_array_push(x_3, x_5);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set_uint8(x_9, sizeof(void*)*1, x_2);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkConst(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Sat_AIG_mkConst___redArg(x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkConst___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
lean_dec(x_2);
x_4 = l_Std_Sat_AIG_mkConst___redArg(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkConst___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_5);
lean_dec(x_5);
x_7 = l_Std_Sat_AIG_mkConst(x_1, x_2, x_3, x_4, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_AIG_isConstant___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_12; lean_object* x_13; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_array_fget(x_6, x_4);
x_12 = lean_box(1);
x_13 = lean_box(0);
if (x_5 == 0)
{
if (x_3 == 0)
{
uint8_t x_14; 
x_14 = lean_unbox(x_12);
x_8 = x_14;
goto block_11;
}
else
{
uint8_t x_15; 
x_15 = lean_unbox(x_13);
x_8 = x_15;
goto block_11;
}
}
else
{
if (x_3 == 0)
{
uint8_t x_16; 
x_16 = lean_unbox(x_13);
x_8 = x_16;
goto block_11;
}
else
{
uint8_t x_17; 
x_17 = lean_unbox(x_12);
x_8 = x_17;
goto block_11;
}
}
block_11:
{
if (lean_obj_tag(x_7) == 0)
{
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
lean_dec(x_7);
x_9 = lean_box(0);
x_10 = lean_unbox(x_9);
return x_10;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_Sat_AIG_isConstant(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6) {
_start:
{
uint8_t x_7; 
x_7 = l_Std_Sat_AIG_isConstant___redArg(x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_isConstant___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_3);
lean_dec(x_3);
x_5 = l_Std_Sat_AIG_isConstant___redArg(x_1, x_2, x_4);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_isConstant___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; uint8_t x_8; lean_object* x_9; 
x_7 = lean_unbox(x_6);
lean_dec(x_6);
x_8 = l_Std_Sat_AIG_isConstant(x_1, x_2, x_3, x_4, x_5, x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_getConstant___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_array_fget(x_5, x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(x_4);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_6);
x_9 = lean_box(0);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_getConstant(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Sat_AIG_getConstant___redArg(x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_getConstant___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Sat_AIG_getConstant___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_getConstant___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Sat_AIG_getConstant(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
lean_object* initialize_Std_Data_HashSet(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Vector_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Sat_AIG_Basic(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_HashSet(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Vector_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Sat_AIG_instHashableFanin = _init_l_Std_Sat_AIG_instHashableFanin();
lean_mark_persistent(l_Std_Sat_AIG_instHashableFanin);
l_Std_Sat_AIG_instReprFanin = _init_l_Std_Sat_AIG_instReprFanin();
lean_mark_persistent(l_Std_Sat_AIG_instReprFanin);
l_Std_Sat_AIG_instInhabitedFanin = _init_l_Std_Sat_AIG_instInhabitedFanin();
lean_mark_persistent(l_Std_Sat_AIG_instInhabitedFanin);
l_Std_Sat_AIG_term_u27e6___x2c___u27e7 = _init_l_Std_Sat_AIG_term_u27e6___x2c___u27e7();
lean_mark_persistent(l_Std_Sat_AIG_term_u27e6___x2c___u27e7);
l_Std_Sat_AIG_term_u27e6___x2c___x2c___u27e7 = _init_l_Std_Sat_AIG_term_u27e6___x2c___x2c___u27e7();
lean_mark_persistent(l_Std_Sat_AIG_term_u27e6___x2c___x2c___u27e7);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
