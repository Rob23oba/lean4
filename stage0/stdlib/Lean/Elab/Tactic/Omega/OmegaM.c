// Lean compiler output
// Module: Lean.Elab.Tactic.Omega.OmegaM
// Imports: Init.Omega.LinearCombo Init.Omega.Int Init.Omega.Logic Init.Data.BitVec.Basic Lean.Meta.AppBuilder Lean.Meta.Canonicalizer Std.Data.HashMap.Basic Std.Data.HashSet.Basic
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__8___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_intCast_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___Lean_Elab_Tactic_Omega_lookup_spec__3(lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextFull___at___Lean_Meta_recordSynthPendingFailure_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__5___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_Elab_Tactic_Omega_atoms_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_commitWhen___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Elab_Tactic_Omega_lookup_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atoms___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_lit___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_lookup___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Array_qpartition___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_natCast_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Elab_Tactic_Omega_lookup_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___Lean_Elab_Tactic_Omega_lookup_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f___lam__2(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_Elab_Tactic_Omega_atoms_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__9___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundInt_x3f_op(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundInt_x3f___lam__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Expr_mvar___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_commitWhen(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__10___boxed(lean_object**);
lean_object* l_Lean_Level_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_Elab_Tactic_Omega_atoms_spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_qsort_sort___at___Lean_Elab_Tactic_Omega_atoms_spec__1___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_Omega_atoms_spec__3(lean_object*, size_t, size_t, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f___lam__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atomsList___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_commitWhen___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atoms(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_pow(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_Elab_Tactic_Omega_atoms_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Elab_Tactic_Omega_lookup_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_Elab_Tactic_Omega_atoms_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atoms___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectMVars_visit_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f___lam__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkDecideProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_cfg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_commitWhen___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Elab_Tactic_Omega_lookup_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Elab_Tactic_Omega_lookup_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundInt_x3f___lam__1___boxed(lean_object*, lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_SynthInstance_newSubgoal_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_mkEqReflWithExpectedType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___Lean_Meta_mkAppM_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundInt_x3f___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectMVars_visit_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f_op(lean_object*, lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Tactic_Omega_atoms_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Meta_mkExpectedPropHint(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_withoutModifyingState___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundInt_x3f___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_lookup(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_cfg___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__15___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_withoutModifyingState(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundInt_x3f___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_Elab_Tactic_Omega_atoms_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_withoutModifyingState___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_Elab_Tactic_Omega_lookup_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f___lam__3___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_cfg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkListLit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_withoutModifyingState___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundInt_x3f(lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* l_Int_toNat(lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_SynthInstance_findEntry_x3f_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_Elab_Tactic_Omega_atoms_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundInt_x3f___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_withoutModifyingState___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Elab_Tactic_Omega_lookup_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atomsCoeffs(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_int_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundInt_x3f___lam__1(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atomsList___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f___lam__1(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_instToExprInt_mkNat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Canonicalizer_CanonM_run_x27___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atomsCoeffs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atomsList(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFnArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atoms___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_OmegaM_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_Omega_atoms_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atomsList___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_withoutModifyingState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__12___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_nat_x3f(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_Elab_Tactic_Omega_lookup_spec__4(lean_object*, size_t, size_t, lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Elab_Tactic_Omega_lookup_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundInt_x3f___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Tactic_Omega_atoms_spec__0(size_t, size_t, lean_object*);
lean_object* l_Lean_Meta_Canonicalizer_canon(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_st_mk_ref(x_1, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_st_mk_ref(x_2, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_box(x_5);
lean_inc(x_13);
lean_inc(x_16);
x_19 = lean_apply_10(x_3, x_16, x_13, x_4, x_18, x_6, x_7, x_8, x_9, x_10, x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_st_ref_get(x_16, x_21);
lean_dec(x_16);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_st_ref_get(x_13, x_23);
lean_dec(x_13);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_24, 0);
lean_dec(x_26);
lean_ctor_set(x_24, 0, x_20);
return x_24;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_20);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
else
{
lean_dec(x_16);
lean_dec(x_13);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; 
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
lean_inc(x_14);
x_16 = lean_mk_array(x_14, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_9);
lean_ctor_set(x_17, 1, x_16);
lean_inc_n(x_17, 2);
x_18 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___lam__0___boxed), 11, 4);
lean_closure_set(x_18, 0, x_17);
lean_closure_set(x_18, 1, x_17);
lean_closure_set(x_18, 2, x_1);
lean_closure_set(x_18, 3, x_2);
x_19 = lean_box(3);
x_20 = lean_box(0);
x_21 = lean_mk_array(x_14, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_9);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_17);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_unbox(x_19);
x_25 = l_Lean_Meta_Canonicalizer_CanonM_run_x27___redArg(x_18, x_24, x_23, x_3, x_4, x_5, x_6, x_7);
return x_25;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_OmegaM_run(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_5);
lean_dec(x_5);
x_13 = l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___lam__0(x_1, x_2, x_3, x_4, x_12, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_cfg___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_cfg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_cfg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_4);
lean_dec(x_4);
x_12 = l_Lean_Elab_Tactic_Omega_cfg(x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Tactic_Omega_atoms_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_box(0);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
lean_dec(x_5);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_usize_of_nat(x_9);
x_11 = lean_usize_add(x_2, x_10);
x_12 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_11;
x_3 = x_12;
goto _start;
}
}
}
LEAN_EXPORT uint8_t l_Array_qsort_sort___at___Lean_Elab_Tactic_Omega_atoms_spec__1___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_nat_dec_lt(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_Elab_Tactic_Omega_atoms_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_nat_dec_lt(x_2, x_3);
if (x_4 == 0)
{
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_alloc_closure((void*)(l_Array_qsort_sort___at___Lean_Elab_Tactic_Omega_atoms_spec__1___redArg___lam__0___boxed), 2, 0);
lean_inc(x_2);
x_6 = l_Array_qpartition___redArg(x_1, x_5, x_2, x_3);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_nat_dec_le(x_3, x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l_Array_qsort_sort___at___Lean_Elab_Tactic_Omega_atoms_spec__1___redArg(x_8, x_2, x_7);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_7, x_11);
lean_dec(x_7);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
else
{
lean_dec(x_7);
lean_dec(x_2);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_Elab_Tactic_Omega_atoms_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_qsort_sort___at___Lean_Elab_Tactic_Omega_atoms_spec__1___redArg(x_2, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_Elab_Tactic_Omega_atoms_spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_4);
lean_inc(x_3);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_4);
x_7 = lean_array_push(x_1, x_6);
x_1 = x_7;
x_2 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_Omega_atoms_spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_Elab_Tactic_Omega_atoms_spec__2(x_4, x_6);
lean_dec(x_6);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atoms___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_20; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_3 = lean_st_ref_get(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_6 = x_3;
} else {
 lean_dec_ref(x_3);
 x_6 = lean_box(0);
}
x_28 = lean_ctor_get(x_4, 0);
lean_inc(x_28);
x_29 = lean_mk_empty_array_with_capacity(x_28);
lean_dec(x_28);
x_30 = lean_ctor_get(x_4, 1);
lean_inc(x_30);
lean_dec(x_4);
x_31 = lean_unsigned_to_nat(0u);
x_32 = lean_array_get_size(x_30);
x_33 = lean_nat_dec_lt(x_31, x_32);
if (x_33 == 0)
{
lean_dec(x_32);
lean_dec(x_30);
x_20 = x_29;
goto block_27;
}
else
{
uint8_t x_34; 
x_34 = lean_nat_dec_le(x_32, x_32);
if (x_34 == 0)
{
lean_dec(x_32);
lean_dec(x_30);
x_20 = x_29;
goto block_27;
}
else
{
size_t x_35; size_t x_36; lean_object* x_37; 
x_35 = lean_usize_of_nat(x_31);
x_36 = lean_usize_of_nat(x_32);
lean_dec(x_32);
x_37 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_Omega_atoms_spec__3(x_30, x_35, x_36, x_29);
lean_dec(x_30);
x_20 = x_37;
goto block_27;
}
}
block_13:
{
size_t x_8; lean_object* x_9; size_t x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_array_size(x_7);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_usize_of_nat(x_9);
x_11 = l_Array_mapMUnsafe_map___at___Lean_Elab_Tactic_Omega_atoms_spec__0(x_8, x_10, x_7);
if (lean_is_scalar(x_6)) {
 x_12 = lean_alloc_ctor(0, 2, 0);
} else {
 x_12 = x_6;
}
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_5);
return x_12;
}
block_19:
{
lean_object* x_18; 
lean_dec(x_14);
x_18 = l_Array_qsort_sort___at___Lean_Elab_Tactic_Omega_atoms_spec__1___redArg(x_16, x_17, x_15);
lean_dec(x_15);
x_7 = x_18;
goto block_13;
}
block_27:
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_array_get_size(x_20);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_nat_dec_eq(x_21, x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_sub(x_21, x_24);
x_26 = lean_nat_dec_le(x_22, x_25);
if (x_26 == 0)
{
lean_inc(x_25);
x_14 = x_21;
x_15 = x_25;
x_16 = x_20;
x_17 = x_25;
goto block_19;
}
else
{
x_14 = x_21;
x_15 = x_25;
x_16 = x_20;
x_17 = x_22;
goto block_19;
}
}
else
{
lean_dec(x_21);
x_7 = x_20;
goto block_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atoms(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_Omega_atoms___redArg(x_2, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Tactic_Omega_atoms_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Lean_Elab_Tactic_Omega_atoms_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_Elab_Tactic_Omega_atoms_spec__1___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Array_qsort_sort___at___Lean_Elab_Tactic_Omega_atoms_spec__1___redArg___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_Elab_Tactic_Omega_atoms_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_qsort_sort___at___Lean_Elab_Tactic_Omega_atoms_spec__1___redArg(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_Elab_Tactic_Omega_atoms_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_qsort_sort___at___Lean_Elab_Tactic_Omega_atoms_spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_Elab_Tactic_Omega_atoms_spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_Elab_Tactic_Omega_atoms_spec__2(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_Omega_atoms_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_Omega_atoms_spec__3(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atoms___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Tactic_Omega_atoms___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atoms___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_4);
lean_dec(x_4);
x_12 = l_Lean_Elab_Tactic_Omega_atoms(x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atomsList___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = l_Lean_Elab_Tactic_Omega_atoms___redArg(x_1, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_mk_string_unchecked("Int", 3, 3);
x_11 = l_Lean_Name_mkStr1(x_10);
x_12 = lean_box(0);
x_13 = l_Lean_Expr_const___override(x_11, x_12);
x_14 = lean_array_to_list(x_8);
x_15 = l_Lean_Meta_mkListLit(x_13, x_14, x_2, x_3, x_4, x_5, x_9);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atomsList(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_Omega_atomsList___redArg(x_2, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atomsList___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_Tactic_Omega_atomsList___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atomsList___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_4);
lean_dec(x_4);
x_12 = l_Lean_Elab_Tactic_Omega_atomsList(x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_Tactic_Omega_atomsList___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_mk_string_unchecked("Lean", 4, 4);
x_11 = lean_mk_string_unchecked("Omega", 5, 5);
x_12 = lean_mk_string_unchecked("Coeffs", 6, 6);
x_13 = lean_mk_string_unchecked("ofList", 6, 6);
x_14 = l_Lean_Name_mkStr4(x_10, x_11, x_12, x_13);
x_15 = lean_box(0);
x_16 = l_Lean_Expr_const___override(x_14, x_15);
x_17 = l_Lean_Expr_app___override(x_16, x_9);
lean_ctor_set(x_7, 0, x_17);
return x_7;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_18 = lean_ctor_get(x_7, 0);
x_19 = lean_ctor_get(x_7, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_7);
x_20 = lean_mk_string_unchecked("Lean", 4, 4);
x_21 = lean_mk_string_unchecked("Omega", 5, 5);
x_22 = lean_mk_string_unchecked("Coeffs", 6, 6);
x_23 = lean_mk_string_unchecked("ofList", 6, 6);
x_24 = l_Lean_Name_mkStr4(x_20, x_21, x_22, x_23);
x_25 = lean_box(0);
x_26 = l_Lean_Expr_const___override(x_24, x_25);
x_27 = l_Lean_Expr_app___override(x_26, x_18);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_19);
return x_28;
}
}
else
{
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atomsCoeffs(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg(x_2, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atomsCoeffs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_4);
lean_dec(x_4);
x_12 = l_Lean_Elab_Tactic_Omega_atomsCoeffs(x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_commitWhen___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_st_ref_get(x_3, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_st_ref_get(x_2, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_box(x_5);
lean_inc(x_3);
lean_inc(x_2);
x_19 = lean_apply_10(x_1, x_2, x_3, x_4, x_18, x_6, x_7, x_8, x_9, x_10, x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
x_22 = lean_unbox(x_21);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_dec(x_19);
x_24 = lean_ctor_get(x_20, 0);
lean_inc(x_24);
lean_dec(x_20);
x_25 = lean_st_ref_take(x_3, x_23);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_st_ref_set(x_3, x_13, x_26);
lean_dec(x_3);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_st_ref_take(x_2, x_28);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_st_ref_set(x_2, x_16, x_30);
lean_dec(x_2);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_31, 0);
lean_dec(x_33);
lean_ctor_set(x_31, 0, x_24);
return x_31;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_24);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_3);
lean_dec(x_2);
x_36 = !lean_is_exclusive(x_19);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_19, 0);
lean_dec(x_37);
x_38 = lean_ctor_get(x_20, 0);
lean_inc(x_38);
lean_dec(x_20);
lean_ctor_set(x_19, 0, x_38);
return x_19;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_19, 1);
lean_inc(x_39);
lean_dec(x_19);
x_40 = lean_ctor_get(x_20, 0);
lean_inc(x_40);
lean_dec(x_20);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_3);
lean_dec(x_2);
x_42 = !lean_is_exclusive(x_19);
if (x_42 == 0)
{
return x_19;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_19, 0);
x_44 = lean_ctor_get(x_19, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_19);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_commitWhen(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Tactic_Omega_commitWhen___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_commitWhen___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_5);
lean_dec(x_5);
x_13 = l_Lean_Elab_Tactic_Omega_commitWhen___redArg(x_1, x_2, x_3, x_4, x_12, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_commitWhen___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_6);
lean_dec(x_6);
x_14 = l_Lean_Elab_Tactic_Omega_commitWhen(x_1, x_2, x_3, x_4, x_5, x_13, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_withoutModifyingState___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_box(x_5);
x_13 = lean_apply_10(x_1, x_2, x_3, x_4, x_12, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_13, 0);
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_13);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_19);
return x_22;
}
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_13);
if (x_23 == 0)
{
return x_13;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_13, 0);
x_25 = lean_ctor_get(x_13, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_13);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_withoutModifyingState___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_withoutModifyingState___redArg___lam__0___boxed), 11, 1);
lean_closure_set(x_12, 0, x_1);
x_13 = l_Lean_Elab_Tactic_Omega_commitWhen___redArg(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_withoutModifyingState(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Tactic_Omega_withoutModifyingState___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_withoutModifyingState___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_5);
lean_dec(x_5);
x_13 = l_Lean_Elab_Tactic_Omega_withoutModifyingState___redArg___lam__0(x_1, x_2, x_3, x_4, x_12, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_withoutModifyingState___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_5);
lean_dec(x_5);
x_13 = l_Lean_Elab_Tactic_Omega_withoutModifyingState___redArg(x_1, x_2, x_3, x_4, x_12, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_withoutModifyingState___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_6);
lean_dec(x_6);
x_14 = l_Lean_Elab_Tactic_Omega_withoutModifyingState(x_1, x_2, x_3, x_4, x_5, x_13, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_natCast_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
lean_inc(x_1);
x_2 = l_Lean_Expr_getAppFnArgs(x_1);
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_Lean_Expr_nat_x3f(x_1);
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 1)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
lean_dec(x_3);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_mk_string_unchecked("Nat", 3, 3);
x_11 = lean_string_dec_eq(x_9, x_10);
lean_dec(x_10);
lean_dec(x_9);
if (x_11 == 0)
{
lean_dec(x_7);
lean_dec(x_4);
if (lean_obj_tag(x_8) == 0)
{
return x_5;
}
else
{
lean_dec(x_8);
return x_5;
}
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_mk_string_unchecked("cast", 4, 4);
x_13 = lean_string_dec_eq(x_7, x_12);
lean_dec(x_12);
lean_dec(x_7);
if (x_13 == 0)
{
lean_dec(x_4);
if (lean_obj_tag(x_8) == 0)
{
return x_5;
}
else
{
lean_dec(x_8);
return x_5;
}
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_array_get_size(x_4);
x_15 = lean_unsigned_to_nat(3u);
x_16 = lean_nat_dec_eq(x_14, x_15);
lean_dec(x_14);
if (x_16 == 0)
{
lean_dec(x_4);
if (lean_obj_tag(x_8) == 0)
{
return x_5;
}
else
{
lean_dec(x_8);
return x_5;
}
}
else
{
lean_object* x_17; 
x_17 = lean_unsigned_to_nat(2u);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_5);
x_18 = lean_array_fget(x_4, x_17);
lean_dec(x_4);
x_19 = l_Lean_Expr_nat_x3f(x_18);
return x_19;
}
else
{
lean_dec(x_8);
lean_dec(x_4);
return x_5;
}
}
}
}
}
else
{
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
else
{
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_intCast_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
lean_inc(x_1);
x_2 = l_Lean_Expr_getAppFnArgs(x_1);
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_Lean_Expr_int_x3f(x_1);
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 1)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
lean_dec(x_3);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_mk_string_unchecked("Nat", 3, 3);
x_11 = lean_string_dec_eq(x_9, x_10);
lean_dec(x_10);
lean_dec(x_9);
if (x_11 == 0)
{
lean_dec(x_7);
lean_dec(x_4);
if (lean_obj_tag(x_8) == 0)
{
return x_5;
}
else
{
lean_dec(x_8);
return x_5;
}
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_mk_string_unchecked("cast", 4, 4);
x_13 = lean_string_dec_eq(x_7, x_12);
lean_dec(x_12);
lean_dec(x_7);
if (x_13 == 0)
{
lean_dec(x_4);
if (lean_obj_tag(x_8) == 0)
{
return x_5;
}
else
{
lean_dec(x_8);
return x_5;
}
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_array_get_size(x_4);
x_15 = lean_unsigned_to_nat(3u);
x_16 = lean_nat_dec_eq(x_14, x_15);
lean_dec(x_14);
if (x_16 == 0)
{
lean_dec(x_4);
if (lean_obj_tag(x_8) == 0)
{
return x_5;
}
else
{
lean_dec(x_8);
return x_5;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_unsigned_to_nat(2u);
x_18 = lean_array_fget(x_4, x_17);
lean_dec(x_4);
x_19 = l_Lean_Expr_nat_x3f(x_18);
if (lean_obj_tag(x_19) == 0)
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_20; 
lean_dec(x_5);
x_20 = lean_box(0);
return x_20;
}
else
{
lean_dec(x_8);
return x_5;
}
}
else
{
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_21; 
lean_dec(x_5);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 0);
x_23 = lean_nat_to_int(x_22);
lean_ctor_set(x_19, 0, x_23);
return x_19;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_19, 0);
lean_inc(x_24);
lean_dec(x_19);
x_25 = lean_nat_to_int(x_24);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
else
{
lean_dec(x_19);
lean_dec(x_8);
return x_5;
}
}
}
}
}
}
else
{
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
else
{
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f_op(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Tactic_Omega_groundNat_x3f(x_2);
if (lean_obj_tag(x_4) == 0)
{
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
x_6 = l_Lean_Elab_Tactic_Omega_groundNat_x3f(x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_dec(x_5);
lean_dec(x_1);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_apply_2(x_1, x_5, x_8);
lean_ctor_set(x_6, 0, x_9);
return x_6;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
lean_dec(x_6);
x_11 = lean_apply_2(x_1, x_5, x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_nat_pow(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_nat_div(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f___lam__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_nat_sub(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f___lam__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_nat_mul(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f___lam__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_nat_add(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
lean_inc(x_1);
x_2 = l_Lean_Expr_getAppFnArgs(x_1);
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_Lean_Expr_nat_x3f(x_1);
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 1)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
lean_dec(x_3);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_mk_string_unchecked("Nat", 3, 3);
x_11 = lean_string_dec_eq(x_9, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_mk_string_unchecked("HAdd", 4, 4);
x_13 = lean_string_dec_eq(x_9, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_mk_string_unchecked("HMul", 4, 4);
x_15 = lean_string_dec_eq(x_9, x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_mk_string_unchecked("HSub", 4, 4);
x_17 = lean_string_dec_eq(x_9, x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_mk_string_unchecked("HDiv", 4, 4);
x_19 = lean_string_dec_eq(x_9, x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_mk_string_unchecked("HPow", 4, 4);
x_21 = lean_string_dec_eq(x_9, x_20);
lean_dec(x_20);
lean_dec(x_9);
if (x_21 == 0)
{
lean_dec(x_7);
lean_dec(x_4);
if (lean_obj_tag(x_8) == 0)
{
return x_5;
}
else
{
lean_dec(x_8);
return x_5;
}
}
else
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_mk_string_unchecked("hPow", 4, 4);
x_23 = lean_string_dec_eq(x_7, x_22);
lean_dec(x_22);
lean_dec(x_7);
if (x_23 == 0)
{
lean_dec(x_4);
if (lean_obj_tag(x_8) == 0)
{
return x_5;
}
else
{
lean_dec(x_8);
return x_5;
}
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_array_get_size(x_4);
x_25 = lean_unsigned_to_nat(6u);
x_26 = lean_nat_dec_eq(x_24, x_25);
lean_dec(x_24);
if (x_26 == 0)
{
lean_dec(x_4);
if (lean_obj_tag(x_8) == 0)
{
return x_5;
}
else
{
lean_dec(x_8);
return x_5;
}
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_unsigned_to_nat(4u);
x_28 = lean_unsigned_to_nat(5u);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_5);
x_29 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___lam__0___boxed), 2, 0);
x_30 = lean_array_fget(x_4, x_27);
x_31 = lean_array_fget(x_4, x_28);
lean_dec(x_4);
x_32 = l_Lean_Elab_Tactic_Omega_groundNat_x3f_op(x_29, x_30, x_31);
return x_32;
}
else
{
lean_dec(x_8);
lean_dec(x_4);
return x_5;
}
}
}
}
}
else
{
lean_object* x_33; uint8_t x_34; 
lean_dec(x_9);
x_33 = lean_mk_string_unchecked("hDiv", 4, 4);
x_34 = lean_string_dec_eq(x_7, x_33);
lean_dec(x_33);
lean_dec(x_7);
if (x_34 == 0)
{
lean_dec(x_4);
if (lean_obj_tag(x_8) == 0)
{
return x_5;
}
else
{
lean_dec(x_8);
return x_5;
}
}
else
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_array_get_size(x_4);
x_36 = lean_unsigned_to_nat(6u);
x_37 = lean_nat_dec_eq(x_35, x_36);
lean_dec(x_35);
if (x_37 == 0)
{
lean_dec(x_4);
if (lean_obj_tag(x_8) == 0)
{
return x_5;
}
else
{
lean_dec(x_8);
return x_5;
}
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_unsigned_to_nat(4u);
x_39 = lean_unsigned_to_nat(5u);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_5);
x_40 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___lam__1___boxed), 2, 0);
x_41 = lean_array_fget(x_4, x_38);
x_42 = lean_array_fget(x_4, x_39);
lean_dec(x_4);
x_43 = l_Lean_Elab_Tactic_Omega_groundNat_x3f_op(x_40, x_41, x_42);
return x_43;
}
else
{
lean_dec(x_8);
lean_dec(x_4);
return x_5;
}
}
}
}
}
else
{
lean_object* x_44; uint8_t x_45; 
lean_dec(x_9);
x_44 = lean_mk_string_unchecked("hSub", 4, 4);
x_45 = lean_string_dec_eq(x_7, x_44);
lean_dec(x_44);
lean_dec(x_7);
if (x_45 == 0)
{
lean_dec(x_4);
if (lean_obj_tag(x_8) == 0)
{
return x_5;
}
else
{
lean_dec(x_8);
return x_5;
}
}
else
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_46 = lean_array_get_size(x_4);
x_47 = lean_unsigned_to_nat(6u);
x_48 = lean_nat_dec_eq(x_46, x_47);
lean_dec(x_46);
if (x_48 == 0)
{
lean_dec(x_4);
if (lean_obj_tag(x_8) == 0)
{
return x_5;
}
else
{
lean_dec(x_8);
return x_5;
}
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_unsigned_to_nat(4u);
x_50 = lean_unsigned_to_nat(5u);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_5);
x_51 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___lam__2___boxed), 2, 0);
x_52 = lean_array_fget(x_4, x_49);
x_53 = lean_array_fget(x_4, x_50);
lean_dec(x_4);
x_54 = l_Lean_Elab_Tactic_Omega_groundNat_x3f_op(x_51, x_52, x_53);
return x_54;
}
else
{
lean_dec(x_8);
lean_dec(x_4);
return x_5;
}
}
}
}
}
else
{
lean_object* x_55; uint8_t x_56; 
lean_dec(x_9);
x_55 = lean_mk_string_unchecked("hMul", 4, 4);
x_56 = lean_string_dec_eq(x_7, x_55);
lean_dec(x_55);
lean_dec(x_7);
if (x_56 == 0)
{
lean_dec(x_4);
if (lean_obj_tag(x_8) == 0)
{
return x_5;
}
else
{
lean_dec(x_8);
return x_5;
}
}
else
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_57 = lean_array_get_size(x_4);
x_58 = lean_unsigned_to_nat(6u);
x_59 = lean_nat_dec_eq(x_57, x_58);
lean_dec(x_57);
if (x_59 == 0)
{
lean_dec(x_4);
if (lean_obj_tag(x_8) == 0)
{
return x_5;
}
else
{
lean_dec(x_8);
return x_5;
}
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_unsigned_to_nat(4u);
x_61 = lean_unsigned_to_nat(5u);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_5);
x_62 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___lam__3___boxed), 2, 0);
x_63 = lean_array_fget(x_4, x_60);
x_64 = lean_array_fget(x_4, x_61);
lean_dec(x_4);
x_65 = l_Lean_Elab_Tactic_Omega_groundNat_x3f_op(x_62, x_63, x_64);
return x_65;
}
else
{
lean_dec(x_8);
lean_dec(x_4);
return x_5;
}
}
}
}
}
else
{
lean_object* x_66; uint8_t x_67; 
lean_dec(x_9);
x_66 = lean_mk_string_unchecked("hAdd", 4, 4);
x_67 = lean_string_dec_eq(x_7, x_66);
lean_dec(x_66);
lean_dec(x_7);
if (x_67 == 0)
{
lean_dec(x_4);
if (lean_obj_tag(x_8) == 0)
{
return x_5;
}
else
{
lean_dec(x_8);
return x_5;
}
}
else
{
lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_68 = lean_array_get_size(x_4);
x_69 = lean_unsigned_to_nat(6u);
x_70 = lean_nat_dec_eq(x_68, x_69);
lean_dec(x_68);
if (x_70 == 0)
{
lean_dec(x_4);
if (lean_obj_tag(x_8) == 0)
{
return x_5;
}
else
{
lean_dec(x_8);
return x_5;
}
}
else
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_unsigned_to_nat(4u);
x_72 = lean_unsigned_to_nat(5u);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_5);
x_73 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___lam__4___boxed), 2, 0);
x_74 = lean_array_fget(x_4, x_71);
x_75 = lean_array_fget(x_4, x_72);
lean_dec(x_4);
x_76 = l_Lean_Elab_Tactic_Omega_groundNat_x3f_op(x_73, x_74, x_75);
return x_76;
}
else
{
lean_dec(x_8);
lean_dec(x_4);
return x_5;
}
}
}
}
}
else
{
lean_object* x_77; uint8_t x_78; 
lean_dec(x_9);
x_77 = lean_mk_string_unchecked("cast", 4, 4);
x_78 = lean_string_dec_eq(x_7, x_77);
lean_dec(x_77);
lean_dec(x_7);
if (x_78 == 0)
{
lean_dec(x_4);
if (lean_obj_tag(x_8) == 0)
{
return x_5;
}
else
{
lean_dec(x_8);
return x_5;
}
}
else
{
lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_79 = lean_array_get_size(x_4);
x_80 = lean_unsigned_to_nat(3u);
x_81 = lean_nat_dec_eq(x_79, x_80);
lean_dec(x_79);
if (x_81 == 0)
{
lean_dec(x_4);
if (lean_obj_tag(x_8) == 0)
{
return x_5;
}
else
{
lean_dec(x_8);
return x_5;
}
}
else
{
lean_object* x_82; 
x_82 = lean_unsigned_to_nat(2u);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_83; 
lean_dec(x_5);
x_83 = lean_array_fget(x_4, x_82);
lean_dec(x_4);
x_1 = x_83;
goto _start;
}
else
{
lean_dec(x_8);
lean_dec(x_4);
return x_5;
}
}
}
}
}
else
{
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
else
{
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___lam__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f___lam__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___lam__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f___lam__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___lam__3(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f___lam__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___lam__4(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundInt_x3f_op(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Tactic_Omega_groundInt_x3f(x_2);
if (lean_obj_tag(x_4) == 0)
{
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
x_6 = l_Lean_Elab_Tactic_Omega_groundInt_x3f(x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_dec(x_5);
lean_dec(x_1);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_apply_2(x_1, x_5, x_8);
lean_ctor_set(x_6, 0, x_9);
return x_6;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
lean_dec(x_6);
x_11 = lean_apply_2(x_1, x_5, x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundInt_x3f___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_int_ediv(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundInt_x3f___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_int_sub(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundInt_x3f___lam__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_int_mul(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundInt_x3f___lam__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_int_add(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundInt_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
lean_inc(x_1);
x_2 = l_Lean_Expr_getAppFnArgs(x_1);
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_Lean_Expr_int_x3f(x_1);
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 1)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
lean_dec(x_3);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_mk_string_unchecked("Nat", 3, 3);
x_11 = lean_string_dec_eq(x_9, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_mk_string_unchecked("HAdd", 4, 4);
x_13 = lean_string_dec_eq(x_9, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_mk_string_unchecked("HMul", 4, 4);
x_15 = lean_string_dec_eq(x_9, x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_mk_string_unchecked("HSub", 4, 4);
x_17 = lean_string_dec_eq(x_9, x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_mk_string_unchecked("HDiv", 4, 4);
x_19 = lean_string_dec_eq(x_9, x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_mk_string_unchecked("HPow", 4, 4);
x_21 = lean_string_dec_eq(x_9, x_20);
lean_dec(x_20);
lean_dec(x_9);
if (x_21 == 0)
{
lean_dec(x_7);
lean_dec(x_4);
if (lean_obj_tag(x_8) == 0)
{
return x_5;
}
else
{
lean_dec(x_8);
return x_5;
}
}
else
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_mk_string_unchecked("hPow", 4, 4);
x_23 = lean_string_dec_eq(x_7, x_22);
lean_dec(x_22);
lean_dec(x_7);
if (x_23 == 0)
{
lean_dec(x_4);
if (lean_obj_tag(x_8) == 0)
{
return x_5;
}
else
{
lean_dec(x_8);
return x_5;
}
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_array_get_size(x_4);
x_25 = lean_unsigned_to_nat(6u);
x_26 = lean_nat_dec_eq(x_24, x_25);
lean_dec(x_24);
if (x_26 == 0)
{
lean_dec(x_4);
if (lean_obj_tag(x_8) == 0)
{
return x_5;
}
else
{
lean_dec(x_8);
return x_5;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_unsigned_to_nat(4u);
x_28 = lean_array_fget(x_4, x_27);
x_29 = l_Lean_Elab_Tactic_Omega_groundInt_x3f(x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_dec(x_4);
if (lean_obj_tag(x_8) == 0)
{
lean_dec(x_5);
return x_29;
}
else
{
lean_dec(x_8);
return x_5;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_unsigned_to_nat(5u);
x_32 = lean_array_fget(x_4, x_31);
lean_dec(x_4);
x_33 = l_Lean_Elab_Tactic_Omega_groundNat_x3f(x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_dec(x_30);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_34; 
lean_dec(x_5);
x_34 = lean_box(0);
return x_34;
}
else
{
lean_dec(x_8);
return x_5;
}
}
else
{
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_35; 
lean_dec(x_5);
x_35 = !lean_is_exclusive(x_33);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_33, 0);
x_37 = l_Int_pow(x_30, x_36);
lean_dec(x_36);
lean_dec(x_30);
lean_ctor_set(x_33, 0, x_37);
return x_33;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_33, 0);
lean_inc(x_38);
lean_dec(x_33);
x_39 = l_Int_pow(x_30, x_38);
lean_dec(x_38);
lean_dec(x_30);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_39);
return x_40;
}
}
else
{
lean_dec(x_33);
lean_dec(x_30);
lean_dec(x_8);
return x_5;
}
}
}
}
}
}
}
else
{
lean_object* x_41; uint8_t x_42; 
lean_dec(x_9);
x_41 = lean_mk_string_unchecked("hDiv", 4, 4);
x_42 = lean_string_dec_eq(x_7, x_41);
lean_dec(x_41);
lean_dec(x_7);
if (x_42 == 0)
{
lean_dec(x_4);
if (lean_obj_tag(x_8) == 0)
{
return x_5;
}
else
{
lean_dec(x_8);
return x_5;
}
}
else
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_43 = lean_array_get_size(x_4);
x_44 = lean_unsigned_to_nat(6u);
x_45 = lean_nat_dec_eq(x_43, x_44);
lean_dec(x_43);
if (x_45 == 0)
{
lean_dec(x_4);
if (lean_obj_tag(x_8) == 0)
{
return x_5;
}
else
{
lean_dec(x_8);
return x_5;
}
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_unsigned_to_nat(4u);
x_47 = lean_unsigned_to_nat(5u);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_5);
x_48 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_groundInt_x3f___lam__0___boxed), 2, 0);
x_49 = lean_array_fget(x_4, x_46);
x_50 = lean_array_fget(x_4, x_47);
lean_dec(x_4);
x_51 = l_Lean_Elab_Tactic_Omega_groundInt_x3f_op(x_48, x_49, x_50);
return x_51;
}
else
{
lean_dec(x_8);
lean_dec(x_4);
return x_5;
}
}
}
}
}
else
{
lean_object* x_52; uint8_t x_53; 
lean_dec(x_9);
x_52 = lean_mk_string_unchecked("hSub", 4, 4);
x_53 = lean_string_dec_eq(x_7, x_52);
lean_dec(x_52);
lean_dec(x_7);
if (x_53 == 0)
{
lean_dec(x_4);
if (lean_obj_tag(x_8) == 0)
{
return x_5;
}
else
{
lean_dec(x_8);
return x_5;
}
}
else
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_54 = lean_array_get_size(x_4);
x_55 = lean_unsigned_to_nat(6u);
x_56 = lean_nat_dec_eq(x_54, x_55);
lean_dec(x_54);
if (x_56 == 0)
{
lean_dec(x_4);
if (lean_obj_tag(x_8) == 0)
{
return x_5;
}
else
{
lean_dec(x_8);
return x_5;
}
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_unsigned_to_nat(4u);
x_58 = lean_unsigned_to_nat(5u);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_5);
x_59 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_groundInt_x3f___lam__1___boxed), 2, 0);
x_60 = lean_array_fget(x_4, x_57);
x_61 = lean_array_fget(x_4, x_58);
lean_dec(x_4);
x_62 = l_Lean_Elab_Tactic_Omega_groundInt_x3f_op(x_59, x_60, x_61);
return x_62;
}
else
{
lean_dec(x_8);
lean_dec(x_4);
return x_5;
}
}
}
}
}
else
{
lean_object* x_63; uint8_t x_64; 
lean_dec(x_9);
x_63 = lean_mk_string_unchecked("hMul", 4, 4);
x_64 = lean_string_dec_eq(x_7, x_63);
lean_dec(x_63);
lean_dec(x_7);
if (x_64 == 0)
{
lean_dec(x_4);
if (lean_obj_tag(x_8) == 0)
{
return x_5;
}
else
{
lean_dec(x_8);
return x_5;
}
}
else
{
lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_65 = lean_array_get_size(x_4);
x_66 = lean_unsigned_to_nat(6u);
x_67 = lean_nat_dec_eq(x_65, x_66);
lean_dec(x_65);
if (x_67 == 0)
{
lean_dec(x_4);
if (lean_obj_tag(x_8) == 0)
{
return x_5;
}
else
{
lean_dec(x_8);
return x_5;
}
}
else
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_unsigned_to_nat(4u);
x_69 = lean_unsigned_to_nat(5u);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_5);
x_70 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_groundInt_x3f___lam__2___boxed), 2, 0);
x_71 = lean_array_fget(x_4, x_68);
x_72 = lean_array_fget(x_4, x_69);
lean_dec(x_4);
x_73 = l_Lean_Elab_Tactic_Omega_groundInt_x3f_op(x_70, x_71, x_72);
return x_73;
}
else
{
lean_dec(x_8);
lean_dec(x_4);
return x_5;
}
}
}
}
}
else
{
lean_object* x_74; uint8_t x_75; 
lean_dec(x_9);
x_74 = lean_mk_string_unchecked("hAdd", 4, 4);
x_75 = lean_string_dec_eq(x_7, x_74);
lean_dec(x_74);
lean_dec(x_7);
if (x_75 == 0)
{
lean_dec(x_4);
if (lean_obj_tag(x_8) == 0)
{
return x_5;
}
else
{
lean_dec(x_8);
return x_5;
}
}
else
{
lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_76 = lean_array_get_size(x_4);
x_77 = lean_unsigned_to_nat(6u);
x_78 = lean_nat_dec_eq(x_76, x_77);
lean_dec(x_76);
if (x_78 == 0)
{
lean_dec(x_4);
if (lean_obj_tag(x_8) == 0)
{
return x_5;
}
else
{
lean_dec(x_8);
return x_5;
}
}
else
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_unsigned_to_nat(4u);
x_80 = lean_unsigned_to_nat(5u);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_5);
x_81 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_groundInt_x3f___lam__3___boxed), 2, 0);
x_82 = lean_array_fget(x_4, x_79);
x_83 = lean_array_fget(x_4, x_80);
lean_dec(x_4);
x_84 = l_Lean_Elab_Tactic_Omega_groundInt_x3f_op(x_81, x_82, x_83);
return x_84;
}
else
{
lean_dec(x_8);
lean_dec(x_4);
return x_5;
}
}
}
}
}
else
{
lean_object* x_85; uint8_t x_86; 
lean_dec(x_9);
x_85 = lean_mk_string_unchecked("cast", 4, 4);
x_86 = lean_string_dec_eq(x_7, x_85);
lean_dec(x_85);
lean_dec(x_7);
if (x_86 == 0)
{
lean_dec(x_4);
if (lean_obj_tag(x_8) == 0)
{
return x_5;
}
else
{
lean_dec(x_8);
return x_5;
}
}
else
{
lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_87 = lean_array_get_size(x_4);
x_88 = lean_unsigned_to_nat(3u);
x_89 = lean_nat_dec_eq(x_87, x_88);
lean_dec(x_87);
if (x_89 == 0)
{
lean_dec(x_4);
if (lean_obj_tag(x_8) == 0)
{
return x_5;
}
else
{
lean_dec(x_8);
return x_5;
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_unsigned_to_nat(2u);
x_91 = lean_array_fget(x_4, x_90);
lean_dec(x_4);
x_92 = l_Lean_Elab_Tactic_Omega_groundNat_x3f(x_91);
if (lean_obj_tag(x_92) == 0)
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_93; 
lean_dec(x_5);
x_93 = lean_box(0);
return x_93;
}
else
{
lean_dec(x_8);
return x_5;
}
}
else
{
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_94; 
lean_dec(x_5);
x_94 = !lean_is_exclusive(x_92);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_ctor_get(x_92, 0);
x_96 = lean_nat_to_int(x_95);
lean_ctor_set(x_92, 0, x_96);
return x_92;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_92, 0);
lean_inc(x_97);
lean_dec(x_92);
x_98 = lean_nat_to_int(x_97);
x_99 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_99, 0, x_98);
return x_99;
}
}
else
{
lean_dec(x_92);
lean_dec(x_8);
return x_5;
}
}
}
}
}
}
else
{
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
else
{
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundInt_x3f___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Tactic_Omega_groundInt_x3f___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundInt_x3f___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Tactic_Omega_groundInt_x3f___lam__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundInt_x3f___lam__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Tactic_Omega_groundInt_x3f___lam__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundInt_x3f___lam__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Tactic_Omega_groundInt_x3f___lam__3(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_mkEqReflWithExpectedType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_8 = l_Lean_Meta_mkEqRefl(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Meta_mkEq(x_1, x_2, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = l_Lean_Meta_mkExpectedPropHint(x_9, x_13);
lean_ctor_set(x_11, 0, x_14);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_11, 0);
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_11);
x_17 = l_Lean_Meta_mkExpectedPropHint(x_9, x_15);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
lean_dec(x_9);
return x_11;
}
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_12 = lean_unsigned_to_nat(8u);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_unsigned_to_nat(2u);
x_15 = lean_nat_shiftl(x_12, x_14);
x_16 = lean_unsigned_to_nat(3u);
x_17 = lean_nat_div(x_15, x_16);
lean_dec(x_15);
x_18 = l_Nat_nextPowerOfTwo(x_17);
lean_dec(x_17);
x_19 = lean_box(0);
x_20 = lean_mk_array(x_18, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_13);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_11);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(x_6);
x_14 = lean_apply_11(x_1, x_2, x_3, x_4, x_5, x_13, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, uint8_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_mk_string_unchecked("max", 3, 3);
x_17 = lean_string_dec_eq(x_1, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_16);
x_18 = l_Lean_Name_str___override(x_2, x_3);
x_19 = l_Lean_Name_str___override(x_18, x_1);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_4);
x_21 = lean_box(x_9);
x_22 = lean_apply_11(x_5, x_20, x_6, x_7, x_8, x_21, x_10, x_11, x_12, x_13, x_14, x_15);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
lean_dec(x_1);
x_23 = lean_array_get_size(x_4);
x_24 = lean_unsigned_to_nat(4u);
x_25 = lean_nat_dec_eq(x_23, x_24);
lean_dec(x_23);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = l_Lean_Name_str___override(x_2, x_3);
x_27 = l_Lean_Name_str___override(x_26, x_16);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_4);
x_29 = lean_box(x_9);
x_30 = lean_apply_11(x_5, x_28, x_6, x_7, x_8, x_29, x_10, x_11, x_12, x_13, x_14, x_15);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint64_t x_88; lean_object* x_89; uint64_t x_90; uint64_t x_91; uint64_t x_92; lean_object* x_93; uint64_t x_94; uint64_t x_95; uint64_t x_96; size_t x_97; size_t x_98; lean_object* x_99; size_t x_100; size_t x_101; size_t x_102; lean_object* x_103; uint8_t x_104; 
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_31 = lean_unsigned_to_nat(2u);
x_32 = lean_array_fget(x_4, x_31);
x_33 = lean_unsigned_to_nat(3u);
x_34 = lean_array_fget(x_4, x_33);
lean_dec(x_4);
x_35 = lean_unsigned_to_nat(8u);
x_36 = lean_nat_shiftl(x_35, x_31);
x_37 = lean_nat_div(x_36, x_33);
lean_dec(x_36);
x_38 = l_Nat_nextPowerOfTwo(x_37);
lean_dec(x_37);
x_39 = lean_box(0);
x_40 = lean_mk_array(x_38, x_39);
x_41 = lean_mk_string_unchecked("Int", 3, 3);
x_42 = lean_mk_string_unchecked("le_max_left", 11, 11);
lean_inc(x_41);
x_43 = l_Lean_Name_mkStr2(x_41, x_42);
x_44 = lean_box(0);
x_85 = l_Lean_Expr_const___override(x_43, x_44);
lean_inc(x_34);
lean_inc(x_32);
x_86 = l_Lean_mkAppB(x_85, x_32, x_34);
x_87 = lean_array_get_size(x_40);
x_88 = l_Lean_Expr_hash(x_86);
x_89 = lean_unsigned_to_nat(32u);
x_90 = lean_uint64_of_nat(x_89);
x_91 = lean_uint64_shift_right(x_88, x_90);
x_92 = lean_uint64_xor(x_88, x_91);
x_93 = lean_unsigned_to_nat(16u);
x_94 = lean_uint64_of_nat(x_93);
x_95 = lean_uint64_shift_right(x_92, x_94);
x_96 = lean_uint64_xor(x_92, x_95);
x_97 = lean_uint64_to_usize(x_96);
x_98 = lean_usize_of_nat(x_87);
lean_dec(x_87);
x_99 = lean_unsigned_to_nat(1u);
x_100 = lean_usize_of_nat(x_99);
x_101 = lean_usize_sub(x_98, x_100);
x_102 = lean_usize_land(x_97, x_101);
x_103 = lean_array_uget(x_40, x_102);
x_104 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectMVars_visit_spec__0___redArg(x_86, x_103);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; 
x_105 = lean_box(0);
x_106 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_106, 0, x_86);
lean_ctor_set(x_106, 1, x_105);
lean_ctor_set(x_106, 2, x_103);
x_107 = lean_array_uset(x_40, x_102, x_106);
x_108 = lean_nat_shiftl(x_99, x_31);
x_109 = lean_nat_div(x_108, x_33);
lean_dec(x_108);
x_110 = lean_array_get_size(x_107);
x_111 = lean_nat_dec_le(x_109, x_110);
lean_dec(x_110);
lean_dec(x_109);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; 
x_112 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectMVars_visit_spec__1(lean_box(0), x_107);
lean_inc(x_112);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_99);
lean_ctor_set(x_113, 1, x_112);
x_45 = x_113;
x_46 = x_99;
x_47 = x_112;
goto block_84;
}
else
{
lean_object* x_114; 
lean_inc(x_107);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_99);
lean_ctor_set(x_114, 1, x_107);
x_45 = x_114;
x_46 = x_99;
x_47 = x_107;
goto block_84;
}
}
else
{
lean_object* x_115; lean_object* x_116; 
lean_dec(x_103);
lean_dec(x_86);
x_115 = lean_unsigned_to_nat(0u);
lean_inc(x_40);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_40);
x_45 = x_116;
x_46 = x_115;
x_47 = x_40;
goto block_84;
}
block_84:
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint64_t x_53; lean_object* x_54; uint64_t x_55; uint64_t x_56; uint64_t x_57; lean_object* x_58; uint64_t x_59; uint64_t x_60; uint64_t x_61; size_t x_62; size_t x_63; lean_object* x_64; size_t x_65; size_t x_66; size_t x_67; lean_object* x_68; uint8_t x_69; 
x_48 = lean_mk_string_unchecked("le_max_right", 12, 12);
x_49 = l_Lean_Name_mkStr2(x_41, x_48);
x_50 = l_Lean_Expr_const___override(x_49, x_44);
x_51 = l_Lean_mkAppB(x_50, x_32, x_34);
x_52 = lean_array_get_size(x_47);
x_53 = l_Lean_Expr_hash(x_51);
x_54 = lean_unsigned_to_nat(32u);
x_55 = lean_uint64_of_nat(x_54);
x_56 = lean_uint64_shift_right(x_53, x_55);
x_57 = lean_uint64_xor(x_53, x_56);
x_58 = lean_unsigned_to_nat(16u);
x_59 = lean_uint64_of_nat(x_58);
x_60 = lean_uint64_shift_right(x_57, x_59);
x_61 = lean_uint64_xor(x_57, x_60);
x_62 = lean_uint64_to_usize(x_61);
x_63 = lean_usize_of_nat(x_52);
lean_dec(x_52);
x_64 = lean_unsigned_to_nat(1u);
x_65 = lean_usize_of_nat(x_64);
x_66 = lean_usize_sub(x_63, x_65);
x_67 = lean_usize_land(x_62, x_66);
x_68 = lean_array_uget(x_47, x_67);
x_69 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectMVars_visit_spec__0___redArg(x_51, x_68);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
lean_dec(x_45);
x_70 = lean_box(0);
x_71 = lean_nat_add(x_46, x_64);
x_72 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_72, 0, x_51);
lean_ctor_set(x_72, 1, x_70);
lean_ctor_set(x_72, 2, x_68);
x_73 = lean_array_uset(x_47, x_67, x_72);
x_74 = lean_nat_shiftl(x_71, x_31);
x_75 = lean_nat_div(x_74, x_33);
lean_dec(x_74);
x_76 = lean_array_get_size(x_73);
x_77 = lean_nat_dec_le(x_75, x_76);
lean_dec(x_76);
lean_dec(x_75);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectMVars_visit_spec__1(lean_box(0), x_73);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_71);
lean_ctor_set(x_79, 1, x_78);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_15);
return x_80;
}
else
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_71);
lean_ctor_set(x_81, 1, x_73);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_15);
return x_82;
}
}
else
{
lean_object* x_83; 
lean_dec(x_68);
lean_dec(x_51);
lean_dec(x_47);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_45);
lean_ctor_set(x_83, 1, x_15);
return x_83;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, uint8_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_mk_string_unchecked("min", 3, 3);
x_17 = lean_string_dec_eq(x_1, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_16);
x_18 = l_Lean_Name_str___override(x_2, x_3);
x_19 = l_Lean_Name_str___override(x_18, x_1);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_4);
x_21 = lean_box(x_9);
x_22 = lean_apply_11(x_5, x_20, x_6, x_7, x_8, x_21, x_10, x_11, x_12, x_13, x_14, x_15);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
lean_dec(x_1);
x_23 = lean_array_get_size(x_4);
x_24 = lean_unsigned_to_nat(4u);
x_25 = lean_nat_dec_eq(x_23, x_24);
lean_dec(x_23);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = l_Lean_Name_str___override(x_2, x_3);
x_27 = l_Lean_Name_str___override(x_26, x_16);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_4);
x_29 = lean_box(x_9);
x_30 = lean_apply_11(x_5, x_28, x_6, x_7, x_8, x_29, x_10, x_11, x_12, x_13, x_14, x_15);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint64_t x_88; lean_object* x_89; uint64_t x_90; uint64_t x_91; uint64_t x_92; lean_object* x_93; uint64_t x_94; uint64_t x_95; uint64_t x_96; size_t x_97; size_t x_98; lean_object* x_99; size_t x_100; size_t x_101; size_t x_102; lean_object* x_103; uint8_t x_104; 
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_31 = lean_unsigned_to_nat(2u);
x_32 = lean_array_fget(x_4, x_31);
x_33 = lean_unsigned_to_nat(3u);
x_34 = lean_array_fget(x_4, x_33);
lean_dec(x_4);
x_35 = lean_unsigned_to_nat(8u);
x_36 = lean_nat_shiftl(x_35, x_31);
x_37 = lean_nat_div(x_36, x_33);
lean_dec(x_36);
x_38 = l_Nat_nextPowerOfTwo(x_37);
lean_dec(x_37);
x_39 = lean_box(0);
x_40 = lean_mk_array(x_38, x_39);
x_41 = lean_mk_string_unchecked("Int", 3, 3);
x_42 = lean_mk_string_unchecked("min_le_left", 11, 11);
lean_inc(x_41);
x_43 = l_Lean_Name_mkStr2(x_41, x_42);
x_44 = lean_box(0);
x_85 = l_Lean_Expr_const___override(x_43, x_44);
lean_inc(x_34);
lean_inc(x_32);
x_86 = l_Lean_mkAppB(x_85, x_32, x_34);
x_87 = lean_array_get_size(x_40);
x_88 = l_Lean_Expr_hash(x_86);
x_89 = lean_unsigned_to_nat(32u);
x_90 = lean_uint64_of_nat(x_89);
x_91 = lean_uint64_shift_right(x_88, x_90);
x_92 = lean_uint64_xor(x_88, x_91);
x_93 = lean_unsigned_to_nat(16u);
x_94 = lean_uint64_of_nat(x_93);
x_95 = lean_uint64_shift_right(x_92, x_94);
x_96 = lean_uint64_xor(x_92, x_95);
x_97 = lean_uint64_to_usize(x_96);
x_98 = lean_usize_of_nat(x_87);
lean_dec(x_87);
x_99 = lean_unsigned_to_nat(1u);
x_100 = lean_usize_of_nat(x_99);
x_101 = lean_usize_sub(x_98, x_100);
x_102 = lean_usize_land(x_97, x_101);
x_103 = lean_array_uget(x_40, x_102);
x_104 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectMVars_visit_spec__0___redArg(x_86, x_103);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; 
x_105 = lean_box(0);
x_106 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_106, 0, x_86);
lean_ctor_set(x_106, 1, x_105);
lean_ctor_set(x_106, 2, x_103);
x_107 = lean_array_uset(x_40, x_102, x_106);
x_108 = lean_nat_shiftl(x_99, x_31);
x_109 = lean_nat_div(x_108, x_33);
lean_dec(x_108);
x_110 = lean_array_get_size(x_107);
x_111 = lean_nat_dec_le(x_109, x_110);
lean_dec(x_110);
lean_dec(x_109);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; 
x_112 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectMVars_visit_spec__1(lean_box(0), x_107);
lean_inc(x_112);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_99);
lean_ctor_set(x_113, 1, x_112);
x_45 = x_113;
x_46 = x_99;
x_47 = x_112;
goto block_84;
}
else
{
lean_object* x_114; 
lean_inc(x_107);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_99);
lean_ctor_set(x_114, 1, x_107);
x_45 = x_114;
x_46 = x_99;
x_47 = x_107;
goto block_84;
}
}
else
{
lean_object* x_115; lean_object* x_116; 
lean_dec(x_103);
lean_dec(x_86);
x_115 = lean_unsigned_to_nat(0u);
lean_inc(x_40);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_40);
x_45 = x_116;
x_46 = x_115;
x_47 = x_40;
goto block_84;
}
block_84:
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint64_t x_53; lean_object* x_54; uint64_t x_55; uint64_t x_56; uint64_t x_57; lean_object* x_58; uint64_t x_59; uint64_t x_60; uint64_t x_61; size_t x_62; size_t x_63; lean_object* x_64; size_t x_65; size_t x_66; size_t x_67; lean_object* x_68; uint8_t x_69; 
x_48 = lean_mk_string_unchecked("min_le_right", 12, 12);
x_49 = l_Lean_Name_mkStr2(x_41, x_48);
x_50 = l_Lean_Expr_const___override(x_49, x_44);
x_51 = l_Lean_mkAppB(x_50, x_32, x_34);
x_52 = lean_array_get_size(x_47);
x_53 = l_Lean_Expr_hash(x_51);
x_54 = lean_unsigned_to_nat(32u);
x_55 = lean_uint64_of_nat(x_54);
x_56 = lean_uint64_shift_right(x_53, x_55);
x_57 = lean_uint64_xor(x_53, x_56);
x_58 = lean_unsigned_to_nat(16u);
x_59 = lean_uint64_of_nat(x_58);
x_60 = lean_uint64_shift_right(x_57, x_59);
x_61 = lean_uint64_xor(x_57, x_60);
x_62 = lean_uint64_to_usize(x_61);
x_63 = lean_usize_of_nat(x_52);
lean_dec(x_52);
x_64 = lean_unsigned_to_nat(1u);
x_65 = lean_usize_of_nat(x_64);
x_66 = lean_usize_sub(x_63, x_65);
x_67 = lean_usize_land(x_62, x_66);
x_68 = lean_array_uget(x_47, x_67);
x_69 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectMVars_visit_spec__0___redArg(x_51, x_68);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
lean_dec(x_45);
x_70 = lean_box(0);
x_71 = lean_nat_add(x_46, x_64);
x_72 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_72, 0, x_51);
lean_ctor_set(x_72, 1, x_70);
lean_ctor_set(x_72, 2, x_68);
x_73 = lean_array_uset(x_47, x_67, x_72);
x_74 = lean_nat_shiftl(x_71, x_31);
x_75 = lean_nat_div(x_74, x_33);
lean_dec(x_74);
x_76 = lean_array_get_size(x_73);
x_77 = lean_nat_dec_le(x_75, x_76);
lean_dec(x_76);
lean_dec(x_75);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectMVars_visit_spec__1(lean_box(0), x_73);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_71);
lean_ctor_set(x_79, 1, x_78);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_15);
return x_80;
}
else
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_71);
lean_ctor_set(x_81, 1, x_73);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_15);
return x_82;
}
}
else
{
lean_object* x_83; 
lean_dec(x_68);
lean_dec(x_51);
lean_dec(x_47);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_45);
lean_ctor_set(x_83, 1, x_15);
return x_83;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, uint8_t x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; 
x_17 = l_Lean_Expr_getAppFnArgs(x_1);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
switch (lean_obj_tag(x_18)) {
case 0:
{
uint8_t x_19; 
lean_dec(x_5);
lean_dec(x_4);
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_17, 0);
lean_dec(x_20);
lean_ctor_set(x_17, 0, x_2);
x_21 = lean_box(x_10);
x_22 = lean_apply_11(x_3, x_17, x_7, x_8, x_9, x_21, x_11, x_12, x_13, x_14, x_15, x_16);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_dec(x_17);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_2);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_box(x_10);
x_26 = lean_apply_11(x_3, x_24, x_7, x_8, x_9, x_25, x_11, x_12, x_13, x_14, x_15, x_16);
return x_26;
}
}
case 1:
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_18, 0);
lean_inc(x_27);
switch (lean_obj_tag(x_27)) {
case 0:
{
uint8_t x_28; 
lean_dec(x_5);
lean_dec(x_4);
x_28 = !lean_is_exclusive(x_17);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_17, 0);
lean_dec(x_29);
x_30 = lean_ctor_get(x_18, 1);
lean_inc(x_30);
lean_dec(x_18);
x_31 = l_Lean_Name_str___override(x_2, x_30);
lean_ctor_set(x_17, 0, x_31);
x_32 = lean_box(x_10);
x_33 = lean_apply_11(x_3, x_17, x_7, x_8, x_9, x_32, x_11, x_12, x_13, x_14, x_15, x_16);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_34 = lean_ctor_get(x_17, 1);
lean_inc(x_34);
lean_dec(x_17);
x_35 = lean_ctor_get(x_18, 1);
lean_inc(x_35);
lean_dec(x_18);
x_36 = l_Lean_Name_str___override(x_2, x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_34);
x_38 = lean_box(x_10);
x_39 = lean_apply_11(x_3, x_37, x_7, x_8, x_9, x_38, x_11, x_12, x_13, x_14, x_15, x_16);
return x_39;
}
}
case 1:
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_27, 0);
lean_inc(x_40);
switch (lean_obj_tag(x_40)) {
case 0:
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_17);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_42 = lean_ctor_get(x_17, 1);
x_43 = lean_ctor_get(x_17, 0);
lean_dec(x_43);
x_44 = lean_ctor_get(x_18, 1);
lean_inc(x_44);
lean_dec(x_18);
x_45 = lean_ctor_get(x_27, 1);
lean_inc(x_45);
lean_dec(x_27);
x_46 = lean_string_dec_eq(x_45, x_4);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_5);
lean_dec(x_4);
x_47 = l_Lean_Name_str___override(x_2, x_45);
x_48 = l_Lean_Name_str___override(x_47, x_44);
lean_ctor_set(x_17, 0, x_48);
x_49 = lean_box(x_10);
x_50 = lean_apply_11(x_3, x_17, x_7, x_8, x_9, x_49, x_11, x_12, x_13, x_14, x_15, x_16);
return x_50;
}
else
{
lean_object* x_51; uint8_t x_52; 
lean_dec(x_45);
x_51 = lean_mk_string_unchecked("cast", 4, 4);
x_52 = lean_string_dec_eq(x_44, x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_51);
lean_dec(x_5);
x_53 = l_Lean_Name_str___override(x_2, x_4);
x_54 = l_Lean_Name_str___override(x_53, x_44);
lean_ctor_set(x_17, 0, x_54);
x_55 = lean_box(x_10);
x_56 = lean_apply_11(x_3, x_17, x_7, x_8, x_9, x_55, x_11, x_12, x_13, x_14, x_15, x_16);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; 
lean_dec(x_44);
x_57 = lean_array_get_size(x_42);
x_58 = lean_unsigned_to_nat(3u);
x_59 = lean_nat_dec_eq(x_57, x_58);
lean_dec(x_57);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_5);
x_60 = l_Lean_Name_str___override(x_2, x_4);
x_61 = l_Lean_Name_str___override(x_60, x_51);
lean_ctor_set(x_17, 0, x_61);
x_62 = lean_box(x_10);
x_63 = lean_apply_11(x_3, x_17, x_7, x_8, x_9, x_62, x_11, x_12, x_13, x_14, x_15, x_16);
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_unsigned_to_nat(0u);
x_65 = lean_array_fget(x_42, x_64);
switch (lean_obj_tag(x_65)) {
case 0:
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_5);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
lean_dec(x_65);
x_67 = l_Lean_Name_str___override(x_2, x_4);
x_68 = l_Lean_Name_str___override(x_67, x_51);
x_69 = l_Lean_Expr_bvar___override(x_66);
x_70 = lean_unsigned_to_nat(1u);
x_71 = lean_array_fget(x_42, x_70);
x_72 = lean_unsigned_to_nat(2u);
x_73 = lean_array_fget(x_42, x_72);
lean_dec(x_42);
x_74 = lean_mk_empty_array_with_capacity(x_58);
x_75 = lean_array_push(x_74, x_69);
x_76 = lean_array_push(x_75, x_71);
x_77 = lean_array_push(x_76, x_73);
lean_ctor_set(x_17, 1, x_77);
lean_ctor_set(x_17, 0, x_68);
x_78 = lean_box(x_10);
x_79 = lean_apply_11(x_3, x_17, x_7, x_8, x_9, x_78, x_11, x_12, x_13, x_14, x_15, x_16);
return x_79;
}
case 1:
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_5);
x_80 = lean_ctor_get(x_65, 0);
lean_inc(x_80);
lean_dec(x_65);
x_81 = l_Lean_Name_str___override(x_2, x_4);
x_82 = l_Lean_Name_str___override(x_81, x_51);
x_83 = l_Lean_Expr_fvar___override(x_80);
x_84 = lean_unsigned_to_nat(1u);
x_85 = lean_array_fget(x_42, x_84);
x_86 = lean_unsigned_to_nat(2u);
x_87 = lean_array_fget(x_42, x_86);
lean_dec(x_42);
x_88 = lean_mk_empty_array_with_capacity(x_58);
x_89 = lean_array_push(x_88, x_83);
x_90 = lean_array_push(x_89, x_85);
x_91 = lean_array_push(x_90, x_87);
lean_ctor_set(x_17, 1, x_91);
lean_ctor_set(x_17, 0, x_82);
x_92 = lean_box(x_10);
x_93 = lean_apply_11(x_3, x_17, x_7, x_8, x_9, x_92, x_11, x_12, x_13, x_14, x_15, x_16);
return x_93;
}
case 2:
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec(x_5);
x_94 = lean_ctor_get(x_65, 0);
lean_inc(x_94);
lean_dec(x_65);
x_95 = l_Lean_Name_str___override(x_2, x_4);
x_96 = l_Lean_Name_str___override(x_95, x_51);
x_97 = l_Lean_Expr_mvar___override(x_94);
x_98 = lean_unsigned_to_nat(1u);
x_99 = lean_array_fget(x_42, x_98);
x_100 = lean_unsigned_to_nat(2u);
x_101 = lean_array_fget(x_42, x_100);
lean_dec(x_42);
x_102 = lean_mk_empty_array_with_capacity(x_58);
x_103 = lean_array_push(x_102, x_97);
x_104 = lean_array_push(x_103, x_99);
x_105 = lean_array_push(x_104, x_101);
lean_ctor_set(x_17, 1, x_105);
lean_ctor_set(x_17, 0, x_96);
x_106 = lean_box(x_10);
x_107 = lean_apply_11(x_3, x_17, x_7, x_8, x_9, x_106, x_11, x_12, x_13, x_14, x_15, x_16);
return x_107;
}
case 3:
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec(x_5);
x_108 = lean_ctor_get(x_65, 0);
lean_inc(x_108);
lean_dec(x_65);
x_109 = l_Lean_Name_str___override(x_2, x_4);
x_110 = l_Lean_Name_str___override(x_109, x_51);
x_111 = l_Lean_Expr_sort___override(x_108);
x_112 = lean_unsigned_to_nat(1u);
x_113 = lean_array_fget(x_42, x_112);
x_114 = lean_unsigned_to_nat(2u);
x_115 = lean_array_fget(x_42, x_114);
lean_dec(x_42);
x_116 = lean_mk_empty_array_with_capacity(x_58);
x_117 = lean_array_push(x_116, x_111);
x_118 = lean_array_push(x_117, x_113);
x_119 = lean_array_push(x_118, x_115);
lean_ctor_set(x_17, 1, x_119);
lean_ctor_set(x_17, 0, x_110);
x_120 = lean_box(x_10);
x_121 = lean_apply_11(x_3, x_17, x_7, x_8, x_9, x_120, x_11, x_12, x_13, x_14, x_15, x_16);
return x_121;
}
case 4:
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_122 = lean_ctor_get(x_65, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_65, 1);
lean_inc(x_123);
lean_dec(x_65);
lean_inc(x_2);
x_124 = l_Lean_Name_str___override(x_2, x_4);
x_125 = l_Lean_Name_str___override(x_124, x_51);
x_126 = lean_unsigned_to_nat(1u);
x_127 = lean_array_fget(x_42, x_126);
x_128 = lean_unsigned_to_nat(2u);
x_129 = lean_array_fget(x_42, x_128);
lean_dec(x_42);
x_130 = lean_mk_empty_array_with_capacity(x_58);
switch (lean_obj_tag(x_122)) {
case 0:
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_dec(x_5);
x_131 = l_Lean_Expr_const___override(x_2, x_123);
x_132 = lean_array_push(x_130, x_131);
x_133 = lean_array_push(x_132, x_127);
x_134 = lean_array_push(x_133, x_129);
lean_ctor_set(x_17, 1, x_134);
lean_ctor_set(x_17, 0, x_125);
x_135 = lean_box(x_10);
x_136 = lean_apply_11(x_3, x_17, x_7, x_8, x_9, x_135, x_11, x_12, x_13, x_14, x_15, x_16);
return x_136;
}
case 1:
{
lean_object* x_137; 
x_137 = lean_ctor_get(x_122, 0);
lean_inc(x_137);
switch (lean_obj_tag(x_137)) {
case 0:
{
lean_object* x_138; lean_object* x_139; uint8_t x_140; 
x_138 = lean_ctor_get(x_122, 1);
lean_inc(x_138);
lean_dec(x_122);
x_139 = lean_mk_string_unchecked("Int", 3, 3);
x_140 = lean_string_dec_eq(x_138, x_139);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
lean_dec(x_139);
lean_dec(x_5);
x_141 = l_Lean_Name_str___override(x_2, x_138);
x_142 = l_Lean_Expr_const___override(x_141, x_123);
x_143 = lean_array_push(x_130, x_142);
x_144 = lean_array_push(x_143, x_127);
x_145 = lean_array_push(x_144, x_129);
lean_ctor_set(x_17, 1, x_145);
lean_ctor_set(x_17, 0, x_125);
x_146 = lean_box(x_10);
x_147 = lean_apply_11(x_3, x_17, x_7, x_8, x_9, x_146, x_11, x_12, x_13, x_14, x_15, x_16);
return x_147;
}
else
{
lean_dec(x_138);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; uint64_t x_161; lean_object* x_162; uint64_t x_163; uint64_t x_164; uint64_t x_165; lean_object* x_166; uint64_t x_167; uint64_t x_168; uint64_t x_169; size_t x_170; size_t x_171; size_t x_172; size_t x_173; size_t x_174; lean_object* x_175; uint8_t x_176; 
lean_dec(x_130);
lean_dec(x_127);
lean_dec(x_125);
lean_free_object(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_148 = lean_unsigned_to_nat(8u);
x_149 = lean_nat_shiftl(x_148, x_128);
x_150 = lean_nat_div(x_149, x_58);
lean_dec(x_149);
x_151 = l_Nat_nextPowerOfTwo(x_150);
lean_dec(x_150);
x_152 = lean_box(0);
x_153 = lean_mk_array(x_151, x_152);
x_154 = lean_mk_string_unchecked("Lean", 4, 4);
x_155 = lean_mk_string_unchecked("Omega", 5, 5);
x_156 = lean_mk_string_unchecked("emod_ofNat_nonneg", 17, 17);
x_157 = l_Lean_Name_mkStr4(x_154, x_155, x_139, x_156);
x_158 = l_Lean_Expr_const___override(x_157, x_123);
x_159 = l_Lean_mkAppB(x_158, x_129, x_5);
x_160 = lean_array_get_size(x_153);
x_161 = l_Lean_Expr_hash(x_159);
x_162 = lean_unsigned_to_nat(32u);
x_163 = lean_uint64_of_nat(x_162);
x_164 = lean_uint64_shift_right(x_161, x_163);
x_165 = lean_uint64_xor(x_161, x_164);
x_166 = lean_unsigned_to_nat(16u);
x_167 = lean_uint64_of_nat(x_166);
x_168 = lean_uint64_shift_right(x_165, x_167);
x_169 = lean_uint64_xor(x_165, x_168);
x_170 = lean_uint64_to_usize(x_169);
x_171 = lean_usize_of_nat(x_160);
lean_dec(x_160);
x_172 = lean_usize_of_nat(x_126);
x_173 = lean_usize_sub(x_171, x_172);
x_174 = lean_usize_land(x_170, x_173);
x_175 = lean_array_uget(x_153, x_174);
x_176 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectMVars_visit_spec__0___redArg(x_159, x_175);
if (x_176 == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; uint8_t x_183; 
x_177 = lean_box(0);
x_178 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_178, 0, x_159);
lean_ctor_set(x_178, 1, x_177);
lean_ctor_set(x_178, 2, x_175);
x_179 = lean_array_uset(x_153, x_174, x_178);
x_180 = lean_nat_shiftl(x_126, x_128);
x_181 = lean_nat_div(x_180, x_58);
lean_dec(x_180);
x_182 = lean_array_get_size(x_179);
x_183 = lean_nat_dec_le(x_181, x_182);
lean_dec(x_182);
lean_dec(x_181);
if (x_183 == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_184 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectMVars_visit_spec__1(lean_box(0), x_179);
x_185 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_185, 0, x_126);
lean_ctor_set(x_185, 1, x_184);
x_186 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set(x_186, 1, x_16);
return x_186;
}
else
{
lean_object* x_187; lean_object* x_188; 
x_187 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_187, 0, x_126);
lean_ctor_set(x_187, 1, x_179);
x_188 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_188, 0, x_187);
lean_ctor_set(x_188, 1, x_16);
return x_188;
}
}
else
{
lean_object* x_189; lean_object* x_190; 
lean_dec(x_175);
lean_dec(x_159);
x_189 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_189, 0, x_64);
lean_ctor_set(x_189, 1, x_153);
x_190 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_190, 0, x_189);
lean_ctor_set(x_190, 1, x_16);
return x_190;
}
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
lean_dec(x_5);
x_191 = l_Lean_Name_str___override(x_2, x_139);
x_192 = l_Lean_Expr_const___override(x_191, x_123);
x_193 = lean_array_push(x_130, x_192);
x_194 = lean_array_push(x_193, x_127);
x_195 = lean_array_push(x_194, x_129);
lean_ctor_set(x_17, 1, x_195);
lean_ctor_set(x_17, 0, x_125);
x_196 = lean_box(x_10);
x_197 = lean_apply_11(x_3, x_17, x_7, x_8, x_9, x_196, x_11, x_12, x_13, x_14, x_15, x_16);
return x_197;
}
}
}
case 1:
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
lean_dec(x_5);
lean_dec(x_2);
x_198 = lean_ctor_get(x_122, 1);
lean_inc(x_198);
lean_dec(x_122);
x_199 = lean_ctor_get(x_137, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_137, 1);
lean_inc(x_200);
lean_dec(x_137);
x_201 = l_Lean_Name_str___override(x_199, x_200);
x_202 = l_Lean_Name_str___override(x_201, x_198);
x_203 = l_Lean_Expr_const___override(x_202, x_123);
x_204 = lean_array_push(x_130, x_203);
x_205 = lean_array_push(x_204, x_127);
x_206 = lean_array_push(x_205, x_129);
lean_ctor_set(x_17, 1, x_206);
lean_ctor_set(x_17, 0, x_125);
x_207 = lean_box(x_10);
x_208 = lean_apply_11(x_3, x_17, x_7, x_8, x_9, x_207, x_11, x_12, x_13, x_14, x_15, x_16);
return x_208;
}
default: 
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
lean_dec(x_5);
lean_dec(x_2);
x_209 = lean_ctor_get(x_122, 1);
lean_inc(x_209);
lean_dec(x_122);
x_210 = lean_ctor_get(x_137, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_137, 1);
lean_inc(x_211);
lean_dec(x_137);
x_212 = l_Lean_Name_num___override(x_210, x_211);
x_213 = l_Lean_Name_str___override(x_212, x_209);
x_214 = l_Lean_Expr_const___override(x_213, x_123);
x_215 = lean_array_push(x_130, x_214);
x_216 = lean_array_push(x_215, x_127);
x_217 = lean_array_push(x_216, x_129);
lean_ctor_set(x_17, 1, x_217);
lean_ctor_set(x_17, 0, x_125);
x_218 = lean_box(x_10);
x_219 = lean_apply_11(x_3, x_17, x_7, x_8, x_9, x_218, x_11, x_12, x_13, x_14, x_15, x_16);
return x_219;
}
}
}
default: 
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
lean_dec(x_5);
lean_dec(x_2);
x_220 = lean_ctor_get(x_122, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_122, 1);
lean_inc(x_221);
lean_dec(x_122);
x_222 = l_Lean_Name_num___override(x_220, x_221);
x_223 = l_Lean_Expr_const___override(x_222, x_123);
x_224 = lean_array_push(x_130, x_223);
x_225 = lean_array_push(x_224, x_127);
x_226 = lean_array_push(x_225, x_129);
lean_ctor_set(x_17, 1, x_226);
lean_ctor_set(x_17, 0, x_125);
x_227 = lean_box(x_10);
x_228 = lean_apply_11(x_3, x_17, x_7, x_8, x_9, x_227, x_11, x_12, x_13, x_14, x_15, x_16);
return x_228;
}
}
}
case 5:
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; 
lean_dec(x_5);
x_229 = lean_ctor_get(x_65, 0);
lean_inc(x_229);
x_230 = lean_ctor_get(x_65, 1);
lean_inc(x_230);
lean_dec(x_65);
x_231 = l_Lean_Name_str___override(x_2, x_4);
x_232 = l_Lean_Name_str___override(x_231, x_51);
x_233 = l_Lean_Expr_app___override(x_229, x_230);
x_234 = lean_unsigned_to_nat(1u);
x_235 = lean_array_fget(x_42, x_234);
x_236 = lean_unsigned_to_nat(2u);
x_237 = lean_array_fget(x_42, x_236);
lean_dec(x_42);
x_238 = lean_mk_empty_array_with_capacity(x_58);
x_239 = lean_array_push(x_238, x_233);
x_240 = lean_array_push(x_239, x_235);
x_241 = lean_array_push(x_240, x_237);
lean_ctor_set(x_17, 1, x_241);
lean_ctor_set(x_17, 0, x_232);
x_242 = lean_box(x_10);
x_243 = lean_apply_11(x_3, x_17, x_7, x_8, x_9, x_242, x_11, x_12, x_13, x_14, x_15, x_16);
return x_243;
}
case 6:
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; uint8_t x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; 
lean_dec(x_5);
x_244 = lean_ctor_get(x_65, 0);
lean_inc(x_244);
x_245 = lean_ctor_get(x_65, 1);
lean_inc(x_245);
x_246 = lean_ctor_get(x_65, 2);
lean_inc(x_246);
x_247 = lean_ctor_get_uint8(x_65, sizeof(void*)*3 + 8);
lean_dec(x_65);
x_248 = l_Lean_Name_str___override(x_2, x_4);
x_249 = l_Lean_Name_str___override(x_248, x_51);
x_250 = l_Lean_Expr_lam___override(x_244, x_245, x_246, x_247);
x_251 = lean_unsigned_to_nat(1u);
x_252 = lean_array_fget(x_42, x_251);
x_253 = lean_unsigned_to_nat(2u);
x_254 = lean_array_fget(x_42, x_253);
lean_dec(x_42);
x_255 = lean_mk_empty_array_with_capacity(x_58);
x_256 = lean_array_push(x_255, x_250);
x_257 = lean_array_push(x_256, x_252);
x_258 = lean_array_push(x_257, x_254);
lean_ctor_set(x_17, 1, x_258);
lean_ctor_set(x_17, 0, x_249);
x_259 = lean_box(x_10);
x_260 = lean_apply_11(x_3, x_17, x_7, x_8, x_9, x_259, x_11, x_12, x_13, x_14, x_15, x_16);
return x_260;
}
case 7:
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; uint8_t x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; 
lean_dec(x_5);
x_261 = lean_ctor_get(x_65, 0);
lean_inc(x_261);
x_262 = lean_ctor_get(x_65, 1);
lean_inc(x_262);
x_263 = lean_ctor_get(x_65, 2);
lean_inc(x_263);
x_264 = lean_ctor_get_uint8(x_65, sizeof(void*)*3 + 8);
lean_dec(x_65);
x_265 = l_Lean_Name_str___override(x_2, x_4);
x_266 = l_Lean_Name_str___override(x_265, x_51);
x_267 = l_Lean_Expr_forallE___override(x_261, x_262, x_263, x_264);
x_268 = lean_unsigned_to_nat(1u);
x_269 = lean_array_fget(x_42, x_268);
x_270 = lean_unsigned_to_nat(2u);
x_271 = lean_array_fget(x_42, x_270);
lean_dec(x_42);
x_272 = lean_mk_empty_array_with_capacity(x_58);
x_273 = lean_array_push(x_272, x_267);
x_274 = lean_array_push(x_273, x_269);
x_275 = lean_array_push(x_274, x_271);
lean_ctor_set(x_17, 1, x_275);
lean_ctor_set(x_17, 0, x_266);
x_276 = lean_box(x_10);
x_277 = lean_apply_11(x_3, x_17, x_7, x_8, x_9, x_276, x_11, x_12, x_13, x_14, x_15, x_16);
return x_277;
}
case 8:
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; uint8_t x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; 
lean_dec(x_5);
x_278 = lean_ctor_get(x_65, 0);
lean_inc(x_278);
x_279 = lean_ctor_get(x_65, 1);
lean_inc(x_279);
x_280 = lean_ctor_get(x_65, 2);
lean_inc(x_280);
x_281 = lean_ctor_get(x_65, 3);
lean_inc(x_281);
x_282 = lean_ctor_get_uint8(x_65, sizeof(void*)*4 + 8);
lean_dec(x_65);
x_283 = l_Lean_Name_str___override(x_2, x_4);
x_284 = l_Lean_Name_str___override(x_283, x_51);
x_285 = l_Lean_Expr_letE___override(x_278, x_279, x_280, x_281, x_282);
x_286 = lean_unsigned_to_nat(1u);
x_287 = lean_array_fget(x_42, x_286);
x_288 = lean_unsigned_to_nat(2u);
x_289 = lean_array_fget(x_42, x_288);
lean_dec(x_42);
x_290 = lean_mk_empty_array_with_capacity(x_58);
x_291 = lean_array_push(x_290, x_285);
x_292 = lean_array_push(x_291, x_287);
x_293 = lean_array_push(x_292, x_289);
lean_ctor_set(x_17, 1, x_293);
lean_ctor_set(x_17, 0, x_284);
x_294 = lean_box(x_10);
x_295 = lean_apply_11(x_3, x_17, x_7, x_8, x_9, x_294, x_11, x_12, x_13, x_14, x_15, x_16);
return x_295;
}
case 9:
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; 
lean_dec(x_5);
x_296 = lean_ctor_get(x_65, 0);
lean_inc(x_296);
lean_dec(x_65);
x_297 = l_Lean_Name_str___override(x_2, x_4);
x_298 = l_Lean_Name_str___override(x_297, x_51);
x_299 = l_Lean_Expr_lit___override(x_296);
x_300 = lean_unsigned_to_nat(1u);
x_301 = lean_array_fget(x_42, x_300);
x_302 = lean_unsigned_to_nat(2u);
x_303 = lean_array_fget(x_42, x_302);
lean_dec(x_42);
x_304 = lean_mk_empty_array_with_capacity(x_58);
x_305 = lean_array_push(x_304, x_299);
x_306 = lean_array_push(x_305, x_301);
x_307 = lean_array_push(x_306, x_303);
lean_ctor_set(x_17, 1, x_307);
lean_ctor_set(x_17, 0, x_298);
x_308 = lean_box(x_10);
x_309 = lean_apply_11(x_3, x_17, x_7, x_8, x_9, x_308, x_11, x_12, x_13, x_14, x_15, x_16);
return x_309;
}
case 10:
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; 
lean_dec(x_5);
x_310 = lean_ctor_get(x_65, 0);
lean_inc(x_310);
x_311 = lean_ctor_get(x_65, 1);
lean_inc(x_311);
lean_dec(x_65);
x_312 = l_Lean_Name_str___override(x_2, x_4);
x_313 = l_Lean_Name_str___override(x_312, x_51);
x_314 = l_Lean_Expr_mdata___override(x_310, x_311);
x_315 = lean_unsigned_to_nat(1u);
x_316 = lean_array_fget(x_42, x_315);
x_317 = lean_unsigned_to_nat(2u);
x_318 = lean_array_fget(x_42, x_317);
lean_dec(x_42);
x_319 = lean_mk_empty_array_with_capacity(x_58);
x_320 = lean_array_push(x_319, x_314);
x_321 = lean_array_push(x_320, x_316);
x_322 = lean_array_push(x_321, x_318);
lean_ctor_set(x_17, 1, x_322);
lean_ctor_set(x_17, 0, x_313);
x_323 = lean_box(x_10);
x_324 = lean_apply_11(x_3, x_17, x_7, x_8, x_9, x_323, x_11, x_12, x_13, x_14, x_15, x_16);
return x_324;
}
default: 
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; 
lean_dec(x_5);
x_325 = lean_ctor_get(x_65, 0);
lean_inc(x_325);
x_326 = lean_ctor_get(x_65, 1);
lean_inc(x_326);
x_327 = lean_ctor_get(x_65, 2);
lean_inc(x_327);
lean_dec(x_65);
x_328 = l_Lean_Name_str___override(x_2, x_4);
x_329 = l_Lean_Name_str___override(x_328, x_51);
x_330 = l_Lean_Expr_proj___override(x_325, x_326, x_327);
x_331 = lean_unsigned_to_nat(1u);
x_332 = lean_array_fget(x_42, x_331);
x_333 = lean_unsigned_to_nat(2u);
x_334 = lean_array_fget(x_42, x_333);
lean_dec(x_42);
x_335 = lean_mk_empty_array_with_capacity(x_58);
x_336 = lean_array_push(x_335, x_330);
x_337 = lean_array_push(x_336, x_332);
x_338 = lean_array_push(x_337, x_334);
lean_ctor_set(x_17, 1, x_338);
lean_ctor_set(x_17, 0, x_329);
x_339 = lean_box(x_10);
x_340 = lean_apply_11(x_3, x_17, x_7, x_8, x_9, x_339, x_11, x_12, x_13, x_14, x_15, x_16);
return x_340;
}
}
}
}
}
}
else
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; uint8_t x_344; 
x_341 = lean_ctor_get(x_17, 1);
lean_inc(x_341);
lean_dec(x_17);
x_342 = lean_ctor_get(x_18, 1);
lean_inc(x_342);
lean_dec(x_18);
x_343 = lean_ctor_get(x_27, 1);
lean_inc(x_343);
lean_dec(x_27);
x_344 = lean_string_dec_eq(x_343, x_4);
if (x_344 == 0)
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; 
lean_dec(x_5);
lean_dec(x_4);
x_345 = l_Lean_Name_str___override(x_2, x_343);
x_346 = l_Lean_Name_str___override(x_345, x_342);
x_347 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_347, 0, x_346);
lean_ctor_set(x_347, 1, x_341);
x_348 = lean_box(x_10);
x_349 = lean_apply_11(x_3, x_347, x_7, x_8, x_9, x_348, x_11, x_12, x_13, x_14, x_15, x_16);
return x_349;
}
else
{
lean_object* x_350; uint8_t x_351; 
lean_dec(x_343);
x_350 = lean_mk_string_unchecked("cast", 4, 4);
x_351 = lean_string_dec_eq(x_342, x_350);
if (x_351 == 0)
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; 
lean_dec(x_350);
lean_dec(x_5);
x_352 = l_Lean_Name_str___override(x_2, x_4);
x_353 = l_Lean_Name_str___override(x_352, x_342);
x_354 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_354, 0, x_353);
lean_ctor_set(x_354, 1, x_341);
x_355 = lean_box(x_10);
x_356 = lean_apply_11(x_3, x_354, x_7, x_8, x_9, x_355, x_11, x_12, x_13, x_14, x_15, x_16);
return x_356;
}
else
{
lean_object* x_357; lean_object* x_358; uint8_t x_359; 
lean_dec(x_342);
x_357 = lean_array_get_size(x_341);
x_358 = lean_unsigned_to_nat(3u);
x_359 = lean_nat_dec_eq(x_357, x_358);
lean_dec(x_357);
if (x_359 == 0)
{
lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; 
lean_dec(x_5);
x_360 = l_Lean_Name_str___override(x_2, x_4);
x_361 = l_Lean_Name_str___override(x_360, x_350);
x_362 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_362, 0, x_361);
lean_ctor_set(x_362, 1, x_341);
x_363 = lean_box(x_10);
x_364 = lean_apply_11(x_3, x_362, x_7, x_8, x_9, x_363, x_11, x_12, x_13, x_14, x_15, x_16);
return x_364;
}
else
{
lean_object* x_365; lean_object* x_366; 
x_365 = lean_unsigned_to_nat(0u);
x_366 = lean_array_fget(x_341, x_365);
switch (lean_obj_tag(x_366)) {
case 0:
{
lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; 
lean_dec(x_5);
x_367 = lean_ctor_get(x_366, 0);
lean_inc(x_367);
lean_dec(x_366);
x_368 = l_Lean_Name_str___override(x_2, x_4);
x_369 = l_Lean_Name_str___override(x_368, x_350);
x_370 = l_Lean_Expr_bvar___override(x_367);
x_371 = lean_unsigned_to_nat(1u);
x_372 = lean_array_fget(x_341, x_371);
x_373 = lean_unsigned_to_nat(2u);
x_374 = lean_array_fget(x_341, x_373);
lean_dec(x_341);
x_375 = lean_mk_empty_array_with_capacity(x_358);
x_376 = lean_array_push(x_375, x_370);
x_377 = lean_array_push(x_376, x_372);
x_378 = lean_array_push(x_377, x_374);
x_379 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_379, 0, x_369);
lean_ctor_set(x_379, 1, x_378);
x_380 = lean_box(x_10);
x_381 = lean_apply_11(x_3, x_379, x_7, x_8, x_9, x_380, x_11, x_12, x_13, x_14, x_15, x_16);
return x_381;
}
case 1:
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; 
lean_dec(x_5);
x_382 = lean_ctor_get(x_366, 0);
lean_inc(x_382);
lean_dec(x_366);
x_383 = l_Lean_Name_str___override(x_2, x_4);
x_384 = l_Lean_Name_str___override(x_383, x_350);
x_385 = l_Lean_Expr_fvar___override(x_382);
x_386 = lean_unsigned_to_nat(1u);
x_387 = lean_array_fget(x_341, x_386);
x_388 = lean_unsigned_to_nat(2u);
x_389 = lean_array_fget(x_341, x_388);
lean_dec(x_341);
x_390 = lean_mk_empty_array_with_capacity(x_358);
x_391 = lean_array_push(x_390, x_385);
x_392 = lean_array_push(x_391, x_387);
x_393 = lean_array_push(x_392, x_389);
x_394 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_394, 0, x_384);
lean_ctor_set(x_394, 1, x_393);
x_395 = lean_box(x_10);
x_396 = lean_apply_11(x_3, x_394, x_7, x_8, x_9, x_395, x_11, x_12, x_13, x_14, x_15, x_16);
return x_396;
}
case 2:
{
lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; 
lean_dec(x_5);
x_397 = lean_ctor_get(x_366, 0);
lean_inc(x_397);
lean_dec(x_366);
x_398 = l_Lean_Name_str___override(x_2, x_4);
x_399 = l_Lean_Name_str___override(x_398, x_350);
x_400 = l_Lean_Expr_mvar___override(x_397);
x_401 = lean_unsigned_to_nat(1u);
x_402 = lean_array_fget(x_341, x_401);
x_403 = lean_unsigned_to_nat(2u);
x_404 = lean_array_fget(x_341, x_403);
lean_dec(x_341);
x_405 = lean_mk_empty_array_with_capacity(x_358);
x_406 = lean_array_push(x_405, x_400);
x_407 = lean_array_push(x_406, x_402);
x_408 = lean_array_push(x_407, x_404);
x_409 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_409, 0, x_399);
lean_ctor_set(x_409, 1, x_408);
x_410 = lean_box(x_10);
x_411 = lean_apply_11(x_3, x_409, x_7, x_8, x_9, x_410, x_11, x_12, x_13, x_14, x_15, x_16);
return x_411;
}
case 3:
{
lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; 
lean_dec(x_5);
x_412 = lean_ctor_get(x_366, 0);
lean_inc(x_412);
lean_dec(x_366);
x_413 = l_Lean_Name_str___override(x_2, x_4);
x_414 = l_Lean_Name_str___override(x_413, x_350);
x_415 = l_Lean_Expr_sort___override(x_412);
x_416 = lean_unsigned_to_nat(1u);
x_417 = lean_array_fget(x_341, x_416);
x_418 = lean_unsigned_to_nat(2u);
x_419 = lean_array_fget(x_341, x_418);
lean_dec(x_341);
x_420 = lean_mk_empty_array_with_capacity(x_358);
x_421 = lean_array_push(x_420, x_415);
x_422 = lean_array_push(x_421, x_417);
x_423 = lean_array_push(x_422, x_419);
x_424 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_424, 0, x_414);
lean_ctor_set(x_424, 1, x_423);
x_425 = lean_box(x_10);
x_426 = lean_apply_11(x_3, x_424, x_7, x_8, x_9, x_425, x_11, x_12, x_13, x_14, x_15, x_16);
return x_426;
}
case 4:
{
lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; 
x_427 = lean_ctor_get(x_366, 0);
lean_inc(x_427);
x_428 = lean_ctor_get(x_366, 1);
lean_inc(x_428);
lean_dec(x_366);
lean_inc(x_2);
x_429 = l_Lean_Name_str___override(x_2, x_4);
x_430 = l_Lean_Name_str___override(x_429, x_350);
x_431 = lean_unsigned_to_nat(1u);
x_432 = lean_array_fget(x_341, x_431);
x_433 = lean_unsigned_to_nat(2u);
x_434 = lean_array_fget(x_341, x_433);
lean_dec(x_341);
x_435 = lean_mk_empty_array_with_capacity(x_358);
switch (lean_obj_tag(x_427)) {
case 0:
{
lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; 
lean_dec(x_5);
x_436 = l_Lean_Expr_const___override(x_2, x_428);
x_437 = lean_array_push(x_435, x_436);
x_438 = lean_array_push(x_437, x_432);
x_439 = lean_array_push(x_438, x_434);
x_440 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_440, 0, x_430);
lean_ctor_set(x_440, 1, x_439);
x_441 = lean_box(x_10);
x_442 = lean_apply_11(x_3, x_440, x_7, x_8, x_9, x_441, x_11, x_12, x_13, x_14, x_15, x_16);
return x_442;
}
case 1:
{
lean_object* x_443; 
x_443 = lean_ctor_get(x_427, 0);
lean_inc(x_443);
switch (lean_obj_tag(x_443)) {
case 0:
{
lean_object* x_444; lean_object* x_445; uint8_t x_446; 
x_444 = lean_ctor_get(x_427, 1);
lean_inc(x_444);
lean_dec(x_427);
x_445 = lean_mk_string_unchecked("Int", 3, 3);
x_446 = lean_string_dec_eq(x_444, x_445);
if (x_446 == 0)
{
lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; 
lean_dec(x_445);
lean_dec(x_5);
x_447 = l_Lean_Name_str___override(x_2, x_444);
x_448 = l_Lean_Expr_const___override(x_447, x_428);
x_449 = lean_array_push(x_435, x_448);
x_450 = lean_array_push(x_449, x_432);
x_451 = lean_array_push(x_450, x_434);
x_452 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_452, 0, x_430);
lean_ctor_set(x_452, 1, x_451);
x_453 = lean_box(x_10);
x_454 = lean_apply_11(x_3, x_452, x_7, x_8, x_9, x_453, x_11, x_12, x_13, x_14, x_15, x_16);
return x_454;
}
else
{
lean_dec(x_444);
if (lean_obj_tag(x_428) == 0)
{
lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; uint64_t x_468; lean_object* x_469; uint64_t x_470; uint64_t x_471; uint64_t x_472; lean_object* x_473; uint64_t x_474; uint64_t x_475; uint64_t x_476; size_t x_477; size_t x_478; size_t x_479; size_t x_480; size_t x_481; lean_object* x_482; uint8_t x_483; 
lean_dec(x_435);
lean_dec(x_432);
lean_dec(x_430);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_455 = lean_unsigned_to_nat(8u);
x_456 = lean_nat_shiftl(x_455, x_433);
x_457 = lean_nat_div(x_456, x_358);
lean_dec(x_456);
x_458 = l_Nat_nextPowerOfTwo(x_457);
lean_dec(x_457);
x_459 = lean_box(0);
x_460 = lean_mk_array(x_458, x_459);
x_461 = lean_mk_string_unchecked("Lean", 4, 4);
x_462 = lean_mk_string_unchecked("Omega", 5, 5);
x_463 = lean_mk_string_unchecked("emod_ofNat_nonneg", 17, 17);
x_464 = l_Lean_Name_mkStr4(x_461, x_462, x_445, x_463);
x_465 = l_Lean_Expr_const___override(x_464, x_428);
x_466 = l_Lean_mkAppB(x_465, x_434, x_5);
x_467 = lean_array_get_size(x_460);
x_468 = l_Lean_Expr_hash(x_466);
x_469 = lean_unsigned_to_nat(32u);
x_470 = lean_uint64_of_nat(x_469);
x_471 = lean_uint64_shift_right(x_468, x_470);
x_472 = lean_uint64_xor(x_468, x_471);
x_473 = lean_unsigned_to_nat(16u);
x_474 = lean_uint64_of_nat(x_473);
x_475 = lean_uint64_shift_right(x_472, x_474);
x_476 = lean_uint64_xor(x_472, x_475);
x_477 = lean_uint64_to_usize(x_476);
x_478 = lean_usize_of_nat(x_467);
lean_dec(x_467);
x_479 = lean_usize_of_nat(x_431);
x_480 = lean_usize_sub(x_478, x_479);
x_481 = lean_usize_land(x_477, x_480);
x_482 = lean_array_uget(x_460, x_481);
x_483 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectMVars_visit_spec__0___redArg(x_466, x_482);
if (x_483 == 0)
{
lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; uint8_t x_490; 
x_484 = lean_box(0);
x_485 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_485, 0, x_466);
lean_ctor_set(x_485, 1, x_484);
lean_ctor_set(x_485, 2, x_482);
x_486 = lean_array_uset(x_460, x_481, x_485);
x_487 = lean_nat_shiftl(x_431, x_433);
x_488 = lean_nat_div(x_487, x_358);
lean_dec(x_487);
x_489 = lean_array_get_size(x_486);
x_490 = lean_nat_dec_le(x_488, x_489);
lean_dec(x_489);
lean_dec(x_488);
if (x_490 == 0)
{
lean_object* x_491; lean_object* x_492; lean_object* x_493; 
x_491 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectMVars_visit_spec__1(lean_box(0), x_486);
x_492 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_492, 0, x_431);
lean_ctor_set(x_492, 1, x_491);
x_493 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_493, 0, x_492);
lean_ctor_set(x_493, 1, x_16);
return x_493;
}
else
{
lean_object* x_494; lean_object* x_495; 
x_494 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_494, 0, x_431);
lean_ctor_set(x_494, 1, x_486);
x_495 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_495, 0, x_494);
lean_ctor_set(x_495, 1, x_16);
return x_495;
}
}
else
{
lean_object* x_496; lean_object* x_497; 
lean_dec(x_482);
lean_dec(x_466);
x_496 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_496, 0, x_365);
lean_ctor_set(x_496, 1, x_460);
x_497 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_497, 0, x_496);
lean_ctor_set(x_497, 1, x_16);
return x_497;
}
}
else
{
lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; 
lean_dec(x_5);
x_498 = l_Lean_Name_str___override(x_2, x_445);
x_499 = l_Lean_Expr_const___override(x_498, x_428);
x_500 = lean_array_push(x_435, x_499);
x_501 = lean_array_push(x_500, x_432);
x_502 = lean_array_push(x_501, x_434);
x_503 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_503, 0, x_430);
lean_ctor_set(x_503, 1, x_502);
x_504 = lean_box(x_10);
x_505 = lean_apply_11(x_3, x_503, x_7, x_8, x_9, x_504, x_11, x_12, x_13, x_14, x_15, x_16);
return x_505;
}
}
}
case 1:
{
lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; 
lean_dec(x_5);
lean_dec(x_2);
x_506 = lean_ctor_get(x_427, 1);
lean_inc(x_506);
lean_dec(x_427);
x_507 = lean_ctor_get(x_443, 0);
lean_inc(x_507);
x_508 = lean_ctor_get(x_443, 1);
lean_inc(x_508);
lean_dec(x_443);
x_509 = l_Lean_Name_str___override(x_507, x_508);
x_510 = l_Lean_Name_str___override(x_509, x_506);
x_511 = l_Lean_Expr_const___override(x_510, x_428);
x_512 = lean_array_push(x_435, x_511);
x_513 = lean_array_push(x_512, x_432);
x_514 = lean_array_push(x_513, x_434);
x_515 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_515, 0, x_430);
lean_ctor_set(x_515, 1, x_514);
x_516 = lean_box(x_10);
x_517 = lean_apply_11(x_3, x_515, x_7, x_8, x_9, x_516, x_11, x_12, x_13, x_14, x_15, x_16);
return x_517;
}
default: 
{
lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; 
lean_dec(x_5);
lean_dec(x_2);
x_518 = lean_ctor_get(x_427, 1);
lean_inc(x_518);
lean_dec(x_427);
x_519 = lean_ctor_get(x_443, 0);
lean_inc(x_519);
x_520 = lean_ctor_get(x_443, 1);
lean_inc(x_520);
lean_dec(x_443);
x_521 = l_Lean_Name_num___override(x_519, x_520);
x_522 = l_Lean_Name_str___override(x_521, x_518);
x_523 = l_Lean_Expr_const___override(x_522, x_428);
x_524 = lean_array_push(x_435, x_523);
x_525 = lean_array_push(x_524, x_432);
x_526 = lean_array_push(x_525, x_434);
x_527 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_527, 0, x_430);
lean_ctor_set(x_527, 1, x_526);
x_528 = lean_box(x_10);
x_529 = lean_apply_11(x_3, x_527, x_7, x_8, x_9, x_528, x_11, x_12, x_13, x_14, x_15, x_16);
return x_529;
}
}
}
default: 
{
lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; 
lean_dec(x_5);
lean_dec(x_2);
x_530 = lean_ctor_get(x_427, 0);
lean_inc(x_530);
x_531 = lean_ctor_get(x_427, 1);
lean_inc(x_531);
lean_dec(x_427);
x_532 = l_Lean_Name_num___override(x_530, x_531);
x_533 = l_Lean_Expr_const___override(x_532, x_428);
x_534 = lean_array_push(x_435, x_533);
x_535 = lean_array_push(x_534, x_432);
x_536 = lean_array_push(x_535, x_434);
x_537 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_537, 0, x_430);
lean_ctor_set(x_537, 1, x_536);
x_538 = lean_box(x_10);
x_539 = lean_apply_11(x_3, x_537, x_7, x_8, x_9, x_538, x_11, x_12, x_13, x_14, x_15, x_16);
return x_539;
}
}
}
case 5:
{
lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; 
lean_dec(x_5);
x_540 = lean_ctor_get(x_366, 0);
lean_inc(x_540);
x_541 = lean_ctor_get(x_366, 1);
lean_inc(x_541);
lean_dec(x_366);
x_542 = l_Lean_Name_str___override(x_2, x_4);
x_543 = l_Lean_Name_str___override(x_542, x_350);
x_544 = l_Lean_Expr_app___override(x_540, x_541);
x_545 = lean_unsigned_to_nat(1u);
x_546 = lean_array_fget(x_341, x_545);
x_547 = lean_unsigned_to_nat(2u);
x_548 = lean_array_fget(x_341, x_547);
lean_dec(x_341);
x_549 = lean_mk_empty_array_with_capacity(x_358);
x_550 = lean_array_push(x_549, x_544);
x_551 = lean_array_push(x_550, x_546);
x_552 = lean_array_push(x_551, x_548);
x_553 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_553, 0, x_543);
lean_ctor_set(x_553, 1, x_552);
x_554 = lean_box(x_10);
x_555 = lean_apply_11(x_3, x_553, x_7, x_8, x_9, x_554, x_11, x_12, x_13, x_14, x_15, x_16);
return x_555;
}
case 6:
{
lean_object* x_556; lean_object* x_557; lean_object* x_558; uint8_t x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; 
lean_dec(x_5);
x_556 = lean_ctor_get(x_366, 0);
lean_inc(x_556);
x_557 = lean_ctor_get(x_366, 1);
lean_inc(x_557);
x_558 = lean_ctor_get(x_366, 2);
lean_inc(x_558);
x_559 = lean_ctor_get_uint8(x_366, sizeof(void*)*3 + 8);
lean_dec(x_366);
x_560 = l_Lean_Name_str___override(x_2, x_4);
x_561 = l_Lean_Name_str___override(x_560, x_350);
x_562 = l_Lean_Expr_lam___override(x_556, x_557, x_558, x_559);
x_563 = lean_unsigned_to_nat(1u);
x_564 = lean_array_fget(x_341, x_563);
x_565 = lean_unsigned_to_nat(2u);
x_566 = lean_array_fget(x_341, x_565);
lean_dec(x_341);
x_567 = lean_mk_empty_array_with_capacity(x_358);
x_568 = lean_array_push(x_567, x_562);
x_569 = lean_array_push(x_568, x_564);
x_570 = lean_array_push(x_569, x_566);
x_571 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_571, 0, x_561);
lean_ctor_set(x_571, 1, x_570);
x_572 = lean_box(x_10);
x_573 = lean_apply_11(x_3, x_571, x_7, x_8, x_9, x_572, x_11, x_12, x_13, x_14, x_15, x_16);
return x_573;
}
case 7:
{
lean_object* x_574; lean_object* x_575; lean_object* x_576; uint8_t x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; 
lean_dec(x_5);
x_574 = lean_ctor_get(x_366, 0);
lean_inc(x_574);
x_575 = lean_ctor_get(x_366, 1);
lean_inc(x_575);
x_576 = lean_ctor_get(x_366, 2);
lean_inc(x_576);
x_577 = lean_ctor_get_uint8(x_366, sizeof(void*)*3 + 8);
lean_dec(x_366);
x_578 = l_Lean_Name_str___override(x_2, x_4);
x_579 = l_Lean_Name_str___override(x_578, x_350);
x_580 = l_Lean_Expr_forallE___override(x_574, x_575, x_576, x_577);
x_581 = lean_unsigned_to_nat(1u);
x_582 = lean_array_fget(x_341, x_581);
x_583 = lean_unsigned_to_nat(2u);
x_584 = lean_array_fget(x_341, x_583);
lean_dec(x_341);
x_585 = lean_mk_empty_array_with_capacity(x_358);
x_586 = lean_array_push(x_585, x_580);
x_587 = lean_array_push(x_586, x_582);
x_588 = lean_array_push(x_587, x_584);
x_589 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_589, 0, x_579);
lean_ctor_set(x_589, 1, x_588);
x_590 = lean_box(x_10);
x_591 = lean_apply_11(x_3, x_589, x_7, x_8, x_9, x_590, x_11, x_12, x_13, x_14, x_15, x_16);
return x_591;
}
case 8:
{
lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; uint8_t x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; 
lean_dec(x_5);
x_592 = lean_ctor_get(x_366, 0);
lean_inc(x_592);
x_593 = lean_ctor_get(x_366, 1);
lean_inc(x_593);
x_594 = lean_ctor_get(x_366, 2);
lean_inc(x_594);
x_595 = lean_ctor_get(x_366, 3);
lean_inc(x_595);
x_596 = lean_ctor_get_uint8(x_366, sizeof(void*)*4 + 8);
lean_dec(x_366);
x_597 = l_Lean_Name_str___override(x_2, x_4);
x_598 = l_Lean_Name_str___override(x_597, x_350);
x_599 = l_Lean_Expr_letE___override(x_592, x_593, x_594, x_595, x_596);
x_600 = lean_unsigned_to_nat(1u);
x_601 = lean_array_fget(x_341, x_600);
x_602 = lean_unsigned_to_nat(2u);
x_603 = lean_array_fget(x_341, x_602);
lean_dec(x_341);
x_604 = lean_mk_empty_array_with_capacity(x_358);
x_605 = lean_array_push(x_604, x_599);
x_606 = lean_array_push(x_605, x_601);
x_607 = lean_array_push(x_606, x_603);
x_608 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_608, 0, x_598);
lean_ctor_set(x_608, 1, x_607);
x_609 = lean_box(x_10);
x_610 = lean_apply_11(x_3, x_608, x_7, x_8, x_9, x_609, x_11, x_12, x_13, x_14, x_15, x_16);
return x_610;
}
case 9:
{
lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; 
lean_dec(x_5);
x_611 = lean_ctor_get(x_366, 0);
lean_inc(x_611);
lean_dec(x_366);
x_612 = l_Lean_Name_str___override(x_2, x_4);
x_613 = l_Lean_Name_str___override(x_612, x_350);
x_614 = l_Lean_Expr_lit___override(x_611);
x_615 = lean_unsigned_to_nat(1u);
x_616 = lean_array_fget(x_341, x_615);
x_617 = lean_unsigned_to_nat(2u);
x_618 = lean_array_fget(x_341, x_617);
lean_dec(x_341);
x_619 = lean_mk_empty_array_with_capacity(x_358);
x_620 = lean_array_push(x_619, x_614);
x_621 = lean_array_push(x_620, x_616);
x_622 = lean_array_push(x_621, x_618);
x_623 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_623, 0, x_613);
lean_ctor_set(x_623, 1, x_622);
x_624 = lean_box(x_10);
x_625 = lean_apply_11(x_3, x_623, x_7, x_8, x_9, x_624, x_11, x_12, x_13, x_14, x_15, x_16);
return x_625;
}
case 10:
{
lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; 
lean_dec(x_5);
x_626 = lean_ctor_get(x_366, 0);
lean_inc(x_626);
x_627 = lean_ctor_get(x_366, 1);
lean_inc(x_627);
lean_dec(x_366);
x_628 = l_Lean_Name_str___override(x_2, x_4);
x_629 = l_Lean_Name_str___override(x_628, x_350);
x_630 = l_Lean_Expr_mdata___override(x_626, x_627);
x_631 = lean_unsigned_to_nat(1u);
x_632 = lean_array_fget(x_341, x_631);
x_633 = lean_unsigned_to_nat(2u);
x_634 = lean_array_fget(x_341, x_633);
lean_dec(x_341);
x_635 = lean_mk_empty_array_with_capacity(x_358);
x_636 = lean_array_push(x_635, x_630);
x_637 = lean_array_push(x_636, x_632);
x_638 = lean_array_push(x_637, x_634);
x_639 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_639, 0, x_629);
lean_ctor_set(x_639, 1, x_638);
x_640 = lean_box(x_10);
x_641 = lean_apply_11(x_3, x_639, x_7, x_8, x_9, x_640, x_11, x_12, x_13, x_14, x_15, x_16);
return x_641;
}
default: 
{
lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; 
lean_dec(x_5);
x_642 = lean_ctor_get(x_366, 0);
lean_inc(x_642);
x_643 = lean_ctor_get(x_366, 1);
lean_inc(x_643);
x_644 = lean_ctor_get(x_366, 2);
lean_inc(x_644);
lean_dec(x_366);
x_645 = l_Lean_Name_str___override(x_2, x_4);
x_646 = l_Lean_Name_str___override(x_645, x_350);
x_647 = l_Lean_Expr_proj___override(x_642, x_643, x_644);
x_648 = lean_unsigned_to_nat(1u);
x_649 = lean_array_fget(x_341, x_648);
x_650 = lean_unsigned_to_nat(2u);
x_651 = lean_array_fget(x_341, x_650);
lean_dec(x_341);
x_652 = lean_mk_empty_array_with_capacity(x_358);
x_653 = lean_array_push(x_652, x_647);
x_654 = lean_array_push(x_653, x_649);
x_655 = lean_array_push(x_654, x_651);
x_656 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_656, 0, x_646);
lean_ctor_set(x_656, 1, x_655);
x_657 = lean_box(x_10);
x_658 = lean_apply_11(x_3, x_656, x_7, x_8, x_9, x_657, x_11, x_12, x_13, x_14, x_15, x_16);
return x_658;
}
}
}
}
}
}
}
case 1:
{
uint8_t x_659; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_659 = !lean_is_exclusive(x_17);
if (x_659 == 0)
{
lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; 
x_660 = lean_ctor_get(x_17, 0);
lean_dec(x_660);
x_661 = lean_ctor_get(x_18, 1);
lean_inc(x_661);
lean_dec(x_18);
x_662 = lean_ctor_get(x_27, 1);
lean_inc(x_662);
lean_dec(x_27);
x_663 = lean_ctor_get(x_40, 0);
lean_inc(x_663);
x_664 = lean_ctor_get(x_40, 1);
lean_inc(x_664);
lean_dec(x_40);
x_665 = l_Lean_Name_str___override(x_663, x_664);
x_666 = l_Lean_Name_str___override(x_665, x_662);
x_667 = l_Lean_Name_str___override(x_666, x_661);
lean_ctor_set(x_17, 0, x_667);
x_668 = lean_box(x_10);
x_669 = lean_apply_11(x_3, x_17, x_7, x_8, x_9, x_668, x_11, x_12, x_13, x_14, x_15, x_16);
return x_669;
}
else
{
lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; 
x_670 = lean_ctor_get(x_17, 1);
lean_inc(x_670);
lean_dec(x_17);
x_671 = lean_ctor_get(x_18, 1);
lean_inc(x_671);
lean_dec(x_18);
x_672 = lean_ctor_get(x_27, 1);
lean_inc(x_672);
lean_dec(x_27);
x_673 = lean_ctor_get(x_40, 0);
lean_inc(x_673);
x_674 = lean_ctor_get(x_40, 1);
lean_inc(x_674);
lean_dec(x_40);
x_675 = l_Lean_Name_str___override(x_673, x_674);
x_676 = l_Lean_Name_str___override(x_675, x_672);
x_677 = l_Lean_Name_str___override(x_676, x_671);
x_678 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_678, 0, x_677);
lean_ctor_set(x_678, 1, x_670);
x_679 = lean_box(x_10);
x_680 = lean_apply_11(x_3, x_678, x_7, x_8, x_9, x_679, x_11, x_12, x_13, x_14, x_15, x_16);
return x_680;
}
}
default: 
{
uint8_t x_681; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_681 = !lean_is_exclusive(x_17);
if (x_681 == 0)
{
lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; 
x_682 = lean_ctor_get(x_17, 0);
lean_dec(x_682);
x_683 = lean_ctor_get(x_18, 1);
lean_inc(x_683);
lean_dec(x_18);
x_684 = lean_ctor_get(x_27, 1);
lean_inc(x_684);
lean_dec(x_27);
x_685 = lean_ctor_get(x_40, 0);
lean_inc(x_685);
x_686 = lean_ctor_get(x_40, 1);
lean_inc(x_686);
lean_dec(x_40);
x_687 = l_Lean_Name_num___override(x_685, x_686);
x_688 = l_Lean_Name_str___override(x_687, x_684);
x_689 = l_Lean_Name_str___override(x_688, x_683);
lean_ctor_set(x_17, 0, x_689);
x_690 = lean_box(x_10);
x_691 = lean_apply_11(x_3, x_17, x_7, x_8, x_9, x_690, x_11, x_12, x_13, x_14, x_15, x_16);
return x_691;
}
else
{
lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; 
x_692 = lean_ctor_get(x_17, 1);
lean_inc(x_692);
lean_dec(x_17);
x_693 = lean_ctor_get(x_18, 1);
lean_inc(x_693);
lean_dec(x_18);
x_694 = lean_ctor_get(x_27, 1);
lean_inc(x_694);
lean_dec(x_27);
x_695 = lean_ctor_get(x_40, 0);
lean_inc(x_695);
x_696 = lean_ctor_get(x_40, 1);
lean_inc(x_696);
lean_dec(x_40);
x_697 = l_Lean_Name_num___override(x_695, x_696);
x_698 = l_Lean_Name_str___override(x_697, x_694);
x_699 = l_Lean_Name_str___override(x_698, x_693);
x_700 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_700, 0, x_699);
lean_ctor_set(x_700, 1, x_692);
x_701 = lean_box(x_10);
x_702 = lean_apply_11(x_3, x_700, x_7, x_8, x_9, x_701, x_11, x_12, x_13, x_14, x_15, x_16);
return x_702;
}
}
}
}
default: 
{
uint8_t x_703; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_703 = !lean_is_exclusive(x_17);
if (x_703 == 0)
{
lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; 
x_704 = lean_ctor_get(x_17, 0);
lean_dec(x_704);
x_705 = lean_ctor_get(x_18, 1);
lean_inc(x_705);
lean_dec(x_18);
x_706 = lean_ctor_get(x_27, 0);
lean_inc(x_706);
x_707 = lean_ctor_get(x_27, 1);
lean_inc(x_707);
lean_dec(x_27);
x_708 = l_Lean_Name_num___override(x_706, x_707);
x_709 = l_Lean_Name_str___override(x_708, x_705);
lean_ctor_set(x_17, 0, x_709);
x_710 = lean_box(x_10);
x_711 = lean_apply_11(x_3, x_17, x_7, x_8, x_9, x_710, x_11, x_12, x_13, x_14, x_15, x_16);
return x_711;
}
else
{
lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; 
x_712 = lean_ctor_get(x_17, 1);
lean_inc(x_712);
lean_dec(x_17);
x_713 = lean_ctor_get(x_18, 1);
lean_inc(x_713);
lean_dec(x_18);
x_714 = lean_ctor_get(x_27, 0);
lean_inc(x_714);
x_715 = lean_ctor_get(x_27, 1);
lean_inc(x_715);
lean_dec(x_27);
x_716 = l_Lean_Name_num___override(x_714, x_715);
x_717 = l_Lean_Name_str___override(x_716, x_713);
x_718 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_718, 0, x_717);
lean_ctor_set(x_718, 1, x_712);
x_719 = lean_box(x_10);
x_720 = lean_apply_11(x_3, x_718, x_7, x_8, x_9, x_719, x_11, x_12, x_13, x_14, x_15, x_16);
return x_720;
}
}
}
}
default: 
{
uint8_t x_721; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_721 = !lean_is_exclusive(x_17);
if (x_721 == 0)
{
lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; 
x_722 = lean_ctor_get(x_17, 0);
lean_dec(x_722);
x_723 = lean_ctor_get(x_18, 0);
lean_inc(x_723);
x_724 = lean_ctor_get(x_18, 1);
lean_inc(x_724);
lean_dec(x_18);
x_725 = l_Lean_Name_num___override(x_723, x_724);
lean_ctor_set(x_17, 0, x_725);
x_726 = lean_box(x_10);
x_727 = lean_apply_11(x_3, x_17, x_7, x_8, x_9, x_726, x_11, x_12, x_13, x_14, x_15, x_16);
return x_727;
}
else
{
lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; 
x_728 = lean_ctor_get(x_17, 1);
lean_inc(x_728);
lean_dec(x_17);
x_729 = lean_ctor_get(x_18, 0);
lean_inc(x_729);
x_730 = lean_ctor_get(x_18, 1);
lean_inc(x_730);
lean_dec(x_18);
x_731 = l_Lean_Name_num___override(x_729, x_730);
x_732 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_732, 0, x_731);
lean_ctor_set(x_732, 1, x_728);
x_733 = lean_box(x_10);
x_734 = lean_apply_11(x_3, x_732, x_7, x_8, x_9, x_733, x_11, x_12, x_13, x_14, x_15, x_16);
return x_734;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, uint8_t x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
lean_object* x_19; lean_object* x_32; uint8_t x_33; 
x_32 = lean_mk_string_unchecked("hMod", 4, 4);
x_33 = lean_string_dec_eq(x_1, x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_32);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_34 = l_Lean_Name_str___override(x_2, x_3);
x_35 = l_Lean_Name_str___override(x_34, x_1);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_4);
x_37 = lean_box(x_12);
x_38 = lean_apply_11(x_5, x_36, x_9, x_10, x_11, x_37, x_13, x_14, x_15, x_16, x_17, x_18);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
lean_dec(x_1);
x_39 = lean_array_get_size(x_4);
x_40 = lean_unsigned_to_nat(6u);
x_41 = lean_nat_dec_eq(x_39, x_40);
lean_dec(x_39);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_42 = l_Lean_Name_str___override(x_2, x_3);
x_43 = l_Lean_Name_str___override(x_42, x_32);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_4);
x_45 = lean_box(x_12);
x_46 = lean_apply_11(x_5, x_44, x_9, x_10, x_11, x_45, x_13, x_14, x_15, x_16, x_17, x_18);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_32);
lean_dec(x_5);
lean_dec(x_3);
x_47 = lean_unsigned_to_nat(5u);
x_48 = lean_array_fget(x_4, x_47);
lean_inc(x_48);
x_49 = l_Lean_Expr_getAppFnArgs(x_48);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
switch (lean_obj_tag(x_50)) {
case 0:
{
uint8_t x_51; 
lean_dec(x_48);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_51 = !lean_is_exclusive(x_49);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_49, 0);
lean_dec(x_52);
lean_ctor_set(x_49, 0, x_2);
x_53 = lean_box(x_12);
x_54 = lean_apply_11(x_6, x_49, x_9, x_10, x_11, x_53, x_13, x_14, x_15, x_16, x_17, x_18);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_49, 1);
lean_inc(x_55);
lean_dec(x_49);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_2);
lean_ctor_set(x_56, 1, x_55);
x_57 = lean_box(x_12);
x_58 = lean_apply_11(x_6, x_56, x_9, x_10, x_11, x_57, x_13, x_14, x_15, x_16, x_17, x_18);
return x_58;
}
}
case 1:
{
lean_object* x_59; 
x_59 = lean_ctor_get(x_50, 0);
lean_inc(x_59);
switch (lean_obj_tag(x_59)) {
case 0:
{
uint8_t x_60; 
lean_dec(x_48);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_60 = !lean_is_exclusive(x_49);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_61 = lean_ctor_get(x_49, 0);
lean_dec(x_61);
x_62 = lean_ctor_get(x_50, 1);
lean_inc(x_62);
lean_dec(x_50);
x_63 = l_Lean_Name_str___override(x_2, x_62);
lean_ctor_set(x_49, 0, x_63);
x_64 = lean_box(x_12);
x_65 = lean_apply_11(x_6, x_49, x_9, x_10, x_11, x_64, x_13, x_14, x_15, x_16, x_17, x_18);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_66 = lean_ctor_get(x_49, 1);
lean_inc(x_66);
lean_dec(x_49);
x_67 = lean_ctor_get(x_50, 1);
lean_inc(x_67);
lean_dec(x_50);
x_68 = l_Lean_Name_str___override(x_2, x_67);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_66);
x_70 = lean_box(x_12);
x_71 = lean_apply_11(x_6, x_69, x_9, x_10, x_11, x_70, x_13, x_14, x_15, x_16, x_17, x_18);
return x_71;
}
}
case 1:
{
lean_object* x_72; 
x_72 = lean_ctor_get(x_59, 0);
lean_inc(x_72);
switch (lean_obj_tag(x_72)) {
case 0:
{
uint8_t x_73; 
x_73 = !lean_is_exclusive(x_49);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_74 = lean_ctor_get(x_49, 1);
x_75 = lean_ctor_get(x_49, 0);
lean_dec(x_75);
x_76 = lean_ctor_get(x_50, 1);
lean_inc(x_76);
lean_dec(x_50);
x_77 = lean_ctor_get(x_59, 1);
lean_inc(x_77);
lean_dec(x_59);
x_78 = lean_unsigned_to_nat(4u);
x_79 = lean_array_fget(x_4, x_78);
lean_dec(x_4);
x_80 = lean_mk_string_unchecked("HPow", 4, 4);
x_81 = lean_string_dec_eq(x_77, x_80);
if (x_81 == 0)
{
uint8_t x_82; 
x_82 = lean_string_dec_eq(x_77, x_7);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_48);
lean_dec(x_8);
lean_dec(x_7);
x_83 = l_Lean_Name_str___override(x_2, x_77);
x_84 = l_Lean_Name_str___override(x_83, x_76);
lean_ctor_set(x_49, 0, x_84);
x_85 = lean_box(x_12);
x_86 = lean_apply_11(x_6, x_49, x_9, x_10, x_11, x_85, x_13, x_14, x_15, x_16, x_17, x_18);
return x_86;
}
else
{
lean_object* x_87; uint8_t x_88; 
lean_dec(x_77);
x_87 = lean_mk_string_unchecked("cast", 4, 4);
x_88 = lean_string_dec_eq(x_76, x_87);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_87);
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_48);
lean_dec(x_8);
x_89 = l_Lean_Name_str___override(x_2, x_7);
x_90 = l_Lean_Name_str___override(x_89, x_76);
lean_ctor_set(x_49, 0, x_90);
x_91 = lean_box(x_12);
x_92 = lean_apply_11(x_6, x_49, x_9, x_10, x_11, x_91, x_13, x_14, x_15, x_16, x_17, x_18);
return x_92;
}
else
{
lean_object* x_93; lean_object* x_94; uint8_t x_95; 
lean_dec(x_76);
x_93 = lean_array_get_size(x_74);
x_94 = lean_unsigned_to_nat(3u);
x_95 = lean_nat_dec_eq(x_93, x_94);
lean_dec(x_93);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_48);
lean_dec(x_8);
x_96 = l_Lean_Name_str___override(x_2, x_7);
x_97 = l_Lean_Name_str___override(x_96, x_87);
lean_ctor_set(x_49, 0, x_97);
x_98 = lean_box(x_12);
x_99 = lean_apply_11(x_6, x_49, x_9, x_10, x_11, x_98, x_13, x_14, x_15, x_16, x_17, x_18);
return x_99;
}
else
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_unsigned_to_nat(0u);
x_101 = lean_array_fget(x_74, x_100);
switch (lean_obj_tag(x_101)) {
case 0:
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_48);
lean_dec(x_8);
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
lean_dec(x_101);
x_103 = l_Lean_Name_str___override(x_2, x_7);
x_104 = l_Lean_Name_str___override(x_103, x_87);
x_105 = l_Lean_Expr_bvar___override(x_102);
x_106 = lean_unsigned_to_nat(1u);
x_107 = lean_array_fget(x_74, x_106);
x_108 = lean_unsigned_to_nat(2u);
x_109 = lean_array_fget(x_74, x_108);
lean_dec(x_74);
x_110 = lean_mk_empty_array_with_capacity(x_94);
x_111 = lean_array_push(x_110, x_105);
x_112 = lean_array_push(x_111, x_107);
x_113 = lean_array_push(x_112, x_109);
lean_ctor_set(x_49, 1, x_113);
lean_ctor_set(x_49, 0, x_104);
x_114 = lean_box(x_12);
x_115 = lean_apply_11(x_6, x_49, x_9, x_10, x_11, x_114, x_13, x_14, x_15, x_16, x_17, x_18);
return x_115;
}
case 1:
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_48);
lean_dec(x_8);
x_116 = lean_ctor_get(x_101, 0);
lean_inc(x_116);
lean_dec(x_101);
x_117 = l_Lean_Name_str___override(x_2, x_7);
x_118 = l_Lean_Name_str___override(x_117, x_87);
x_119 = l_Lean_Expr_fvar___override(x_116);
x_120 = lean_unsigned_to_nat(1u);
x_121 = lean_array_fget(x_74, x_120);
x_122 = lean_unsigned_to_nat(2u);
x_123 = lean_array_fget(x_74, x_122);
lean_dec(x_74);
x_124 = lean_mk_empty_array_with_capacity(x_94);
x_125 = lean_array_push(x_124, x_119);
x_126 = lean_array_push(x_125, x_121);
x_127 = lean_array_push(x_126, x_123);
lean_ctor_set(x_49, 1, x_127);
lean_ctor_set(x_49, 0, x_118);
x_128 = lean_box(x_12);
x_129 = lean_apply_11(x_6, x_49, x_9, x_10, x_11, x_128, x_13, x_14, x_15, x_16, x_17, x_18);
return x_129;
}
case 2:
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_48);
lean_dec(x_8);
x_130 = lean_ctor_get(x_101, 0);
lean_inc(x_130);
lean_dec(x_101);
x_131 = l_Lean_Name_str___override(x_2, x_7);
x_132 = l_Lean_Name_str___override(x_131, x_87);
x_133 = l_Lean_Expr_mvar___override(x_130);
x_134 = lean_unsigned_to_nat(1u);
x_135 = lean_array_fget(x_74, x_134);
x_136 = lean_unsigned_to_nat(2u);
x_137 = lean_array_fget(x_74, x_136);
lean_dec(x_74);
x_138 = lean_mk_empty_array_with_capacity(x_94);
x_139 = lean_array_push(x_138, x_133);
x_140 = lean_array_push(x_139, x_135);
x_141 = lean_array_push(x_140, x_137);
lean_ctor_set(x_49, 1, x_141);
lean_ctor_set(x_49, 0, x_132);
x_142 = lean_box(x_12);
x_143 = lean_apply_11(x_6, x_49, x_9, x_10, x_11, x_142, x_13, x_14, x_15, x_16, x_17, x_18);
return x_143;
}
case 3:
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_48);
lean_dec(x_8);
x_144 = lean_ctor_get(x_101, 0);
lean_inc(x_144);
lean_dec(x_101);
x_145 = l_Lean_Name_str___override(x_2, x_7);
x_146 = l_Lean_Name_str___override(x_145, x_87);
x_147 = l_Lean_Expr_sort___override(x_144);
x_148 = lean_unsigned_to_nat(1u);
x_149 = lean_array_fget(x_74, x_148);
x_150 = lean_unsigned_to_nat(2u);
x_151 = lean_array_fget(x_74, x_150);
lean_dec(x_74);
x_152 = lean_mk_empty_array_with_capacity(x_94);
x_153 = lean_array_push(x_152, x_147);
x_154 = lean_array_push(x_153, x_149);
x_155 = lean_array_push(x_154, x_151);
lean_ctor_set(x_49, 1, x_155);
lean_ctor_set(x_49, 0, x_146);
x_156 = lean_box(x_12);
x_157 = lean_apply_11(x_6, x_49, x_9, x_10, x_11, x_156, x_13, x_14, x_15, x_16, x_17, x_18);
return x_157;
}
case 4:
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_158 = lean_ctor_get(x_101, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_101, 1);
lean_inc(x_159);
lean_dec(x_101);
lean_inc(x_7);
lean_inc(x_2);
x_160 = l_Lean_Name_str___override(x_2, x_7);
x_161 = l_Lean_Name_str___override(x_160, x_87);
lean_inc(x_159);
lean_inc(x_2);
x_162 = l_Lean_Expr_const___override(x_2, x_159);
x_163 = lean_unsigned_to_nat(1u);
x_164 = lean_array_fget(x_74, x_163);
x_165 = lean_unsigned_to_nat(2u);
x_176 = lean_array_fget(x_74, x_165);
lean_dec(x_74);
x_177 = lean_mk_empty_array_with_capacity(x_94);
lean_inc(x_177);
x_178 = lean_array_push(x_177, x_162);
switch (lean_obj_tag(x_158)) {
case 0:
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
lean_dec(x_177);
lean_dec(x_159);
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_48);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_179 = lean_array_push(x_178, x_164);
x_180 = lean_array_push(x_179, x_176);
lean_ctor_set(x_49, 1, x_180);
lean_ctor_set(x_49, 0, x_161);
x_181 = lean_box(x_12);
x_182 = lean_apply_11(x_6, x_49, x_9, x_10, x_11, x_181, x_13, x_14, x_15, x_16, x_17, x_18);
return x_182;
}
case 1:
{
lean_object* x_183; 
lean_dec(x_178);
x_183 = lean_ctor_get(x_158, 0);
lean_inc(x_183);
switch (lean_obj_tag(x_183)) {
case 0:
{
lean_object* x_184; lean_object* x_185; uint8_t x_186; 
x_184 = lean_ctor_get(x_158, 1);
lean_inc(x_184);
lean_dec(x_158);
x_185 = lean_mk_string_unchecked("Int", 3, 3);
x_186 = lean_string_dec_eq(x_184, x_185);
if (x_186 == 0)
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
lean_dec(x_185);
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_48);
lean_dec(x_8);
lean_dec(x_7);
x_187 = l_Lean_Name_str___override(x_2, x_184);
x_188 = l_Lean_Expr_const___override(x_187, x_159);
x_189 = lean_array_push(x_177, x_188);
x_190 = lean_array_push(x_189, x_164);
x_191 = lean_array_push(x_190, x_176);
lean_ctor_set(x_49, 1, x_191);
lean_ctor_set(x_49, 0, x_161);
x_192 = lean_box(x_12);
x_193 = lean_apply_11(x_6, x_49, x_9, x_10, x_11, x_192, x_13, x_14, x_15, x_16, x_17, x_18);
return x_193;
}
else
{
lean_dec(x_184);
if (lean_obj_tag(x_159) == 0)
{
lean_object* x_194; lean_object* x_195; 
lean_dec(x_177);
lean_dec(x_164);
lean_dec(x_161);
lean_free_object(x_49);
lean_dec(x_6);
lean_inc(x_176);
x_194 = l_Lean_Expr_getAppFnArgs(x_176);
x_195 = lean_ctor_get(x_194, 0);
lean_inc(x_195);
switch (lean_obj_tag(x_195)) {
case 0:
{
uint8_t x_196; 
lean_dec(x_185);
lean_dec(x_176);
lean_dec(x_80);
x_196 = !lean_is_exclusive(x_194);
if (x_196 == 0)
{
lean_object* x_197; lean_object* x_198; 
x_197 = lean_ctor_get(x_194, 0);
lean_dec(x_197);
lean_inc(x_2);
lean_ctor_set(x_194, 0, x_2);
x_198 = l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__4(x_79, x_2, x_8, x_7, x_48, x_194, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_194);
return x_198;
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_199 = lean_ctor_get(x_194, 1);
lean_inc(x_199);
lean_dec(x_194);
lean_inc(x_2);
x_200 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_200, 0, x_2);
lean_ctor_set(x_200, 1, x_199);
x_201 = l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__4(x_79, x_2, x_8, x_7, x_48, x_200, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_200);
return x_201;
}
}
case 1:
{
lean_object* x_202; 
x_202 = lean_ctor_get(x_195, 0);
lean_inc(x_202);
switch (lean_obj_tag(x_202)) {
case 0:
{
uint8_t x_203; 
lean_dec(x_185);
lean_dec(x_176);
lean_dec(x_80);
x_203 = !lean_is_exclusive(x_194);
if (x_203 == 0)
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_204 = lean_ctor_get(x_194, 0);
lean_dec(x_204);
x_205 = lean_ctor_get(x_195, 1);
lean_inc(x_205);
lean_dec(x_195);
lean_inc(x_2);
x_206 = l_Lean_Name_str___override(x_2, x_205);
lean_ctor_set(x_194, 0, x_206);
x_207 = l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__4(x_79, x_2, x_8, x_7, x_48, x_194, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_194);
return x_207;
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_208 = lean_ctor_get(x_194, 1);
lean_inc(x_208);
lean_dec(x_194);
x_209 = lean_ctor_get(x_195, 1);
lean_inc(x_209);
lean_dec(x_195);
lean_inc(x_2);
x_210 = l_Lean_Name_str___override(x_2, x_209);
x_211 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_211, 0, x_210);
lean_ctor_set(x_211, 1, x_208);
x_212 = l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__4(x_79, x_2, x_8, x_7, x_48, x_211, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_211);
return x_212;
}
}
case 1:
{
lean_object* x_213; 
x_213 = lean_ctor_get(x_202, 0);
lean_inc(x_213);
switch (lean_obj_tag(x_213)) {
case 0:
{
uint8_t x_214; 
x_214 = !lean_is_exclusive(x_194);
if (x_214 == 0)
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; uint8_t x_219; 
x_215 = lean_ctor_get(x_194, 1);
x_216 = lean_ctor_get(x_194, 0);
lean_dec(x_216);
x_217 = lean_ctor_get(x_195, 1);
lean_inc(x_217);
lean_dec(x_195);
x_218 = lean_ctor_get(x_202, 1);
lean_inc(x_218);
lean_dec(x_202);
x_219 = lean_string_dec_eq(x_218, x_80);
if (x_219 == 0)
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; 
lean_dec(x_185);
lean_dec(x_176);
lean_dec(x_80);
lean_inc(x_2);
x_220 = l_Lean_Name_str___override(x_2, x_218);
x_221 = l_Lean_Name_str___override(x_220, x_217);
lean_ctor_set(x_194, 0, x_221);
x_222 = l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__4(x_79, x_2, x_8, x_7, x_48, x_194, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_194);
return x_222;
}
else
{
lean_object* x_223; uint8_t x_224; 
lean_dec(x_218);
x_223 = lean_mk_string_unchecked("hPow", 4, 4);
x_224 = lean_string_dec_eq(x_217, x_223);
if (x_224 == 0)
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; 
lean_dec(x_223);
lean_dec(x_185);
lean_dec(x_176);
lean_inc(x_2);
x_225 = l_Lean_Name_str___override(x_2, x_80);
x_226 = l_Lean_Name_str___override(x_225, x_217);
lean_ctor_set(x_194, 0, x_226);
x_227 = l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__4(x_79, x_2, x_8, x_7, x_48, x_194, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_194);
return x_227;
}
else
{
lean_object* x_228; uint8_t x_229; 
lean_dec(x_217);
x_228 = lean_array_get_size(x_215);
x_229 = lean_nat_dec_eq(x_228, x_40);
lean_dec(x_228);
if (x_229 == 0)
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; 
lean_dec(x_185);
lean_dec(x_176);
lean_inc(x_2);
x_230 = l_Lean_Name_str___override(x_2, x_80);
x_231 = l_Lean_Name_str___override(x_230, x_223);
lean_ctor_set(x_194, 0, x_231);
x_232 = l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__4(x_79, x_2, x_8, x_7, x_48, x_194, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_194);
return x_232;
}
else
{
lean_object* x_233; lean_object* x_234; 
lean_dec(x_223);
lean_free_object(x_194);
lean_dec(x_80);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_233 = lean_array_fget(x_215, x_78);
lean_inc(x_233);
x_234 = l_Lean_Elab_Tactic_Omega_natCast_x3f(x_233);
if (lean_obj_tag(x_234) == 0)
{
lean_dec(x_233);
lean_dec(x_215);
lean_dec(x_185);
lean_dec(x_176);
lean_dec(x_79);
lean_dec(x_48);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_7);
x_166 = x_18;
goto block_175;
}
else
{
lean_object* x_235; uint8_t x_236; 
x_235 = lean_ctor_get(x_234, 0);
lean_inc(x_235);
lean_dec(x_234);
x_236 = lean_nat_dec_eq(x_235, x_100);
lean_dec(x_235);
if (x_236 == 0)
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_237 = lean_mk_string_unchecked("LT", 2, 2);
x_238 = lean_mk_string_unchecked("lt", 2, 2);
x_239 = l_Lean_Name_mkStr2(x_237, x_238);
x_240 = l_Lean_Level_ofNat(x_100);
x_241 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_241, 0, x_240);
lean_ctor_set(x_241, 1, x_159);
lean_inc(x_241);
x_242 = l_Lean_Expr_const___override(x_239, x_241);
lean_inc(x_7);
x_243 = l_Lean_Name_mkStr1(x_7);
x_244 = l_Lean_Expr_const___override(x_243, x_159);
x_245 = lean_mk_string_unchecked("instLTNat", 9, 9);
x_246 = l_Lean_Name_mkStr1(x_245);
x_247 = l_Lean_Expr_const___override(x_246, x_159);
x_248 = l_Lean_mkNatLit(x_100);
lean_inc(x_233);
x_249 = l_Lean_mkApp4(x_242, x_244, x_247, x_248, x_233);
x_250 = l_Lean_Meta_mkDecideProof(x_249, x_14, x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_250) == 0)
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_348; uint8_t x_349; 
x_251 = lean_ctor_get(x_250, 0);
lean_inc(x_251);
x_252 = lean_ctor_get(x_250, 1);
lean_inc(x_252);
if (lean_is_exclusive(x_250)) {
 lean_ctor_release(x_250, 0);
 lean_ctor_release(x_250, 1);
 x_253 = x_250;
} else {
 lean_dec_ref(x_250);
 x_253 = lean_box(0);
}
x_254 = lean_array_fget(x_215, x_47);
lean_dec(x_215);
x_255 = lean_mk_string_unchecked("pos_pow_of_pos", 14, 14);
x_256 = l_Lean_Name_mkStr2(x_7, x_255);
x_257 = l_Lean_Expr_const___override(x_256, x_159);
x_258 = l_Lean_mkApp3(x_257, x_233, x_254, x_251);
x_259 = lean_mk_string_unchecked("Lean", 4, 4);
x_260 = lean_mk_string_unchecked("Omega", 5, 5);
x_261 = lean_mk_string_unchecked("ofNat_pos_of_pos", 16, 16);
lean_inc(x_185);
x_262 = l_Lean_Name_mkStr4(x_259, x_260, x_185, x_261);
x_263 = l_Lean_Expr_const___override(x_262, x_159);
x_264 = l_Lean_mkAppB(x_263, x_176, x_258);
x_304 = lean_unsigned_to_nat(8u);
x_305 = lean_nat_shiftl(x_304, x_165);
x_306 = lean_nat_div(x_305, x_94);
lean_dec(x_305);
x_307 = l_Nat_nextPowerOfTwo(x_306);
lean_dec(x_306);
x_308 = lean_box(0);
x_309 = lean_mk_array(x_307, x_308);
x_310 = lean_mk_string_unchecked("emod_nonneg", 11, 11);
lean_inc(x_185);
x_311 = l_Lean_Name_mkStr2(x_185, x_310);
x_312 = l_Lean_Expr_const___override(x_311, x_159);
x_313 = lean_mk_string_unchecked("ne_of_gt", 8, 8);
lean_inc(x_185);
x_314 = l_Lean_Name_mkStr2(x_185, x_313);
x_315 = l_Lean_Expr_const___override(x_314, x_159);
x_348 = lean_nat_to_int(x_100);
x_349 = lean_int_dec_le(x_348, x_348);
if (x_349 == 0)
{
lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; 
x_350 = lean_mk_string_unchecked("Neg", 3, 3);
x_351 = lean_mk_string_unchecked("neg", 3, 3);
x_352 = l_Lean_Name_mkStr2(x_350, x_351);
x_353 = l_Lean_Expr_const___override(x_352, x_241);
lean_inc(x_185);
x_354 = l_Lean_Name_mkStr1(x_185);
x_355 = l_Lean_Expr_const___override(x_354, x_159);
x_356 = lean_mk_string_unchecked("instNegInt", 10, 10);
lean_inc(x_185);
x_357 = l_Lean_Name_mkStr2(x_185, x_356);
x_358 = l_Lean_Expr_const___override(x_357, x_159);
x_359 = lean_int_neg(x_348);
lean_dec(x_348);
x_360 = l_Int_toNat(x_359);
lean_dec(x_359);
x_361 = l_Lean_instToExprInt_mkNat(x_360);
x_362 = l_Lean_mkApp3(x_353, x_355, x_358, x_361);
x_316 = x_362;
goto block_347;
}
else
{
lean_object* x_363; lean_object* x_364; 
lean_dec(x_241);
x_363 = l_Int_toNat(x_348);
lean_dec(x_348);
x_364 = l_Lean_instToExprInt_mkNat(x_363);
x_316 = x_364;
goto block_347;
}
block_303:
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; uint64_t x_273; lean_object* x_274; uint64_t x_275; uint64_t x_276; uint64_t x_277; lean_object* x_278; uint64_t x_279; uint64_t x_280; uint64_t x_281; size_t x_282; size_t x_283; size_t x_284; size_t x_285; size_t x_286; lean_object* x_287; uint8_t x_288; 
x_268 = lean_mk_string_unchecked("emod_lt_of_pos", 14, 14);
x_269 = l_Lean_Name_mkStr2(x_185, x_268);
x_270 = l_Lean_Expr_const___override(x_269, x_159);
x_271 = l_Lean_mkApp3(x_270, x_79, x_48, x_264);
x_272 = lean_array_get_size(x_267);
x_273 = l_Lean_Expr_hash(x_271);
x_274 = lean_unsigned_to_nat(32u);
x_275 = lean_uint64_of_nat(x_274);
x_276 = lean_uint64_shift_right(x_273, x_275);
x_277 = lean_uint64_xor(x_273, x_276);
x_278 = lean_unsigned_to_nat(16u);
x_279 = lean_uint64_of_nat(x_278);
x_280 = lean_uint64_shift_right(x_277, x_279);
x_281 = lean_uint64_xor(x_277, x_280);
x_282 = lean_uint64_to_usize(x_281);
x_283 = lean_usize_of_nat(x_272);
lean_dec(x_272);
x_284 = lean_usize_of_nat(x_163);
x_285 = lean_usize_sub(x_283, x_284);
x_286 = lean_usize_land(x_282, x_285);
x_287 = lean_array_uget(x_267, x_286);
x_288 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectMVars_visit_spec__0___redArg(x_271, x_287);
if (x_288 == 0)
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; uint8_t x_296; 
lean_dec(x_265);
x_289 = lean_box(0);
x_290 = lean_nat_add(x_266, x_163);
lean_dec(x_266);
x_291 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_291, 0, x_271);
lean_ctor_set(x_291, 1, x_289);
lean_ctor_set(x_291, 2, x_287);
x_292 = lean_array_uset(x_267, x_286, x_291);
x_293 = lean_nat_shiftl(x_290, x_165);
x_294 = lean_nat_div(x_293, x_94);
lean_dec(x_293);
x_295 = lean_array_get_size(x_292);
x_296 = lean_nat_dec_le(x_294, x_295);
lean_dec(x_295);
lean_dec(x_294);
if (x_296 == 0)
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; 
x_297 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectMVars_visit_spec__1(lean_box(0), x_292);
x_298 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_298, 0, x_290);
lean_ctor_set(x_298, 1, x_297);
if (lean_is_scalar(x_253)) {
 x_299 = lean_alloc_ctor(0, 2, 0);
} else {
 x_299 = x_253;
}
lean_ctor_set(x_299, 0, x_298);
lean_ctor_set(x_299, 1, x_252);
return x_299;
}
else
{
lean_object* x_300; lean_object* x_301; 
x_300 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_300, 0, x_290);
lean_ctor_set(x_300, 1, x_292);
if (lean_is_scalar(x_253)) {
 x_301 = lean_alloc_ctor(0, 2, 0);
} else {
 x_301 = x_253;
}
lean_ctor_set(x_301, 0, x_300);
lean_ctor_set(x_301, 1, x_252);
return x_301;
}
}
else
{
lean_object* x_302; 
lean_dec(x_287);
lean_dec(x_271);
lean_dec(x_267);
lean_dec(x_266);
if (lean_is_scalar(x_253)) {
 x_302 = lean_alloc_ctor(0, 2, 0);
} else {
 x_302 = x_253;
}
lean_ctor_set(x_302, 0, x_265);
lean_ctor_set(x_302, 1, x_252);
return x_302;
}
}
block_347:
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; uint64_t x_320; lean_object* x_321; uint64_t x_322; uint64_t x_323; uint64_t x_324; lean_object* x_325; uint64_t x_326; uint64_t x_327; uint64_t x_328; size_t x_329; size_t x_330; size_t x_331; size_t x_332; size_t x_333; lean_object* x_334; uint8_t x_335; 
lean_inc(x_264);
lean_inc(x_48);
x_317 = l_Lean_mkApp3(x_315, x_48, x_316, x_264);
lean_inc(x_48);
lean_inc(x_79);
x_318 = l_Lean_mkApp3(x_312, x_79, x_48, x_317);
x_319 = lean_array_get_size(x_309);
x_320 = l_Lean_Expr_hash(x_318);
x_321 = lean_unsigned_to_nat(32u);
x_322 = lean_uint64_of_nat(x_321);
x_323 = lean_uint64_shift_right(x_320, x_322);
x_324 = lean_uint64_xor(x_320, x_323);
x_325 = lean_unsigned_to_nat(16u);
x_326 = lean_uint64_of_nat(x_325);
x_327 = lean_uint64_shift_right(x_324, x_326);
x_328 = lean_uint64_xor(x_324, x_327);
x_329 = lean_uint64_to_usize(x_328);
x_330 = lean_usize_of_nat(x_319);
lean_dec(x_319);
x_331 = lean_usize_of_nat(x_163);
x_332 = lean_usize_sub(x_330, x_331);
x_333 = lean_usize_land(x_329, x_332);
x_334 = lean_array_uget(x_309, x_333);
x_335 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectMVars_visit_spec__0___redArg(x_318, x_334);
if (x_335 == 0)
{
lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; uint8_t x_342; 
x_336 = lean_box(0);
x_337 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_337, 0, x_318);
lean_ctor_set(x_337, 1, x_336);
lean_ctor_set(x_337, 2, x_334);
x_338 = lean_array_uset(x_309, x_333, x_337);
x_339 = lean_nat_shiftl(x_163, x_165);
x_340 = lean_nat_div(x_339, x_94);
lean_dec(x_339);
x_341 = lean_array_get_size(x_338);
x_342 = lean_nat_dec_le(x_340, x_341);
lean_dec(x_341);
lean_dec(x_340);
if (x_342 == 0)
{
lean_object* x_343; lean_object* x_344; 
x_343 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectMVars_visit_spec__1(lean_box(0), x_338);
lean_inc(x_343);
x_344 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_344, 0, x_163);
lean_ctor_set(x_344, 1, x_343);
x_265 = x_344;
x_266 = x_163;
x_267 = x_343;
goto block_303;
}
else
{
lean_object* x_345; 
lean_inc(x_338);
x_345 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_345, 0, x_163);
lean_ctor_set(x_345, 1, x_338);
x_265 = x_345;
x_266 = x_163;
x_267 = x_338;
goto block_303;
}
}
else
{
lean_object* x_346; 
lean_dec(x_334);
lean_dec(x_318);
lean_inc(x_309);
x_346 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_346, 0, x_100);
lean_ctor_set(x_346, 1, x_309);
x_265 = x_346;
x_266 = x_100;
x_267 = x_309;
goto block_303;
}
}
}
else
{
uint8_t x_365; 
lean_dec(x_241);
lean_dec(x_233);
lean_dec(x_215);
lean_dec(x_185);
lean_dec(x_176);
lean_dec(x_79);
lean_dec(x_48);
lean_dec(x_7);
x_365 = !lean_is_exclusive(x_250);
if (x_365 == 0)
{
return x_250;
}
else
{
lean_object* x_366; lean_object* x_367; lean_object* x_368; 
x_366 = lean_ctor_get(x_250, 0);
x_367 = lean_ctor_get(x_250, 1);
lean_inc(x_367);
lean_inc(x_366);
lean_dec(x_250);
x_368 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_368, 0, x_366);
lean_ctor_set(x_368, 1, x_367);
return x_368;
}
}
}
else
{
lean_dec(x_233);
lean_dec(x_215);
lean_dec(x_185);
lean_dec(x_176);
lean_dec(x_79);
lean_dec(x_48);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_7);
x_166 = x_18;
goto block_175;
}
}
}
}
}
}
else
{
lean_object* x_369; lean_object* x_370; lean_object* x_371; uint8_t x_372; 
x_369 = lean_ctor_get(x_194, 1);
lean_inc(x_369);
lean_dec(x_194);
x_370 = lean_ctor_get(x_195, 1);
lean_inc(x_370);
lean_dec(x_195);
x_371 = lean_ctor_get(x_202, 1);
lean_inc(x_371);
lean_dec(x_202);
x_372 = lean_string_dec_eq(x_371, x_80);
if (x_372 == 0)
{
lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; 
lean_dec(x_185);
lean_dec(x_176);
lean_dec(x_80);
lean_inc(x_2);
x_373 = l_Lean_Name_str___override(x_2, x_371);
x_374 = l_Lean_Name_str___override(x_373, x_370);
x_375 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_375, 0, x_374);
lean_ctor_set(x_375, 1, x_369);
x_376 = l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__4(x_79, x_2, x_8, x_7, x_48, x_375, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_375);
return x_376;
}
else
{
lean_object* x_377; uint8_t x_378; 
lean_dec(x_371);
x_377 = lean_mk_string_unchecked("hPow", 4, 4);
x_378 = lean_string_dec_eq(x_370, x_377);
if (x_378 == 0)
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; 
lean_dec(x_377);
lean_dec(x_185);
lean_dec(x_176);
lean_inc(x_2);
x_379 = l_Lean_Name_str___override(x_2, x_80);
x_380 = l_Lean_Name_str___override(x_379, x_370);
x_381 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_381, 0, x_380);
lean_ctor_set(x_381, 1, x_369);
x_382 = l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__4(x_79, x_2, x_8, x_7, x_48, x_381, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_381);
return x_382;
}
else
{
lean_object* x_383; uint8_t x_384; 
lean_dec(x_370);
x_383 = lean_array_get_size(x_369);
x_384 = lean_nat_dec_eq(x_383, x_40);
lean_dec(x_383);
if (x_384 == 0)
{
lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; 
lean_dec(x_185);
lean_dec(x_176);
lean_inc(x_2);
x_385 = l_Lean_Name_str___override(x_2, x_80);
x_386 = l_Lean_Name_str___override(x_385, x_377);
x_387 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_387, 0, x_386);
lean_ctor_set(x_387, 1, x_369);
x_388 = l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__4(x_79, x_2, x_8, x_7, x_48, x_387, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_387);
return x_388;
}
else
{
lean_object* x_389; lean_object* x_390; 
lean_dec(x_377);
lean_dec(x_80);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_389 = lean_array_fget(x_369, x_78);
lean_inc(x_389);
x_390 = l_Lean_Elab_Tactic_Omega_natCast_x3f(x_389);
if (lean_obj_tag(x_390) == 0)
{
lean_dec(x_389);
lean_dec(x_369);
lean_dec(x_185);
lean_dec(x_176);
lean_dec(x_79);
lean_dec(x_48);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_7);
x_166 = x_18;
goto block_175;
}
else
{
lean_object* x_391; uint8_t x_392; 
x_391 = lean_ctor_get(x_390, 0);
lean_inc(x_391);
lean_dec(x_390);
x_392 = lean_nat_dec_eq(x_391, x_100);
lean_dec(x_391);
if (x_392 == 0)
{
lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; 
x_393 = lean_mk_string_unchecked("LT", 2, 2);
x_394 = lean_mk_string_unchecked("lt", 2, 2);
x_395 = l_Lean_Name_mkStr2(x_393, x_394);
x_396 = l_Lean_Level_ofNat(x_100);
x_397 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_397, 0, x_396);
lean_ctor_set(x_397, 1, x_159);
lean_inc(x_397);
x_398 = l_Lean_Expr_const___override(x_395, x_397);
lean_inc(x_7);
x_399 = l_Lean_Name_mkStr1(x_7);
x_400 = l_Lean_Expr_const___override(x_399, x_159);
x_401 = lean_mk_string_unchecked("instLTNat", 9, 9);
x_402 = l_Lean_Name_mkStr1(x_401);
x_403 = l_Lean_Expr_const___override(x_402, x_159);
x_404 = l_Lean_mkNatLit(x_100);
lean_inc(x_389);
x_405 = l_Lean_mkApp4(x_398, x_400, x_403, x_404, x_389);
x_406 = l_Lean_Meta_mkDecideProof(x_405, x_14, x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_406) == 0)
{
lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_504; uint8_t x_505; 
x_407 = lean_ctor_get(x_406, 0);
lean_inc(x_407);
x_408 = lean_ctor_get(x_406, 1);
lean_inc(x_408);
if (lean_is_exclusive(x_406)) {
 lean_ctor_release(x_406, 0);
 lean_ctor_release(x_406, 1);
 x_409 = x_406;
} else {
 lean_dec_ref(x_406);
 x_409 = lean_box(0);
}
x_410 = lean_array_fget(x_369, x_47);
lean_dec(x_369);
x_411 = lean_mk_string_unchecked("pos_pow_of_pos", 14, 14);
x_412 = l_Lean_Name_mkStr2(x_7, x_411);
x_413 = l_Lean_Expr_const___override(x_412, x_159);
x_414 = l_Lean_mkApp3(x_413, x_389, x_410, x_407);
x_415 = lean_mk_string_unchecked("Lean", 4, 4);
x_416 = lean_mk_string_unchecked("Omega", 5, 5);
x_417 = lean_mk_string_unchecked("ofNat_pos_of_pos", 16, 16);
lean_inc(x_185);
x_418 = l_Lean_Name_mkStr4(x_415, x_416, x_185, x_417);
x_419 = l_Lean_Expr_const___override(x_418, x_159);
x_420 = l_Lean_mkAppB(x_419, x_176, x_414);
x_460 = lean_unsigned_to_nat(8u);
x_461 = lean_nat_shiftl(x_460, x_165);
x_462 = lean_nat_div(x_461, x_94);
lean_dec(x_461);
x_463 = l_Nat_nextPowerOfTwo(x_462);
lean_dec(x_462);
x_464 = lean_box(0);
x_465 = lean_mk_array(x_463, x_464);
x_466 = lean_mk_string_unchecked("emod_nonneg", 11, 11);
lean_inc(x_185);
x_467 = l_Lean_Name_mkStr2(x_185, x_466);
x_468 = l_Lean_Expr_const___override(x_467, x_159);
x_469 = lean_mk_string_unchecked("ne_of_gt", 8, 8);
lean_inc(x_185);
x_470 = l_Lean_Name_mkStr2(x_185, x_469);
x_471 = l_Lean_Expr_const___override(x_470, x_159);
x_504 = lean_nat_to_int(x_100);
x_505 = lean_int_dec_le(x_504, x_504);
if (x_505 == 0)
{
lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; 
x_506 = lean_mk_string_unchecked("Neg", 3, 3);
x_507 = lean_mk_string_unchecked("neg", 3, 3);
x_508 = l_Lean_Name_mkStr2(x_506, x_507);
x_509 = l_Lean_Expr_const___override(x_508, x_397);
lean_inc(x_185);
x_510 = l_Lean_Name_mkStr1(x_185);
x_511 = l_Lean_Expr_const___override(x_510, x_159);
x_512 = lean_mk_string_unchecked("instNegInt", 10, 10);
lean_inc(x_185);
x_513 = l_Lean_Name_mkStr2(x_185, x_512);
x_514 = l_Lean_Expr_const___override(x_513, x_159);
x_515 = lean_int_neg(x_504);
lean_dec(x_504);
x_516 = l_Int_toNat(x_515);
lean_dec(x_515);
x_517 = l_Lean_instToExprInt_mkNat(x_516);
x_518 = l_Lean_mkApp3(x_509, x_511, x_514, x_517);
x_472 = x_518;
goto block_503;
}
else
{
lean_object* x_519; lean_object* x_520; 
lean_dec(x_397);
x_519 = l_Int_toNat(x_504);
lean_dec(x_504);
x_520 = l_Lean_instToExprInt_mkNat(x_519);
x_472 = x_520;
goto block_503;
}
block_459:
{
lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; uint64_t x_429; lean_object* x_430; uint64_t x_431; uint64_t x_432; uint64_t x_433; lean_object* x_434; uint64_t x_435; uint64_t x_436; uint64_t x_437; size_t x_438; size_t x_439; size_t x_440; size_t x_441; size_t x_442; lean_object* x_443; uint8_t x_444; 
x_424 = lean_mk_string_unchecked("emod_lt_of_pos", 14, 14);
x_425 = l_Lean_Name_mkStr2(x_185, x_424);
x_426 = l_Lean_Expr_const___override(x_425, x_159);
x_427 = l_Lean_mkApp3(x_426, x_79, x_48, x_420);
x_428 = lean_array_get_size(x_423);
x_429 = l_Lean_Expr_hash(x_427);
x_430 = lean_unsigned_to_nat(32u);
x_431 = lean_uint64_of_nat(x_430);
x_432 = lean_uint64_shift_right(x_429, x_431);
x_433 = lean_uint64_xor(x_429, x_432);
x_434 = lean_unsigned_to_nat(16u);
x_435 = lean_uint64_of_nat(x_434);
x_436 = lean_uint64_shift_right(x_433, x_435);
x_437 = lean_uint64_xor(x_433, x_436);
x_438 = lean_uint64_to_usize(x_437);
x_439 = lean_usize_of_nat(x_428);
lean_dec(x_428);
x_440 = lean_usize_of_nat(x_163);
x_441 = lean_usize_sub(x_439, x_440);
x_442 = lean_usize_land(x_438, x_441);
x_443 = lean_array_uget(x_423, x_442);
x_444 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectMVars_visit_spec__0___redArg(x_427, x_443);
if (x_444 == 0)
{
lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; uint8_t x_452; 
lean_dec(x_421);
x_445 = lean_box(0);
x_446 = lean_nat_add(x_422, x_163);
lean_dec(x_422);
x_447 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_447, 0, x_427);
lean_ctor_set(x_447, 1, x_445);
lean_ctor_set(x_447, 2, x_443);
x_448 = lean_array_uset(x_423, x_442, x_447);
x_449 = lean_nat_shiftl(x_446, x_165);
x_450 = lean_nat_div(x_449, x_94);
lean_dec(x_449);
x_451 = lean_array_get_size(x_448);
x_452 = lean_nat_dec_le(x_450, x_451);
lean_dec(x_451);
lean_dec(x_450);
if (x_452 == 0)
{
lean_object* x_453; lean_object* x_454; lean_object* x_455; 
x_453 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectMVars_visit_spec__1(lean_box(0), x_448);
x_454 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_454, 0, x_446);
lean_ctor_set(x_454, 1, x_453);
if (lean_is_scalar(x_409)) {
 x_455 = lean_alloc_ctor(0, 2, 0);
} else {
 x_455 = x_409;
}
lean_ctor_set(x_455, 0, x_454);
lean_ctor_set(x_455, 1, x_408);
return x_455;
}
else
{
lean_object* x_456; lean_object* x_457; 
x_456 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_456, 0, x_446);
lean_ctor_set(x_456, 1, x_448);
if (lean_is_scalar(x_409)) {
 x_457 = lean_alloc_ctor(0, 2, 0);
} else {
 x_457 = x_409;
}
lean_ctor_set(x_457, 0, x_456);
lean_ctor_set(x_457, 1, x_408);
return x_457;
}
}
else
{
lean_object* x_458; 
lean_dec(x_443);
lean_dec(x_427);
lean_dec(x_423);
lean_dec(x_422);
if (lean_is_scalar(x_409)) {
 x_458 = lean_alloc_ctor(0, 2, 0);
} else {
 x_458 = x_409;
}
lean_ctor_set(x_458, 0, x_421);
lean_ctor_set(x_458, 1, x_408);
return x_458;
}
}
block_503:
{
lean_object* x_473; lean_object* x_474; lean_object* x_475; uint64_t x_476; lean_object* x_477; uint64_t x_478; uint64_t x_479; uint64_t x_480; lean_object* x_481; uint64_t x_482; uint64_t x_483; uint64_t x_484; size_t x_485; size_t x_486; size_t x_487; size_t x_488; size_t x_489; lean_object* x_490; uint8_t x_491; 
lean_inc(x_420);
lean_inc(x_48);
x_473 = l_Lean_mkApp3(x_471, x_48, x_472, x_420);
lean_inc(x_48);
lean_inc(x_79);
x_474 = l_Lean_mkApp3(x_468, x_79, x_48, x_473);
x_475 = lean_array_get_size(x_465);
x_476 = l_Lean_Expr_hash(x_474);
x_477 = lean_unsigned_to_nat(32u);
x_478 = lean_uint64_of_nat(x_477);
x_479 = lean_uint64_shift_right(x_476, x_478);
x_480 = lean_uint64_xor(x_476, x_479);
x_481 = lean_unsigned_to_nat(16u);
x_482 = lean_uint64_of_nat(x_481);
x_483 = lean_uint64_shift_right(x_480, x_482);
x_484 = lean_uint64_xor(x_480, x_483);
x_485 = lean_uint64_to_usize(x_484);
x_486 = lean_usize_of_nat(x_475);
lean_dec(x_475);
x_487 = lean_usize_of_nat(x_163);
x_488 = lean_usize_sub(x_486, x_487);
x_489 = lean_usize_land(x_485, x_488);
x_490 = lean_array_uget(x_465, x_489);
x_491 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectMVars_visit_spec__0___redArg(x_474, x_490);
if (x_491 == 0)
{
lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; uint8_t x_498; 
x_492 = lean_box(0);
x_493 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_493, 0, x_474);
lean_ctor_set(x_493, 1, x_492);
lean_ctor_set(x_493, 2, x_490);
x_494 = lean_array_uset(x_465, x_489, x_493);
x_495 = lean_nat_shiftl(x_163, x_165);
x_496 = lean_nat_div(x_495, x_94);
lean_dec(x_495);
x_497 = lean_array_get_size(x_494);
x_498 = lean_nat_dec_le(x_496, x_497);
lean_dec(x_497);
lean_dec(x_496);
if (x_498 == 0)
{
lean_object* x_499; lean_object* x_500; 
x_499 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectMVars_visit_spec__1(lean_box(0), x_494);
lean_inc(x_499);
x_500 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_500, 0, x_163);
lean_ctor_set(x_500, 1, x_499);
x_421 = x_500;
x_422 = x_163;
x_423 = x_499;
goto block_459;
}
else
{
lean_object* x_501; 
lean_inc(x_494);
x_501 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_501, 0, x_163);
lean_ctor_set(x_501, 1, x_494);
x_421 = x_501;
x_422 = x_163;
x_423 = x_494;
goto block_459;
}
}
else
{
lean_object* x_502; 
lean_dec(x_490);
lean_dec(x_474);
lean_inc(x_465);
x_502 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_502, 0, x_100);
lean_ctor_set(x_502, 1, x_465);
x_421 = x_502;
x_422 = x_100;
x_423 = x_465;
goto block_459;
}
}
}
else
{
lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; 
lean_dec(x_397);
lean_dec(x_389);
lean_dec(x_369);
lean_dec(x_185);
lean_dec(x_176);
lean_dec(x_79);
lean_dec(x_48);
lean_dec(x_7);
x_521 = lean_ctor_get(x_406, 0);
lean_inc(x_521);
x_522 = lean_ctor_get(x_406, 1);
lean_inc(x_522);
if (lean_is_exclusive(x_406)) {
 lean_ctor_release(x_406, 0);
 lean_ctor_release(x_406, 1);
 x_523 = x_406;
} else {
 lean_dec_ref(x_406);
 x_523 = lean_box(0);
}
if (lean_is_scalar(x_523)) {
 x_524 = lean_alloc_ctor(1, 2, 0);
} else {
 x_524 = x_523;
}
lean_ctor_set(x_524, 0, x_521);
lean_ctor_set(x_524, 1, x_522);
return x_524;
}
}
else
{
lean_dec(x_389);
lean_dec(x_369);
lean_dec(x_185);
lean_dec(x_176);
lean_dec(x_79);
lean_dec(x_48);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_7);
x_166 = x_18;
goto block_175;
}
}
}
}
}
}
}
case 1:
{
uint8_t x_525; 
lean_dec(x_185);
lean_dec(x_176);
lean_dec(x_80);
x_525 = !lean_is_exclusive(x_194);
if (x_525 == 0)
{
lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; 
x_526 = lean_ctor_get(x_194, 0);
lean_dec(x_526);
x_527 = lean_ctor_get(x_195, 1);
lean_inc(x_527);
lean_dec(x_195);
x_528 = lean_ctor_get(x_202, 1);
lean_inc(x_528);
lean_dec(x_202);
x_529 = lean_ctor_get(x_213, 0);
lean_inc(x_529);
x_530 = lean_ctor_get(x_213, 1);
lean_inc(x_530);
lean_dec(x_213);
x_531 = l_Lean_Name_str___override(x_529, x_530);
x_532 = l_Lean_Name_str___override(x_531, x_528);
x_533 = l_Lean_Name_str___override(x_532, x_527);
lean_ctor_set(x_194, 0, x_533);
x_534 = l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__4(x_79, x_2, x_8, x_7, x_48, x_194, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_194);
return x_534;
}
else
{
lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; 
x_535 = lean_ctor_get(x_194, 1);
lean_inc(x_535);
lean_dec(x_194);
x_536 = lean_ctor_get(x_195, 1);
lean_inc(x_536);
lean_dec(x_195);
x_537 = lean_ctor_get(x_202, 1);
lean_inc(x_537);
lean_dec(x_202);
x_538 = lean_ctor_get(x_213, 0);
lean_inc(x_538);
x_539 = lean_ctor_get(x_213, 1);
lean_inc(x_539);
lean_dec(x_213);
x_540 = l_Lean_Name_str___override(x_538, x_539);
x_541 = l_Lean_Name_str___override(x_540, x_537);
x_542 = l_Lean_Name_str___override(x_541, x_536);
x_543 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_543, 0, x_542);
lean_ctor_set(x_543, 1, x_535);
x_544 = l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__4(x_79, x_2, x_8, x_7, x_48, x_543, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_543);
return x_544;
}
}
default: 
{
uint8_t x_545; 
lean_dec(x_185);
lean_dec(x_176);
lean_dec(x_80);
x_545 = !lean_is_exclusive(x_194);
if (x_545 == 0)
{
lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; 
x_546 = lean_ctor_get(x_194, 0);
lean_dec(x_546);
x_547 = lean_ctor_get(x_195, 1);
lean_inc(x_547);
lean_dec(x_195);
x_548 = lean_ctor_get(x_202, 1);
lean_inc(x_548);
lean_dec(x_202);
x_549 = lean_ctor_get(x_213, 0);
lean_inc(x_549);
x_550 = lean_ctor_get(x_213, 1);
lean_inc(x_550);
lean_dec(x_213);
x_551 = l_Lean_Name_num___override(x_549, x_550);
x_552 = l_Lean_Name_str___override(x_551, x_548);
x_553 = l_Lean_Name_str___override(x_552, x_547);
lean_ctor_set(x_194, 0, x_553);
x_554 = l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__4(x_79, x_2, x_8, x_7, x_48, x_194, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_194);
return x_554;
}
else
{
lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; 
x_555 = lean_ctor_get(x_194, 1);
lean_inc(x_555);
lean_dec(x_194);
x_556 = lean_ctor_get(x_195, 1);
lean_inc(x_556);
lean_dec(x_195);
x_557 = lean_ctor_get(x_202, 1);
lean_inc(x_557);
lean_dec(x_202);
x_558 = lean_ctor_get(x_213, 0);
lean_inc(x_558);
x_559 = lean_ctor_get(x_213, 1);
lean_inc(x_559);
lean_dec(x_213);
x_560 = l_Lean_Name_num___override(x_558, x_559);
x_561 = l_Lean_Name_str___override(x_560, x_557);
x_562 = l_Lean_Name_str___override(x_561, x_556);
x_563 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_563, 0, x_562);
lean_ctor_set(x_563, 1, x_555);
x_564 = l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__4(x_79, x_2, x_8, x_7, x_48, x_563, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_563);
return x_564;
}
}
}
}
default: 
{
uint8_t x_565; 
lean_dec(x_185);
lean_dec(x_176);
lean_dec(x_80);
x_565 = !lean_is_exclusive(x_194);
if (x_565 == 0)
{
lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; 
x_566 = lean_ctor_get(x_194, 0);
lean_dec(x_566);
x_567 = lean_ctor_get(x_195, 1);
lean_inc(x_567);
lean_dec(x_195);
x_568 = lean_ctor_get(x_202, 0);
lean_inc(x_568);
x_569 = lean_ctor_get(x_202, 1);
lean_inc(x_569);
lean_dec(x_202);
x_570 = l_Lean_Name_num___override(x_568, x_569);
x_571 = l_Lean_Name_str___override(x_570, x_567);
lean_ctor_set(x_194, 0, x_571);
x_572 = l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__4(x_79, x_2, x_8, x_7, x_48, x_194, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_194);
return x_572;
}
else
{
lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; 
x_573 = lean_ctor_get(x_194, 1);
lean_inc(x_573);
lean_dec(x_194);
x_574 = lean_ctor_get(x_195, 1);
lean_inc(x_574);
lean_dec(x_195);
x_575 = lean_ctor_get(x_202, 0);
lean_inc(x_575);
x_576 = lean_ctor_get(x_202, 1);
lean_inc(x_576);
lean_dec(x_202);
x_577 = l_Lean_Name_num___override(x_575, x_576);
x_578 = l_Lean_Name_str___override(x_577, x_574);
x_579 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_579, 0, x_578);
lean_ctor_set(x_579, 1, x_573);
x_580 = l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__4(x_79, x_2, x_8, x_7, x_48, x_579, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_579);
return x_580;
}
}
}
}
default: 
{
uint8_t x_581; 
lean_dec(x_185);
lean_dec(x_176);
lean_dec(x_80);
x_581 = !lean_is_exclusive(x_194);
if (x_581 == 0)
{
lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; 
x_582 = lean_ctor_get(x_194, 0);
lean_dec(x_582);
x_583 = lean_ctor_get(x_195, 0);
lean_inc(x_583);
x_584 = lean_ctor_get(x_195, 1);
lean_inc(x_584);
lean_dec(x_195);
x_585 = l_Lean_Name_num___override(x_583, x_584);
lean_ctor_set(x_194, 0, x_585);
x_586 = l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__4(x_79, x_2, x_8, x_7, x_48, x_194, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_194);
return x_586;
}
else
{
lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; 
x_587 = lean_ctor_get(x_194, 1);
lean_inc(x_587);
lean_dec(x_194);
x_588 = lean_ctor_get(x_195, 0);
lean_inc(x_588);
x_589 = lean_ctor_get(x_195, 1);
lean_inc(x_589);
lean_dec(x_195);
x_590 = l_Lean_Name_num___override(x_588, x_589);
x_591 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_591, 0, x_590);
lean_ctor_set(x_591, 1, x_587);
x_592 = l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__4(x_79, x_2, x_8, x_7, x_48, x_591, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_591);
return x_592;
}
}
}
}
else
{
lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; 
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_48);
lean_dec(x_8);
lean_dec(x_7);
x_593 = l_Lean_Name_str___override(x_2, x_185);
x_594 = l_Lean_Expr_const___override(x_593, x_159);
x_595 = lean_array_push(x_177, x_594);
x_596 = lean_array_push(x_595, x_164);
x_597 = lean_array_push(x_596, x_176);
lean_ctor_set(x_49, 1, x_597);
lean_ctor_set(x_49, 0, x_161);
x_598 = lean_box(x_12);
x_599 = lean_apply_11(x_6, x_49, x_9, x_10, x_11, x_598, x_13, x_14, x_15, x_16, x_17, x_18);
return x_599;
}
}
}
case 1:
{
lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; 
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_48);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_600 = lean_ctor_get(x_158, 1);
lean_inc(x_600);
lean_dec(x_158);
x_601 = lean_ctor_get(x_183, 0);
lean_inc(x_601);
x_602 = lean_ctor_get(x_183, 1);
lean_inc(x_602);
lean_dec(x_183);
x_603 = l_Lean_Name_str___override(x_601, x_602);
x_604 = l_Lean_Name_str___override(x_603, x_600);
x_605 = l_Lean_Expr_const___override(x_604, x_159);
x_606 = lean_array_push(x_177, x_605);
x_607 = lean_array_push(x_606, x_164);
x_608 = lean_array_push(x_607, x_176);
lean_ctor_set(x_49, 1, x_608);
lean_ctor_set(x_49, 0, x_161);
x_609 = lean_box(x_12);
x_610 = lean_apply_11(x_6, x_49, x_9, x_10, x_11, x_609, x_13, x_14, x_15, x_16, x_17, x_18);
return x_610;
}
default: 
{
lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; 
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_48);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_611 = lean_ctor_get(x_158, 1);
lean_inc(x_611);
lean_dec(x_158);
x_612 = lean_ctor_get(x_183, 0);
lean_inc(x_612);
x_613 = lean_ctor_get(x_183, 1);
lean_inc(x_613);
lean_dec(x_183);
x_614 = l_Lean_Name_num___override(x_612, x_613);
x_615 = l_Lean_Name_str___override(x_614, x_611);
x_616 = l_Lean_Expr_const___override(x_615, x_159);
x_617 = lean_array_push(x_177, x_616);
x_618 = lean_array_push(x_617, x_164);
x_619 = lean_array_push(x_618, x_176);
lean_ctor_set(x_49, 1, x_619);
lean_ctor_set(x_49, 0, x_161);
x_620 = lean_box(x_12);
x_621 = lean_apply_11(x_6, x_49, x_9, x_10, x_11, x_620, x_13, x_14, x_15, x_16, x_17, x_18);
return x_621;
}
}
}
default: 
{
lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; 
lean_dec(x_178);
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_48);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_622 = lean_ctor_get(x_158, 0);
lean_inc(x_622);
x_623 = lean_ctor_get(x_158, 1);
lean_inc(x_623);
lean_dec(x_158);
x_624 = l_Lean_Name_num___override(x_622, x_623);
x_625 = l_Lean_Expr_const___override(x_624, x_159);
x_626 = lean_array_push(x_177, x_625);
x_627 = lean_array_push(x_626, x_164);
x_628 = lean_array_push(x_627, x_176);
lean_ctor_set(x_49, 1, x_628);
lean_ctor_set(x_49, 0, x_161);
x_629 = lean_box(x_12);
x_630 = lean_apply_11(x_6, x_49, x_9, x_10, x_11, x_629, x_13, x_14, x_15, x_16, x_17, x_18);
return x_630;
}
}
block_175:
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_167 = lean_unsigned_to_nat(8u);
x_168 = lean_nat_shiftl(x_167, x_165);
x_169 = lean_nat_div(x_168, x_94);
lean_dec(x_168);
x_170 = l_Nat_nextPowerOfTwo(x_169);
lean_dec(x_169);
x_171 = lean_box(0);
x_172 = lean_mk_array(x_170, x_171);
x_173 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_173, 0, x_100);
lean_ctor_set(x_173, 1, x_172);
x_174 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_166);
return x_174;
}
}
case 5:
{
lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; 
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_48);
lean_dec(x_8);
x_631 = lean_ctor_get(x_101, 0);
lean_inc(x_631);
x_632 = lean_ctor_get(x_101, 1);
lean_inc(x_632);
lean_dec(x_101);
x_633 = l_Lean_Name_str___override(x_2, x_7);
x_634 = l_Lean_Name_str___override(x_633, x_87);
x_635 = l_Lean_Expr_app___override(x_631, x_632);
x_636 = lean_unsigned_to_nat(1u);
x_637 = lean_array_fget(x_74, x_636);
x_638 = lean_unsigned_to_nat(2u);
x_639 = lean_array_fget(x_74, x_638);
lean_dec(x_74);
x_640 = lean_mk_empty_array_with_capacity(x_94);
x_641 = lean_array_push(x_640, x_635);
x_642 = lean_array_push(x_641, x_637);
x_643 = lean_array_push(x_642, x_639);
lean_ctor_set(x_49, 1, x_643);
lean_ctor_set(x_49, 0, x_634);
x_644 = lean_box(x_12);
x_645 = lean_apply_11(x_6, x_49, x_9, x_10, x_11, x_644, x_13, x_14, x_15, x_16, x_17, x_18);
return x_645;
}
case 6:
{
lean_object* x_646; lean_object* x_647; lean_object* x_648; uint8_t x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; 
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_48);
lean_dec(x_8);
x_646 = lean_ctor_get(x_101, 0);
lean_inc(x_646);
x_647 = lean_ctor_get(x_101, 1);
lean_inc(x_647);
x_648 = lean_ctor_get(x_101, 2);
lean_inc(x_648);
x_649 = lean_ctor_get_uint8(x_101, sizeof(void*)*3 + 8);
lean_dec(x_101);
x_650 = l_Lean_Name_str___override(x_2, x_7);
x_651 = l_Lean_Name_str___override(x_650, x_87);
x_652 = l_Lean_Expr_lam___override(x_646, x_647, x_648, x_649);
x_653 = lean_unsigned_to_nat(1u);
x_654 = lean_array_fget(x_74, x_653);
x_655 = lean_unsigned_to_nat(2u);
x_656 = lean_array_fget(x_74, x_655);
lean_dec(x_74);
x_657 = lean_mk_empty_array_with_capacity(x_94);
x_658 = lean_array_push(x_657, x_652);
x_659 = lean_array_push(x_658, x_654);
x_660 = lean_array_push(x_659, x_656);
lean_ctor_set(x_49, 1, x_660);
lean_ctor_set(x_49, 0, x_651);
x_661 = lean_box(x_12);
x_662 = lean_apply_11(x_6, x_49, x_9, x_10, x_11, x_661, x_13, x_14, x_15, x_16, x_17, x_18);
return x_662;
}
case 7:
{
lean_object* x_663; lean_object* x_664; lean_object* x_665; uint8_t x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; 
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_48);
lean_dec(x_8);
x_663 = lean_ctor_get(x_101, 0);
lean_inc(x_663);
x_664 = lean_ctor_get(x_101, 1);
lean_inc(x_664);
x_665 = lean_ctor_get(x_101, 2);
lean_inc(x_665);
x_666 = lean_ctor_get_uint8(x_101, sizeof(void*)*3 + 8);
lean_dec(x_101);
x_667 = l_Lean_Name_str___override(x_2, x_7);
x_668 = l_Lean_Name_str___override(x_667, x_87);
x_669 = l_Lean_Expr_forallE___override(x_663, x_664, x_665, x_666);
x_670 = lean_unsigned_to_nat(1u);
x_671 = lean_array_fget(x_74, x_670);
x_672 = lean_unsigned_to_nat(2u);
x_673 = lean_array_fget(x_74, x_672);
lean_dec(x_74);
x_674 = lean_mk_empty_array_with_capacity(x_94);
x_675 = lean_array_push(x_674, x_669);
x_676 = lean_array_push(x_675, x_671);
x_677 = lean_array_push(x_676, x_673);
lean_ctor_set(x_49, 1, x_677);
lean_ctor_set(x_49, 0, x_668);
x_678 = lean_box(x_12);
x_679 = lean_apply_11(x_6, x_49, x_9, x_10, x_11, x_678, x_13, x_14, x_15, x_16, x_17, x_18);
return x_679;
}
case 8:
{
lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; uint8_t x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; 
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_48);
lean_dec(x_8);
x_680 = lean_ctor_get(x_101, 0);
lean_inc(x_680);
x_681 = lean_ctor_get(x_101, 1);
lean_inc(x_681);
x_682 = lean_ctor_get(x_101, 2);
lean_inc(x_682);
x_683 = lean_ctor_get(x_101, 3);
lean_inc(x_683);
x_684 = lean_ctor_get_uint8(x_101, sizeof(void*)*4 + 8);
lean_dec(x_101);
x_685 = l_Lean_Name_str___override(x_2, x_7);
x_686 = l_Lean_Name_str___override(x_685, x_87);
x_687 = l_Lean_Expr_letE___override(x_680, x_681, x_682, x_683, x_684);
x_688 = lean_unsigned_to_nat(1u);
x_689 = lean_array_fget(x_74, x_688);
x_690 = lean_unsigned_to_nat(2u);
x_691 = lean_array_fget(x_74, x_690);
lean_dec(x_74);
x_692 = lean_mk_empty_array_with_capacity(x_94);
x_693 = lean_array_push(x_692, x_687);
x_694 = lean_array_push(x_693, x_689);
x_695 = lean_array_push(x_694, x_691);
lean_ctor_set(x_49, 1, x_695);
lean_ctor_set(x_49, 0, x_686);
x_696 = lean_box(x_12);
x_697 = lean_apply_11(x_6, x_49, x_9, x_10, x_11, x_696, x_13, x_14, x_15, x_16, x_17, x_18);
return x_697;
}
case 9:
{
lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; 
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_48);
lean_dec(x_8);
x_698 = lean_ctor_get(x_101, 0);
lean_inc(x_698);
lean_dec(x_101);
x_699 = l_Lean_Name_str___override(x_2, x_7);
x_700 = l_Lean_Name_str___override(x_699, x_87);
x_701 = l_Lean_Expr_lit___override(x_698);
x_702 = lean_unsigned_to_nat(1u);
x_703 = lean_array_fget(x_74, x_702);
x_704 = lean_unsigned_to_nat(2u);
x_705 = lean_array_fget(x_74, x_704);
lean_dec(x_74);
x_706 = lean_mk_empty_array_with_capacity(x_94);
x_707 = lean_array_push(x_706, x_701);
x_708 = lean_array_push(x_707, x_703);
x_709 = lean_array_push(x_708, x_705);
lean_ctor_set(x_49, 1, x_709);
lean_ctor_set(x_49, 0, x_700);
x_710 = lean_box(x_12);
x_711 = lean_apply_11(x_6, x_49, x_9, x_10, x_11, x_710, x_13, x_14, x_15, x_16, x_17, x_18);
return x_711;
}
case 10:
{
lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; 
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_48);
lean_dec(x_8);
x_712 = lean_ctor_get(x_101, 0);
lean_inc(x_712);
x_713 = lean_ctor_get(x_101, 1);
lean_inc(x_713);
lean_dec(x_101);
x_714 = l_Lean_Name_str___override(x_2, x_7);
x_715 = l_Lean_Name_str___override(x_714, x_87);
x_716 = l_Lean_Expr_mdata___override(x_712, x_713);
x_717 = lean_unsigned_to_nat(1u);
x_718 = lean_array_fget(x_74, x_717);
x_719 = lean_unsigned_to_nat(2u);
x_720 = lean_array_fget(x_74, x_719);
lean_dec(x_74);
x_721 = lean_mk_empty_array_with_capacity(x_94);
x_722 = lean_array_push(x_721, x_716);
x_723 = lean_array_push(x_722, x_718);
x_724 = lean_array_push(x_723, x_720);
lean_ctor_set(x_49, 1, x_724);
lean_ctor_set(x_49, 0, x_715);
x_725 = lean_box(x_12);
x_726 = lean_apply_11(x_6, x_49, x_9, x_10, x_11, x_725, x_13, x_14, x_15, x_16, x_17, x_18);
return x_726;
}
default: 
{
lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; 
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_48);
lean_dec(x_8);
x_727 = lean_ctor_get(x_101, 0);
lean_inc(x_727);
x_728 = lean_ctor_get(x_101, 1);
lean_inc(x_728);
x_729 = lean_ctor_get(x_101, 2);
lean_inc(x_729);
lean_dec(x_101);
x_730 = l_Lean_Name_str___override(x_2, x_7);
x_731 = l_Lean_Name_str___override(x_730, x_87);
x_732 = l_Lean_Expr_proj___override(x_727, x_728, x_729);
x_733 = lean_unsigned_to_nat(1u);
x_734 = lean_array_fget(x_74, x_733);
x_735 = lean_unsigned_to_nat(2u);
x_736 = lean_array_fget(x_74, x_735);
lean_dec(x_74);
x_737 = lean_mk_empty_array_with_capacity(x_94);
x_738 = lean_array_push(x_737, x_732);
x_739 = lean_array_push(x_738, x_734);
x_740 = lean_array_push(x_739, x_736);
lean_ctor_set(x_49, 1, x_740);
lean_ctor_set(x_49, 0, x_731);
x_741 = lean_box(x_12);
x_742 = lean_apply_11(x_6, x_49, x_9, x_10, x_11, x_741, x_13, x_14, x_15, x_16, x_17, x_18);
return x_742;
}
}
}
}
}
}
else
{
lean_object* x_743; uint8_t x_744; 
lean_dec(x_77);
lean_dec(x_8);
lean_dec(x_7);
x_743 = lean_mk_string_unchecked("hPow", 4, 4);
x_744 = lean_string_dec_eq(x_76, x_743);
if (x_744 == 0)
{
lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; 
lean_dec(x_743);
lean_dec(x_79);
lean_dec(x_48);
x_745 = l_Lean_Name_str___override(x_2, x_80);
x_746 = l_Lean_Name_str___override(x_745, x_76);
lean_ctor_set(x_49, 0, x_746);
x_747 = lean_box(x_12);
x_748 = lean_apply_11(x_6, x_49, x_9, x_10, x_11, x_747, x_13, x_14, x_15, x_16, x_17, x_18);
return x_748;
}
else
{
lean_object* x_749; uint8_t x_750; 
lean_dec(x_76);
x_749 = lean_array_get_size(x_74);
x_750 = lean_nat_dec_eq(x_749, x_40);
lean_dec(x_749);
if (x_750 == 0)
{
lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; 
lean_dec(x_79);
lean_dec(x_48);
x_751 = l_Lean_Name_str___override(x_2, x_80);
x_752 = l_Lean_Name_str___override(x_751, x_743);
lean_ctor_set(x_49, 0, x_752);
x_753 = lean_box(x_12);
x_754 = lean_apply_11(x_6, x_49, x_9, x_10, x_11, x_753, x_13, x_14, x_15, x_16, x_17, x_18);
return x_754;
}
else
{
lean_object* x_755; lean_object* x_756; 
lean_dec(x_743);
lean_dec(x_80);
lean_free_object(x_49);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_2);
x_755 = lean_array_fget(x_74, x_78);
lean_inc(x_755);
x_756 = l_Lean_Elab_Tactic_Omega_natCast_x3f(x_755);
if (lean_obj_tag(x_756) == 0)
{
lean_dec(x_755);
lean_dec(x_79);
lean_dec(x_74);
lean_dec(x_48);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
x_19 = x_18;
goto block_31;
}
else
{
lean_object* x_757; lean_object* x_758; uint8_t x_759; 
x_757 = lean_ctor_get(x_756, 0);
lean_inc(x_757);
lean_dec(x_756);
x_758 = lean_unsigned_to_nat(0u);
x_759 = lean_nat_dec_eq(x_757, x_758);
lean_dec(x_757);
if (x_759 == 0)
{
lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_813; lean_object* x_814; lean_object* x_815; lean_object* x_816; lean_object* x_817; lean_object* x_818; lean_object* x_879; uint8_t x_880; 
x_760 = lean_array_fget(x_74, x_47);
lean_dec(x_74);
x_761 = lean_mk_string_unchecked("LT", 2, 2);
x_762 = lean_mk_string_unchecked("lt", 2, 2);
x_763 = l_Lean_Name_mkStr2(x_761, x_762);
x_764 = l_Lean_Level_ofNat(x_758);
x_765 = lean_box(0);
x_766 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_766, 0, x_764);
lean_ctor_set(x_766, 1, x_765);
lean_inc(x_766);
x_767 = l_Lean_Expr_const___override(x_763, x_766);
x_768 = lean_mk_string_unchecked("Int", 3, 3);
lean_inc(x_768);
x_813 = l_Lean_Name_mkStr1(x_768);
x_814 = l_Lean_Expr_const___override(x_813, x_765);
x_815 = lean_mk_string_unchecked("instLTInt", 9, 9);
lean_inc(x_768);
x_816 = l_Lean_Name_mkStr2(x_768, x_815);
x_817 = l_Lean_Expr_const___override(x_816, x_765);
x_879 = lean_nat_to_int(x_758);
x_880 = lean_int_dec_le(x_879, x_879);
if (x_880 == 0)
{
lean_object* x_881; lean_object* x_882; lean_object* x_883; lean_object* x_884; lean_object* x_885; lean_object* x_886; lean_object* x_887; lean_object* x_888; lean_object* x_889; lean_object* x_890; lean_object* x_891; 
x_881 = lean_mk_string_unchecked("Neg", 3, 3);
x_882 = lean_mk_string_unchecked("neg", 3, 3);
x_883 = l_Lean_Name_mkStr2(x_881, x_882);
x_884 = l_Lean_Expr_const___override(x_883, x_766);
x_885 = lean_mk_string_unchecked("instNegInt", 10, 10);
lean_inc(x_768);
x_886 = l_Lean_Name_mkStr2(x_768, x_885);
x_887 = l_Lean_Expr_const___override(x_886, x_765);
x_888 = lean_int_neg(x_879);
lean_dec(x_879);
x_889 = l_Int_toNat(x_888);
lean_dec(x_888);
x_890 = l_Lean_instToExprInt_mkNat(x_889);
lean_inc(x_814);
x_891 = l_Lean_mkApp3(x_884, x_814, x_887, x_890);
x_818 = x_891;
goto block_878;
}
else
{
lean_object* x_892; lean_object* x_893; 
lean_dec(x_766);
x_892 = l_Int_toNat(x_879);
lean_dec(x_879);
x_893 = l_Lean_instToExprInt_mkNat(x_892);
x_818 = x_893;
goto block_878;
}
block_812:
{
lean_object* x_774; lean_object* x_775; lean_object* x_776; lean_object* x_777; lean_object* x_778; uint64_t x_779; lean_object* x_780; uint64_t x_781; uint64_t x_782; uint64_t x_783; lean_object* x_784; uint64_t x_785; uint64_t x_786; uint64_t x_787; size_t x_788; size_t x_789; lean_object* x_790; size_t x_791; size_t x_792; size_t x_793; lean_object* x_794; uint8_t x_795; 
x_774 = lean_mk_string_unchecked("emod_lt_of_pos", 14, 14);
x_775 = l_Lean_Name_mkStr2(x_768, x_774);
x_776 = l_Lean_Expr_const___override(x_775, x_765);
x_777 = l_Lean_mkApp3(x_776, x_79, x_48, x_770);
x_778 = lean_array_get_size(x_773);
x_779 = l_Lean_Expr_hash(x_777);
x_780 = lean_unsigned_to_nat(32u);
x_781 = lean_uint64_of_nat(x_780);
x_782 = lean_uint64_shift_right(x_779, x_781);
x_783 = lean_uint64_xor(x_779, x_782);
x_784 = lean_unsigned_to_nat(16u);
x_785 = lean_uint64_of_nat(x_784);
x_786 = lean_uint64_shift_right(x_783, x_785);
x_787 = lean_uint64_xor(x_783, x_786);
x_788 = lean_uint64_to_usize(x_787);
x_789 = lean_usize_of_nat(x_778);
lean_dec(x_778);
x_790 = lean_unsigned_to_nat(1u);
x_791 = lean_usize_of_nat(x_790);
x_792 = lean_usize_sub(x_789, x_791);
x_793 = lean_usize_land(x_788, x_792);
x_794 = lean_array_uget(x_773, x_793);
x_795 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectMVars_visit_spec__0___redArg(x_777, x_794);
if (x_795 == 0)
{
lean_object* x_796; lean_object* x_797; lean_object* x_798; lean_object* x_799; lean_object* x_800; lean_object* x_801; lean_object* x_802; lean_object* x_803; lean_object* x_804; uint8_t x_805; 
lean_dec(x_771);
x_796 = lean_box(0);
x_797 = lean_nat_add(x_772, x_790);
lean_dec(x_772);
x_798 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_798, 0, x_777);
lean_ctor_set(x_798, 1, x_796);
lean_ctor_set(x_798, 2, x_794);
x_799 = lean_array_uset(x_773, x_793, x_798);
x_800 = lean_unsigned_to_nat(2u);
x_801 = lean_nat_shiftl(x_797, x_800);
x_802 = lean_unsigned_to_nat(3u);
x_803 = lean_nat_div(x_801, x_802);
lean_dec(x_801);
x_804 = lean_array_get_size(x_799);
x_805 = lean_nat_dec_le(x_803, x_804);
lean_dec(x_804);
lean_dec(x_803);
if (x_805 == 0)
{
lean_object* x_806; lean_object* x_807; lean_object* x_808; 
x_806 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectMVars_visit_spec__1(lean_box(0), x_799);
x_807 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_807, 0, x_797);
lean_ctor_set(x_807, 1, x_806);
x_808 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_808, 0, x_807);
lean_ctor_set(x_808, 1, x_769);
return x_808;
}
else
{
lean_object* x_809; lean_object* x_810; 
x_809 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_809, 0, x_797);
lean_ctor_set(x_809, 1, x_799);
x_810 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_810, 0, x_809);
lean_ctor_set(x_810, 1, x_769);
return x_810;
}
}
else
{
lean_object* x_811; 
lean_dec(x_794);
lean_dec(x_777);
lean_dec(x_773);
lean_dec(x_772);
x_811 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_811, 0, x_771);
lean_ctor_set(x_811, 1, x_769);
return x_811;
}
}
block_878:
{
lean_object* x_819; lean_object* x_820; 
lean_inc(x_755);
lean_inc(x_818);
x_819 = l_Lean_mkApp4(x_767, x_814, x_817, x_818, x_755);
x_820 = l_Lean_Meta_mkDecideProof(x_819, x_14, x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_820) == 0)
{
lean_object* x_821; lean_object* x_822; lean_object* x_823; lean_object* x_824; lean_object* x_825; lean_object* x_826; lean_object* x_827; lean_object* x_828; lean_object* x_829; lean_object* x_830; lean_object* x_831; lean_object* x_832; lean_object* x_833; lean_object* x_834; lean_object* x_835; lean_object* x_836; lean_object* x_837; lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; lean_object* x_844; lean_object* x_845; uint64_t x_846; lean_object* x_847; uint64_t x_848; uint64_t x_849; uint64_t x_850; lean_object* x_851; uint64_t x_852; uint64_t x_853; uint64_t x_854; size_t x_855; size_t x_856; lean_object* x_857; size_t x_858; size_t x_859; size_t x_860; lean_object* x_861; uint8_t x_862; 
x_821 = lean_ctor_get(x_820, 0);
lean_inc(x_821);
x_822 = lean_ctor_get(x_820, 1);
lean_inc(x_822);
lean_dec(x_820);
x_823 = lean_mk_string_unchecked("Lean", 4, 4);
x_824 = lean_mk_string_unchecked("Omega", 5, 5);
x_825 = lean_mk_string_unchecked("pos_pow_of_pos", 14, 14);
lean_inc(x_768);
x_826 = l_Lean_Name_mkStr4(x_823, x_824, x_768, x_825);
x_827 = l_Lean_Expr_const___override(x_826, x_765);
x_828 = l_Lean_mkApp3(x_827, x_755, x_760, x_821);
x_829 = lean_unsigned_to_nat(8u);
x_830 = lean_unsigned_to_nat(2u);
x_831 = lean_nat_shiftl(x_829, x_830);
x_832 = lean_unsigned_to_nat(3u);
x_833 = lean_nat_div(x_831, x_832);
lean_dec(x_831);
x_834 = l_Nat_nextPowerOfTwo(x_833);
lean_dec(x_833);
x_835 = lean_box(0);
x_836 = lean_mk_array(x_834, x_835);
x_837 = lean_mk_string_unchecked("emod_nonneg", 11, 11);
lean_inc(x_768);
x_838 = l_Lean_Name_mkStr2(x_768, x_837);
x_839 = l_Lean_Expr_const___override(x_838, x_765);
x_840 = lean_mk_string_unchecked("ne_of_gt", 8, 8);
lean_inc(x_768);
x_841 = l_Lean_Name_mkStr2(x_768, x_840);
x_842 = l_Lean_Expr_const___override(x_841, x_765);
lean_inc(x_828);
lean_inc(x_48);
x_843 = l_Lean_mkApp3(x_842, x_48, x_818, x_828);
lean_inc(x_48);
lean_inc(x_79);
x_844 = l_Lean_mkApp3(x_839, x_79, x_48, x_843);
x_845 = lean_array_get_size(x_836);
x_846 = l_Lean_Expr_hash(x_844);
x_847 = lean_unsigned_to_nat(32u);
x_848 = lean_uint64_of_nat(x_847);
x_849 = lean_uint64_shift_right(x_846, x_848);
x_850 = lean_uint64_xor(x_846, x_849);
x_851 = lean_unsigned_to_nat(16u);
x_852 = lean_uint64_of_nat(x_851);
x_853 = lean_uint64_shift_right(x_850, x_852);
x_854 = lean_uint64_xor(x_850, x_853);
x_855 = lean_uint64_to_usize(x_854);
x_856 = lean_usize_of_nat(x_845);
lean_dec(x_845);
x_857 = lean_unsigned_to_nat(1u);
x_858 = lean_usize_of_nat(x_857);
x_859 = lean_usize_sub(x_856, x_858);
x_860 = lean_usize_land(x_855, x_859);
x_861 = lean_array_uget(x_836, x_860);
x_862 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectMVars_visit_spec__0___redArg(x_844, x_861);
if (x_862 == 0)
{
lean_object* x_863; lean_object* x_864; lean_object* x_865; lean_object* x_866; lean_object* x_867; lean_object* x_868; uint8_t x_869; 
x_863 = lean_box(0);
x_864 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_864, 0, x_844);
lean_ctor_set(x_864, 1, x_863);
lean_ctor_set(x_864, 2, x_861);
x_865 = lean_array_uset(x_836, x_860, x_864);
x_866 = lean_nat_shiftl(x_857, x_830);
x_867 = lean_nat_div(x_866, x_832);
lean_dec(x_866);
x_868 = lean_array_get_size(x_865);
x_869 = lean_nat_dec_le(x_867, x_868);
lean_dec(x_868);
lean_dec(x_867);
if (x_869 == 0)
{
lean_object* x_870; lean_object* x_871; 
x_870 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectMVars_visit_spec__1(lean_box(0), x_865);
lean_inc(x_870);
x_871 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_871, 0, x_857);
lean_ctor_set(x_871, 1, x_870);
x_769 = x_822;
x_770 = x_828;
x_771 = x_871;
x_772 = x_857;
x_773 = x_870;
goto block_812;
}
else
{
lean_object* x_872; 
lean_inc(x_865);
x_872 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_872, 0, x_857);
lean_ctor_set(x_872, 1, x_865);
x_769 = x_822;
x_770 = x_828;
x_771 = x_872;
x_772 = x_857;
x_773 = x_865;
goto block_812;
}
}
else
{
lean_object* x_873; 
lean_dec(x_861);
lean_dec(x_844);
lean_inc(x_836);
x_873 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_873, 0, x_758);
lean_ctor_set(x_873, 1, x_836);
x_769 = x_822;
x_770 = x_828;
x_771 = x_873;
x_772 = x_758;
x_773 = x_836;
goto block_812;
}
}
else
{
uint8_t x_874; 
lean_dec(x_818);
lean_dec(x_768);
lean_dec(x_760);
lean_dec(x_755);
lean_dec(x_79);
lean_dec(x_48);
x_874 = !lean_is_exclusive(x_820);
if (x_874 == 0)
{
return x_820;
}
else
{
lean_object* x_875; lean_object* x_876; lean_object* x_877; 
x_875 = lean_ctor_get(x_820, 0);
x_876 = lean_ctor_get(x_820, 1);
lean_inc(x_876);
lean_inc(x_875);
lean_dec(x_820);
x_877 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_877, 0, x_875);
lean_ctor_set(x_877, 1, x_876);
return x_877;
}
}
}
}
else
{
lean_dec(x_755);
lean_dec(x_79);
lean_dec(x_74);
lean_dec(x_48);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
x_19 = x_18;
goto block_31;
}
}
}
}
}
}
else
{
lean_object* x_894; lean_object* x_895; lean_object* x_896; lean_object* x_897; lean_object* x_898; lean_object* x_899; uint8_t x_900; 
x_894 = lean_ctor_get(x_49, 1);
lean_inc(x_894);
lean_dec(x_49);
x_895 = lean_ctor_get(x_50, 1);
lean_inc(x_895);
lean_dec(x_50);
x_896 = lean_ctor_get(x_59, 1);
lean_inc(x_896);
lean_dec(x_59);
x_897 = lean_unsigned_to_nat(4u);
x_898 = lean_array_fget(x_4, x_897);
lean_dec(x_4);
x_899 = lean_mk_string_unchecked("HPow", 4, 4);
x_900 = lean_string_dec_eq(x_896, x_899);
if (x_900 == 0)
{
uint8_t x_901; 
x_901 = lean_string_dec_eq(x_896, x_7);
if (x_901 == 0)
{
lean_object* x_902; lean_object* x_903; lean_object* x_904; lean_object* x_905; lean_object* x_906; 
lean_dec(x_899);
lean_dec(x_898);
lean_dec(x_48);
lean_dec(x_8);
lean_dec(x_7);
x_902 = l_Lean_Name_str___override(x_2, x_896);
x_903 = l_Lean_Name_str___override(x_902, x_895);
x_904 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_904, 0, x_903);
lean_ctor_set(x_904, 1, x_894);
x_905 = lean_box(x_12);
x_906 = lean_apply_11(x_6, x_904, x_9, x_10, x_11, x_905, x_13, x_14, x_15, x_16, x_17, x_18);
return x_906;
}
else
{
lean_object* x_907; uint8_t x_908; 
lean_dec(x_896);
x_907 = lean_mk_string_unchecked("cast", 4, 4);
x_908 = lean_string_dec_eq(x_895, x_907);
if (x_908 == 0)
{
lean_object* x_909; lean_object* x_910; lean_object* x_911; lean_object* x_912; lean_object* x_913; 
lean_dec(x_907);
lean_dec(x_899);
lean_dec(x_898);
lean_dec(x_48);
lean_dec(x_8);
x_909 = l_Lean_Name_str___override(x_2, x_7);
x_910 = l_Lean_Name_str___override(x_909, x_895);
x_911 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_911, 0, x_910);
lean_ctor_set(x_911, 1, x_894);
x_912 = lean_box(x_12);
x_913 = lean_apply_11(x_6, x_911, x_9, x_10, x_11, x_912, x_13, x_14, x_15, x_16, x_17, x_18);
return x_913;
}
else
{
lean_object* x_914; lean_object* x_915; uint8_t x_916; 
lean_dec(x_895);
x_914 = lean_array_get_size(x_894);
x_915 = lean_unsigned_to_nat(3u);
x_916 = lean_nat_dec_eq(x_914, x_915);
lean_dec(x_914);
if (x_916 == 0)
{
lean_object* x_917; lean_object* x_918; lean_object* x_919; lean_object* x_920; lean_object* x_921; 
lean_dec(x_899);
lean_dec(x_898);
lean_dec(x_48);
lean_dec(x_8);
x_917 = l_Lean_Name_str___override(x_2, x_7);
x_918 = l_Lean_Name_str___override(x_917, x_907);
x_919 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_919, 0, x_918);
lean_ctor_set(x_919, 1, x_894);
x_920 = lean_box(x_12);
x_921 = lean_apply_11(x_6, x_919, x_9, x_10, x_11, x_920, x_13, x_14, x_15, x_16, x_17, x_18);
return x_921;
}
else
{
lean_object* x_922; lean_object* x_923; 
x_922 = lean_unsigned_to_nat(0u);
x_923 = lean_array_fget(x_894, x_922);
switch (lean_obj_tag(x_923)) {
case 0:
{
lean_object* x_924; lean_object* x_925; lean_object* x_926; lean_object* x_927; lean_object* x_928; lean_object* x_929; lean_object* x_930; lean_object* x_931; lean_object* x_932; lean_object* x_933; lean_object* x_934; lean_object* x_935; lean_object* x_936; lean_object* x_937; lean_object* x_938; 
lean_dec(x_899);
lean_dec(x_898);
lean_dec(x_48);
lean_dec(x_8);
x_924 = lean_ctor_get(x_923, 0);
lean_inc(x_924);
lean_dec(x_923);
x_925 = l_Lean_Name_str___override(x_2, x_7);
x_926 = l_Lean_Name_str___override(x_925, x_907);
x_927 = l_Lean_Expr_bvar___override(x_924);
x_928 = lean_unsigned_to_nat(1u);
x_929 = lean_array_fget(x_894, x_928);
x_930 = lean_unsigned_to_nat(2u);
x_931 = lean_array_fget(x_894, x_930);
lean_dec(x_894);
x_932 = lean_mk_empty_array_with_capacity(x_915);
x_933 = lean_array_push(x_932, x_927);
x_934 = lean_array_push(x_933, x_929);
x_935 = lean_array_push(x_934, x_931);
x_936 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_936, 0, x_926);
lean_ctor_set(x_936, 1, x_935);
x_937 = lean_box(x_12);
x_938 = lean_apply_11(x_6, x_936, x_9, x_10, x_11, x_937, x_13, x_14, x_15, x_16, x_17, x_18);
return x_938;
}
case 1:
{
lean_object* x_939; lean_object* x_940; lean_object* x_941; lean_object* x_942; lean_object* x_943; lean_object* x_944; lean_object* x_945; lean_object* x_946; lean_object* x_947; lean_object* x_948; lean_object* x_949; lean_object* x_950; lean_object* x_951; lean_object* x_952; lean_object* x_953; 
lean_dec(x_899);
lean_dec(x_898);
lean_dec(x_48);
lean_dec(x_8);
x_939 = lean_ctor_get(x_923, 0);
lean_inc(x_939);
lean_dec(x_923);
x_940 = l_Lean_Name_str___override(x_2, x_7);
x_941 = l_Lean_Name_str___override(x_940, x_907);
x_942 = l_Lean_Expr_fvar___override(x_939);
x_943 = lean_unsigned_to_nat(1u);
x_944 = lean_array_fget(x_894, x_943);
x_945 = lean_unsigned_to_nat(2u);
x_946 = lean_array_fget(x_894, x_945);
lean_dec(x_894);
x_947 = lean_mk_empty_array_with_capacity(x_915);
x_948 = lean_array_push(x_947, x_942);
x_949 = lean_array_push(x_948, x_944);
x_950 = lean_array_push(x_949, x_946);
x_951 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_951, 0, x_941);
lean_ctor_set(x_951, 1, x_950);
x_952 = lean_box(x_12);
x_953 = lean_apply_11(x_6, x_951, x_9, x_10, x_11, x_952, x_13, x_14, x_15, x_16, x_17, x_18);
return x_953;
}
case 2:
{
lean_object* x_954; lean_object* x_955; lean_object* x_956; lean_object* x_957; lean_object* x_958; lean_object* x_959; lean_object* x_960; lean_object* x_961; lean_object* x_962; lean_object* x_963; lean_object* x_964; lean_object* x_965; lean_object* x_966; lean_object* x_967; lean_object* x_968; 
lean_dec(x_899);
lean_dec(x_898);
lean_dec(x_48);
lean_dec(x_8);
x_954 = lean_ctor_get(x_923, 0);
lean_inc(x_954);
lean_dec(x_923);
x_955 = l_Lean_Name_str___override(x_2, x_7);
x_956 = l_Lean_Name_str___override(x_955, x_907);
x_957 = l_Lean_Expr_mvar___override(x_954);
x_958 = lean_unsigned_to_nat(1u);
x_959 = lean_array_fget(x_894, x_958);
x_960 = lean_unsigned_to_nat(2u);
x_961 = lean_array_fget(x_894, x_960);
lean_dec(x_894);
x_962 = lean_mk_empty_array_with_capacity(x_915);
x_963 = lean_array_push(x_962, x_957);
x_964 = lean_array_push(x_963, x_959);
x_965 = lean_array_push(x_964, x_961);
x_966 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_966, 0, x_956);
lean_ctor_set(x_966, 1, x_965);
x_967 = lean_box(x_12);
x_968 = lean_apply_11(x_6, x_966, x_9, x_10, x_11, x_967, x_13, x_14, x_15, x_16, x_17, x_18);
return x_968;
}
case 3:
{
lean_object* x_969; lean_object* x_970; lean_object* x_971; lean_object* x_972; lean_object* x_973; lean_object* x_974; lean_object* x_975; lean_object* x_976; lean_object* x_977; lean_object* x_978; lean_object* x_979; lean_object* x_980; lean_object* x_981; lean_object* x_982; lean_object* x_983; 
lean_dec(x_899);
lean_dec(x_898);
lean_dec(x_48);
lean_dec(x_8);
x_969 = lean_ctor_get(x_923, 0);
lean_inc(x_969);
lean_dec(x_923);
x_970 = l_Lean_Name_str___override(x_2, x_7);
x_971 = l_Lean_Name_str___override(x_970, x_907);
x_972 = l_Lean_Expr_sort___override(x_969);
x_973 = lean_unsigned_to_nat(1u);
x_974 = lean_array_fget(x_894, x_973);
x_975 = lean_unsigned_to_nat(2u);
x_976 = lean_array_fget(x_894, x_975);
lean_dec(x_894);
x_977 = lean_mk_empty_array_with_capacity(x_915);
x_978 = lean_array_push(x_977, x_972);
x_979 = lean_array_push(x_978, x_974);
x_980 = lean_array_push(x_979, x_976);
x_981 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_981, 0, x_971);
lean_ctor_set(x_981, 1, x_980);
x_982 = lean_box(x_12);
x_983 = lean_apply_11(x_6, x_981, x_9, x_10, x_11, x_982, x_13, x_14, x_15, x_16, x_17, x_18);
return x_983;
}
case 4:
{
lean_object* x_984; lean_object* x_985; lean_object* x_986; lean_object* x_987; lean_object* x_988; lean_object* x_989; lean_object* x_990; lean_object* x_991; lean_object* x_992; lean_object* x_1002; lean_object* x_1003; lean_object* x_1004; 
x_984 = lean_ctor_get(x_923, 0);
lean_inc(x_984);
x_985 = lean_ctor_get(x_923, 1);
lean_inc(x_985);
lean_dec(x_923);
lean_inc(x_7);
lean_inc(x_2);
x_986 = l_Lean_Name_str___override(x_2, x_7);
x_987 = l_Lean_Name_str___override(x_986, x_907);
lean_inc(x_985);
lean_inc(x_2);
x_988 = l_Lean_Expr_const___override(x_2, x_985);
x_989 = lean_unsigned_to_nat(1u);
x_990 = lean_array_fget(x_894, x_989);
x_991 = lean_unsigned_to_nat(2u);
x_1002 = lean_array_fget(x_894, x_991);
lean_dec(x_894);
x_1003 = lean_mk_empty_array_with_capacity(x_915);
lean_inc(x_1003);
x_1004 = lean_array_push(x_1003, x_988);
switch (lean_obj_tag(x_984)) {
case 0:
{
lean_object* x_1005; lean_object* x_1006; lean_object* x_1007; lean_object* x_1008; lean_object* x_1009; 
lean_dec(x_1003);
lean_dec(x_985);
lean_dec(x_899);
lean_dec(x_898);
lean_dec(x_48);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_1005 = lean_array_push(x_1004, x_990);
x_1006 = lean_array_push(x_1005, x_1002);
x_1007 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1007, 0, x_987);
lean_ctor_set(x_1007, 1, x_1006);
x_1008 = lean_box(x_12);
x_1009 = lean_apply_11(x_6, x_1007, x_9, x_10, x_11, x_1008, x_13, x_14, x_15, x_16, x_17, x_18);
return x_1009;
}
case 1:
{
lean_object* x_1010; 
lean_dec(x_1004);
x_1010 = lean_ctor_get(x_984, 0);
lean_inc(x_1010);
switch (lean_obj_tag(x_1010)) {
case 0:
{
lean_object* x_1011; lean_object* x_1012; uint8_t x_1013; 
x_1011 = lean_ctor_get(x_984, 1);
lean_inc(x_1011);
lean_dec(x_984);
x_1012 = lean_mk_string_unchecked("Int", 3, 3);
x_1013 = lean_string_dec_eq(x_1011, x_1012);
if (x_1013 == 0)
{
lean_object* x_1014; lean_object* x_1015; lean_object* x_1016; lean_object* x_1017; lean_object* x_1018; lean_object* x_1019; lean_object* x_1020; lean_object* x_1021; 
lean_dec(x_1012);
lean_dec(x_899);
lean_dec(x_898);
lean_dec(x_48);
lean_dec(x_8);
lean_dec(x_7);
x_1014 = l_Lean_Name_str___override(x_2, x_1011);
x_1015 = l_Lean_Expr_const___override(x_1014, x_985);
x_1016 = lean_array_push(x_1003, x_1015);
x_1017 = lean_array_push(x_1016, x_990);
x_1018 = lean_array_push(x_1017, x_1002);
x_1019 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1019, 0, x_987);
lean_ctor_set(x_1019, 1, x_1018);
x_1020 = lean_box(x_12);
x_1021 = lean_apply_11(x_6, x_1019, x_9, x_10, x_11, x_1020, x_13, x_14, x_15, x_16, x_17, x_18);
return x_1021;
}
else
{
lean_dec(x_1011);
if (lean_obj_tag(x_985) == 0)
{
lean_object* x_1022; lean_object* x_1023; 
lean_dec(x_1003);
lean_dec(x_990);
lean_dec(x_987);
lean_dec(x_6);
lean_inc(x_1002);
x_1022 = l_Lean_Expr_getAppFnArgs(x_1002);
x_1023 = lean_ctor_get(x_1022, 0);
lean_inc(x_1023);
switch (lean_obj_tag(x_1023)) {
case 0:
{
lean_object* x_1024; lean_object* x_1025; lean_object* x_1026; lean_object* x_1027; 
lean_dec(x_1012);
lean_dec(x_1002);
lean_dec(x_899);
x_1024 = lean_ctor_get(x_1022, 1);
lean_inc(x_1024);
if (lean_is_exclusive(x_1022)) {
 lean_ctor_release(x_1022, 0);
 lean_ctor_release(x_1022, 1);
 x_1025 = x_1022;
} else {
 lean_dec_ref(x_1022);
 x_1025 = lean_box(0);
}
lean_inc(x_2);
if (lean_is_scalar(x_1025)) {
 x_1026 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1026 = x_1025;
}
lean_ctor_set(x_1026, 0, x_2);
lean_ctor_set(x_1026, 1, x_1024);
x_1027 = l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__4(x_898, x_2, x_8, x_7, x_48, x_1026, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_1026);
return x_1027;
}
case 1:
{
lean_object* x_1028; 
x_1028 = lean_ctor_get(x_1023, 0);
lean_inc(x_1028);
switch (lean_obj_tag(x_1028)) {
case 0:
{
lean_object* x_1029; lean_object* x_1030; lean_object* x_1031; lean_object* x_1032; lean_object* x_1033; lean_object* x_1034; 
lean_dec(x_1012);
lean_dec(x_1002);
lean_dec(x_899);
x_1029 = lean_ctor_get(x_1022, 1);
lean_inc(x_1029);
if (lean_is_exclusive(x_1022)) {
 lean_ctor_release(x_1022, 0);
 lean_ctor_release(x_1022, 1);
 x_1030 = x_1022;
} else {
 lean_dec_ref(x_1022);
 x_1030 = lean_box(0);
}
x_1031 = lean_ctor_get(x_1023, 1);
lean_inc(x_1031);
lean_dec(x_1023);
lean_inc(x_2);
x_1032 = l_Lean_Name_str___override(x_2, x_1031);
if (lean_is_scalar(x_1030)) {
 x_1033 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1033 = x_1030;
}
lean_ctor_set(x_1033, 0, x_1032);
lean_ctor_set(x_1033, 1, x_1029);
x_1034 = l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__4(x_898, x_2, x_8, x_7, x_48, x_1033, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_1033);
return x_1034;
}
case 1:
{
lean_object* x_1035; 
x_1035 = lean_ctor_get(x_1028, 0);
lean_inc(x_1035);
switch (lean_obj_tag(x_1035)) {
case 0:
{
lean_object* x_1036; lean_object* x_1037; lean_object* x_1038; lean_object* x_1039; uint8_t x_1040; 
x_1036 = lean_ctor_get(x_1022, 1);
lean_inc(x_1036);
if (lean_is_exclusive(x_1022)) {
 lean_ctor_release(x_1022, 0);
 lean_ctor_release(x_1022, 1);
 x_1037 = x_1022;
} else {
 lean_dec_ref(x_1022);
 x_1037 = lean_box(0);
}
x_1038 = lean_ctor_get(x_1023, 1);
lean_inc(x_1038);
lean_dec(x_1023);
x_1039 = lean_ctor_get(x_1028, 1);
lean_inc(x_1039);
lean_dec(x_1028);
x_1040 = lean_string_dec_eq(x_1039, x_899);
if (x_1040 == 0)
{
lean_object* x_1041; lean_object* x_1042; lean_object* x_1043; lean_object* x_1044; 
lean_dec(x_1012);
lean_dec(x_1002);
lean_dec(x_899);
lean_inc(x_2);
x_1041 = l_Lean_Name_str___override(x_2, x_1039);
x_1042 = l_Lean_Name_str___override(x_1041, x_1038);
if (lean_is_scalar(x_1037)) {
 x_1043 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1043 = x_1037;
}
lean_ctor_set(x_1043, 0, x_1042);
lean_ctor_set(x_1043, 1, x_1036);
x_1044 = l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__4(x_898, x_2, x_8, x_7, x_48, x_1043, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_1043);
return x_1044;
}
else
{
lean_object* x_1045; uint8_t x_1046; 
lean_dec(x_1039);
x_1045 = lean_mk_string_unchecked("hPow", 4, 4);
x_1046 = lean_string_dec_eq(x_1038, x_1045);
if (x_1046 == 0)
{
lean_object* x_1047; lean_object* x_1048; lean_object* x_1049; lean_object* x_1050; 
lean_dec(x_1045);
lean_dec(x_1012);
lean_dec(x_1002);
lean_inc(x_2);
x_1047 = l_Lean_Name_str___override(x_2, x_899);
x_1048 = l_Lean_Name_str___override(x_1047, x_1038);
if (lean_is_scalar(x_1037)) {
 x_1049 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1049 = x_1037;
}
lean_ctor_set(x_1049, 0, x_1048);
lean_ctor_set(x_1049, 1, x_1036);
x_1050 = l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__4(x_898, x_2, x_8, x_7, x_48, x_1049, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_1049);
return x_1050;
}
else
{
lean_object* x_1051; uint8_t x_1052; 
lean_dec(x_1038);
x_1051 = lean_array_get_size(x_1036);
x_1052 = lean_nat_dec_eq(x_1051, x_40);
lean_dec(x_1051);
if (x_1052 == 0)
{
lean_object* x_1053; lean_object* x_1054; lean_object* x_1055; lean_object* x_1056; 
lean_dec(x_1012);
lean_dec(x_1002);
lean_inc(x_2);
x_1053 = l_Lean_Name_str___override(x_2, x_899);
x_1054 = l_Lean_Name_str___override(x_1053, x_1045);
if (lean_is_scalar(x_1037)) {
 x_1055 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1055 = x_1037;
}
lean_ctor_set(x_1055, 0, x_1054);
lean_ctor_set(x_1055, 1, x_1036);
x_1056 = l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__4(x_898, x_2, x_8, x_7, x_48, x_1055, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_1055);
return x_1056;
}
else
{
lean_object* x_1057; lean_object* x_1058; 
lean_dec(x_1045);
lean_dec(x_1037);
lean_dec(x_899);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_1057 = lean_array_fget(x_1036, x_897);
lean_inc(x_1057);
x_1058 = l_Lean_Elab_Tactic_Omega_natCast_x3f(x_1057);
if (lean_obj_tag(x_1058) == 0)
{
lean_dec(x_1057);
lean_dec(x_1036);
lean_dec(x_1012);
lean_dec(x_1002);
lean_dec(x_898);
lean_dec(x_48);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_7);
x_992 = x_18;
goto block_1001;
}
else
{
lean_object* x_1059; uint8_t x_1060; 
x_1059 = lean_ctor_get(x_1058, 0);
lean_inc(x_1059);
lean_dec(x_1058);
x_1060 = lean_nat_dec_eq(x_1059, x_922);
lean_dec(x_1059);
if (x_1060 == 0)
{
lean_object* x_1061; lean_object* x_1062; lean_object* x_1063; lean_object* x_1064; lean_object* x_1065; lean_object* x_1066; lean_object* x_1067; lean_object* x_1068; lean_object* x_1069; lean_object* x_1070; lean_object* x_1071; lean_object* x_1072; lean_object* x_1073; lean_object* x_1074; 
x_1061 = lean_mk_string_unchecked("LT", 2, 2);
x_1062 = lean_mk_string_unchecked("lt", 2, 2);
x_1063 = l_Lean_Name_mkStr2(x_1061, x_1062);
x_1064 = l_Lean_Level_ofNat(x_922);
x_1065 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1065, 0, x_1064);
lean_ctor_set(x_1065, 1, x_985);
lean_inc(x_1065);
x_1066 = l_Lean_Expr_const___override(x_1063, x_1065);
lean_inc(x_7);
x_1067 = l_Lean_Name_mkStr1(x_7);
x_1068 = l_Lean_Expr_const___override(x_1067, x_985);
x_1069 = lean_mk_string_unchecked("instLTNat", 9, 9);
x_1070 = l_Lean_Name_mkStr1(x_1069);
x_1071 = l_Lean_Expr_const___override(x_1070, x_985);
x_1072 = l_Lean_mkNatLit(x_922);
lean_inc(x_1057);
x_1073 = l_Lean_mkApp4(x_1066, x_1068, x_1071, x_1072, x_1057);
x_1074 = l_Lean_Meta_mkDecideProof(x_1073, x_14, x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_1074) == 0)
{
lean_object* x_1075; lean_object* x_1076; lean_object* x_1077; lean_object* x_1078; lean_object* x_1079; lean_object* x_1080; lean_object* x_1081; lean_object* x_1082; lean_object* x_1083; lean_object* x_1084; lean_object* x_1085; lean_object* x_1086; lean_object* x_1087; lean_object* x_1088; lean_object* x_1089; lean_object* x_1090; lean_object* x_1091; lean_object* x_1128; lean_object* x_1129; lean_object* x_1130; lean_object* x_1131; lean_object* x_1132; lean_object* x_1133; lean_object* x_1134; lean_object* x_1135; lean_object* x_1136; lean_object* x_1137; lean_object* x_1138; lean_object* x_1139; lean_object* x_1140; lean_object* x_1172; uint8_t x_1173; 
x_1075 = lean_ctor_get(x_1074, 0);
lean_inc(x_1075);
x_1076 = lean_ctor_get(x_1074, 1);
lean_inc(x_1076);
if (lean_is_exclusive(x_1074)) {
 lean_ctor_release(x_1074, 0);
 lean_ctor_release(x_1074, 1);
 x_1077 = x_1074;
} else {
 lean_dec_ref(x_1074);
 x_1077 = lean_box(0);
}
x_1078 = lean_array_fget(x_1036, x_47);
lean_dec(x_1036);
x_1079 = lean_mk_string_unchecked("pos_pow_of_pos", 14, 14);
x_1080 = l_Lean_Name_mkStr2(x_7, x_1079);
x_1081 = l_Lean_Expr_const___override(x_1080, x_985);
x_1082 = l_Lean_mkApp3(x_1081, x_1057, x_1078, x_1075);
x_1083 = lean_mk_string_unchecked("Lean", 4, 4);
x_1084 = lean_mk_string_unchecked("Omega", 5, 5);
x_1085 = lean_mk_string_unchecked("ofNat_pos_of_pos", 16, 16);
lean_inc(x_1012);
x_1086 = l_Lean_Name_mkStr4(x_1083, x_1084, x_1012, x_1085);
x_1087 = l_Lean_Expr_const___override(x_1086, x_985);
x_1088 = l_Lean_mkAppB(x_1087, x_1002, x_1082);
x_1128 = lean_unsigned_to_nat(8u);
x_1129 = lean_nat_shiftl(x_1128, x_991);
x_1130 = lean_nat_div(x_1129, x_915);
lean_dec(x_1129);
x_1131 = l_Nat_nextPowerOfTwo(x_1130);
lean_dec(x_1130);
x_1132 = lean_box(0);
x_1133 = lean_mk_array(x_1131, x_1132);
x_1134 = lean_mk_string_unchecked("emod_nonneg", 11, 11);
lean_inc(x_1012);
x_1135 = l_Lean_Name_mkStr2(x_1012, x_1134);
x_1136 = l_Lean_Expr_const___override(x_1135, x_985);
x_1137 = lean_mk_string_unchecked("ne_of_gt", 8, 8);
lean_inc(x_1012);
x_1138 = l_Lean_Name_mkStr2(x_1012, x_1137);
x_1139 = l_Lean_Expr_const___override(x_1138, x_985);
x_1172 = lean_nat_to_int(x_922);
x_1173 = lean_int_dec_le(x_1172, x_1172);
if (x_1173 == 0)
{
lean_object* x_1174; lean_object* x_1175; lean_object* x_1176; lean_object* x_1177; lean_object* x_1178; lean_object* x_1179; lean_object* x_1180; lean_object* x_1181; lean_object* x_1182; lean_object* x_1183; lean_object* x_1184; lean_object* x_1185; lean_object* x_1186; 
x_1174 = lean_mk_string_unchecked("Neg", 3, 3);
x_1175 = lean_mk_string_unchecked("neg", 3, 3);
x_1176 = l_Lean_Name_mkStr2(x_1174, x_1175);
x_1177 = l_Lean_Expr_const___override(x_1176, x_1065);
lean_inc(x_1012);
x_1178 = l_Lean_Name_mkStr1(x_1012);
x_1179 = l_Lean_Expr_const___override(x_1178, x_985);
x_1180 = lean_mk_string_unchecked("instNegInt", 10, 10);
lean_inc(x_1012);
x_1181 = l_Lean_Name_mkStr2(x_1012, x_1180);
x_1182 = l_Lean_Expr_const___override(x_1181, x_985);
x_1183 = lean_int_neg(x_1172);
lean_dec(x_1172);
x_1184 = l_Int_toNat(x_1183);
lean_dec(x_1183);
x_1185 = l_Lean_instToExprInt_mkNat(x_1184);
x_1186 = l_Lean_mkApp3(x_1177, x_1179, x_1182, x_1185);
x_1140 = x_1186;
goto block_1171;
}
else
{
lean_object* x_1187; lean_object* x_1188; 
lean_dec(x_1065);
x_1187 = l_Int_toNat(x_1172);
lean_dec(x_1172);
x_1188 = l_Lean_instToExprInt_mkNat(x_1187);
x_1140 = x_1188;
goto block_1171;
}
block_1127:
{
lean_object* x_1092; lean_object* x_1093; lean_object* x_1094; lean_object* x_1095; lean_object* x_1096; uint64_t x_1097; lean_object* x_1098; uint64_t x_1099; uint64_t x_1100; uint64_t x_1101; lean_object* x_1102; uint64_t x_1103; uint64_t x_1104; uint64_t x_1105; size_t x_1106; size_t x_1107; size_t x_1108; size_t x_1109; size_t x_1110; lean_object* x_1111; uint8_t x_1112; 
x_1092 = lean_mk_string_unchecked("emod_lt_of_pos", 14, 14);
x_1093 = l_Lean_Name_mkStr2(x_1012, x_1092);
x_1094 = l_Lean_Expr_const___override(x_1093, x_985);
x_1095 = l_Lean_mkApp3(x_1094, x_898, x_48, x_1088);
x_1096 = lean_array_get_size(x_1091);
x_1097 = l_Lean_Expr_hash(x_1095);
x_1098 = lean_unsigned_to_nat(32u);
x_1099 = lean_uint64_of_nat(x_1098);
x_1100 = lean_uint64_shift_right(x_1097, x_1099);
x_1101 = lean_uint64_xor(x_1097, x_1100);
x_1102 = lean_unsigned_to_nat(16u);
x_1103 = lean_uint64_of_nat(x_1102);
x_1104 = lean_uint64_shift_right(x_1101, x_1103);
x_1105 = lean_uint64_xor(x_1101, x_1104);
x_1106 = lean_uint64_to_usize(x_1105);
x_1107 = lean_usize_of_nat(x_1096);
lean_dec(x_1096);
x_1108 = lean_usize_of_nat(x_989);
x_1109 = lean_usize_sub(x_1107, x_1108);
x_1110 = lean_usize_land(x_1106, x_1109);
x_1111 = lean_array_uget(x_1091, x_1110);
x_1112 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectMVars_visit_spec__0___redArg(x_1095, x_1111);
if (x_1112 == 0)
{
lean_object* x_1113; lean_object* x_1114; lean_object* x_1115; lean_object* x_1116; lean_object* x_1117; lean_object* x_1118; lean_object* x_1119; uint8_t x_1120; 
lean_dec(x_1089);
x_1113 = lean_box(0);
x_1114 = lean_nat_add(x_1090, x_989);
lean_dec(x_1090);
x_1115 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1115, 0, x_1095);
lean_ctor_set(x_1115, 1, x_1113);
lean_ctor_set(x_1115, 2, x_1111);
x_1116 = lean_array_uset(x_1091, x_1110, x_1115);
x_1117 = lean_nat_shiftl(x_1114, x_991);
x_1118 = lean_nat_div(x_1117, x_915);
lean_dec(x_1117);
x_1119 = lean_array_get_size(x_1116);
x_1120 = lean_nat_dec_le(x_1118, x_1119);
lean_dec(x_1119);
lean_dec(x_1118);
if (x_1120 == 0)
{
lean_object* x_1121; lean_object* x_1122; lean_object* x_1123; 
x_1121 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectMVars_visit_spec__1(lean_box(0), x_1116);
x_1122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1122, 0, x_1114);
lean_ctor_set(x_1122, 1, x_1121);
if (lean_is_scalar(x_1077)) {
 x_1123 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1123 = x_1077;
}
lean_ctor_set(x_1123, 0, x_1122);
lean_ctor_set(x_1123, 1, x_1076);
return x_1123;
}
else
{
lean_object* x_1124; lean_object* x_1125; 
x_1124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1124, 0, x_1114);
lean_ctor_set(x_1124, 1, x_1116);
if (lean_is_scalar(x_1077)) {
 x_1125 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1125 = x_1077;
}
lean_ctor_set(x_1125, 0, x_1124);
lean_ctor_set(x_1125, 1, x_1076);
return x_1125;
}
}
else
{
lean_object* x_1126; 
lean_dec(x_1111);
lean_dec(x_1095);
lean_dec(x_1091);
lean_dec(x_1090);
if (lean_is_scalar(x_1077)) {
 x_1126 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1126 = x_1077;
}
lean_ctor_set(x_1126, 0, x_1089);
lean_ctor_set(x_1126, 1, x_1076);
return x_1126;
}
}
block_1171:
{
lean_object* x_1141; lean_object* x_1142; lean_object* x_1143; uint64_t x_1144; lean_object* x_1145; uint64_t x_1146; uint64_t x_1147; uint64_t x_1148; lean_object* x_1149; uint64_t x_1150; uint64_t x_1151; uint64_t x_1152; size_t x_1153; size_t x_1154; size_t x_1155; size_t x_1156; size_t x_1157; lean_object* x_1158; uint8_t x_1159; 
lean_inc(x_1088);
lean_inc(x_48);
x_1141 = l_Lean_mkApp3(x_1139, x_48, x_1140, x_1088);
lean_inc(x_48);
lean_inc(x_898);
x_1142 = l_Lean_mkApp3(x_1136, x_898, x_48, x_1141);
x_1143 = lean_array_get_size(x_1133);
x_1144 = l_Lean_Expr_hash(x_1142);
x_1145 = lean_unsigned_to_nat(32u);
x_1146 = lean_uint64_of_nat(x_1145);
x_1147 = lean_uint64_shift_right(x_1144, x_1146);
x_1148 = lean_uint64_xor(x_1144, x_1147);
x_1149 = lean_unsigned_to_nat(16u);
x_1150 = lean_uint64_of_nat(x_1149);
x_1151 = lean_uint64_shift_right(x_1148, x_1150);
x_1152 = lean_uint64_xor(x_1148, x_1151);
x_1153 = lean_uint64_to_usize(x_1152);
x_1154 = lean_usize_of_nat(x_1143);
lean_dec(x_1143);
x_1155 = lean_usize_of_nat(x_989);
x_1156 = lean_usize_sub(x_1154, x_1155);
x_1157 = lean_usize_land(x_1153, x_1156);
x_1158 = lean_array_uget(x_1133, x_1157);
x_1159 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectMVars_visit_spec__0___redArg(x_1142, x_1158);
if (x_1159 == 0)
{
lean_object* x_1160; lean_object* x_1161; lean_object* x_1162; lean_object* x_1163; lean_object* x_1164; lean_object* x_1165; uint8_t x_1166; 
x_1160 = lean_box(0);
x_1161 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1161, 0, x_1142);
lean_ctor_set(x_1161, 1, x_1160);
lean_ctor_set(x_1161, 2, x_1158);
x_1162 = lean_array_uset(x_1133, x_1157, x_1161);
x_1163 = lean_nat_shiftl(x_989, x_991);
x_1164 = lean_nat_div(x_1163, x_915);
lean_dec(x_1163);
x_1165 = lean_array_get_size(x_1162);
x_1166 = lean_nat_dec_le(x_1164, x_1165);
lean_dec(x_1165);
lean_dec(x_1164);
if (x_1166 == 0)
{
lean_object* x_1167; lean_object* x_1168; 
x_1167 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectMVars_visit_spec__1(lean_box(0), x_1162);
lean_inc(x_1167);
x_1168 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1168, 0, x_989);
lean_ctor_set(x_1168, 1, x_1167);
x_1089 = x_1168;
x_1090 = x_989;
x_1091 = x_1167;
goto block_1127;
}
else
{
lean_object* x_1169; 
lean_inc(x_1162);
x_1169 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1169, 0, x_989);
lean_ctor_set(x_1169, 1, x_1162);
x_1089 = x_1169;
x_1090 = x_989;
x_1091 = x_1162;
goto block_1127;
}
}
else
{
lean_object* x_1170; 
lean_dec(x_1158);
lean_dec(x_1142);
lean_inc(x_1133);
x_1170 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1170, 0, x_922);
lean_ctor_set(x_1170, 1, x_1133);
x_1089 = x_1170;
x_1090 = x_922;
x_1091 = x_1133;
goto block_1127;
}
}
}
else
{
lean_object* x_1189; lean_object* x_1190; lean_object* x_1191; lean_object* x_1192; 
lean_dec(x_1065);
lean_dec(x_1057);
lean_dec(x_1036);
lean_dec(x_1012);
lean_dec(x_1002);
lean_dec(x_898);
lean_dec(x_48);
lean_dec(x_7);
x_1189 = lean_ctor_get(x_1074, 0);
lean_inc(x_1189);
x_1190 = lean_ctor_get(x_1074, 1);
lean_inc(x_1190);
if (lean_is_exclusive(x_1074)) {
 lean_ctor_release(x_1074, 0);
 lean_ctor_release(x_1074, 1);
 x_1191 = x_1074;
} else {
 lean_dec_ref(x_1074);
 x_1191 = lean_box(0);
}
if (lean_is_scalar(x_1191)) {
 x_1192 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1192 = x_1191;
}
lean_ctor_set(x_1192, 0, x_1189);
lean_ctor_set(x_1192, 1, x_1190);
return x_1192;
}
}
else
{
lean_dec(x_1057);
lean_dec(x_1036);
lean_dec(x_1012);
lean_dec(x_1002);
lean_dec(x_898);
lean_dec(x_48);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_7);
x_992 = x_18;
goto block_1001;
}
}
}
}
}
}
case 1:
{
lean_object* x_1193; lean_object* x_1194; lean_object* x_1195; lean_object* x_1196; lean_object* x_1197; lean_object* x_1198; lean_object* x_1199; lean_object* x_1200; lean_object* x_1201; lean_object* x_1202; lean_object* x_1203; 
lean_dec(x_1012);
lean_dec(x_1002);
lean_dec(x_899);
x_1193 = lean_ctor_get(x_1022, 1);
lean_inc(x_1193);
if (lean_is_exclusive(x_1022)) {
 lean_ctor_release(x_1022, 0);
 lean_ctor_release(x_1022, 1);
 x_1194 = x_1022;
} else {
 lean_dec_ref(x_1022);
 x_1194 = lean_box(0);
}
x_1195 = lean_ctor_get(x_1023, 1);
lean_inc(x_1195);
lean_dec(x_1023);
x_1196 = lean_ctor_get(x_1028, 1);
lean_inc(x_1196);
lean_dec(x_1028);
x_1197 = lean_ctor_get(x_1035, 0);
lean_inc(x_1197);
x_1198 = lean_ctor_get(x_1035, 1);
lean_inc(x_1198);
lean_dec(x_1035);
x_1199 = l_Lean_Name_str___override(x_1197, x_1198);
x_1200 = l_Lean_Name_str___override(x_1199, x_1196);
x_1201 = l_Lean_Name_str___override(x_1200, x_1195);
if (lean_is_scalar(x_1194)) {
 x_1202 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1202 = x_1194;
}
lean_ctor_set(x_1202, 0, x_1201);
lean_ctor_set(x_1202, 1, x_1193);
x_1203 = l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__4(x_898, x_2, x_8, x_7, x_48, x_1202, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_1202);
return x_1203;
}
default: 
{
lean_object* x_1204; lean_object* x_1205; lean_object* x_1206; lean_object* x_1207; lean_object* x_1208; lean_object* x_1209; lean_object* x_1210; lean_object* x_1211; lean_object* x_1212; lean_object* x_1213; lean_object* x_1214; 
lean_dec(x_1012);
lean_dec(x_1002);
lean_dec(x_899);
x_1204 = lean_ctor_get(x_1022, 1);
lean_inc(x_1204);
if (lean_is_exclusive(x_1022)) {
 lean_ctor_release(x_1022, 0);
 lean_ctor_release(x_1022, 1);
 x_1205 = x_1022;
} else {
 lean_dec_ref(x_1022);
 x_1205 = lean_box(0);
}
x_1206 = lean_ctor_get(x_1023, 1);
lean_inc(x_1206);
lean_dec(x_1023);
x_1207 = lean_ctor_get(x_1028, 1);
lean_inc(x_1207);
lean_dec(x_1028);
x_1208 = lean_ctor_get(x_1035, 0);
lean_inc(x_1208);
x_1209 = lean_ctor_get(x_1035, 1);
lean_inc(x_1209);
lean_dec(x_1035);
x_1210 = l_Lean_Name_num___override(x_1208, x_1209);
x_1211 = l_Lean_Name_str___override(x_1210, x_1207);
x_1212 = l_Lean_Name_str___override(x_1211, x_1206);
if (lean_is_scalar(x_1205)) {
 x_1213 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1213 = x_1205;
}
lean_ctor_set(x_1213, 0, x_1212);
lean_ctor_set(x_1213, 1, x_1204);
x_1214 = l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__4(x_898, x_2, x_8, x_7, x_48, x_1213, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_1213);
return x_1214;
}
}
}
default: 
{
lean_object* x_1215; lean_object* x_1216; lean_object* x_1217; lean_object* x_1218; lean_object* x_1219; lean_object* x_1220; lean_object* x_1221; lean_object* x_1222; lean_object* x_1223; 
lean_dec(x_1012);
lean_dec(x_1002);
lean_dec(x_899);
x_1215 = lean_ctor_get(x_1022, 1);
lean_inc(x_1215);
if (lean_is_exclusive(x_1022)) {
 lean_ctor_release(x_1022, 0);
 lean_ctor_release(x_1022, 1);
 x_1216 = x_1022;
} else {
 lean_dec_ref(x_1022);
 x_1216 = lean_box(0);
}
x_1217 = lean_ctor_get(x_1023, 1);
lean_inc(x_1217);
lean_dec(x_1023);
x_1218 = lean_ctor_get(x_1028, 0);
lean_inc(x_1218);
x_1219 = lean_ctor_get(x_1028, 1);
lean_inc(x_1219);
lean_dec(x_1028);
x_1220 = l_Lean_Name_num___override(x_1218, x_1219);
x_1221 = l_Lean_Name_str___override(x_1220, x_1217);
if (lean_is_scalar(x_1216)) {
 x_1222 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1222 = x_1216;
}
lean_ctor_set(x_1222, 0, x_1221);
lean_ctor_set(x_1222, 1, x_1215);
x_1223 = l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__4(x_898, x_2, x_8, x_7, x_48, x_1222, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_1222);
return x_1223;
}
}
}
default: 
{
lean_object* x_1224; lean_object* x_1225; lean_object* x_1226; lean_object* x_1227; lean_object* x_1228; lean_object* x_1229; lean_object* x_1230; 
lean_dec(x_1012);
lean_dec(x_1002);
lean_dec(x_899);
x_1224 = lean_ctor_get(x_1022, 1);
lean_inc(x_1224);
if (lean_is_exclusive(x_1022)) {
 lean_ctor_release(x_1022, 0);
 lean_ctor_release(x_1022, 1);
 x_1225 = x_1022;
} else {
 lean_dec_ref(x_1022);
 x_1225 = lean_box(0);
}
x_1226 = lean_ctor_get(x_1023, 0);
lean_inc(x_1226);
x_1227 = lean_ctor_get(x_1023, 1);
lean_inc(x_1227);
lean_dec(x_1023);
x_1228 = l_Lean_Name_num___override(x_1226, x_1227);
if (lean_is_scalar(x_1225)) {
 x_1229 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1229 = x_1225;
}
lean_ctor_set(x_1229, 0, x_1228);
lean_ctor_set(x_1229, 1, x_1224);
x_1230 = l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__4(x_898, x_2, x_8, x_7, x_48, x_1229, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_1229);
return x_1230;
}
}
}
else
{
lean_object* x_1231; lean_object* x_1232; lean_object* x_1233; lean_object* x_1234; lean_object* x_1235; lean_object* x_1236; lean_object* x_1237; lean_object* x_1238; 
lean_dec(x_899);
lean_dec(x_898);
lean_dec(x_48);
lean_dec(x_8);
lean_dec(x_7);
x_1231 = l_Lean_Name_str___override(x_2, x_1012);
x_1232 = l_Lean_Expr_const___override(x_1231, x_985);
x_1233 = lean_array_push(x_1003, x_1232);
x_1234 = lean_array_push(x_1233, x_990);
x_1235 = lean_array_push(x_1234, x_1002);
x_1236 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1236, 0, x_987);
lean_ctor_set(x_1236, 1, x_1235);
x_1237 = lean_box(x_12);
x_1238 = lean_apply_11(x_6, x_1236, x_9, x_10, x_11, x_1237, x_13, x_14, x_15, x_16, x_17, x_18);
return x_1238;
}
}
}
case 1:
{
lean_object* x_1239; lean_object* x_1240; lean_object* x_1241; lean_object* x_1242; lean_object* x_1243; lean_object* x_1244; lean_object* x_1245; lean_object* x_1246; lean_object* x_1247; lean_object* x_1248; lean_object* x_1249; lean_object* x_1250; 
lean_dec(x_899);
lean_dec(x_898);
lean_dec(x_48);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_1239 = lean_ctor_get(x_984, 1);
lean_inc(x_1239);
lean_dec(x_984);
x_1240 = lean_ctor_get(x_1010, 0);
lean_inc(x_1240);
x_1241 = lean_ctor_get(x_1010, 1);
lean_inc(x_1241);
lean_dec(x_1010);
x_1242 = l_Lean_Name_str___override(x_1240, x_1241);
x_1243 = l_Lean_Name_str___override(x_1242, x_1239);
x_1244 = l_Lean_Expr_const___override(x_1243, x_985);
x_1245 = lean_array_push(x_1003, x_1244);
x_1246 = lean_array_push(x_1245, x_990);
x_1247 = lean_array_push(x_1246, x_1002);
x_1248 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1248, 0, x_987);
lean_ctor_set(x_1248, 1, x_1247);
x_1249 = lean_box(x_12);
x_1250 = lean_apply_11(x_6, x_1248, x_9, x_10, x_11, x_1249, x_13, x_14, x_15, x_16, x_17, x_18);
return x_1250;
}
default: 
{
lean_object* x_1251; lean_object* x_1252; lean_object* x_1253; lean_object* x_1254; lean_object* x_1255; lean_object* x_1256; lean_object* x_1257; lean_object* x_1258; lean_object* x_1259; lean_object* x_1260; lean_object* x_1261; lean_object* x_1262; 
lean_dec(x_899);
lean_dec(x_898);
lean_dec(x_48);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_1251 = lean_ctor_get(x_984, 1);
lean_inc(x_1251);
lean_dec(x_984);
x_1252 = lean_ctor_get(x_1010, 0);
lean_inc(x_1252);
x_1253 = lean_ctor_get(x_1010, 1);
lean_inc(x_1253);
lean_dec(x_1010);
x_1254 = l_Lean_Name_num___override(x_1252, x_1253);
x_1255 = l_Lean_Name_str___override(x_1254, x_1251);
x_1256 = l_Lean_Expr_const___override(x_1255, x_985);
x_1257 = lean_array_push(x_1003, x_1256);
x_1258 = lean_array_push(x_1257, x_990);
x_1259 = lean_array_push(x_1258, x_1002);
x_1260 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1260, 0, x_987);
lean_ctor_set(x_1260, 1, x_1259);
x_1261 = lean_box(x_12);
x_1262 = lean_apply_11(x_6, x_1260, x_9, x_10, x_11, x_1261, x_13, x_14, x_15, x_16, x_17, x_18);
return x_1262;
}
}
}
default: 
{
lean_object* x_1263; lean_object* x_1264; lean_object* x_1265; lean_object* x_1266; lean_object* x_1267; lean_object* x_1268; lean_object* x_1269; lean_object* x_1270; lean_object* x_1271; lean_object* x_1272; 
lean_dec(x_1004);
lean_dec(x_899);
lean_dec(x_898);
lean_dec(x_48);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_1263 = lean_ctor_get(x_984, 0);
lean_inc(x_1263);
x_1264 = lean_ctor_get(x_984, 1);
lean_inc(x_1264);
lean_dec(x_984);
x_1265 = l_Lean_Name_num___override(x_1263, x_1264);
x_1266 = l_Lean_Expr_const___override(x_1265, x_985);
x_1267 = lean_array_push(x_1003, x_1266);
x_1268 = lean_array_push(x_1267, x_990);
x_1269 = lean_array_push(x_1268, x_1002);
x_1270 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1270, 0, x_987);
lean_ctor_set(x_1270, 1, x_1269);
x_1271 = lean_box(x_12);
x_1272 = lean_apply_11(x_6, x_1270, x_9, x_10, x_11, x_1271, x_13, x_14, x_15, x_16, x_17, x_18);
return x_1272;
}
}
block_1001:
{
lean_object* x_993; lean_object* x_994; lean_object* x_995; lean_object* x_996; lean_object* x_997; lean_object* x_998; lean_object* x_999; lean_object* x_1000; 
x_993 = lean_unsigned_to_nat(8u);
x_994 = lean_nat_shiftl(x_993, x_991);
x_995 = lean_nat_div(x_994, x_915);
lean_dec(x_994);
x_996 = l_Nat_nextPowerOfTwo(x_995);
lean_dec(x_995);
x_997 = lean_box(0);
x_998 = lean_mk_array(x_996, x_997);
x_999 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_999, 0, x_922);
lean_ctor_set(x_999, 1, x_998);
x_1000 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1000, 0, x_999);
lean_ctor_set(x_1000, 1, x_992);
return x_1000;
}
}
case 5:
{
lean_object* x_1273; lean_object* x_1274; lean_object* x_1275; lean_object* x_1276; lean_object* x_1277; lean_object* x_1278; lean_object* x_1279; lean_object* x_1280; lean_object* x_1281; lean_object* x_1282; lean_object* x_1283; lean_object* x_1284; lean_object* x_1285; lean_object* x_1286; lean_object* x_1287; lean_object* x_1288; 
lean_dec(x_899);
lean_dec(x_898);
lean_dec(x_48);
lean_dec(x_8);
x_1273 = lean_ctor_get(x_923, 0);
lean_inc(x_1273);
x_1274 = lean_ctor_get(x_923, 1);
lean_inc(x_1274);
lean_dec(x_923);
x_1275 = l_Lean_Name_str___override(x_2, x_7);
x_1276 = l_Lean_Name_str___override(x_1275, x_907);
x_1277 = l_Lean_Expr_app___override(x_1273, x_1274);
x_1278 = lean_unsigned_to_nat(1u);
x_1279 = lean_array_fget(x_894, x_1278);
x_1280 = lean_unsigned_to_nat(2u);
x_1281 = lean_array_fget(x_894, x_1280);
lean_dec(x_894);
x_1282 = lean_mk_empty_array_with_capacity(x_915);
x_1283 = lean_array_push(x_1282, x_1277);
x_1284 = lean_array_push(x_1283, x_1279);
x_1285 = lean_array_push(x_1284, x_1281);
x_1286 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1286, 0, x_1276);
lean_ctor_set(x_1286, 1, x_1285);
x_1287 = lean_box(x_12);
x_1288 = lean_apply_11(x_6, x_1286, x_9, x_10, x_11, x_1287, x_13, x_14, x_15, x_16, x_17, x_18);
return x_1288;
}
case 6:
{
lean_object* x_1289; lean_object* x_1290; lean_object* x_1291; uint8_t x_1292; lean_object* x_1293; lean_object* x_1294; lean_object* x_1295; lean_object* x_1296; lean_object* x_1297; lean_object* x_1298; lean_object* x_1299; lean_object* x_1300; lean_object* x_1301; lean_object* x_1302; lean_object* x_1303; lean_object* x_1304; lean_object* x_1305; lean_object* x_1306; 
lean_dec(x_899);
lean_dec(x_898);
lean_dec(x_48);
lean_dec(x_8);
x_1289 = lean_ctor_get(x_923, 0);
lean_inc(x_1289);
x_1290 = lean_ctor_get(x_923, 1);
lean_inc(x_1290);
x_1291 = lean_ctor_get(x_923, 2);
lean_inc(x_1291);
x_1292 = lean_ctor_get_uint8(x_923, sizeof(void*)*3 + 8);
lean_dec(x_923);
x_1293 = l_Lean_Name_str___override(x_2, x_7);
x_1294 = l_Lean_Name_str___override(x_1293, x_907);
x_1295 = l_Lean_Expr_lam___override(x_1289, x_1290, x_1291, x_1292);
x_1296 = lean_unsigned_to_nat(1u);
x_1297 = lean_array_fget(x_894, x_1296);
x_1298 = lean_unsigned_to_nat(2u);
x_1299 = lean_array_fget(x_894, x_1298);
lean_dec(x_894);
x_1300 = lean_mk_empty_array_with_capacity(x_915);
x_1301 = lean_array_push(x_1300, x_1295);
x_1302 = lean_array_push(x_1301, x_1297);
x_1303 = lean_array_push(x_1302, x_1299);
x_1304 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1304, 0, x_1294);
lean_ctor_set(x_1304, 1, x_1303);
x_1305 = lean_box(x_12);
x_1306 = lean_apply_11(x_6, x_1304, x_9, x_10, x_11, x_1305, x_13, x_14, x_15, x_16, x_17, x_18);
return x_1306;
}
case 7:
{
lean_object* x_1307; lean_object* x_1308; lean_object* x_1309; uint8_t x_1310; lean_object* x_1311; lean_object* x_1312; lean_object* x_1313; lean_object* x_1314; lean_object* x_1315; lean_object* x_1316; lean_object* x_1317; lean_object* x_1318; lean_object* x_1319; lean_object* x_1320; lean_object* x_1321; lean_object* x_1322; lean_object* x_1323; lean_object* x_1324; 
lean_dec(x_899);
lean_dec(x_898);
lean_dec(x_48);
lean_dec(x_8);
x_1307 = lean_ctor_get(x_923, 0);
lean_inc(x_1307);
x_1308 = lean_ctor_get(x_923, 1);
lean_inc(x_1308);
x_1309 = lean_ctor_get(x_923, 2);
lean_inc(x_1309);
x_1310 = lean_ctor_get_uint8(x_923, sizeof(void*)*3 + 8);
lean_dec(x_923);
x_1311 = l_Lean_Name_str___override(x_2, x_7);
x_1312 = l_Lean_Name_str___override(x_1311, x_907);
x_1313 = l_Lean_Expr_forallE___override(x_1307, x_1308, x_1309, x_1310);
x_1314 = lean_unsigned_to_nat(1u);
x_1315 = lean_array_fget(x_894, x_1314);
x_1316 = lean_unsigned_to_nat(2u);
x_1317 = lean_array_fget(x_894, x_1316);
lean_dec(x_894);
x_1318 = lean_mk_empty_array_with_capacity(x_915);
x_1319 = lean_array_push(x_1318, x_1313);
x_1320 = lean_array_push(x_1319, x_1315);
x_1321 = lean_array_push(x_1320, x_1317);
x_1322 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1322, 0, x_1312);
lean_ctor_set(x_1322, 1, x_1321);
x_1323 = lean_box(x_12);
x_1324 = lean_apply_11(x_6, x_1322, x_9, x_10, x_11, x_1323, x_13, x_14, x_15, x_16, x_17, x_18);
return x_1324;
}
case 8:
{
lean_object* x_1325; lean_object* x_1326; lean_object* x_1327; lean_object* x_1328; uint8_t x_1329; lean_object* x_1330; lean_object* x_1331; lean_object* x_1332; lean_object* x_1333; lean_object* x_1334; lean_object* x_1335; lean_object* x_1336; lean_object* x_1337; lean_object* x_1338; lean_object* x_1339; lean_object* x_1340; lean_object* x_1341; lean_object* x_1342; lean_object* x_1343; 
lean_dec(x_899);
lean_dec(x_898);
lean_dec(x_48);
lean_dec(x_8);
x_1325 = lean_ctor_get(x_923, 0);
lean_inc(x_1325);
x_1326 = lean_ctor_get(x_923, 1);
lean_inc(x_1326);
x_1327 = lean_ctor_get(x_923, 2);
lean_inc(x_1327);
x_1328 = lean_ctor_get(x_923, 3);
lean_inc(x_1328);
x_1329 = lean_ctor_get_uint8(x_923, sizeof(void*)*4 + 8);
lean_dec(x_923);
x_1330 = l_Lean_Name_str___override(x_2, x_7);
x_1331 = l_Lean_Name_str___override(x_1330, x_907);
x_1332 = l_Lean_Expr_letE___override(x_1325, x_1326, x_1327, x_1328, x_1329);
x_1333 = lean_unsigned_to_nat(1u);
x_1334 = lean_array_fget(x_894, x_1333);
x_1335 = lean_unsigned_to_nat(2u);
x_1336 = lean_array_fget(x_894, x_1335);
lean_dec(x_894);
x_1337 = lean_mk_empty_array_with_capacity(x_915);
x_1338 = lean_array_push(x_1337, x_1332);
x_1339 = lean_array_push(x_1338, x_1334);
x_1340 = lean_array_push(x_1339, x_1336);
x_1341 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1341, 0, x_1331);
lean_ctor_set(x_1341, 1, x_1340);
x_1342 = lean_box(x_12);
x_1343 = lean_apply_11(x_6, x_1341, x_9, x_10, x_11, x_1342, x_13, x_14, x_15, x_16, x_17, x_18);
return x_1343;
}
case 9:
{
lean_object* x_1344; lean_object* x_1345; lean_object* x_1346; lean_object* x_1347; lean_object* x_1348; lean_object* x_1349; lean_object* x_1350; lean_object* x_1351; lean_object* x_1352; lean_object* x_1353; lean_object* x_1354; lean_object* x_1355; lean_object* x_1356; lean_object* x_1357; lean_object* x_1358; 
lean_dec(x_899);
lean_dec(x_898);
lean_dec(x_48);
lean_dec(x_8);
x_1344 = lean_ctor_get(x_923, 0);
lean_inc(x_1344);
lean_dec(x_923);
x_1345 = l_Lean_Name_str___override(x_2, x_7);
x_1346 = l_Lean_Name_str___override(x_1345, x_907);
x_1347 = l_Lean_Expr_lit___override(x_1344);
x_1348 = lean_unsigned_to_nat(1u);
x_1349 = lean_array_fget(x_894, x_1348);
x_1350 = lean_unsigned_to_nat(2u);
x_1351 = lean_array_fget(x_894, x_1350);
lean_dec(x_894);
x_1352 = lean_mk_empty_array_with_capacity(x_915);
x_1353 = lean_array_push(x_1352, x_1347);
x_1354 = lean_array_push(x_1353, x_1349);
x_1355 = lean_array_push(x_1354, x_1351);
x_1356 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1356, 0, x_1346);
lean_ctor_set(x_1356, 1, x_1355);
x_1357 = lean_box(x_12);
x_1358 = lean_apply_11(x_6, x_1356, x_9, x_10, x_11, x_1357, x_13, x_14, x_15, x_16, x_17, x_18);
return x_1358;
}
case 10:
{
lean_object* x_1359; lean_object* x_1360; lean_object* x_1361; lean_object* x_1362; lean_object* x_1363; lean_object* x_1364; lean_object* x_1365; lean_object* x_1366; lean_object* x_1367; lean_object* x_1368; lean_object* x_1369; lean_object* x_1370; lean_object* x_1371; lean_object* x_1372; lean_object* x_1373; lean_object* x_1374; 
lean_dec(x_899);
lean_dec(x_898);
lean_dec(x_48);
lean_dec(x_8);
x_1359 = lean_ctor_get(x_923, 0);
lean_inc(x_1359);
x_1360 = lean_ctor_get(x_923, 1);
lean_inc(x_1360);
lean_dec(x_923);
x_1361 = l_Lean_Name_str___override(x_2, x_7);
x_1362 = l_Lean_Name_str___override(x_1361, x_907);
x_1363 = l_Lean_Expr_mdata___override(x_1359, x_1360);
x_1364 = lean_unsigned_to_nat(1u);
x_1365 = lean_array_fget(x_894, x_1364);
x_1366 = lean_unsigned_to_nat(2u);
x_1367 = lean_array_fget(x_894, x_1366);
lean_dec(x_894);
x_1368 = lean_mk_empty_array_with_capacity(x_915);
x_1369 = lean_array_push(x_1368, x_1363);
x_1370 = lean_array_push(x_1369, x_1365);
x_1371 = lean_array_push(x_1370, x_1367);
x_1372 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1372, 0, x_1362);
lean_ctor_set(x_1372, 1, x_1371);
x_1373 = lean_box(x_12);
x_1374 = lean_apply_11(x_6, x_1372, x_9, x_10, x_11, x_1373, x_13, x_14, x_15, x_16, x_17, x_18);
return x_1374;
}
default: 
{
lean_object* x_1375; lean_object* x_1376; lean_object* x_1377; lean_object* x_1378; lean_object* x_1379; lean_object* x_1380; lean_object* x_1381; lean_object* x_1382; lean_object* x_1383; lean_object* x_1384; lean_object* x_1385; lean_object* x_1386; lean_object* x_1387; lean_object* x_1388; lean_object* x_1389; lean_object* x_1390; lean_object* x_1391; 
lean_dec(x_899);
lean_dec(x_898);
lean_dec(x_48);
lean_dec(x_8);
x_1375 = lean_ctor_get(x_923, 0);
lean_inc(x_1375);
x_1376 = lean_ctor_get(x_923, 1);
lean_inc(x_1376);
x_1377 = lean_ctor_get(x_923, 2);
lean_inc(x_1377);
lean_dec(x_923);
x_1378 = l_Lean_Name_str___override(x_2, x_7);
x_1379 = l_Lean_Name_str___override(x_1378, x_907);
x_1380 = l_Lean_Expr_proj___override(x_1375, x_1376, x_1377);
x_1381 = lean_unsigned_to_nat(1u);
x_1382 = lean_array_fget(x_894, x_1381);
x_1383 = lean_unsigned_to_nat(2u);
x_1384 = lean_array_fget(x_894, x_1383);
lean_dec(x_894);
x_1385 = lean_mk_empty_array_with_capacity(x_915);
x_1386 = lean_array_push(x_1385, x_1380);
x_1387 = lean_array_push(x_1386, x_1382);
x_1388 = lean_array_push(x_1387, x_1384);
x_1389 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1389, 0, x_1379);
lean_ctor_set(x_1389, 1, x_1388);
x_1390 = lean_box(x_12);
x_1391 = lean_apply_11(x_6, x_1389, x_9, x_10, x_11, x_1390, x_13, x_14, x_15, x_16, x_17, x_18);
return x_1391;
}
}
}
}
}
}
else
{
lean_object* x_1392; uint8_t x_1393; 
lean_dec(x_896);
lean_dec(x_8);
lean_dec(x_7);
x_1392 = lean_mk_string_unchecked("hPow", 4, 4);
x_1393 = lean_string_dec_eq(x_895, x_1392);
if (x_1393 == 0)
{
lean_object* x_1394; lean_object* x_1395; lean_object* x_1396; lean_object* x_1397; lean_object* x_1398; 
lean_dec(x_1392);
lean_dec(x_898);
lean_dec(x_48);
x_1394 = l_Lean_Name_str___override(x_2, x_899);
x_1395 = l_Lean_Name_str___override(x_1394, x_895);
x_1396 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1396, 0, x_1395);
lean_ctor_set(x_1396, 1, x_894);
x_1397 = lean_box(x_12);
x_1398 = lean_apply_11(x_6, x_1396, x_9, x_10, x_11, x_1397, x_13, x_14, x_15, x_16, x_17, x_18);
return x_1398;
}
else
{
lean_object* x_1399; uint8_t x_1400; 
lean_dec(x_895);
x_1399 = lean_array_get_size(x_894);
x_1400 = lean_nat_dec_eq(x_1399, x_40);
lean_dec(x_1399);
if (x_1400 == 0)
{
lean_object* x_1401; lean_object* x_1402; lean_object* x_1403; lean_object* x_1404; lean_object* x_1405; 
lean_dec(x_898);
lean_dec(x_48);
x_1401 = l_Lean_Name_str___override(x_2, x_899);
x_1402 = l_Lean_Name_str___override(x_1401, x_1392);
x_1403 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1403, 0, x_1402);
lean_ctor_set(x_1403, 1, x_894);
x_1404 = lean_box(x_12);
x_1405 = lean_apply_11(x_6, x_1403, x_9, x_10, x_11, x_1404, x_13, x_14, x_15, x_16, x_17, x_18);
return x_1405;
}
else
{
lean_object* x_1406; lean_object* x_1407; 
lean_dec(x_1392);
lean_dec(x_899);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_2);
x_1406 = lean_array_fget(x_894, x_897);
lean_inc(x_1406);
x_1407 = l_Lean_Elab_Tactic_Omega_natCast_x3f(x_1406);
if (lean_obj_tag(x_1407) == 0)
{
lean_dec(x_1406);
lean_dec(x_898);
lean_dec(x_894);
lean_dec(x_48);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
x_19 = x_18;
goto block_31;
}
else
{
lean_object* x_1408; lean_object* x_1409; uint8_t x_1410; 
x_1408 = lean_ctor_get(x_1407, 0);
lean_inc(x_1408);
lean_dec(x_1407);
x_1409 = lean_unsigned_to_nat(0u);
x_1410 = lean_nat_dec_eq(x_1408, x_1409);
lean_dec(x_1408);
if (x_1410 == 0)
{
lean_object* x_1411; lean_object* x_1412; lean_object* x_1413; lean_object* x_1414; lean_object* x_1415; lean_object* x_1416; lean_object* x_1417; lean_object* x_1418; lean_object* x_1419; lean_object* x_1420; lean_object* x_1421; lean_object* x_1422; lean_object* x_1423; lean_object* x_1424; lean_object* x_1464; lean_object* x_1465; lean_object* x_1466; lean_object* x_1467; lean_object* x_1468; lean_object* x_1469; lean_object* x_1530; uint8_t x_1531; 
x_1411 = lean_array_fget(x_894, x_47);
lean_dec(x_894);
x_1412 = lean_mk_string_unchecked("LT", 2, 2);
x_1413 = lean_mk_string_unchecked("lt", 2, 2);
x_1414 = l_Lean_Name_mkStr2(x_1412, x_1413);
x_1415 = l_Lean_Level_ofNat(x_1409);
x_1416 = lean_box(0);
x_1417 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1417, 0, x_1415);
lean_ctor_set(x_1417, 1, x_1416);
lean_inc(x_1417);
x_1418 = l_Lean_Expr_const___override(x_1414, x_1417);
x_1419 = lean_mk_string_unchecked("Int", 3, 3);
lean_inc(x_1419);
x_1464 = l_Lean_Name_mkStr1(x_1419);
x_1465 = l_Lean_Expr_const___override(x_1464, x_1416);
x_1466 = lean_mk_string_unchecked("instLTInt", 9, 9);
lean_inc(x_1419);
x_1467 = l_Lean_Name_mkStr2(x_1419, x_1466);
x_1468 = l_Lean_Expr_const___override(x_1467, x_1416);
x_1530 = lean_nat_to_int(x_1409);
x_1531 = lean_int_dec_le(x_1530, x_1530);
if (x_1531 == 0)
{
lean_object* x_1532; lean_object* x_1533; lean_object* x_1534; lean_object* x_1535; lean_object* x_1536; lean_object* x_1537; lean_object* x_1538; lean_object* x_1539; lean_object* x_1540; lean_object* x_1541; lean_object* x_1542; 
x_1532 = lean_mk_string_unchecked("Neg", 3, 3);
x_1533 = lean_mk_string_unchecked("neg", 3, 3);
x_1534 = l_Lean_Name_mkStr2(x_1532, x_1533);
x_1535 = l_Lean_Expr_const___override(x_1534, x_1417);
x_1536 = lean_mk_string_unchecked("instNegInt", 10, 10);
lean_inc(x_1419);
x_1537 = l_Lean_Name_mkStr2(x_1419, x_1536);
x_1538 = l_Lean_Expr_const___override(x_1537, x_1416);
x_1539 = lean_int_neg(x_1530);
lean_dec(x_1530);
x_1540 = l_Int_toNat(x_1539);
lean_dec(x_1539);
x_1541 = l_Lean_instToExprInt_mkNat(x_1540);
lean_inc(x_1465);
x_1542 = l_Lean_mkApp3(x_1535, x_1465, x_1538, x_1541);
x_1469 = x_1542;
goto block_1529;
}
else
{
lean_object* x_1543; lean_object* x_1544; 
lean_dec(x_1417);
x_1543 = l_Int_toNat(x_1530);
lean_dec(x_1530);
x_1544 = l_Lean_instToExprInt_mkNat(x_1543);
x_1469 = x_1544;
goto block_1529;
}
block_1463:
{
lean_object* x_1425; lean_object* x_1426; lean_object* x_1427; lean_object* x_1428; lean_object* x_1429; uint64_t x_1430; lean_object* x_1431; uint64_t x_1432; uint64_t x_1433; uint64_t x_1434; lean_object* x_1435; uint64_t x_1436; uint64_t x_1437; uint64_t x_1438; size_t x_1439; size_t x_1440; lean_object* x_1441; size_t x_1442; size_t x_1443; size_t x_1444; lean_object* x_1445; uint8_t x_1446; 
x_1425 = lean_mk_string_unchecked("emod_lt_of_pos", 14, 14);
x_1426 = l_Lean_Name_mkStr2(x_1419, x_1425);
x_1427 = l_Lean_Expr_const___override(x_1426, x_1416);
x_1428 = l_Lean_mkApp3(x_1427, x_898, x_48, x_1421);
x_1429 = lean_array_get_size(x_1424);
x_1430 = l_Lean_Expr_hash(x_1428);
x_1431 = lean_unsigned_to_nat(32u);
x_1432 = lean_uint64_of_nat(x_1431);
x_1433 = lean_uint64_shift_right(x_1430, x_1432);
x_1434 = lean_uint64_xor(x_1430, x_1433);
x_1435 = lean_unsigned_to_nat(16u);
x_1436 = lean_uint64_of_nat(x_1435);
x_1437 = lean_uint64_shift_right(x_1434, x_1436);
x_1438 = lean_uint64_xor(x_1434, x_1437);
x_1439 = lean_uint64_to_usize(x_1438);
x_1440 = lean_usize_of_nat(x_1429);
lean_dec(x_1429);
x_1441 = lean_unsigned_to_nat(1u);
x_1442 = lean_usize_of_nat(x_1441);
x_1443 = lean_usize_sub(x_1440, x_1442);
x_1444 = lean_usize_land(x_1439, x_1443);
x_1445 = lean_array_uget(x_1424, x_1444);
x_1446 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectMVars_visit_spec__0___redArg(x_1428, x_1445);
if (x_1446 == 0)
{
lean_object* x_1447; lean_object* x_1448; lean_object* x_1449; lean_object* x_1450; lean_object* x_1451; lean_object* x_1452; lean_object* x_1453; lean_object* x_1454; lean_object* x_1455; uint8_t x_1456; 
lean_dec(x_1422);
x_1447 = lean_box(0);
x_1448 = lean_nat_add(x_1423, x_1441);
lean_dec(x_1423);
x_1449 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1449, 0, x_1428);
lean_ctor_set(x_1449, 1, x_1447);
lean_ctor_set(x_1449, 2, x_1445);
x_1450 = lean_array_uset(x_1424, x_1444, x_1449);
x_1451 = lean_unsigned_to_nat(2u);
x_1452 = lean_nat_shiftl(x_1448, x_1451);
x_1453 = lean_unsigned_to_nat(3u);
x_1454 = lean_nat_div(x_1452, x_1453);
lean_dec(x_1452);
x_1455 = lean_array_get_size(x_1450);
x_1456 = lean_nat_dec_le(x_1454, x_1455);
lean_dec(x_1455);
lean_dec(x_1454);
if (x_1456 == 0)
{
lean_object* x_1457; lean_object* x_1458; lean_object* x_1459; 
x_1457 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectMVars_visit_spec__1(lean_box(0), x_1450);
x_1458 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1458, 0, x_1448);
lean_ctor_set(x_1458, 1, x_1457);
x_1459 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1459, 0, x_1458);
lean_ctor_set(x_1459, 1, x_1420);
return x_1459;
}
else
{
lean_object* x_1460; lean_object* x_1461; 
x_1460 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1460, 0, x_1448);
lean_ctor_set(x_1460, 1, x_1450);
x_1461 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1461, 0, x_1460);
lean_ctor_set(x_1461, 1, x_1420);
return x_1461;
}
}
else
{
lean_object* x_1462; 
lean_dec(x_1445);
lean_dec(x_1428);
lean_dec(x_1424);
lean_dec(x_1423);
x_1462 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1462, 0, x_1422);
lean_ctor_set(x_1462, 1, x_1420);
return x_1462;
}
}
block_1529:
{
lean_object* x_1470; lean_object* x_1471; 
lean_inc(x_1406);
lean_inc(x_1469);
x_1470 = l_Lean_mkApp4(x_1418, x_1465, x_1468, x_1469, x_1406);
x_1471 = l_Lean_Meta_mkDecideProof(x_1470, x_14, x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_1471) == 0)
{
lean_object* x_1472; lean_object* x_1473; lean_object* x_1474; lean_object* x_1475; lean_object* x_1476; lean_object* x_1477; lean_object* x_1478; lean_object* x_1479; lean_object* x_1480; lean_object* x_1481; lean_object* x_1482; lean_object* x_1483; lean_object* x_1484; lean_object* x_1485; lean_object* x_1486; lean_object* x_1487; lean_object* x_1488; lean_object* x_1489; lean_object* x_1490; lean_object* x_1491; lean_object* x_1492; lean_object* x_1493; lean_object* x_1494; lean_object* x_1495; lean_object* x_1496; uint64_t x_1497; lean_object* x_1498; uint64_t x_1499; uint64_t x_1500; uint64_t x_1501; lean_object* x_1502; uint64_t x_1503; uint64_t x_1504; uint64_t x_1505; size_t x_1506; size_t x_1507; lean_object* x_1508; size_t x_1509; size_t x_1510; size_t x_1511; lean_object* x_1512; uint8_t x_1513; 
x_1472 = lean_ctor_get(x_1471, 0);
lean_inc(x_1472);
x_1473 = lean_ctor_get(x_1471, 1);
lean_inc(x_1473);
lean_dec(x_1471);
x_1474 = lean_mk_string_unchecked("Lean", 4, 4);
x_1475 = lean_mk_string_unchecked("Omega", 5, 5);
x_1476 = lean_mk_string_unchecked("pos_pow_of_pos", 14, 14);
lean_inc(x_1419);
x_1477 = l_Lean_Name_mkStr4(x_1474, x_1475, x_1419, x_1476);
x_1478 = l_Lean_Expr_const___override(x_1477, x_1416);
x_1479 = l_Lean_mkApp3(x_1478, x_1406, x_1411, x_1472);
x_1480 = lean_unsigned_to_nat(8u);
x_1481 = lean_unsigned_to_nat(2u);
x_1482 = lean_nat_shiftl(x_1480, x_1481);
x_1483 = lean_unsigned_to_nat(3u);
x_1484 = lean_nat_div(x_1482, x_1483);
lean_dec(x_1482);
x_1485 = l_Nat_nextPowerOfTwo(x_1484);
lean_dec(x_1484);
x_1486 = lean_box(0);
x_1487 = lean_mk_array(x_1485, x_1486);
x_1488 = lean_mk_string_unchecked("emod_nonneg", 11, 11);
lean_inc(x_1419);
x_1489 = l_Lean_Name_mkStr2(x_1419, x_1488);
x_1490 = l_Lean_Expr_const___override(x_1489, x_1416);
x_1491 = lean_mk_string_unchecked("ne_of_gt", 8, 8);
lean_inc(x_1419);
x_1492 = l_Lean_Name_mkStr2(x_1419, x_1491);
x_1493 = l_Lean_Expr_const___override(x_1492, x_1416);
lean_inc(x_1479);
lean_inc(x_48);
x_1494 = l_Lean_mkApp3(x_1493, x_48, x_1469, x_1479);
lean_inc(x_48);
lean_inc(x_898);
x_1495 = l_Lean_mkApp3(x_1490, x_898, x_48, x_1494);
x_1496 = lean_array_get_size(x_1487);
x_1497 = l_Lean_Expr_hash(x_1495);
x_1498 = lean_unsigned_to_nat(32u);
x_1499 = lean_uint64_of_nat(x_1498);
x_1500 = lean_uint64_shift_right(x_1497, x_1499);
x_1501 = lean_uint64_xor(x_1497, x_1500);
x_1502 = lean_unsigned_to_nat(16u);
x_1503 = lean_uint64_of_nat(x_1502);
x_1504 = lean_uint64_shift_right(x_1501, x_1503);
x_1505 = lean_uint64_xor(x_1501, x_1504);
x_1506 = lean_uint64_to_usize(x_1505);
x_1507 = lean_usize_of_nat(x_1496);
lean_dec(x_1496);
x_1508 = lean_unsigned_to_nat(1u);
x_1509 = lean_usize_of_nat(x_1508);
x_1510 = lean_usize_sub(x_1507, x_1509);
x_1511 = lean_usize_land(x_1506, x_1510);
x_1512 = lean_array_uget(x_1487, x_1511);
x_1513 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectMVars_visit_spec__0___redArg(x_1495, x_1512);
if (x_1513 == 0)
{
lean_object* x_1514; lean_object* x_1515; lean_object* x_1516; lean_object* x_1517; lean_object* x_1518; lean_object* x_1519; uint8_t x_1520; 
x_1514 = lean_box(0);
x_1515 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1515, 0, x_1495);
lean_ctor_set(x_1515, 1, x_1514);
lean_ctor_set(x_1515, 2, x_1512);
x_1516 = lean_array_uset(x_1487, x_1511, x_1515);
x_1517 = lean_nat_shiftl(x_1508, x_1481);
x_1518 = lean_nat_div(x_1517, x_1483);
lean_dec(x_1517);
x_1519 = lean_array_get_size(x_1516);
x_1520 = lean_nat_dec_le(x_1518, x_1519);
lean_dec(x_1519);
lean_dec(x_1518);
if (x_1520 == 0)
{
lean_object* x_1521; lean_object* x_1522; 
x_1521 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectMVars_visit_spec__1(lean_box(0), x_1516);
lean_inc(x_1521);
x_1522 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1522, 0, x_1508);
lean_ctor_set(x_1522, 1, x_1521);
x_1420 = x_1473;
x_1421 = x_1479;
x_1422 = x_1522;
x_1423 = x_1508;
x_1424 = x_1521;
goto block_1463;
}
else
{
lean_object* x_1523; 
lean_inc(x_1516);
x_1523 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1523, 0, x_1508);
lean_ctor_set(x_1523, 1, x_1516);
x_1420 = x_1473;
x_1421 = x_1479;
x_1422 = x_1523;
x_1423 = x_1508;
x_1424 = x_1516;
goto block_1463;
}
}
else
{
lean_object* x_1524; 
lean_dec(x_1512);
lean_dec(x_1495);
lean_inc(x_1487);
x_1524 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1524, 0, x_1409);
lean_ctor_set(x_1524, 1, x_1487);
x_1420 = x_1473;
x_1421 = x_1479;
x_1422 = x_1524;
x_1423 = x_1409;
x_1424 = x_1487;
goto block_1463;
}
}
else
{
lean_object* x_1525; lean_object* x_1526; lean_object* x_1527; lean_object* x_1528; 
lean_dec(x_1469);
lean_dec(x_1419);
lean_dec(x_1411);
lean_dec(x_1406);
lean_dec(x_898);
lean_dec(x_48);
x_1525 = lean_ctor_get(x_1471, 0);
lean_inc(x_1525);
x_1526 = lean_ctor_get(x_1471, 1);
lean_inc(x_1526);
if (lean_is_exclusive(x_1471)) {
 lean_ctor_release(x_1471, 0);
 lean_ctor_release(x_1471, 1);
 x_1527 = x_1471;
} else {
 lean_dec_ref(x_1471);
 x_1527 = lean_box(0);
}
if (lean_is_scalar(x_1527)) {
 x_1528 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1528 = x_1527;
}
lean_ctor_set(x_1528, 0, x_1525);
lean_ctor_set(x_1528, 1, x_1526);
return x_1528;
}
}
}
else
{
lean_dec(x_1406);
lean_dec(x_898);
lean_dec(x_894);
lean_dec(x_48);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
x_19 = x_18;
goto block_31;
}
}
}
}
}
}
}
case 1:
{
uint8_t x_1545; 
lean_dec(x_48);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_1545 = !lean_is_exclusive(x_49);
if (x_1545 == 0)
{
lean_object* x_1546; lean_object* x_1547; lean_object* x_1548; lean_object* x_1549; lean_object* x_1550; lean_object* x_1551; lean_object* x_1552; lean_object* x_1553; lean_object* x_1554; lean_object* x_1555; 
x_1546 = lean_ctor_get(x_49, 0);
lean_dec(x_1546);
x_1547 = lean_ctor_get(x_50, 1);
lean_inc(x_1547);
lean_dec(x_50);
x_1548 = lean_ctor_get(x_59, 1);
lean_inc(x_1548);
lean_dec(x_59);
x_1549 = lean_ctor_get(x_72, 0);
lean_inc(x_1549);
x_1550 = lean_ctor_get(x_72, 1);
lean_inc(x_1550);
lean_dec(x_72);
x_1551 = l_Lean_Name_str___override(x_1549, x_1550);
x_1552 = l_Lean_Name_str___override(x_1551, x_1548);
x_1553 = l_Lean_Name_str___override(x_1552, x_1547);
lean_ctor_set(x_49, 0, x_1553);
x_1554 = lean_box(x_12);
x_1555 = lean_apply_11(x_6, x_49, x_9, x_10, x_11, x_1554, x_13, x_14, x_15, x_16, x_17, x_18);
return x_1555;
}
else
{
lean_object* x_1556; lean_object* x_1557; lean_object* x_1558; lean_object* x_1559; lean_object* x_1560; lean_object* x_1561; lean_object* x_1562; lean_object* x_1563; lean_object* x_1564; lean_object* x_1565; lean_object* x_1566; 
x_1556 = lean_ctor_get(x_49, 1);
lean_inc(x_1556);
lean_dec(x_49);
x_1557 = lean_ctor_get(x_50, 1);
lean_inc(x_1557);
lean_dec(x_50);
x_1558 = lean_ctor_get(x_59, 1);
lean_inc(x_1558);
lean_dec(x_59);
x_1559 = lean_ctor_get(x_72, 0);
lean_inc(x_1559);
x_1560 = lean_ctor_get(x_72, 1);
lean_inc(x_1560);
lean_dec(x_72);
x_1561 = l_Lean_Name_str___override(x_1559, x_1560);
x_1562 = l_Lean_Name_str___override(x_1561, x_1558);
x_1563 = l_Lean_Name_str___override(x_1562, x_1557);
x_1564 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1564, 0, x_1563);
lean_ctor_set(x_1564, 1, x_1556);
x_1565 = lean_box(x_12);
x_1566 = lean_apply_11(x_6, x_1564, x_9, x_10, x_11, x_1565, x_13, x_14, x_15, x_16, x_17, x_18);
return x_1566;
}
}
default: 
{
uint8_t x_1567; 
lean_dec(x_48);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_1567 = !lean_is_exclusive(x_49);
if (x_1567 == 0)
{
lean_object* x_1568; lean_object* x_1569; lean_object* x_1570; lean_object* x_1571; lean_object* x_1572; lean_object* x_1573; lean_object* x_1574; lean_object* x_1575; lean_object* x_1576; lean_object* x_1577; 
x_1568 = lean_ctor_get(x_49, 0);
lean_dec(x_1568);
x_1569 = lean_ctor_get(x_50, 1);
lean_inc(x_1569);
lean_dec(x_50);
x_1570 = lean_ctor_get(x_59, 1);
lean_inc(x_1570);
lean_dec(x_59);
x_1571 = lean_ctor_get(x_72, 0);
lean_inc(x_1571);
x_1572 = lean_ctor_get(x_72, 1);
lean_inc(x_1572);
lean_dec(x_72);
x_1573 = l_Lean_Name_num___override(x_1571, x_1572);
x_1574 = l_Lean_Name_str___override(x_1573, x_1570);
x_1575 = l_Lean_Name_str___override(x_1574, x_1569);
lean_ctor_set(x_49, 0, x_1575);
x_1576 = lean_box(x_12);
x_1577 = lean_apply_11(x_6, x_49, x_9, x_10, x_11, x_1576, x_13, x_14, x_15, x_16, x_17, x_18);
return x_1577;
}
else
{
lean_object* x_1578; lean_object* x_1579; lean_object* x_1580; lean_object* x_1581; lean_object* x_1582; lean_object* x_1583; lean_object* x_1584; lean_object* x_1585; lean_object* x_1586; lean_object* x_1587; lean_object* x_1588; 
x_1578 = lean_ctor_get(x_49, 1);
lean_inc(x_1578);
lean_dec(x_49);
x_1579 = lean_ctor_get(x_50, 1);
lean_inc(x_1579);
lean_dec(x_50);
x_1580 = lean_ctor_get(x_59, 1);
lean_inc(x_1580);
lean_dec(x_59);
x_1581 = lean_ctor_get(x_72, 0);
lean_inc(x_1581);
x_1582 = lean_ctor_get(x_72, 1);
lean_inc(x_1582);
lean_dec(x_72);
x_1583 = l_Lean_Name_num___override(x_1581, x_1582);
x_1584 = l_Lean_Name_str___override(x_1583, x_1580);
x_1585 = l_Lean_Name_str___override(x_1584, x_1579);
x_1586 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1586, 0, x_1585);
lean_ctor_set(x_1586, 1, x_1578);
x_1587 = lean_box(x_12);
x_1588 = lean_apply_11(x_6, x_1586, x_9, x_10, x_11, x_1587, x_13, x_14, x_15, x_16, x_17, x_18);
return x_1588;
}
}
}
}
default: 
{
uint8_t x_1589; 
lean_dec(x_48);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_1589 = !lean_is_exclusive(x_49);
if (x_1589 == 0)
{
lean_object* x_1590; lean_object* x_1591; lean_object* x_1592; lean_object* x_1593; lean_object* x_1594; lean_object* x_1595; lean_object* x_1596; lean_object* x_1597; 
x_1590 = lean_ctor_get(x_49, 0);
lean_dec(x_1590);
x_1591 = lean_ctor_get(x_50, 1);
lean_inc(x_1591);
lean_dec(x_50);
x_1592 = lean_ctor_get(x_59, 0);
lean_inc(x_1592);
x_1593 = lean_ctor_get(x_59, 1);
lean_inc(x_1593);
lean_dec(x_59);
x_1594 = l_Lean_Name_num___override(x_1592, x_1593);
x_1595 = l_Lean_Name_str___override(x_1594, x_1591);
lean_ctor_set(x_49, 0, x_1595);
x_1596 = lean_box(x_12);
x_1597 = lean_apply_11(x_6, x_49, x_9, x_10, x_11, x_1596, x_13, x_14, x_15, x_16, x_17, x_18);
return x_1597;
}
else
{
lean_object* x_1598; lean_object* x_1599; lean_object* x_1600; lean_object* x_1601; lean_object* x_1602; lean_object* x_1603; lean_object* x_1604; lean_object* x_1605; lean_object* x_1606; 
x_1598 = lean_ctor_get(x_49, 1);
lean_inc(x_1598);
lean_dec(x_49);
x_1599 = lean_ctor_get(x_50, 1);
lean_inc(x_1599);
lean_dec(x_50);
x_1600 = lean_ctor_get(x_59, 0);
lean_inc(x_1600);
x_1601 = lean_ctor_get(x_59, 1);
lean_inc(x_1601);
lean_dec(x_59);
x_1602 = l_Lean_Name_num___override(x_1600, x_1601);
x_1603 = l_Lean_Name_str___override(x_1602, x_1599);
x_1604 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1604, 0, x_1603);
lean_ctor_set(x_1604, 1, x_1598);
x_1605 = lean_box(x_12);
x_1606 = lean_apply_11(x_6, x_1604, x_9, x_10, x_11, x_1605, x_13, x_14, x_15, x_16, x_17, x_18);
return x_1606;
}
}
}
}
default: 
{
uint8_t x_1607; 
lean_dec(x_48);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_1607 = !lean_is_exclusive(x_49);
if (x_1607 == 0)
{
lean_object* x_1608; lean_object* x_1609; lean_object* x_1610; lean_object* x_1611; lean_object* x_1612; lean_object* x_1613; 
x_1608 = lean_ctor_get(x_49, 0);
lean_dec(x_1608);
x_1609 = lean_ctor_get(x_50, 0);
lean_inc(x_1609);
x_1610 = lean_ctor_get(x_50, 1);
lean_inc(x_1610);
lean_dec(x_50);
x_1611 = l_Lean_Name_num___override(x_1609, x_1610);
lean_ctor_set(x_49, 0, x_1611);
x_1612 = lean_box(x_12);
x_1613 = lean_apply_11(x_6, x_49, x_9, x_10, x_11, x_1612, x_13, x_14, x_15, x_16, x_17, x_18);
return x_1613;
}
else
{
lean_object* x_1614; lean_object* x_1615; lean_object* x_1616; lean_object* x_1617; lean_object* x_1618; lean_object* x_1619; lean_object* x_1620; 
x_1614 = lean_ctor_get(x_49, 1);
lean_inc(x_1614);
lean_dec(x_49);
x_1615 = lean_ctor_get(x_50, 0);
lean_inc(x_1615);
x_1616 = lean_ctor_get(x_50, 1);
lean_inc(x_1616);
lean_dec(x_50);
x_1617 = l_Lean_Name_num___override(x_1615, x_1616);
x_1618 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1618, 0, x_1617);
lean_ctor_set(x_1618, 1, x_1614);
x_1619 = lean_box(x_12);
x_1620 = lean_apply_11(x_6, x_1618, x_9, x_10, x_11, x_1619, x_13, x_14, x_15, x_16, x_17, x_18);
return x_1620;
}
}
}
}
}
block_31:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_20 = lean_unsigned_to_nat(8u);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_unsigned_to_nat(2u);
x_23 = lean_nat_shiftl(x_20, x_22);
x_24 = lean_unsigned_to_nat(3u);
x_25 = lean_nat_div(x_23, x_24);
lean_dec(x_23);
x_26 = l_Nat_nextPowerOfTwo(x_25);
lean_dec(x_25);
x_27 = lean_box(0);
x_28 = lean_mk_array(x_26, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_21);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_19);
return x_30;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, uint8_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_29; uint8_t x_30; 
x_29 = lean_mk_string_unchecked("hDiv", 4, 4);
x_30 = lean_string_dec_eq(x_1, x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_29);
x_31 = l_Lean_Name_str___override(x_2, x_3);
x_32 = l_Lean_Name_str___override(x_31, x_1);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_4);
x_34 = lean_box(x_9);
x_35 = lean_apply_11(x_5, x_33, x_6, x_7, x_8, x_34, x_10, x_11, x_12, x_13, x_14, x_15);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
lean_dec(x_1);
x_36 = lean_array_get_size(x_4);
x_37 = lean_unsigned_to_nat(6u);
x_38 = lean_nat_dec_eq(x_36, x_37);
lean_dec(x_36);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_39 = l_Lean_Name_str___override(x_2, x_3);
x_40 = l_Lean_Name_str___override(x_39, x_29);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_4);
x_42 = lean_box(x_9);
x_43 = lean_apply_11(x_5, x_41, x_6, x_7, x_8, x_42, x_10, x_11, x_12, x_13, x_14, x_15);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_29);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_44 = lean_unsigned_to_nat(5u);
x_45 = lean_array_fget(x_4, x_44);
lean_inc(x_45);
x_46 = l_Lean_Elab_Tactic_Omega_natCast_x3f(x_45);
if (lean_obj_tag(x_46) == 0)
{
lean_dec(x_45);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_4);
x_16 = x_15;
goto block_28;
}
else
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
lean_dec(x_46);
x_48 = lean_unsigned_to_nat(0u);
x_49 = lean_nat_dec_eq(x_47, x_48);
lean_dec(x_47);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_172; uint8_t x_173; 
x_50 = lean_unsigned_to_nat(4u);
x_51 = lean_array_fget(x_4, x_50);
lean_dec(x_4);
x_52 = lean_mk_string_unchecked("Ne", 2, 2);
x_53 = l_Lean_Name_mkStr1(x_52);
x_54 = lean_unsigned_to_nat(1u);
x_55 = l_Lean_Level_ofNat(x_54);
x_56 = lean_box(0);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
x_58 = l_Lean_Expr_const___override(x_53, x_57);
x_59 = lean_mk_string_unchecked("Int", 3, 3);
lean_inc(x_59);
x_103 = l_Lean_Name_mkStr1(x_59);
x_104 = l_Lean_Expr_const___override(x_103, x_56);
x_172 = lean_nat_to_int(x_48);
x_173 = lean_int_dec_le(x_172, x_172);
if (x_173 == 0)
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_174 = lean_mk_string_unchecked("Neg", 3, 3);
x_175 = lean_mk_string_unchecked("neg", 3, 3);
x_176 = l_Lean_Name_mkStr2(x_174, x_175);
x_177 = l_Lean_Level_ofNat(x_48);
x_178 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_178, 0, x_177);
lean_ctor_set(x_178, 1, x_56);
x_179 = l_Lean_Expr_const___override(x_176, x_178);
x_180 = lean_mk_string_unchecked("instNegInt", 10, 10);
lean_inc(x_59);
x_181 = l_Lean_Name_mkStr2(x_59, x_180);
x_182 = l_Lean_Expr_const___override(x_181, x_56);
x_183 = lean_int_neg(x_172);
lean_dec(x_172);
x_184 = l_Int_toNat(x_183);
lean_dec(x_183);
x_185 = l_Lean_instToExprInt_mkNat(x_184);
lean_inc(x_104);
x_186 = l_Lean_mkApp3(x_179, x_104, x_182, x_185);
x_105 = x_186;
goto block_171;
}
else
{
lean_object* x_187; lean_object* x_188; 
x_187 = l_Int_toNat(x_172);
lean_dec(x_172);
x_188 = l_Lean_instToExprInt_mkNat(x_187);
x_105 = x_188;
goto block_171;
}
block_102:
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint64_t x_70; lean_object* x_71; uint64_t x_72; uint64_t x_73; uint64_t x_74; lean_object* x_75; uint64_t x_76; uint64_t x_77; uint64_t x_78; size_t x_79; size_t x_80; size_t x_81; size_t x_82; size_t x_83; lean_object* x_84; uint8_t x_85; 
x_65 = lean_mk_string_unchecked("lt_mul_ediv_self_add", 20, 20);
x_66 = l_Lean_Name_mkStr2(x_59, x_65);
x_67 = l_Lean_Expr_const___override(x_66, x_56);
x_68 = l_Lean_mkApp3(x_67, x_51, x_45, x_61);
x_69 = lean_array_get_size(x_64);
x_70 = l_Lean_Expr_hash(x_68);
x_71 = lean_unsigned_to_nat(32u);
x_72 = lean_uint64_of_nat(x_71);
x_73 = lean_uint64_shift_right(x_70, x_72);
x_74 = lean_uint64_xor(x_70, x_73);
x_75 = lean_unsigned_to_nat(16u);
x_76 = lean_uint64_of_nat(x_75);
x_77 = lean_uint64_shift_right(x_74, x_76);
x_78 = lean_uint64_xor(x_74, x_77);
x_79 = lean_uint64_to_usize(x_78);
x_80 = lean_usize_of_nat(x_69);
lean_dec(x_69);
x_81 = lean_usize_of_nat(x_54);
x_82 = lean_usize_sub(x_80, x_81);
x_83 = lean_usize_land(x_79, x_82);
x_84 = lean_array_uget(x_64, x_83);
x_85 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectMVars_visit_spec__0___redArg(x_68, x_84);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; 
lean_dec(x_62);
x_86 = lean_box(0);
x_87 = lean_nat_add(x_63, x_54);
lean_dec(x_63);
x_88 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_88, 0, x_68);
lean_ctor_set(x_88, 1, x_86);
lean_ctor_set(x_88, 2, x_84);
x_89 = lean_array_uset(x_64, x_83, x_88);
x_90 = lean_unsigned_to_nat(2u);
x_91 = lean_nat_shiftl(x_87, x_90);
x_92 = lean_unsigned_to_nat(3u);
x_93 = lean_nat_div(x_91, x_92);
lean_dec(x_91);
x_94 = lean_array_get_size(x_89);
x_95 = lean_nat_dec_le(x_93, x_94);
lean_dec(x_94);
lean_dec(x_93);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectMVars_visit_spec__1(lean_box(0), x_89);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_87);
lean_ctor_set(x_97, 1, x_96);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_60);
return x_98;
}
else
{
lean_object* x_99; lean_object* x_100; 
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_87);
lean_ctor_set(x_99, 1, x_89);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_60);
return x_100;
}
}
else
{
lean_object* x_101; 
lean_dec(x_84);
lean_dec(x_68);
lean_dec(x_64);
lean_dec(x_63);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_62);
lean_ctor_set(x_101, 1, x_60);
return x_101;
}
}
block_171:
{
lean_object* x_106; lean_object* x_107; 
lean_inc(x_105);
lean_inc(x_45);
lean_inc(x_104);
x_106 = l_Lean_mkApp3(x_58, x_104, x_45, x_105);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_107 = l_Lean_Meta_mkDecideProof(x_106, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec(x_107);
x_110 = lean_mk_string_unchecked("LT", 2, 2);
x_111 = lean_mk_string_unchecked("lt", 2, 2);
x_112 = l_Lean_Level_ofNat(x_48);
x_113 = lean_mk_string_unchecked("instLTInt", 9, 9);
x_114 = l_Lean_Name_mkStr2(x_110, x_111);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_112);
lean_ctor_set(x_115, 1, x_56);
lean_inc(x_59);
x_116 = l_Lean_Name_mkStr2(x_59, x_113);
x_117 = l_Lean_Expr_const___override(x_114, x_115);
x_118 = l_Lean_Expr_const___override(x_116, x_56);
lean_inc(x_45);
x_119 = l_Lean_mkApp4(x_117, x_104, x_118, x_105, x_45);
x_120 = l_Lean_Meta_mkDecideProof(x_119, x_11, x_12, x_13, x_14, x_109);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; uint64_t x_136; lean_object* x_137; uint64_t x_138; uint64_t x_139; uint64_t x_140; lean_object* x_141; uint64_t x_142; uint64_t x_143; uint64_t x_144; size_t x_145; size_t x_146; size_t x_147; size_t x_148; size_t x_149; lean_object* x_150; uint8_t x_151; 
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
lean_dec(x_120);
x_123 = lean_unsigned_to_nat(8u);
x_124 = lean_unsigned_to_nat(2u);
x_125 = lean_nat_shiftl(x_123, x_124);
x_126 = lean_unsigned_to_nat(3u);
x_127 = lean_nat_div(x_125, x_126);
lean_dec(x_125);
x_128 = l_Nat_nextPowerOfTwo(x_127);
lean_dec(x_127);
x_129 = lean_box(0);
x_130 = lean_mk_array(x_128, x_129);
x_131 = lean_mk_string_unchecked("mul_ediv_self_le", 16, 16);
lean_inc(x_59);
x_132 = l_Lean_Name_mkStr2(x_59, x_131);
x_133 = l_Lean_Expr_const___override(x_132, x_56);
lean_inc(x_45);
lean_inc(x_51);
x_134 = l_Lean_mkApp3(x_133, x_51, x_45, x_108);
x_135 = lean_array_get_size(x_130);
x_136 = l_Lean_Expr_hash(x_134);
x_137 = lean_unsigned_to_nat(32u);
x_138 = lean_uint64_of_nat(x_137);
x_139 = lean_uint64_shift_right(x_136, x_138);
x_140 = lean_uint64_xor(x_136, x_139);
x_141 = lean_unsigned_to_nat(16u);
x_142 = lean_uint64_of_nat(x_141);
x_143 = lean_uint64_shift_right(x_140, x_142);
x_144 = lean_uint64_xor(x_140, x_143);
x_145 = lean_uint64_to_usize(x_144);
x_146 = lean_usize_of_nat(x_135);
lean_dec(x_135);
x_147 = lean_usize_of_nat(x_54);
x_148 = lean_usize_sub(x_146, x_147);
x_149 = lean_usize_land(x_145, x_148);
x_150 = lean_array_uget(x_130, x_149);
x_151 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectMVars_visit_spec__0___redArg(x_134, x_150);
if (x_151 == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; uint8_t x_158; 
x_152 = lean_box(0);
x_153 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_153, 0, x_134);
lean_ctor_set(x_153, 1, x_152);
lean_ctor_set(x_153, 2, x_150);
x_154 = lean_array_uset(x_130, x_149, x_153);
x_155 = lean_nat_shiftl(x_54, x_124);
x_156 = lean_nat_div(x_155, x_126);
lean_dec(x_155);
x_157 = lean_array_get_size(x_154);
x_158 = lean_nat_dec_le(x_156, x_157);
lean_dec(x_157);
lean_dec(x_156);
if (x_158 == 0)
{
lean_object* x_159; lean_object* x_160; 
x_159 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectMVars_visit_spec__1(lean_box(0), x_154);
lean_inc(x_159);
x_160 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_160, 0, x_54);
lean_ctor_set(x_160, 1, x_159);
x_60 = x_122;
x_61 = x_121;
x_62 = x_160;
x_63 = x_54;
x_64 = x_159;
goto block_102;
}
else
{
lean_object* x_161; 
lean_inc(x_154);
x_161 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_161, 0, x_54);
lean_ctor_set(x_161, 1, x_154);
x_60 = x_122;
x_61 = x_121;
x_62 = x_161;
x_63 = x_54;
x_64 = x_154;
goto block_102;
}
}
else
{
lean_object* x_162; 
lean_dec(x_150);
lean_dec(x_134);
lean_inc(x_130);
x_162 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_162, 0, x_48);
lean_ctor_set(x_162, 1, x_130);
x_60 = x_122;
x_61 = x_121;
x_62 = x_162;
x_63 = x_48;
x_64 = x_130;
goto block_102;
}
}
else
{
uint8_t x_163; 
lean_dec(x_108);
lean_dec(x_59);
lean_dec(x_51);
lean_dec(x_45);
x_163 = !lean_is_exclusive(x_120);
if (x_163 == 0)
{
return x_120;
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_164 = lean_ctor_get(x_120, 0);
x_165 = lean_ctor_get(x_120, 1);
lean_inc(x_165);
lean_inc(x_164);
lean_dec(x_120);
x_166 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_166, 0, x_164);
lean_ctor_set(x_166, 1, x_165);
return x_166;
}
}
}
else
{
uint8_t x_167; 
lean_dec(x_105);
lean_dec(x_104);
lean_dec(x_59);
lean_dec(x_51);
lean_dec(x_45);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_167 = !lean_is_exclusive(x_107);
if (x_167 == 0)
{
return x_107;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_168 = lean_ctor_get(x_107, 0);
x_169 = lean_ctor_get(x_107, 1);
lean_inc(x_169);
lean_inc(x_168);
lean_dec(x_107);
x_170 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_170, 0, x_168);
lean_ctor_set(x_170, 1, x_169);
return x_170;
}
}
}
}
else
{
lean_dec(x_45);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_4);
x_16 = x_15;
goto block_28;
}
}
}
}
block_28:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_17 = lean_unsigned_to_nat(8u);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_unsigned_to_nat(2u);
x_20 = lean_nat_shiftl(x_17, x_19);
x_21 = lean_unsigned_to_nat(3u);
x_22 = lean_nat_div(x_20, x_21);
lean_dec(x_20);
x_23 = l_Nat_nextPowerOfTwo(x_22);
lean_dec(x_22);
x_24 = lean_box(0);
x_25 = lean_mk_array(x_23, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_18);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_16);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(x_6);
x_14 = lean_apply_11(x_1, x_2, x_3, x_4, x_5, x_13, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, uint8_t x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint64_t x_27; lean_object* x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; lean_object* x_32; uint64_t x_33; uint64_t x_34; uint64_t x_35; size_t x_36; size_t x_37; size_t x_38; size_t x_39; size_t x_40; lean_object* x_41; uint8_t x_42; 
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
x_21 = lean_mk_string_unchecked("BitVec", 6, 6);
x_22 = lean_mk_string_unchecked("isLt", 4, 4);
x_23 = l_Lean_Name_mkStr2(x_21, x_22);
x_24 = l_Lean_Expr_const___override(x_23, x_2);
x_25 = l_Lean_mkAppB(x_24, x_7, x_8);
x_26 = lean_array_get_size(x_20);
x_27 = l_Lean_Expr_hash(x_25);
x_28 = lean_unsigned_to_nat(32u);
x_29 = lean_uint64_of_nat(x_28);
x_30 = lean_uint64_shift_right(x_27, x_29);
x_31 = lean_uint64_xor(x_27, x_30);
x_32 = lean_unsigned_to_nat(16u);
x_33 = lean_uint64_of_nat(x_32);
x_34 = lean_uint64_shift_right(x_31, x_33);
x_35 = lean_uint64_xor(x_31, x_34);
x_36 = lean_uint64_to_usize(x_35);
x_37 = lean_usize_of_nat(x_26);
lean_dec(x_26);
x_38 = lean_usize_of_nat(x_3);
x_39 = lean_usize_sub(x_37, x_38);
x_40 = lean_usize_land(x_36, x_39);
x_41 = lean_array_uget(x_20, x_40);
x_42 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectMVars_visit_spec__0___redArg(x_25, x_41);
if (x_42 == 0)
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_1);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_44 = lean_ctor_get(x_1, 1);
lean_dec(x_44);
x_45 = lean_ctor_get(x_1, 0);
lean_dec(x_45);
x_46 = lean_box(0);
x_47 = lean_nat_add(x_19, x_3);
lean_dec(x_19);
x_48 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_48, 0, x_25);
lean_ctor_set(x_48, 1, x_46);
lean_ctor_set(x_48, 2, x_41);
x_49 = lean_array_uset(x_20, x_40, x_48);
x_50 = lean_nat_shiftl(x_47, x_4);
x_51 = lean_nat_div(x_50, x_5);
lean_dec(x_50);
x_52 = lean_array_get_size(x_49);
x_53 = lean_nat_dec_le(x_51, x_52);
lean_dec(x_52);
lean_dec(x_51);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; 
x_54 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectMVars_visit_spec__1(lean_box(0), x_49);
lean_ctor_set(x_1, 1, x_54);
lean_ctor_set(x_1, 0, x_47);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_1);
lean_ctor_set(x_55, 1, x_18);
return x_55;
}
else
{
lean_object* x_56; 
lean_ctor_set(x_1, 1, x_49);
lean_ctor_set(x_1, 0, x_47);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_1);
lean_ctor_set(x_56, 1, x_18);
return x_56;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
lean_dec(x_1);
x_57 = lean_box(0);
x_58 = lean_nat_add(x_19, x_3);
lean_dec(x_19);
x_59 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_59, 0, x_25);
lean_ctor_set(x_59, 1, x_57);
lean_ctor_set(x_59, 2, x_41);
x_60 = lean_array_uset(x_20, x_40, x_59);
x_61 = lean_nat_shiftl(x_58, x_4);
x_62 = lean_nat_div(x_61, x_5);
lean_dec(x_61);
x_63 = lean_array_get_size(x_60);
x_64 = lean_nat_dec_le(x_62, x_63);
lean_dec(x_63);
lean_dec(x_62);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectMVars_visit_spec__1(lean_box(0), x_60);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_58);
lean_ctor_set(x_66, 1, x_65);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_18);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_58);
lean_ctor_set(x_68, 1, x_60);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_18);
return x_69;
}
}
}
else
{
lean_object* x_70; 
lean_dec(x_41);
lean_dec(x_25);
lean_dec(x_20);
lean_dec(x_19);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_1);
lean_ctor_set(x_70, 1, x_18);
return x_70;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, uint8_t x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint64_t x_27; lean_object* x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; lean_object* x_32; uint64_t x_33; uint64_t x_34; uint64_t x_35; size_t x_36; size_t x_37; size_t x_38; size_t x_39; size_t x_40; lean_object* x_41; uint8_t x_42; 
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
x_21 = lean_mk_string_unchecked("Fin", 3, 3);
x_22 = lean_mk_string_unchecked("isLt", 4, 4);
x_23 = l_Lean_Name_mkStr2(x_21, x_22);
x_24 = l_Lean_Expr_const___override(x_23, x_2);
x_25 = l_Lean_mkAppB(x_24, x_7, x_8);
x_26 = lean_array_get_size(x_20);
x_27 = l_Lean_Expr_hash(x_25);
x_28 = lean_unsigned_to_nat(32u);
x_29 = lean_uint64_of_nat(x_28);
x_30 = lean_uint64_shift_right(x_27, x_29);
x_31 = lean_uint64_xor(x_27, x_30);
x_32 = lean_unsigned_to_nat(16u);
x_33 = lean_uint64_of_nat(x_32);
x_34 = lean_uint64_shift_right(x_31, x_33);
x_35 = lean_uint64_xor(x_31, x_34);
x_36 = lean_uint64_to_usize(x_35);
x_37 = lean_usize_of_nat(x_26);
lean_dec(x_26);
x_38 = lean_usize_of_nat(x_3);
x_39 = lean_usize_sub(x_37, x_38);
x_40 = lean_usize_land(x_36, x_39);
x_41 = lean_array_uget(x_20, x_40);
x_42 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectMVars_visit_spec__0___redArg(x_25, x_41);
if (x_42 == 0)
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_1);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_44 = lean_ctor_get(x_1, 1);
lean_dec(x_44);
x_45 = lean_ctor_get(x_1, 0);
lean_dec(x_45);
x_46 = lean_box(0);
x_47 = lean_nat_add(x_19, x_3);
lean_dec(x_19);
x_48 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_48, 0, x_25);
lean_ctor_set(x_48, 1, x_46);
lean_ctor_set(x_48, 2, x_41);
x_49 = lean_array_uset(x_20, x_40, x_48);
x_50 = lean_nat_shiftl(x_47, x_4);
x_51 = lean_nat_div(x_50, x_5);
lean_dec(x_50);
x_52 = lean_array_get_size(x_49);
x_53 = lean_nat_dec_le(x_51, x_52);
lean_dec(x_52);
lean_dec(x_51);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; 
x_54 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectMVars_visit_spec__1(lean_box(0), x_49);
lean_ctor_set(x_1, 1, x_54);
lean_ctor_set(x_1, 0, x_47);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_1);
lean_ctor_set(x_55, 1, x_18);
return x_55;
}
else
{
lean_object* x_56; 
lean_ctor_set(x_1, 1, x_49);
lean_ctor_set(x_1, 0, x_47);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_1);
lean_ctor_set(x_56, 1, x_18);
return x_56;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
lean_dec(x_1);
x_57 = lean_box(0);
x_58 = lean_nat_add(x_19, x_3);
lean_dec(x_19);
x_59 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_59, 0, x_25);
lean_ctor_set(x_59, 1, x_57);
lean_ctor_set(x_59, 2, x_41);
x_60 = lean_array_uset(x_20, x_40, x_59);
x_61 = lean_nat_shiftl(x_58, x_4);
x_62 = lean_nat_div(x_61, x_5);
lean_dec(x_61);
x_63 = lean_array_get_size(x_60);
x_64 = lean_nat_dec_le(x_62, x_63);
lean_dec(x_63);
lean_dec(x_62);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectMVars_visit_spec__1(lean_box(0), x_60);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_58);
lean_ctor_set(x_66, 1, x_65);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_18);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_58);
lean_ctor_set(x_68, 1, x_60);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_18);
return x_69;
}
}
}
else
{
lean_object* x_70; 
lean_dec(x_41);
lean_dec(x_25);
lean_dec(x_20);
lean_dec(x_19);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_1);
lean_ctor_set(x_70, 1, x_18);
return x_70;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, uint8_t x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint64_t x_67; lean_object* x_68; uint64_t x_69; uint64_t x_70; uint64_t x_71; lean_object* x_72; uint64_t x_73; uint64_t x_74; uint64_t x_75; size_t x_76; size_t x_77; size_t x_78; size_t x_79; size_t x_80; lean_object* x_81; uint8_t x_82; 
x_60 = lean_ctor_get(x_1, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_1, 1);
lean_inc(x_61);
x_62 = lean_mk_string_unchecked("le_natAbs", 9, 9);
lean_inc(x_2);
x_63 = l_Lean_Name_mkStr2(x_2, x_62);
lean_inc(x_3);
x_64 = l_Lean_Expr_const___override(x_63, x_3);
lean_inc(x_8);
x_65 = l_Lean_Expr_app___override(x_64, x_8);
x_66 = lean_array_get_size(x_61);
x_67 = l_Lean_Expr_hash(x_65);
x_68 = lean_unsigned_to_nat(32u);
x_69 = lean_uint64_of_nat(x_68);
x_70 = lean_uint64_shift_right(x_67, x_69);
x_71 = lean_uint64_xor(x_67, x_70);
x_72 = lean_unsigned_to_nat(16u);
x_73 = lean_uint64_of_nat(x_72);
x_74 = lean_uint64_shift_right(x_71, x_73);
x_75 = lean_uint64_xor(x_71, x_74);
x_76 = lean_uint64_to_usize(x_75);
x_77 = lean_usize_of_nat(x_66);
lean_dec(x_66);
x_78 = lean_usize_of_nat(x_4);
x_79 = lean_usize_sub(x_77, x_78);
x_80 = lean_usize_land(x_76, x_79);
x_81 = lean_array_uget(x_61, x_80);
x_82 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectMVars_visit_spec__0___redArg(x_65, x_81);
if (x_82 == 0)
{
uint8_t x_83; 
x_83 = !lean_is_exclusive(x_1);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_84 = lean_ctor_get(x_1, 1);
lean_dec(x_84);
x_85 = lean_ctor_get(x_1, 0);
lean_dec(x_85);
x_86 = lean_box(0);
x_87 = lean_nat_add(x_60, x_4);
lean_dec(x_60);
x_88 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_88, 0, x_65);
lean_ctor_set(x_88, 1, x_86);
lean_ctor_set(x_88, 2, x_81);
x_89 = lean_array_uset(x_61, x_80, x_88);
x_90 = lean_nat_shiftl(x_87, x_5);
x_91 = lean_nat_div(x_90, x_6);
lean_dec(x_90);
x_92 = lean_array_get_size(x_89);
x_93 = lean_nat_dec_le(x_91, x_92);
lean_dec(x_92);
lean_dec(x_91);
if (x_93 == 0)
{
lean_object* x_94; 
x_94 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectMVars_visit_spec__1(lean_box(0), x_89);
lean_inc(x_94);
lean_inc(x_87);
lean_ctor_set(x_1, 1, x_94);
lean_ctor_set(x_1, 0, x_87);
x_19 = x_1;
x_20 = x_87;
x_21 = x_94;
goto block_59;
}
else
{
lean_inc(x_89);
lean_inc(x_87);
lean_ctor_set(x_1, 1, x_89);
lean_ctor_set(x_1, 0, x_87);
x_19 = x_1;
x_20 = x_87;
x_21 = x_89;
goto block_59;
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; 
lean_dec(x_1);
x_95 = lean_box(0);
x_96 = lean_nat_add(x_60, x_4);
lean_dec(x_60);
x_97 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_97, 0, x_65);
lean_ctor_set(x_97, 1, x_95);
lean_ctor_set(x_97, 2, x_81);
x_98 = lean_array_uset(x_61, x_80, x_97);
x_99 = lean_nat_shiftl(x_96, x_5);
x_100 = lean_nat_div(x_99, x_6);
lean_dec(x_99);
x_101 = lean_array_get_size(x_98);
x_102 = lean_nat_dec_le(x_100, x_101);
lean_dec(x_101);
lean_dec(x_100);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; 
x_103 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectMVars_visit_spec__1(lean_box(0), x_98);
lean_inc(x_103);
lean_inc(x_96);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_96);
lean_ctor_set(x_104, 1, x_103);
x_19 = x_104;
x_20 = x_96;
x_21 = x_103;
goto block_59;
}
else
{
lean_object* x_105; 
lean_inc(x_98);
lean_inc(x_96);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_96);
lean_ctor_set(x_105, 1, x_98);
x_19 = x_105;
x_20 = x_96;
x_21 = x_98;
goto block_59;
}
}
}
else
{
lean_dec(x_81);
lean_dec(x_65);
x_19 = x_1;
x_20 = x_60;
x_21 = x_61;
goto block_59;
}
block_59:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint64_t x_29; lean_object* x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; lean_object* x_34; uint64_t x_35; uint64_t x_36; uint64_t x_37; size_t x_38; size_t x_39; size_t x_40; size_t x_41; size_t x_42; lean_object* x_43; uint8_t x_44; 
x_22 = lean_mk_string_unchecked("Lean", 4, 4);
x_23 = lean_mk_string_unchecked("Omega", 5, 5);
x_24 = lean_mk_string_unchecked("neg_le_natAbs", 13, 13);
x_25 = l_Lean_Name_mkStr4(x_22, x_23, x_2, x_24);
x_26 = l_Lean_Expr_const___override(x_25, x_3);
x_27 = l_Lean_Expr_app___override(x_26, x_8);
x_28 = lean_array_get_size(x_21);
x_29 = l_Lean_Expr_hash(x_27);
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
x_40 = lean_usize_of_nat(x_4);
x_41 = lean_usize_sub(x_39, x_40);
x_42 = lean_usize_land(x_38, x_41);
x_43 = lean_array_uget(x_21, x_42);
x_44 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectMVars_visit_spec__0___redArg(x_27, x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
lean_dec(x_19);
x_45 = lean_box(0);
x_46 = lean_nat_add(x_20, x_4);
lean_dec(x_20);
x_47 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_47, 0, x_27);
lean_ctor_set(x_47, 1, x_45);
lean_ctor_set(x_47, 2, x_43);
x_48 = lean_array_uset(x_21, x_42, x_47);
x_49 = lean_nat_shiftl(x_46, x_5);
x_50 = lean_nat_div(x_49, x_6);
lean_dec(x_49);
x_51 = lean_array_get_size(x_48);
x_52 = lean_nat_dec_le(x_50, x_51);
lean_dec(x_51);
lean_dec(x_50);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectMVars_visit_spec__1(lean_box(0), x_48);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_46);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_18);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_46);
lean_ctor_set(x_56, 1, x_48);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_18);
return x_57;
}
}
else
{
lean_object* x_58; 
lean_dec(x_43);
lean_dec(x_27);
lean_dec(x_21);
lean_dec(x_20);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_19);
lean_ctor_set(x_58, 1, x_18);
return x_58;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, uint8_t x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; uint64_t x_306; lean_object* x_307; uint64_t x_308; uint64_t x_309; uint64_t x_310; lean_object* x_311; uint64_t x_312; uint64_t x_313; uint64_t x_314; size_t x_315; size_t x_316; size_t x_317; size_t x_318; size_t x_319; lean_object* x_320; uint8_t x_321; 
x_17 = lean_unsigned_to_nat(8u);
x_18 = lean_nat_shiftl(x_17, x_1);
x_19 = lean_nat_div(x_18, x_2);
lean_dec(x_18);
x_20 = l_Nat_nextPowerOfTwo(x_19);
lean_dec(x_19);
x_21 = lean_box(0);
x_22 = lean_mk_array(x_20, x_21);
x_23 = lean_mk_string_unchecked("Int", 3, 3);
x_301 = lean_mk_string_unchecked("ofNat_nonneg", 12, 12);
lean_inc(x_23);
x_302 = l_Lean_Name_mkStr2(x_23, x_301);
lean_inc(x_3);
x_303 = l_Lean_Expr_const___override(x_302, x_3);
lean_inc(x_5);
x_304 = l_Lean_Expr_app___override(x_303, x_5);
x_305 = lean_array_get_size(x_22);
x_306 = l_Lean_Expr_hash(x_304);
x_307 = lean_unsigned_to_nat(32u);
x_308 = lean_uint64_of_nat(x_307);
x_309 = lean_uint64_shift_right(x_306, x_308);
x_310 = lean_uint64_xor(x_306, x_309);
x_311 = lean_unsigned_to_nat(16u);
x_312 = lean_uint64_of_nat(x_311);
x_313 = lean_uint64_shift_right(x_310, x_312);
x_314 = lean_uint64_xor(x_310, x_313);
x_315 = lean_uint64_to_usize(x_314);
x_316 = lean_usize_of_nat(x_305);
lean_dec(x_305);
x_317 = lean_usize_of_nat(x_4);
x_318 = lean_usize_sub(x_316, x_317);
x_319 = lean_usize_land(x_315, x_318);
x_320 = lean_array_uget(x_22, x_319);
x_321 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectMVars_visit_spec__0___redArg(x_304, x_320);
if (x_321 == 0)
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; uint8_t x_328; 
x_322 = lean_box(0);
x_323 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_323, 0, x_304);
lean_ctor_set(x_323, 1, x_322);
lean_ctor_set(x_323, 2, x_320);
x_324 = lean_array_uset(x_22, x_319, x_323);
x_325 = lean_nat_shiftl(x_4, x_1);
x_326 = lean_nat_div(x_325, x_2);
lean_dec(x_325);
x_327 = lean_array_get_size(x_324);
x_328 = lean_nat_dec_le(x_326, x_327);
lean_dec(x_327);
lean_dec(x_326);
if (x_328 == 0)
{
lean_object* x_329; lean_object* x_330; 
x_329 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectMVars_visit_spec__1(lean_box(0), x_324);
lean_inc(x_4);
x_330 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_330, 0, x_4);
lean_ctor_set(x_330, 1, x_329);
x_24 = x_330;
goto block_300;
}
else
{
lean_object* x_331; 
lean_inc(x_4);
x_331 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_331, 0, x_4);
lean_ctor_set(x_331, 1, x_324);
x_24 = x_331;
goto block_300;
}
}
else
{
lean_object* x_332; 
lean_dec(x_320);
lean_dec(x_304);
lean_inc(x_6);
x_332 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_332, 0, x_6);
lean_ctor_set(x_332, 1, x_22);
x_24 = x_332;
goto block_300;
}
block_300:
{
uint8_t x_25; 
x_25 = lean_ctor_get_uint8(x_9, 1);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = l_Lean_Expr_getAppFnArgs(x_5);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
if (lean_obj_tag(x_27) == 1)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
if (lean_obj_tag(x_28) == 1)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_26);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_31 = lean_ctor_get(x_26, 1);
x_32 = lean_ctor_get(x_26, 0);
lean_dec(x_32);
x_33 = lean_ctor_get(x_27, 1);
lean_inc(x_33);
lean_dec(x_27);
x_34 = lean_ctor_get(x_28, 1);
lean_inc(x_34);
lean_dec(x_28);
x_35 = lean_string_dec_eq(x_34, x_23);
if (x_35 == 0)
{
lean_object* x_36; uint8_t x_37; 
lean_dec(x_23);
x_36 = lean_mk_string_unchecked("Fin", 3, 3);
x_37 = lean_string_dec_eq(x_34, x_36);
lean_dec(x_36);
if (x_37 == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_mk_string_unchecked("BitVec", 6, 6);
x_39 = lean_string_dec_eq(x_34, x_38);
lean_dec(x_38);
lean_dec(x_34);
if (x_39 == 0)
{
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_ctor_set(x_26, 1, x_16);
lean_ctor_set(x_26, 0, x_24);
return x_26;
}
else
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_mk_string_unchecked("toNat", 5, 5);
x_41 = lean_string_dec_eq(x_33, x_40);
lean_dec(x_40);
lean_dec(x_33);
if (x_41 == 0)
{
lean_dec(x_31);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_ctor_set(x_26, 1, x_16);
lean_ctor_set(x_26, 0, x_24);
return x_26;
}
else
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_array_get_size(x_31);
x_43 = lean_nat_dec_eq(x_42, x_1);
lean_dec(x_42);
if (x_43 == 0)
{
lean_dec(x_31);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_ctor_set(x_26, 1, x_16);
lean_ctor_set(x_26, 0, x_24);
return x_26;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_free_object(x_26);
x_44 = lean_array_fget(x_31, x_6);
lean_dec(x_6);
x_45 = lean_array_fget(x_31, x_4);
lean_dec(x_31);
x_46 = l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__9(x_24, x_3, x_4, x_1, x_2, x_25, x_44, x_45, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_4);
return x_46;
}
}
}
}
else
{
lean_object* x_47; uint8_t x_48; 
lean_dec(x_34);
x_47 = lean_mk_string_unchecked("val", 3, 3);
x_48 = lean_string_dec_eq(x_33, x_47);
lean_dec(x_47);
lean_dec(x_33);
if (x_48 == 0)
{
lean_dec(x_31);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_ctor_set(x_26, 1, x_16);
lean_ctor_set(x_26, 0, x_24);
return x_26;
}
else
{
lean_object* x_49; uint8_t x_50; 
x_49 = lean_array_get_size(x_31);
x_50 = lean_nat_dec_eq(x_49, x_1);
lean_dec(x_49);
if (x_50 == 0)
{
lean_dec(x_31);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_ctor_set(x_26, 1, x_16);
lean_ctor_set(x_26, 0, x_24);
return x_26;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_free_object(x_26);
x_51 = lean_array_fget(x_31, x_6);
lean_dec(x_6);
x_52 = lean_array_fget(x_31, x_4);
lean_dec(x_31);
x_53 = l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__8(x_24, x_3, x_4, x_1, x_2, x_25, x_51, x_52, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_4);
return x_53;
}
}
}
}
else
{
lean_object* x_54; uint8_t x_55; 
lean_dec(x_34);
x_54 = lean_mk_string_unchecked("natAbs", 6, 6);
x_55 = lean_string_dec_eq(x_33, x_54);
lean_dec(x_54);
lean_dec(x_33);
if (x_55 == 0)
{
lean_dec(x_31);
lean_dec(x_23);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_ctor_set(x_26, 1, x_16);
lean_ctor_set(x_26, 0, x_24);
return x_26;
}
else
{
lean_object* x_56; uint8_t x_57; 
x_56 = lean_array_get_size(x_31);
x_57 = lean_nat_dec_eq(x_56, x_4);
lean_dec(x_56);
if (x_57 == 0)
{
lean_dec(x_31);
lean_dec(x_23);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_ctor_set(x_26, 1, x_16);
lean_ctor_set(x_26, 0, x_24);
return x_26;
}
else
{
lean_object* x_58; lean_object* x_59; 
lean_free_object(x_26);
x_58 = lean_array_fget(x_31, x_6);
lean_dec(x_6);
lean_dec(x_31);
x_59 = l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__10(x_24, x_23, x_3, x_4, x_1, x_2, x_25, x_58, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_4);
return x_59;
}
}
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_60 = lean_ctor_get(x_26, 1);
lean_inc(x_60);
lean_dec(x_26);
x_61 = lean_ctor_get(x_27, 1);
lean_inc(x_61);
lean_dec(x_27);
x_62 = lean_ctor_get(x_28, 1);
lean_inc(x_62);
lean_dec(x_28);
x_63 = lean_string_dec_eq(x_62, x_23);
if (x_63 == 0)
{
lean_object* x_64; uint8_t x_65; 
lean_dec(x_23);
x_64 = lean_mk_string_unchecked("Fin", 3, 3);
x_65 = lean_string_dec_eq(x_62, x_64);
lean_dec(x_64);
if (x_65 == 0)
{
lean_object* x_66; uint8_t x_67; 
x_66 = lean_mk_string_unchecked("BitVec", 6, 6);
x_67 = lean_string_dec_eq(x_62, x_66);
lean_dec(x_66);
lean_dec(x_62);
if (x_67 == 0)
{
lean_object* x_68; 
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_24);
lean_ctor_set(x_68, 1, x_16);
return x_68;
}
else
{
lean_object* x_69; uint8_t x_70; 
x_69 = lean_mk_string_unchecked("toNat", 5, 5);
x_70 = lean_string_dec_eq(x_61, x_69);
lean_dec(x_69);
lean_dec(x_61);
if (x_70 == 0)
{
lean_object* x_71; 
lean_dec(x_60);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_24);
lean_ctor_set(x_71, 1, x_16);
return x_71;
}
else
{
lean_object* x_72; uint8_t x_73; 
x_72 = lean_array_get_size(x_60);
x_73 = lean_nat_dec_eq(x_72, x_1);
lean_dec(x_72);
if (x_73 == 0)
{
lean_object* x_74; 
lean_dec(x_60);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_24);
lean_ctor_set(x_74, 1, x_16);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_array_fget(x_60, x_6);
lean_dec(x_6);
x_76 = lean_array_fget(x_60, x_4);
lean_dec(x_60);
x_77 = l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__9(x_24, x_3, x_4, x_1, x_2, x_25, x_75, x_76, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_4);
return x_77;
}
}
}
}
else
{
lean_object* x_78; uint8_t x_79; 
lean_dec(x_62);
x_78 = lean_mk_string_unchecked("val", 3, 3);
x_79 = lean_string_dec_eq(x_61, x_78);
lean_dec(x_78);
lean_dec(x_61);
if (x_79 == 0)
{
lean_object* x_80; 
lean_dec(x_60);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_24);
lean_ctor_set(x_80, 1, x_16);
return x_80;
}
else
{
lean_object* x_81; uint8_t x_82; 
x_81 = lean_array_get_size(x_60);
x_82 = lean_nat_dec_eq(x_81, x_1);
lean_dec(x_81);
if (x_82 == 0)
{
lean_object* x_83; 
lean_dec(x_60);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_24);
lean_ctor_set(x_83, 1, x_16);
return x_83;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_array_fget(x_60, x_6);
lean_dec(x_6);
x_85 = lean_array_fget(x_60, x_4);
lean_dec(x_60);
x_86 = l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__8(x_24, x_3, x_4, x_1, x_2, x_25, x_84, x_85, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_4);
return x_86;
}
}
}
}
else
{
lean_object* x_87; uint8_t x_88; 
lean_dec(x_62);
x_87 = lean_mk_string_unchecked("natAbs", 6, 6);
x_88 = lean_string_dec_eq(x_61, x_87);
lean_dec(x_87);
lean_dec(x_61);
if (x_88 == 0)
{
lean_object* x_89; 
lean_dec(x_60);
lean_dec(x_23);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_24);
lean_ctor_set(x_89, 1, x_16);
return x_89;
}
else
{
lean_object* x_90; uint8_t x_91; 
x_90 = lean_array_get_size(x_60);
x_91 = lean_nat_dec_eq(x_90, x_4);
lean_dec(x_90);
if (x_91 == 0)
{
lean_object* x_92; 
lean_dec(x_60);
lean_dec(x_23);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_24);
lean_ctor_set(x_92, 1, x_16);
return x_92;
}
else
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_array_fget(x_60, x_6);
lean_dec(x_6);
lean_dec(x_60);
x_94 = l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__10(x_24, x_23, x_3, x_4, x_1, x_2, x_25, x_93, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_4);
return x_94;
}
}
}
}
}
else
{
uint8_t x_95; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_23);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_95 = !lean_is_exclusive(x_26);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_26, 1);
lean_dec(x_96);
x_97 = lean_ctor_get(x_26, 0);
lean_dec(x_97);
lean_ctor_set(x_26, 1, x_16);
lean_ctor_set(x_26, 0, x_24);
return x_26;
}
else
{
lean_object* x_98; 
lean_dec(x_26);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_24);
lean_ctor_set(x_98, 1, x_16);
return x_98;
}
}
}
else
{
uint8_t x_99; 
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_23);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_99 = !lean_is_exclusive(x_26);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_26, 1);
lean_dec(x_100);
x_101 = lean_ctor_get(x_26, 0);
lean_dec(x_101);
lean_ctor_set(x_26, 1, x_16);
lean_ctor_set(x_26, 0, x_24);
return x_26;
}
else
{
lean_object* x_102; 
lean_dec(x_26);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_24);
lean_ctor_set(x_102, 1, x_16);
return x_102;
}
}
}
else
{
uint8_t x_103; 
lean_dec(x_27);
lean_dec(x_23);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_103 = !lean_is_exclusive(x_26);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; 
x_104 = lean_ctor_get(x_26, 1);
lean_dec(x_104);
x_105 = lean_ctor_get(x_26, 0);
lean_dec(x_105);
lean_ctor_set(x_26, 1, x_16);
lean_ctor_set(x_26, 0, x_24);
return x_26;
}
else
{
lean_object* x_106; 
lean_dec(x_26);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_24);
lean_ctor_set(x_106, 1, x_16);
return x_106;
}
}
}
else
{
lean_object* x_107; lean_object* x_108; 
x_107 = l_Lean_Expr_getAppFnArgs(x_5);
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
if (lean_obj_tag(x_108) == 1)
{
lean_object* x_109; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
if (lean_obj_tag(x_109) == 1)
{
lean_object* x_110; 
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
if (lean_obj_tag(x_110) == 0)
{
uint8_t x_111; 
x_111 = !lean_is_exclusive(x_107);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; 
x_112 = lean_ctor_get(x_107, 1);
x_113 = lean_ctor_get(x_107, 0);
lean_dec(x_113);
x_114 = lean_ctor_get(x_108, 1);
lean_inc(x_114);
lean_dec(x_108);
x_115 = lean_ctor_get(x_109, 1);
lean_inc(x_115);
lean_dec(x_109);
x_116 = lean_mk_string_unchecked("HSub", 4, 4);
x_117 = lean_string_dec_eq(x_115, x_116);
lean_dec(x_116);
if (x_117 == 0)
{
uint8_t x_118; 
x_118 = lean_string_dec_eq(x_115, x_23);
if (x_118 == 0)
{
lean_object* x_119; uint8_t x_120; 
lean_dec(x_23);
x_119 = lean_mk_string_unchecked("Fin", 3, 3);
x_120 = lean_string_dec_eq(x_115, x_119);
lean_dec(x_119);
if (x_120 == 0)
{
lean_object* x_121; uint8_t x_122; 
x_121 = lean_mk_string_unchecked("BitVec", 6, 6);
x_122 = lean_string_dec_eq(x_115, x_121);
lean_dec(x_121);
lean_dec(x_115);
if (x_122 == 0)
{
lean_dec(x_114);
lean_dec(x_112);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_ctor_set(x_107, 1, x_16);
lean_ctor_set(x_107, 0, x_24);
return x_107;
}
else
{
lean_object* x_123; uint8_t x_124; 
x_123 = lean_mk_string_unchecked("toNat", 5, 5);
x_124 = lean_string_dec_eq(x_114, x_123);
lean_dec(x_123);
lean_dec(x_114);
if (x_124 == 0)
{
lean_dec(x_112);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_ctor_set(x_107, 1, x_16);
lean_ctor_set(x_107, 0, x_24);
return x_107;
}
else
{
lean_object* x_125; uint8_t x_126; 
x_125 = lean_array_get_size(x_112);
x_126 = lean_nat_dec_eq(x_125, x_1);
lean_dec(x_125);
if (x_126 == 0)
{
lean_dec(x_112);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_ctor_set(x_107, 1, x_16);
lean_ctor_set(x_107, 0, x_24);
return x_107;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_free_object(x_107);
x_127 = lean_array_fget(x_112, x_6);
lean_dec(x_6);
x_128 = lean_array_fget(x_112, x_4);
lean_dec(x_112);
x_129 = l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__9(x_24, x_3, x_4, x_1, x_2, x_25, x_127, x_128, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_4);
return x_129;
}
}
}
}
else
{
lean_object* x_130; uint8_t x_131; 
lean_dec(x_115);
x_130 = lean_mk_string_unchecked("val", 3, 3);
x_131 = lean_string_dec_eq(x_114, x_130);
lean_dec(x_130);
lean_dec(x_114);
if (x_131 == 0)
{
lean_dec(x_112);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_ctor_set(x_107, 1, x_16);
lean_ctor_set(x_107, 0, x_24);
return x_107;
}
else
{
lean_object* x_132; uint8_t x_133; 
x_132 = lean_array_get_size(x_112);
x_133 = lean_nat_dec_eq(x_132, x_1);
lean_dec(x_132);
if (x_133 == 0)
{
lean_dec(x_112);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_ctor_set(x_107, 1, x_16);
lean_ctor_set(x_107, 0, x_24);
return x_107;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_free_object(x_107);
x_134 = lean_array_fget(x_112, x_6);
lean_dec(x_6);
x_135 = lean_array_fget(x_112, x_4);
lean_dec(x_112);
x_136 = l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__8(x_24, x_3, x_4, x_1, x_2, x_25, x_134, x_135, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_4);
return x_136;
}
}
}
}
else
{
lean_object* x_137; uint8_t x_138; 
lean_dec(x_115);
x_137 = lean_mk_string_unchecked("natAbs", 6, 6);
x_138 = lean_string_dec_eq(x_114, x_137);
lean_dec(x_137);
lean_dec(x_114);
if (x_138 == 0)
{
lean_dec(x_112);
lean_dec(x_23);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_ctor_set(x_107, 1, x_16);
lean_ctor_set(x_107, 0, x_24);
return x_107;
}
else
{
lean_object* x_139; uint8_t x_140; 
x_139 = lean_array_get_size(x_112);
x_140 = lean_nat_dec_eq(x_139, x_4);
lean_dec(x_139);
if (x_140 == 0)
{
lean_dec(x_112);
lean_dec(x_23);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_ctor_set(x_107, 1, x_16);
lean_ctor_set(x_107, 0, x_24);
return x_107;
}
else
{
lean_object* x_141; lean_object* x_142; 
lean_free_object(x_107);
x_141 = lean_array_fget(x_112, x_6);
lean_dec(x_6);
lean_dec(x_112);
x_142 = l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__10(x_24, x_23, x_3, x_4, x_1, x_2, x_25, x_141, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_4);
return x_142;
}
}
}
}
else
{
lean_object* x_143; uint8_t x_144; 
lean_dec(x_115);
lean_dec(x_6);
x_143 = lean_mk_string_unchecked("hSub", 4, 4);
x_144 = lean_string_dec_eq(x_114, x_143);
lean_dec(x_143);
lean_dec(x_114);
if (x_144 == 0)
{
lean_dec(x_112);
lean_dec(x_23);
lean_dec(x_4);
lean_dec(x_3);
lean_ctor_set(x_107, 1, x_16);
lean_ctor_set(x_107, 0, x_24);
return x_107;
}
else
{
lean_object* x_145; lean_object* x_146; uint8_t x_147; 
x_145 = lean_array_get_size(x_112);
x_146 = lean_unsigned_to_nat(6u);
x_147 = lean_nat_dec_eq(x_145, x_146);
lean_dec(x_145);
if (x_147 == 0)
{
lean_dec(x_112);
lean_dec(x_23);
lean_dec(x_4);
lean_dec(x_3);
lean_ctor_set(x_107, 1, x_16);
lean_ctor_set(x_107, 0, x_24);
return x_107;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; uint64_t x_161; lean_object* x_162; uint64_t x_163; uint64_t x_164; uint64_t x_165; lean_object* x_166; uint64_t x_167; uint64_t x_168; uint64_t x_169; size_t x_170; size_t x_171; size_t x_172; size_t x_173; size_t x_174; lean_object* x_175; uint8_t x_176; 
x_148 = lean_ctor_get(x_24, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_24, 1);
lean_inc(x_149);
x_150 = lean_mk_string_unchecked("Lean", 4, 4);
x_151 = lean_mk_string_unchecked("Omega", 5, 5);
x_152 = lean_mk_string_unchecked("ofNat_sub_dichotomy", 19, 19);
x_153 = lean_unsigned_to_nat(4u);
x_154 = lean_unsigned_to_nat(5u);
x_155 = l_Lean_Name_mkStr4(x_150, x_151, x_23, x_152);
x_156 = lean_array_fget(x_112, x_153);
x_157 = lean_array_fget(x_112, x_154);
lean_dec(x_112);
x_158 = l_Lean_Expr_const___override(x_155, x_3);
x_159 = l_Lean_mkAppB(x_158, x_156, x_157);
x_160 = lean_array_get_size(x_149);
x_161 = l_Lean_Expr_hash(x_159);
x_162 = lean_unsigned_to_nat(32u);
x_163 = lean_uint64_of_nat(x_162);
x_164 = lean_uint64_shift_right(x_161, x_163);
x_165 = lean_uint64_xor(x_161, x_164);
x_166 = lean_unsigned_to_nat(16u);
x_167 = lean_uint64_of_nat(x_166);
x_168 = lean_uint64_shift_right(x_165, x_167);
x_169 = lean_uint64_xor(x_165, x_168);
x_170 = lean_uint64_to_usize(x_169);
x_171 = lean_usize_of_nat(x_160);
lean_dec(x_160);
x_172 = lean_usize_of_nat(x_4);
x_173 = lean_usize_sub(x_171, x_172);
x_174 = lean_usize_land(x_170, x_173);
x_175 = lean_array_uget(x_149, x_174);
x_176 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectMVars_visit_spec__0___redArg(x_159, x_175);
if (x_176 == 0)
{
uint8_t x_177; 
x_177 = !lean_is_exclusive(x_24);
if (x_177 == 0)
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; uint8_t x_187; 
x_178 = lean_ctor_get(x_24, 1);
lean_dec(x_178);
x_179 = lean_ctor_get(x_24, 0);
lean_dec(x_179);
x_180 = lean_box(0);
x_181 = lean_nat_add(x_148, x_4);
lean_dec(x_4);
lean_dec(x_148);
x_182 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_182, 0, x_159);
lean_ctor_set(x_182, 1, x_180);
lean_ctor_set(x_182, 2, x_175);
x_183 = lean_array_uset(x_149, x_174, x_182);
x_184 = lean_nat_shiftl(x_181, x_1);
x_185 = lean_nat_div(x_184, x_2);
lean_dec(x_184);
x_186 = lean_array_get_size(x_183);
x_187 = lean_nat_dec_le(x_185, x_186);
lean_dec(x_186);
lean_dec(x_185);
if (x_187 == 0)
{
lean_object* x_188; 
x_188 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectMVars_visit_spec__1(lean_box(0), x_183);
lean_ctor_set(x_24, 1, x_188);
lean_ctor_set(x_24, 0, x_181);
lean_ctor_set(x_107, 1, x_16);
lean_ctor_set(x_107, 0, x_24);
return x_107;
}
else
{
lean_ctor_set(x_24, 1, x_183);
lean_ctor_set(x_24, 0, x_181);
lean_ctor_set(x_107, 1, x_16);
lean_ctor_set(x_107, 0, x_24);
return x_107;
}
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; uint8_t x_196; 
lean_dec(x_24);
x_189 = lean_box(0);
x_190 = lean_nat_add(x_148, x_4);
lean_dec(x_4);
lean_dec(x_148);
x_191 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_191, 0, x_159);
lean_ctor_set(x_191, 1, x_189);
lean_ctor_set(x_191, 2, x_175);
x_192 = lean_array_uset(x_149, x_174, x_191);
x_193 = lean_nat_shiftl(x_190, x_1);
x_194 = lean_nat_div(x_193, x_2);
lean_dec(x_193);
x_195 = lean_array_get_size(x_192);
x_196 = lean_nat_dec_le(x_194, x_195);
lean_dec(x_195);
lean_dec(x_194);
if (x_196 == 0)
{
lean_object* x_197; lean_object* x_198; 
x_197 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectMVars_visit_spec__1(lean_box(0), x_192);
x_198 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_198, 0, x_190);
lean_ctor_set(x_198, 1, x_197);
lean_ctor_set(x_107, 1, x_16);
lean_ctor_set(x_107, 0, x_198);
return x_107;
}
else
{
lean_object* x_199; 
x_199 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_199, 0, x_190);
lean_ctor_set(x_199, 1, x_192);
lean_ctor_set(x_107, 1, x_16);
lean_ctor_set(x_107, 0, x_199);
return x_107;
}
}
}
else
{
lean_dec(x_175);
lean_dec(x_159);
lean_dec(x_149);
lean_dec(x_148);
lean_dec(x_4);
lean_ctor_set(x_107, 1, x_16);
lean_ctor_set(x_107, 0, x_24);
return x_107;
}
}
}
}
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; uint8_t x_204; 
x_200 = lean_ctor_get(x_107, 1);
lean_inc(x_200);
lean_dec(x_107);
x_201 = lean_ctor_get(x_108, 1);
lean_inc(x_201);
lean_dec(x_108);
x_202 = lean_ctor_get(x_109, 1);
lean_inc(x_202);
lean_dec(x_109);
x_203 = lean_mk_string_unchecked("HSub", 4, 4);
x_204 = lean_string_dec_eq(x_202, x_203);
lean_dec(x_203);
if (x_204 == 0)
{
uint8_t x_205; 
x_205 = lean_string_dec_eq(x_202, x_23);
if (x_205 == 0)
{
lean_object* x_206; uint8_t x_207; 
lean_dec(x_23);
x_206 = lean_mk_string_unchecked("Fin", 3, 3);
x_207 = lean_string_dec_eq(x_202, x_206);
lean_dec(x_206);
if (x_207 == 0)
{
lean_object* x_208; uint8_t x_209; 
x_208 = lean_mk_string_unchecked("BitVec", 6, 6);
x_209 = lean_string_dec_eq(x_202, x_208);
lean_dec(x_208);
lean_dec(x_202);
if (x_209 == 0)
{
lean_object* x_210; 
lean_dec(x_201);
lean_dec(x_200);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_210 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_210, 0, x_24);
lean_ctor_set(x_210, 1, x_16);
return x_210;
}
else
{
lean_object* x_211; uint8_t x_212; 
x_211 = lean_mk_string_unchecked("toNat", 5, 5);
x_212 = lean_string_dec_eq(x_201, x_211);
lean_dec(x_211);
lean_dec(x_201);
if (x_212 == 0)
{
lean_object* x_213; 
lean_dec(x_200);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_213 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_213, 0, x_24);
lean_ctor_set(x_213, 1, x_16);
return x_213;
}
else
{
lean_object* x_214; uint8_t x_215; 
x_214 = lean_array_get_size(x_200);
x_215 = lean_nat_dec_eq(x_214, x_1);
lean_dec(x_214);
if (x_215 == 0)
{
lean_object* x_216; 
lean_dec(x_200);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_216 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_216, 0, x_24);
lean_ctor_set(x_216, 1, x_16);
return x_216;
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_217 = lean_array_fget(x_200, x_6);
lean_dec(x_6);
x_218 = lean_array_fget(x_200, x_4);
lean_dec(x_200);
x_219 = l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__9(x_24, x_3, x_4, x_1, x_2, x_25, x_217, x_218, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_4);
return x_219;
}
}
}
}
else
{
lean_object* x_220; uint8_t x_221; 
lean_dec(x_202);
x_220 = lean_mk_string_unchecked("val", 3, 3);
x_221 = lean_string_dec_eq(x_201, x_220);
lean_dec(x_220);
lean_dec(x_201);
if (x_221 == 0)
{
lean_object* x_222; 
lean_dec(x_200);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_222 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_222, 0, x_24);
lean_ctor_set(x_222, 1, x_16);
return x_222;
}
else
{
lean_object* x_223; uint8_t x_224; 
x_223 = lean_array_get_size(x_200);
x_224 = lean_nat_dec_eq(x_223, x_1);
lean_dec(x_223);
if (x_224 == 0)
{
lean_object* x_225; 
lean_dec(x_200);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_225 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_225, 0, x_24);
lean_ctor_set(x_225, 1, x_16);
return x_225;
}
else
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_226 = lean_array_fget(x_200, x_6);
lean_dec(x_6);
x_227 = lean_array_fget(x_200, x_4);
lean_dec(x_200);
x_228 = l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__8(x_24, x_3, x_4, x_1, x_2, x_25, x_226, x_227, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_4);
return x_228;
}
}
}
}
else
{
lean_object* x_229; uint8_t x_230; 
lean_dec(x_202);
x_229 = lean_mk_string_unchecked("natAbs", 6, 6);
x_230 = lean_string_dec_eq(x_201, x_229);
lean_dec(x_229);
lean_dec(x_201);
if (x_230 == 0)
{
lean_object* x_231; 
lean_dec(x_200);
lean_dec(x_23);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_231 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_231, 0, x_24);
lean_ctor_set(x_231, 1, x_16);
return x_231;
}
else
{
lean_object* x_232; uint8_t x_233; 
x_232 = lean_array_get_size(x_200);
x_233 = lean_nat_dec_eq(x_232, x_4);
lean_dec(x_232);
if (x_233 == 0)
{
lean_object* x_234; 
lean_dec(x_200);
lean_dec(x_23);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_234 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_234, 0, x_24);
lean_ctor_set(x_234, 1, x_16);
return x_234;
}
else
{
lean_object* x_235; lean_object* x_236; 
x_235 = lean_array_fget(x_200, x_6);
lean_dec(x_6);
lean_dec(x_200);
x_236 = l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__10(x_24, x_23, x_3, x_4, x_1, x_2, x_25, x_235, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_4);
return x_236;
}
}
}
}
else
{
lean_object* x_237; uint8_t x_238; 
lean_dec(x_202);
lean_dec(x_6);
x_237 = lean_mk_string_unchecked("hSub", 4, 4);
x_238 = lean_string_dec_eq(x_201, x_237);
lean_dec(x_237);
lean_dec(x_201);
if (x_238 == 0)
{
lean_object* x_239; 
lean_dec(x_200);
lean_dec(x_23);
lean_dec(x_4);
lean_dec(x_3);
x_239 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_239, 0, x_24);
lean_ctor_set(x_239, 1, x_16);
return x_239;
}
else
{
lean_object* x_240; lean_object* x_241; uint8_t x_242; 
x_240 = lean_array_get_size(x_200);
x_241 = lean_unsigned_to_nat(6u);
x_242 = lean_nat_dec_eq(x_240, x_241);
lean_dec(x_240);
if (x_242 == 0)
{
lean_object* x_243; 
lean_dec(x_200);
lean_dec(x_23);
lean_dec(x_4);
lean_dec(x_3);
x_243 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_243, 0, x_24);
lean_ctor_set(x_243, 1, x_16);
return x_243;
}
else
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; uint64_t x_257; lean_object* x_258; uint64_t x_259; uint64_t x_260; uint64_t x_261; lean_object* x_262; uint64_t x_263; uint64_t x_264; uint64_t x_265; size_t x_266; size_t x_267; size_t x_268; size_t x_269; size_t x_270; lean_object* x_271; uint8_t x_272; 
x_244 = lean_ctor_get(x_24, 0);
lean_inc(x_244);
x_245 = lean_ctor_get(x_24, 1);
lean_inc(x_245);
x_246 = lean_mk_string_unchecked("Lean", 4, 4);
x_247 = lean_mk_string_unchecked("Omega", 5, 5);
x_248 = lean_mk_string_unchecked("ofNat_sub_dichotomy", 19, 19);
x_249 = lean_unsigned_to_nat(4u);
x_250 = lean_unsigned_to_nat(5u);
x_251 = l_Lean_Name_mkStr4(x_246, x_247, x_23, x_248);
x_252 = lean_array_fget(x_200, x_249);
x_253 = lean_array_fget(x_200, x_250);
lean_dec(x_200);
x_254 = l_Lean_Expr_const___override(x_251, x_3);
x_255 = l_Lean_mkAppB(x_254, x_252, x_253);
x_256 = lean_array_get_size(x_245);
x_257 = l_Lean_Expr_hash(x_255);
x_258 = lean_unsigned_to_nat(32u);
x_259 = lean_uint64_of_nat(x_258);
x_260 = lean_uint64_shift_right(x_257, x_259);
x_261 = lean_uint64_xor(x_257, x_260);
x_262 = lean_unsigned_to_nat(16u);
x_263 = lean_uint64_of_nat(x_262);
x_264 = lean_uint64_shift_right(x_261, x_263);
x_265 = lean_uint64_xor(x_261, x_264);
x_266 = lean_uint64_to_usize(x_265);
x_267 = lean_usize_of_nat(x_256);
lean_dec(x_256);
x_268 = lean_usize_of_nat(x_4);
x_269 = lean_usize_sub(x_267, x_268);
x_270 = lean_usize_land(x_266, x_269);
x_271 = lean_array_uget(x_245, x_270);
x_272 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectMVars_visit_spec__0___redArg(x_255, x_271);
if (x_272 == 0)
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; uint8_t x_281; 
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_273 = x_24;
} else {
 lean_dec_ref(x_24);
 x_273 = lean_box(0);
}
x_274 = lean_box(0);
x_275 = lean_nat_add(x_244, x_4);
lean_dec(x_4);
lean_dec(x_244);
x_276 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_276, 0, x_255);
lean_ctor_set(x_276, 1, x_274);
lean_ctor_set(x_276, 2, x_271);
x_277 = lean_array_uset(x_245, x_270, x_276);
x_278 = lean_nat_shiftl(x_275, x_1);
x_279 = lean_nat_div(x_278, x_2);
lean_dec(x_278);
x_280 = lean_array_get_size(x_277);
x_281 = lean_nat_dec_le(x_279, x_280);
lean_dec(x_280);
lean_dec(x_279);
if (x_281 == 0)
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; 
x_282 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectMVars_visit_spec__1(lean_box(0), x_277);
if (lean_is_scalar(x_273)) {
 x_283 = lean_alloc_ctor(0, 2, 0);
} else {
 x_283 = x_273;
}
lean_ctor_set(x_283, 0, x_275);
lean_ctor_set(x_283, 1, x_282);
x_284 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_284, 0, x_283);
lean_ctor_set(x_284, 1, x_16);
return x_284;
}
else
{
lean_object* x_285; lean_object* x_286; 
if (lean_is_scalar(x_273)) {
 x_285 = lean_alloc_ctor(0, 2, 0);
} else {
 x_285 = x_273;
}
lean_ctor_set(x_285, 0, x_275);
lean_ctor_set(x_285, 1, x_277);
x_286 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_286, 0, x_285);
lean_ctor_set(x_286, 1, x_16);
return x_286;
}
}
else
{
lean_object* x_287; 
lean_dec(x_271);
lean_dec(x_255);
lean_dec(x_245);
lean_dec(x_244);
lean_dec(x_4);
x_287 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_287, 0, x_24);
lean_ctor_set(x_287, 1, x_16);
return x_287;
}
}
}
}
}
}
else
{
uint8_t x_288; 
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_108);
lean_dec(x_23);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_288 = !lean_is_exclusive(x_107);
if (x_288 == 0)
{
lean_object* x_289; lean_object* x_290; 
x_289 = lean_ctor_get(x_107, 1);
lean_dec(x_289);
x_290 = lean_ctor_get(x_107, 0);
lean_dec(x_290);
lean_ctor_set(x_107, 1, x_16);
lean_ctor_set(x_107, 0, x_24);
return x_107;
}
else
{
lean_object* x_291; 
lean_dec(x_107);
x_291 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_291, 0, x_24);
lean_ctor_set(x_291, 1, x_16);
return x_291;
}
}
}
else
{
uint8_t x_292; 
lean_dec(x_109);
lean_dec(x_108);
lean_dec(x_23);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_292 = !lean_is_exclusive(x_107);
if (x_292 == 0)
{
lean_object* x_293; lean_object* x_294; 
x_293 = lean_ctor_get(x_107, 1);
lean_dec(x_293);
x_294 = lean_ctor_get(x_107, 0);
lean_dec(x_294);
lean_ctor_set(x_107, 1, x_16);
lean_ctor_set(x_107, 0, x_24);
return x_107;
}
else
{
lean_object* x_295; 
lean_dec(x_107);
x_295 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_295, 0, x_24);
lean_ctor_set(x_295, 1, x_16);
return x_295;
}
}
}
else
{
uint8_t x_296; 
lean_dec(x_108);
lean_dec(x_23);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_296 = !lean_is_exclusive(x_107);
if (x_296 == 0)
{
lean_object* x_297; lean_object* x_298; 
x_297 = lean_ctor_get(x_107, 1);
lean_dec(x_297);
x_298 = lean_ctor_get(x_107, 0);
lean_dec(x_298);
lean_ctor_set(x_107, 1, x_16);
lean_ctor_set(x_107, 0, x_24);
return x_107;
}
else
{
lean_object* x_299; 
lean_dec(x_107);
x_299 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_299, 0, x_24);
lean_ctor_set(x_299, 1, x_16);
return x_299;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, uint8_t x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_8);
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
lean_dec(x_1);
x_20 = l_Lean_Name_str___override(x_2, x_3);
x_21 = l_Lean_Name_str___override(x_20, x_4);
x_22 = l_Lean_Expr_bvar___override(x_19);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_array_fget(x_5, x_23);
x_25 = lean_unsigned_to_nat(2u);
x_26 = lean_array_fget(x_5, x_25);
x_27 = lean_mk_empty_array_with_capacity(x_6);
lean_dec(x_6);
x_28 = lean_array_push(x_27, x_22);
x_29 = lean_array_push(x_28, x_24);
x_30 = lean_array_push(x_29, x_26);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_21);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_box(x_12);
x_33 = lean_apply_11(x_7, x_31, x_9, x_10, x_11, x_32, x_13, x_14, x_15, x_16, x_17, x_18);
return x_33;
}
case 1:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_8);
x_34 = lean_ctor_get(x_1, 0);
lean_inc(x_34);
lean_dec(x_1);
x_35 = l_Lean_Name_str___override(x_2, x_3);
x_36 = l_Lean_Name_str___override(x_35, x_4);
x_37 = l_Lean_Expr_fvar___override(x_34);
x_38 = lean_unsigned_to_nat(1u);
x_39 = lean_array_fget(x_5, x_38);
x_40 = lean_unsigned_to_nat(2u);
x_41 = lean_array_fget(x_5, x_40);
x_42 = lean_mk_empty_array_with_capacity(x_6);
lean_dec(x_6);
x_43 = lean_array_push(x_42, x_37);
x_44 = lean_array_push(x_43, x_39);
x_45 = lean_array_push(x_44, x_41);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_36);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_box(x_12);
x_48 = lean_apply_11(x_7, x_46, x_9, x_10, x_11, x_47, x_13, x_14, x_15, x_16, x_17, x_18);
return x_48;
}
case 2:
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_8);
x_49 = lean_ctor_get(x_1, 0);
lean_inc(x_49);
lean_dec(x_1);
x_50 = l_Lean_Name_str___override(x_2, x_3);
x_51 = l_Lean_Name_str___override(x_50, x_4);
x_52 = l_Lean_Expr_mvar___override(x_49);
x_53 = lean_unsigned_to_nat(1u);
x_54 = lean_array_fget(x_5, x_53);
x_55 = lean_unsigned_to_nat(2u);
x_56 = lean_array_fget(x_5, x_55);
x_57 = lean_mk_empty_array_with_capacity(x_6);
lean_dec(x_6);
x_58 = lean_array_push(x_57, x_52);
x_59 = lean_array_push(x_58, x_54);
x_60 = lean_array_push(x_59, x_56);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_51);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_box(x_12);
x_63 = lean_apply_11(x_7, x_61, x_9, x_10, x_11, x_62, x_13, x_14, x_15, x_16, x_17, x_18);
return x_63;
}
case 3:
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_8);
x_64 = lean_ctor_get(x_1, 0);
lean_inc(x_64);
lean_dec(x_1);
x_65 = l_Lean_Name_str___override(x_2, x_3);
x_66 = l_Lean_Name_str___override(x_65, x_4);
x_67 = l_Lean_Expr_sort___override(x_64);
x_68 = lean_unsigned_to_nat(1u);
x_69 = lean_array_fget(x_5, x_68);
x_70 = lean_unsigned_to_nat(2u);
x_71 = lean_array_fget(x_5, x_70);
x_72 = lean_mk_empty_array_with_capacity(x_6);
lean_dec(x_6);
x_73 = lean_array_push(x_72, x_67);
x_74 = lean_array_push(x_73, x_69);
x_75 = lean_array_push(x_74, x_71);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_66);
lean_ctor_set(x_76, 1, x_75);
x_77 = lean_box(x_12);
x_78 = lean_apply_11(x_7, x_76, x_9, x_10, x_11, x_77, x_13, x_14, x_15, x_16, x_17, x_18);
return x_78;
}
case 4:
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_79 = lean_ctor_get(x_1, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_1, 1);
lean_inc(x_80);
lean_dec(x_1);
lean_inc(x_2);
x_81 = l_Lean_Name_str___override(x_2, x_3);
x_82 = l_Lean_Name_str___override(x_81, x_4);
lean_inc(x_80);
lean_inc(x_2);
x_83 = l_Lean_Expr_const___override(x_2, x_80);
x_84 = lean_unsigned_to_nat(1u);
x_85 = lean_array_fget(x_5, x_84);
x_86 = lean_unsigned_to_nat(2u);
x_87 = lean_array_fget(x_5, x_86);
x_88 = lean_mk_empty_array_with_capacity(x_6);
lean_inc(x_88);
x_89 = lean_array_push(x_88, x_83);
lean_inc(x_85);
x_90 = lean_array_push(x_89, x_85);
switch (lean_obj_tag(x_79)) {
case 0:
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_88);
lean_dec(x_85);
lean_dec(x_80);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
x_91 = lean_array_push(x_90, x_87);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_82);
lean_ctor_set(x_92, 1, x_91);
x_93 = lean_box(x_12);
x_94 = lean_apply_11(x_7, x_92, x_9, x_10, x_11, x_93, x_13, x_14, x_15, x_16, x_17, x_18);
return x_94;
}
case 1:
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_123; lean_object* x_126; uint8_t x_127; 
lean_dec(x_90);
x_95 = lean_ctor_get(x_79, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_79, 1);
lean_inc(x_96);
lean_dec(x_79);
x_126 = lean_mk_string_unchecked("Int", 3, 3);
x_127 = lean_string_dec_eq(x_96, x_126);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
lean_dec(x_126);
lean_dec(x_8);
lean_dec(x_6);
lean_inc(x_96);
x_128 = l_Lean_Name_str___override(x_2, x_96);
lean_inc(x_80);
x_129 = l_Lean_Expr_const___override(x_128, x_80);
lean_inc(x_88);
x_130 = lean_array_push(x_88, x_129);
lean_inc(x_85);
x_131 = lean_array_push(x_130, x_85);
lean_inc(x_87);
x_132 = lean_array_push(x_131, x_87);
lean_inc(x_82);
x_133 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_133, 0, x_82);
lean_ctor_set(x_133, 1, x_132);
x_123 = x_133;
goto block_125;
}
else
{
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_134; 
lean_dec(x_126);
lean_dec(x_2);
lean_inc(x_87);
x_134 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__11___boxed), 16, 6);
lean_closure_set(x_134, 0, x_86);
lean_closure_set(x_134, 1, x_6);
lean_closure_set(x_134, 2, x_80);
lean_closure_set(x_134, 3, x_84);
lean_closure_set(x_134, 4, x_87);
lean_closure_set(x_134, 5, x_8);
x_97 = x_134;
goto block_122;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
lean_dec(x_8);
lean_dec(x_6);
x_135 = l_Lean_Name_str___override(x_2, x_126);
lean_inc(x_80);
x_136 = l_Lean_Expr_const___override(x_135, x_80);
lean_inc(x_88);
x_137 = lean_array_push(x_88, x_136);
lean_inc(x_85);
x_138 = lean_array_push(x_137, x_85);
lean_inc(x_87);
x_139 = lean_array_push(x_138, x_87);
lean_inc(x_82);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_82);
lean_ctor_set(x_140, 1, x_139);
x_123 = x_140;
goto block_125;
}
}
block_122:
{
switch (lean_obj_tag(x_95)) {
case 0:
{
lean_object* x_98; lean_object* x_99; 
lean_dec(x_96);
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_85);
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_7);
x_98 = lean_box(x_12);
x_99 = lean_apply_10(x_97, x_9, x_10, x_11, x_98, x_13, x_14, x_15, x_16, x_17, x_18);
return x_99;
}
case 1:
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_dec(x_97);
x_100 = lean_ctor_get(x_95, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_95, 1);
lean_inc(x_101);
lean_dec(x_95);
x_102 = l_Lean_Name_str___override(x_100, x_101);
x_103 = l_Lean_Name_str___override(x_102, x_96);
x_104 = l_Lean_Expr_const___override(x_103, x_80);
x_105 = lean_array_push(x_88, x_104);
x_106 = lean_array_push(x_105, x_85);
x_107 = lean_array_push(x_106, x_87);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_82);
lean_ctor_set(x_108, 1, x_107);
x_109 = lean_box(x_12);
x_110 = lean_apply_11(x_7, x_108, x_9, x_10, x_11, x_109, x_13, x_14, x_15, x_16, x_17, x_18);
return x_110;
}
default: 
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec(x_97);
x_111 = lean_ctor_get(x_95, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_95, 1);
lean_inc(x_112);
lean_dec(x_95);
x_113 = l_Lean_Name_num___override(x_111, x_112);
x_114 = l_Lean_Name_str___override(x_113, x_96);
x_115 = l_Lean_Expr_const___override(x_114, x_80);
x_116 = lean_array_push(x_88, x_115);
x_117 = lean_array_push(x_116, x_85);
x_118 = lean_array_push(x_117, x_87);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_82);
lean_ctor_set(x_119, 1, x_118);
x_120 = lean_box(x_12);
x_121 = lean_apply_11(x_7, x_119, x_9, x_10, x_11, x_120, x_13, x_14, x_15, x_16, x_17, x_18);
return x_121;
}
}
}
block_125:
{
lean_object* x_124; 
lean_inc(x_7);
x_124 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__3___boxed), 12, 2);
lean_closure_set(x_124, 0, x_7);
lean_closure_set(x_124, 1, x_123);
x_97 = x_124;
goto block_122;
}
}
default: 
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec(x_90);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
x_141 = lean_ctor_get(x_79, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_79, 1);
lean_inc(x_142);
lean_dec(x_79);
x_143 = l_Lean_Name_num___override(x_141, x_142);
x_144 = l_Lean_Expr_const___override(x_143, x_80);
x_145 = lean_array_push(x_88, x_144);
x_146 = lean_array_push(x_145, x_85);
x_147 = lean_array_push(x_146, x_87);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_82);
lean_ctor_set(x_148, 1, x_147);
x_149 = lean_box(x_12);
x_150 = lean_apply_11(x_7, x_148, x_9, x_10, x_11, x_149, x_13, x_14, x_15, x_16, x_17, x_18);
return x_150;
}
}
}
case 5:
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_dec(x_8);
x_151 = lean_ctor_get(x_1, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_1, 1);
lean_inc(x_152);
lean_dec(x_1);
x_153 = l_Lean_Name_str___override(x_2, x_3);
x_154 = l_Lean_Name_str___override(x_153, x_4);
x_155 = l_Lean_Expr_app___override(x_151, x_152);
x_156 = lean_unsigned_to_nat(1u);
x_157 = lean_array_fget(x_5, x_156);
x_158 = lean_unsigned_to_nat(2u);
x_159 = lean_array_fget(x_5, x_158);
x_160 = lean_mk_empty_array_with_capacity(x_6);
lean_dec(x_6);
x_161 = lean_array_push(x_160, x_155);
x_162 = lean_array_push(x_161, x_157);
x_163 = lean_array_push(x_162, x_159);
x_164 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_164, 0, x_154);
lean_ctor_set(x_164, 1, x_163);
x_165 = lean_box(x_12);
x_166 = lean_apply_11(x_7, x_164, x_9, x_10, x_11, x_165, x_13, x_14, x_15, x_16, x_17, x_18);
return x_166;
}
case 6:
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
lean_dec(x_8);
x_167 = lean_ctor_get(x_1, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_1, 1);
lean_inc(x_168);
x_169 = lean_ctor_get(x_1, 2);
lean_inc(x_169);
x_170 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec(x_1);
x_171 = l_Lean_Name_str___override(x_2, x_3);
x_172 = l_Lean_Name_str___override(x_171, x_4);
x_173 = l_Lean_Expr_lam___override(x_167, x_168, x_169, x_170);
x_174 = lean_unsigned_to_nat(1u);
x_175 = lean_array_fget(x_5, x_174);
x_176 = lean_unsigned_to_nat(2u);
x_177 = lean_array_fget(x_5, x_176);
x_178 = lean_mk_empty_array_with_capacity(x_6);
lean_dec(x_6);
x_179 = lean_array_push(x_178, x_173);
x_180 = lean_array_push(x_179, x_175);
x_181 = lean_array_push(x_180, x_177);
x_182 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_182, 0, x_172);
lean_ctor_set(x_182, 1, x_181);
x_183 = lean_box(x_12);
x_184 = lean_apply_11(x_7, x_182, x_9, x_10, x_11, x_183, x_13, x_14, x_15, x_16, x_17, x_18);
return x_184;
}
case 7:
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; uint8_t x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
lean_dec(x_8);
x_185 = lean_ctor_get(x_1, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_1, 1);
lean_inc(x_186);
x_187 = lean_ctor_get(x_1, 2);
lean_inc(x_187);
x_188 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec(x_1);
x_189 = l_Lean_Name_str___override(x_2, x_3);
x_190 = l_Lean_Name_str___override(x_189, x_4);
x_191 = l_Lean_Expr_forallE___override(x_185, x_186, x_187, x_188);
x_192 = lean_unsigned_to_nat(1u);
x_193 = lean_array_fget(x_5, x_192);
x_194 = lean_unsigned_to_nat(2u);
x_195 = lean_array_fget(x_5, x_194);
x_196 = lean_mk_empty_array_with_capacity(x_6);
lean_dec(x_6);
x_197 = lean_array_push(x_196, x_191);
x_198 = lean_array_push(x_197, x_193);
x_199 = lean_array_push(x_198, x_195);
x_200 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_200, 0, x_190);
lean_ctor_set(x_200, 1, x_199);
x_201 = lean_box(x_12);
x_202 = lean_apply_11(x_7, x_200, x_9, x_10, x_11, x_201, x_13, x_14, x_15, x_16, x_17, x_18);
return x_202;
}
case 8:
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; uint8_t x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
lean_dec(x_8);
x_203 = lean_ctor_get(x_1, 0);
lean_inc(x_203);
x_204 = lean_ctor_get(x_1, 1);
lean_inc(x_204);
x_205 = lean_ctor_get(x_1, 2);
lean_inc(x_205);
x_206 = lean_ctor_get(x_1, 3);
lean_inc(x_206);
x_207 = lean_ctor_get_uint8(x_1, sizeof(void*)*4 + 8);
lean_dec(x_1);
x_208 = l_Lean_Name_str___override(x_2, x_3);
x_209 = l_Lean_Name_str___override(x_208, x_4);
x_210 = l_Lean_Expr_letE___override(x_203, x_204, x_205, x_206, x_207);
x_211 = lean_unsigned_to_nat(1u);
x_212 = lean_array_fget(x_5, x_211);
x_213 = lean_unsigned_to_nat(2u);
x_214 = lean_array_fget(x_5, x_213);
x_215 = lean_mk_empty_array_with_capacity(x_6);
lean_dec(x_6);
x_216 = lean_array_push(x_215, x_210);
x_217 = lean_array_push(x_216, x_212);
x_218 = lean_array_push(x_217, x_214);
x_219 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_219, 0, x_209);
lean_ctor_set(x_219, 1, x_218);
x_220 = lean_box(x_12);
x_221 = lean_apply_11(x_7, x_219, x_9, x_10, x_11, x_220, x_13, x_14, x_15, x_16, x_17, x_18);
return x_221;
}
case 9:
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; 
lean_dec(x_8);
x_222 = lean_ctor_get(x_1, 0);
lean_inc(x_222);
lean_dec(x_1);
x_223 = l_Lean_Name_str___override(x_2, x_3);
x_224 = l_Lean_Name_str___override(x_223, x_4);
x_225 = l_Lean_Expr_lit___override(x_222);
x_226 = lean_unsigned_to_nat(1u);
x_227 = lean_array_fget(x_5, x_226);
x_228 = lean_unsigned_to_nat(2u);
x_229 = lean_array_fget(x_5, x_228);
x_230 = lean_mk_empty_array_with_capacity(x_6);
lean_dec(x_6);
x_231 = lean_array_push(x_230, x_225);
x_232 = lean_array_push(x_231, x_227);
x_233 = lean_array_push(x_232, x_229);
x_234 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_234, 0, x_224);
lean_ctor_set(x_234, 1, x_233);
x_235 = lean_box(x_12);
x_236 = lean_apply_11(x_7, x_234, x_9, x_10, x_11, x_235, x_13, x_14, x_15, x_16, x_17, x_18);
return x_236;
}
case 10:
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
lean_dec(x_8);
x_237 = lean_ctor_get(x_1, 0);
lean_inc(x_237);
x_238 = lean_ctor_get(x_1, 1);
lean_inc(x_238);
lean_dec(x_1);
x_239 = l_Lean_Name_str___override(x_2, x_3);
x_240 = l_Lean_Name_str___override(x_239, x_4);
x_241 = l_Lean_Expr_mdata___override(x_237, x_238);
x_242 = lean_unsigned_to_nat(1u);
x_243 = lean_array_fget(x_5, x_242);
x_244 = lean_unsigned_to_nat(2u);
x_245 = lean_array_fget(x_5, x_244);
x_246 = lean_mk_empty_array_with_capacity(x_6);
lean_dec(x_6);
x_247 = lean_array_push(x_246, x_241);
x_248 = lean_array_push(x_247, x_243);
x_249 = lean_array_push(x_248, x_245);
x_250 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_250, 0, x_240);
lean_ctor_set(x_250, 1, x_249);
x_251 = lean_box(x_12);
x_252 = lean_apply_11(x_7, x_250, x_9, x_10, x_11, x_251, x_13, x_14, x_15, x_16, x_17, x_18);
return x_252;
}
default: 
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; 
lean_dec(x_8);
x_253 = lean_ctor_get(x_1, 0);
lean_inc(x_253);
x_254 = lean_ctor_get(x_1, 1);
lean_inc(x_254);
x_255 = lean_ctor_get(x_1, 2);
lean_inc(x_255);
lean_dec(x_1);
x_256 = l_Lean_Name_str___override(x_2, x_3);
x_257 = l_Lean_Name_str___override(x_256, x_4);
x_258 = l_Lean_Expr_proj___override(x_253, x_254, x_255);
x_259 = lean_unsigned_to_nat(1u);
x_260 = lean_array_fget(x_5, x_259);
x_261 = lean_unsigned_to_nat(2u);
x_262 = lean_array_fget(x_5, x_261);
x_263 = lean_mk_empty_array_with_capacity(x_6);
lean_dec(x_6);
x_264 = lean_array_push(x_263, x_258);
x_265 = lean_array_push(x_264, x_260);
x_266 = lean_array_push(x_265, x_262);
x_267 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_267, 0, x_257);
lean_ctor_set(x_267, 1, x_266);
x_268 = lean_box(x_12);
x_269 = lean_apply_11(x_7, x_267, x_9, x_10, x_11, x_268, x_13, x_14, x_15, x_16, x_17, x_18);
return x_269;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__15(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, uint8_t x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19) {
_start:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_20 = lean_mk_string_unchecked("Int", 3, 3);
x_21 = l_Lean_Name_mkStr1(x_20);
x_22 = lean_box(0);
x_23 = l_Lean_Expr_const___override(x_21, x_22);
x_24 = lean_expr_eqv(x_1, x_23);
lean_dec(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_25 = lean_unsigned_to_nat(8u);
x_26 = lean_nat_shiftl(x_25, x_2);
x_27 = lean_nat_div(x_26, x_3);
lean_dec(x_26);
x_28 = l_Nat_nextPowerOfTwo(x_27);
lean_dec(x_27);
x_29 = lean_box(0);
x_30 = lean_mk_array(x_28, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_4);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_19);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint64_t x_48; lean_object* x_49; uint64_t x_50; uint64_t x_51; uint64_t x_52; lean_object* x_53; uint64_t x_54; uint64_t x_55; uint64_t x_56; size_t x_57; size_t x_58; size_t x_59; size_t x_60; size_t x_61; lean_object* x_62; uint8_t x_63; 
x_33 = lean_unsigned_to_nat(8u);
x_34 = lean_nat_shiftl(x_33, x_2);
x_35 = lean_nat_div(x_34, x_3);
lean_dec(x_34);
x_36 = l_Nat_nextPowerOfTwo(x_35);
lean_dec(x_35);
x_37 = lean_box(0);
x_38 = lean_mk_array(x_36, x_37);
x_39 = lean_mk_string_unchecked("Lean", 4, 4);
x_40 = lean_mk_string_unchecked("Omega", 5, 5);
x_41 = lean_mk_string_unchecked("ite_disjunction", 15, 15);
x_42 = l_Lean_Name_mkStr3(x_39, x_40, x_41);
x_43 = l_Lean_Level_ofNat(x_4);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_22);
x_45 = l_Lean_Expr_const___override(x_42, x_44);
x_46 = l_Lean_mkApp5(x_45, x_1, x_5, x_6, x_7, x_8);
x_47 = lean_array_get_size(x_38);
x_48 = l_Lean_Expr_hash(x_46);
x_49 = lean_unsigned_to_nat(32u);
x_50 = lean_uint64_of_nat(x_49);
x_51 = lean_uint64_shift_right(x_48, x_50);
x_52 = lean_uint64_xor(x_48, x_51);
x_53 = lean_unsigned_to_nat(16u);
x_54 = lean_uint64_of_nat(x_53);
x_55 = lean_uint64_shift_right(x_52, x_54);
x_56 = lean_uint64_xor(x_52, x_55);
x_57 = lean_uint64_to_usize(x_56);
x_58 = lean_usize_of_nat(x_47);
lean_dec(x_47);
x_59 = lean_usize_of_nat(x_9);
x_60 = lean_usize_sub(x_58, x_59);
x_61 = lean_usize_land(x_57, x_60);
x_62 = lean_array_uget(x_38, x_61);
x_63 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectMVars_visit_spec__0___redArg(x_46, x_62);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
lean_dec(x_4);
x_64 = lean_box(0);
x_65 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_65, 0, x_46);
lean_ctor_set(x_65, 1, x_64);
lean_ctor_set(x_65, 2, x_62);
x_66 = lean_array_uset(x_38, x_61, x_65);
x_67 = lean_nat_shiftl(x_9, x_2);
x_68 = lean_nat_div(x_67, x_3);
lean_dec(x_67);
x_69 = lean_array_get_size(x_66);
x_70 = lean_nat_dec_le(x_68, x_69);
lean_dec(x_69);
lean_dec(x_68);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectMVars_visit_spec__1(lean_box(0), x_66);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_9);
lean_ctor_set(x_72, 1, x_71);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_19);
return x_73;
}
else
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_9);
lean_ctor_set(x_74, 1, x_66);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_19);
return x_75;
}
}
else
{
lean_object* x_76; lean_object* x_77; 
lean_dec(x_62);
lean_dec(x_46);
lean_dec(x_9);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_4);
lean_ctor_set(x_76, 1, x_38);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_19);
return x_77;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = l_Lean_Expr_getAppFnArgs(x_1);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_15 = x_12;
} else {
 lean_dec_ref(x_12);
 x_15 = lean_box(0);
}
x_16 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__0___boxed), 11, 0);
x_17 = lean_box(0);
switch (lean_obj_tag(x_13)) {
case 0:
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_16);
if (lean_is_scalar(x_15)) {
 x_18 = lean_alloc_ctor(0, 2, 0);
} else {
 x_18 = x_15;
}
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_14);
x_19 = l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__0(x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_18);
return x_19;
}
case 1:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_47; lean_object* x_91; uint8_t x_92; 
x_20 = lean_ctor_get(x_13, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_dec(x_13);
x_91 = lean_mk_string_unchecked("ite", 3, 3);
x_92 = lean_string_dec_eq(x_21, x_91);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_91);
lean_inc(x_21);
x_93 = l_Lean_Name_str___override(x_17, x_21);
lean_inc(x_14);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_14);
lean_inc(x_16);
x_95 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__7___boxed), 12, 2);
lean_closure_set(x_95, 0, x_16);
lean_closure_set(x_95, 1, x_94);
x_47 = x_95;
goto block_90;
}
else
{
lean_object* x_96; lean_object* x_97; uint8_t x_98; 
x_96 = lean_array_get_size(x_14);
x_97 = lean_unsigned_to_nat(5u);
x_98 = lean_nat_dec_eq(x_96, x_97);
lean_dec(x_96);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = l_Lean_Name_str___override(x_17, x_91);
lean_inc(x_14);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_14);
lean_inc(x_16);
x_101 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__7___boxed), 12, 2);
lean_closure_set(x_101, 0, x_16);
lean_closure_set(x_101, 1, x_100);
x_47 = x_101;
goto block_90;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_91);
x_102 = lean_unsigned_to_nat(0u);
x_103 = lean_array_fget(x_14, x_102);
x_104 = lean_unsigned_to_nat(1u);
x_105 = lean_array_fget(x_14, x_104);
x_106 = lean_unsigned_to_nat(2u);
x_107 = lean_array_fget(x_14, x_106);
x_108 = lean_unsigned_to_nat(3u);
x_109 = lean_array_fget(x_14, x_108);
x_110 = lean_unsigned_to_nat(4u);
x_111 = lean_array_fget(x_14, x_110);
x_112 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__15___boxed), 19, 9);
lean_closure_set(x_112, 0, x_103);
lean_closure_set(x_112, 1, x_106);
lean_closure_set(x_112, 2, x_108);
lean_closure_set(x_112, 3, x_102);
lean_closure_set(x_112, 4, x_105);
lean_closure_set(x_112, 5, x_107);
lean_closure_set(x_112, 6, x_109);
lean_closure_set(x_112, 7, x_111);
lean_closure_set(x_112, 8, x_104);
x_47 = x_112;
goto block_90;
}
}
block_41:
{
switch (lean_obj_tag(x_22)) {
case 0:
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_14);
x_25 = lean_box(x_5);
x_26 = lean_apply_10(x_24, x_2, x_3, x_4, x_25, x_6, x_7, x_8, x_9, x_10, x_11);
return x_26;
}
case 1:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_24);
x_27 = lean_ctor_get(x_22, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_22, 1);
lean_inc(x_28);
lean_dec(x_22);
x_29 = l_Lean_Name_str___override(x_27, x_28);
x_30 = l_Lean_Name_str___override(x_29, x_23);
x_31 = l_Lean_Name_str___override(x_30, x_21);
if (lean_is_scalar(x_15)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_15;
}
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_14);
x_33 = l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__0(x_32, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_32);
return x_33;
}
default: 
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_24);
x_34 = lean_ctor_get(x_22, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_22, 1);
lean_inc(x_35);
lean_dec(x_22);
x_36 = l_Lean_Name_num___override(x_34, x_35);
x_37 = l_Lean_Name_str___override(x_36, x_23);
x_38 = l_Lean_Name_str___override(x_37, x_21);
if (lean_is_scalar(x_15)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_15;
}
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_14);
x_40 = l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__0(x_39, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_39);
return x_40;
}
}
}
block_46:
{
lean_object* x_45; 
x_45 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__3___boxed), 12, 2);
lean_closure_set(x_45, 0, x_16);
lean_closure_set(x_45, 1, x_44);
x_22 = x_42;
x_23 = x_43;
x_24 = x_45;
goto block_41;
}
block_90:
{
switch (lean_obj_tag(x_20)) {
case 0:
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_21);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
x_48 = lean_box(x_5);
x_49 = lean_apply_10(x_47, x_2, x_3, x_4, x_48, x_6, x_7, x_8, x_9, x_10, x_11);
return x_49;
}
case 1:
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
lean_dec(x_47);
x_50 = lean_ctor_get(x_20, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_20, 1);
lean_inc(x_51);
lean_dec(x_20);
x_52 = lean_mk_string_unchecked("Nat", 3, 3);
x_53 = lean_string_dec_eq(x_51, x_52);
if (x_53 == 0)
{
lean_object* x_54; uint8_t x_55; 
x_54 = lean_mk_string_unchecked("HDiv", 4, 4);
x_55 = lean_string_dec_eq(x_51, x_54);
if (x_55 == 0)
{
lean_object* x_56; uint8_t x_57; 
lean_dec(x_54);
x_56 = lean_mk_string_unchecked("HMod", 4, 4);
x_57 = lean_string_dec_eq(x_51, x_56);
if (x_57 == 0)
{
lean_object* x_58; uint8_t x_59; 
lean_dec(x_56);
lean_dec(x_52);
x_58 = lean_mk_string_unchecked("Min", 3, 3);
x_59 = lean_string_dec_eq(x_51, x_58);
if (x_59 == 0)
{
lean_object* x_60; uint8_t x_61; 
lean_dec(x_58);
x_60 = lean_mk_string_unchecked("Max", 3, 3);
x_61 = lean_string_dec_eq(x_51, x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_60);
lean_inc(x_51);
x_62 = l_Lean_Name_str___override(x_17, x_51);
lean_inc(x_21);
x_63 = l_Lean_Name_str___override(x_62, x_21);
lean_inc(x_14);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_14);
x_42 = x_50;
x_43 = x_51;
x_44 = x_64;
goto block_46;
}
else
{
lean_object* x_65; 
lean_inc(x_14);
lean_inc(x_21);
x_65 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__1___boxed), 15, 5);
lean_closure_set(x_65, 0, x_21);
lean_closure_set(x_65, 1, x_17);
lean_closure_set(x_65, 2, x_60);
lean_closure_set(x_65, 3, x_14);
lean_closure_set(x_65, 4, x_16);
x_22 = x_50;
x_23 = x_51;
x_24 = x_65;
goto block_41;
}
}
else
{
lean_object* x_66; 
lean_inc(x_14);
lean_inc(x_21);
x_66 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__2___boxed), 15, 5);
lean_closure_set(x_66, 0, x_21);
lean_closure_set(x_66, 1, x_17);
lean_closure_set(x_66, 2, x_58);
lean_closure_set(x_66, 3, x_14);
lean_closure_set(x_66, 4, x_16);
x_22 = x_50;
x_23 = x_51;
x_24 = x_66;
goto block_41;
}
}
else
{
lean_object* x_67; 
lean_inc_n(x_16, 2);
lean_inc(x_14);
lean_inc(x_21);
x_67 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__5___boxed), 18, 8);
lean_closure_set(x_67, 0, x_21);
lean_closure_set(x_67, 1, x_17);
lean_closure_set(x_67, 2, x_56);
lean_closure_set(x_67, 3, x_14);
lean_closure_set(x_67, 4, x_16);
lean_closure_set(x_67, 5, x_16);
lean_closure_set(x_67, 6, x_52);
lean_closure_set(x_67, 7, x_16);
x_22 = x_50;
x_23 = x_51;
x_24 = x_67;
goto block_41;
}
}
else
{
lean_object* x_68; 
lean_dec(x_52);
lean_inc(x_14);
lean_inc(x_21);
x_68 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__6___boxed), 15, 5);
lean_closure_set(x_68, 0, x_21);
lean_closure_set(x_68, 1, x_17);
lean_closure_set(x_68, 2, x_54);
lean_closure_set(x_68, 3, x_14);
lean_closure_set(x_68, 4, x_16);
x_22 = x_50;
x_23 = x_51;
x_24 = x_68;
goto block_41;
}
}
else
{
lean_object* x_69; uint8_t x_70; 
x_69 = lean_mk_string_unchecked("cast", 4, 4);
x_70 = lean_string_dec_eq(x_21, x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_69);
x_71 = l_Lean_Name_str___override(x_17, x_52);
lean_inc(x_21);
x_72 = l_Lean_Name_str___override(x_71, x_21);
lean_inc(x_14);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_14);
x_42 = x_50;
x_43 = x_51;
x_44 = x_73;
goto block_46;
}
else
{
lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_74 = lean_array_get_size(x_14);
x_75 = lean_unsigned_to_nat(3u);
x_76 = lean_nat_dec_eq(x_74, x_75);
lean_dec(x_74);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_77 = l_Lean_Name_str___override(x_17, x_52);
x_78 = l_Lean_Name_str___override(x_77, x_69);
lean_inc(x_14);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_14);
x_80 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__7___boxed), 12, 2);
lean_closure_set(x_80, 0, x_16);
lean_closure_set(x_80, 1, x_79);
x_22 = x_50;
x_23 = x_51;
x_24 = x_80;
goto block_41;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_unsigned_to_nat(0u);
x_82 = lean_array_fget(x_14, x_81);
lean_inc(x_14);
x_83 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__12___boxed), 18, 8);
lean_closure_set(x_83, 0, x_82);
lean_closure_set(x_83, 1, x_17);
lean_closure_set(x_83, 2, x_52);
lean_closure_set(x_83, 3, x_69);
lean_closure_set(x_83, 4, x_14);
lean_closure_set(x_83, 5, x_75);
lean_closure_set(x_83, 6, x_16);
lean_closure_set(x_83, 7, x_81);
x_22 = x_50;
x_23 = x_51;
x_24 = x_83;
goto block_41;
}
}
}
}
default: 
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_47);
lean_dec(x_16);
lean_dec(x_15);
x_84 = lean_ctor_get(x_20, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_20, 1);
lean_inc(x_85);
lean_dec(x_20);
x_86 = l_Lean_Name_num___override(x_84, x_85);
x_87 = l_Lean_Name_str___override(x_86, x_21);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_14);
x_89 = l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__0(x_88, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_88);
return x_89;
}
}
}
}
default: 
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec(x_16);
x_113 = lean_ctor_get(x_13, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_13, 1);
lean_inc(x_114);
lean_dec(x_13);
x_115 = l_Lean_Name_num___override(x_113, x_114);
if (lean_is_scalar(x_15)) {
 x_116 = lean_alloc_ctor(0, 2, 0);
} else {
 x_116 = x_15;
}
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_14);
x_117 = l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__0(x_116, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_116);
return x_117;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_5);
lean_dec(x_5);
x_13 = l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__0(x_1, x_2, x_3, x_4, x_12, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_6);
lean_dec(x_6);
x_14 = l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__3(x_1, x_2, x_3, x_4, x_5, x_13, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_9);
lean_dec(x_9);
x_17 = l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_16, x_10, x_11, x_12, x_13, x_14, x_15);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_9);
lean_dec(x_9);
x_17 = l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_16, x_10, x_11, x_12, x_13, x_14, x_15);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; lean_object* x_18; 
x_17 = lean_unbox(x_10);
lean_dec(x_10);
x_18 = l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_17, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_6);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__5___boxed(lean_object** _args) {
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
lean_object* x_18 = _args[17];
_start:
{
uint8_t x_19; lean_object* x_20; 
x_19 = lean_unbox(x_12);
lean_dec(x_12);
x_20 = l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_19, x_13, x_14, x_15, x_16, x_17, x_18);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_9);
lean_dec(x_9);
x_17 = l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_16, x_10, x_11, x_12, x_13, x_14, x_15);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_6);
lean_dec(x_6);
x_14 = l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__7(x_1, x_2, x_3, x_4, x_5, x_13, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__9___boxed(lean_object** _args) {
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
lean_object* x_18 = _args[17];
_start:
{
uint8_t x_19; uint8_t x_20; lean_object* x_21; 
x_19 = lean_unbox(x_6);
lean_dec(x_6);
x_20 = lean_unbox(x_12);
lean_dec(x_12);
x_21 = l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__9(x_1, x_2, x_3, x_4, x_5, x_19, x_7, x_8, x_9, x_10, x_11, x_20, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__8___boxed(lean_object** _args) {
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
lean_object* x_18 = _args[17];
_start:
{
uint8_t x_19; uint8_t x_20; lean_object* x_21; 
x_19 = lean_unbox(x_6);
lean_dec(x_6);
x_20 = lean_unbox(x_12);
lean_dec(x_12);
x_21 = l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__8(x_1, x_2, x_3, x_4, x_5, x_19, x_7, x_8, x_9, x_10, x_11, x_20, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__10___boxed(lean_object** _args) {
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
lean_object* x_18 = _args[17];
_start:
{
uint8_t x_19; uint8_t x_20; lean_object* x_21; 
x_19 = lean_unbox(x_7);
lean_dec(x_7);
x_20 = lean_unbox(x_12);
lean_dec(x_12);
x_21 = l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__10(x_1, x_2, x_3, x_4, x_5, x_6, x_19, x_8, x_9, x_10, x_11, x_20, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; lean_object* x_18; 
x_17 = lean_unbox(x_10);
lean_dec(x_10);
x_18 = l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__11(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_17, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__12___boxed(lean_object** _args) {
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
lean_object* x_18 = _args[17];
_start:
{
uint8_t x_19; lean_object* x_20; 
x_19 = lean_unbox(x_12);
lean_dec(x_12);
x_20 = l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__12(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_19, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_5);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__15___boxed(lean_object** _args) {
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
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
_start:
{
uint8_t x_20; lean_object* x_21; 
x_20 = lean_unbox(x_13);
lean_dec(x_13);
x_21 = l_Lean_Elab_Tactic_Omega_analyzeAtom___lam__15(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_20, x_14, x_15, x_16, x_17, x_18, x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_2);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_5);
lean_dec(x_5);
x_13 = l_Lean_Elab_Tactic_Omega_analyzeAtom(x_1, x_2, x_3, x_4, x_12, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Elab_Tactic_Omega_lookup_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_2, 12);
x_5 = lean_ctor_get(x_2, 2);
x_6 = l_Lean_checkTraceOption(x_4, x_5, x_1);
x_7 = lean_box(x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Elab_Tactic_Omega_lookup_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_isTracingEnabledFor___at___Lean_Elab_Tactic_Omega_lookup_spec__0___redArg(x_1, x_9, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Elab_Tactic_Omega_lookup_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_8 = l_List_reverse___redArg(x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_13 = lean_infer_type(x_11, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_14);
{
lean_object* _tmp_0 = x_12;
lean_object* _tmp_1 = x_1;
lean_object* _tmp_6 = x_15;
x_1 = _tmp_0;
x_2 = _tmp_1;
x_7 = _tmp_6;
}
goto _start;
}
else
{
uint8_t x_17; 
lean_free_object(x_1);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_17 = !lean_is_exclusive(x_13);
if (x_17 == 0)
{
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 0);
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_13);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_1, 0);
x_22 = lean_ctor_get(x_1, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_23 = lean_infer_type(x_21, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_2);
x_1 = x_22;
x_2 = x_26;
x_7 = x_25;
goto _start;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_22);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_28 = lean_ctor_get(x_23, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_23, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_30 = x_23;
} else {
 lean_dec_ref(x_23);
 x_30 = lean_box(0);
}
if (lean_is_scalar(x_30)) {
 x_31 = lean_alloc_ctor(1, 2, 0);
} else {
 x_31 = x_30;
}
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Elab_Tactic_Omega_lookup_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_List_mapM_loop___at___Lean_Elab_Tactic_Omega_lookup_spec__1___redArg(x_1, x_2, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = l_Lean_addMessageContextFull___at___Lean_Meta_recordSynthPendingFailure_spec__3(x_2, x_3, x_4, x_5, x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_st_ref_take(x_6, x_10);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint64_t x_20; lean_object* x_21; lean_object* x_22; double x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = lean_ctor_get(x_5, 5);
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_13, 2);
lean_inc(x_18);
x_19 = lean_ctor_get(x_13, 3);
lean_inc(x_19);
x_20 = lean_ctor_get_uint64(x_19, sizeof(void*)*1);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_float_of_nat(x_22);
x_24 = lean_box(0);
x_25 = lean_mk_string_unchecked("", 0, 0);
x_26 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_26, 0, x_1);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set_float(x_26, sizeof(void*)*2, x_23);
lean_ctor_set_float(x_26, sizeof(void*)*2 + 8, x_23);
x_27 = lean_unbox(x_24);
lean_ctor_set_uint8(x_26, sizeof(void*)*2 + 16, x_27);
x_28 = lean_mk_empty_array_with_capacity(x_22);
x_29 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_9);
lean_ctor_set(x_29, 2, x_28);
lean_inc(x_15);
lean_ctor_set(x_11, 1, x_29);
lean_ctor_set(x_11, 0, x_15);
x_30 = l_Lean_PersistentArray_push___redArg(x_21, x_11);
x_31 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set_uint64(x_31, sizeof(void*)*1, x_20);
x_32 = lean_ctor_get(x_13, 4);
lean_inc(x_32);
x_33 = lean_ctor_get(x_13, 5);
lean_inc(x_33);
x_34 = lean_ctor_get(x_13, 6);
lean_inc(x_34);
x_35 = lean_ctor_get(x_13, 7);
lean_inc(x_35);
lean_dec(x_13);
x_36 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_36, 0, x_16);
lean_ctor_set(x_36, 1, x_17);
lean_ctor_set(x_36, 2, x_18);
lean_ctor_set(x_36, 3, x_31);
lean_ctor_set(x_36, 4, x_32);
lean_ctor_set(x_36, 5, x_33);
lean_ctor_set(x_36, 6, x_34);
lean_ctor_set(x_36, 7, x_35);
x_37 = lean_st_ref_set(x_6, x_36, x_14);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_37, 0);
lean_dec(x_39);
x_40 = lean_box(0);
lean_ctor_set(x_37, 0, x_40);
return x_37;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_37, 1);
lean_inc(x_41);
lean_dec(x_37);
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
return x_43;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint64_t x_51; lean_object* x_52; lean_object* x_53; double x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_44 = lean_ctor_get(x_11, 0);
x_45 = lean_ctor_get(x_11, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_11);
x_46 = lean_ctor_get(x_5, 5);
x_47 = lean_ctor_get(x_44, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_44, 1);
lean_inc(x_48);
x_49 = lean_ctor_get(x_44, 2);
lean_inc(x_49);
x_50 = lean_ctor_get(x_44, 3);
lean_inc(x_50);
x_51 = lean_ctor_get_uint64(x_50, sizeof(void*)*1);
x_52 = lean_ctor_get(x_50, 0);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_unsigned_to_nat(0u);
x_54 = lean_float_of_nat(x_53);
x_55 = lean_box(0);
x_56 = lean_mk_string_unchecked("", 0, 0);
x_57 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_57, 0, x_1);
lean_ctor_set(x_57, 1, x_56);
lean_ctor_set_float(x_57, sizeof(void*)*2, x_54);
lean_ctor_set_float(x_57, sizeof(void*)*2 + 8, x_54);
x_58 = lean_unbox(x_55);
lean_ctor_set_uint8(x_57, sizeof(void*)*2 + 16, x_58);
x_59 = lean_mk_empty_array_with_capacity(x_53);
x_60 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_9);
lean_ctor_set(x_60, 2, x_59);
lean_inc(x_46);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_46);
lean_ctor_set(x_61, 1, x_60);
x_62 = l_Lean_PersistentArray_push___redArg(x_52, x_61);
x_63 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set_uint64(x_63, sizeof(void*)*1, x_51);
x_64 = lean_ctor_get(x_44, 4);
lean_inc(x_64);
x_65 = lean_ctor_get(x_44, 5);
lean_inc(x_65);
x_66 = lean_ctor_get(x_44, 6);
lean_inc(x_66);
x_67 = lean_ctor_get(x_44, 7);
lean_inc(x_67);
lean_dec(x_44);
x_68 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_68, 0, x_47);
lean_ctor_set(x_68, 1, x_48);
lean_ctor_set(x_68, 2, x_49);
lean_ctor_set(x_68, 3, x_63);
lean_ctor_set(x_68, 4, x_64);
lean_ctor_set(x_68, 5, x_65);
lean_ctor_set(x_68, 6, x_66);
lean_ctor_set(x_68, 7, x_67);
x_69 = lean_st_ref_set(x_6, x_68, x_45);
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_71 = x_69;
} else {
 lean_dec_ref(x_69);
 x_71 = lean_box(0);
}
x_72 = lean_box(0);
if (lean_is_scalar(x_71)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_71;
}
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_70);
return x_73;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__2___redArg(x_1, x_2, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___Lean_Elab_Tactic_Omega_lookup_spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_inc(x_1);
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 2);
x_5 = l_Std_DHashMap_Internal_AssocList_foldrM___at___Lean_Elab_Tactic_Omega_lookup_spec__3(x_1, x_4);
lean_inc(x_3);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_Elab_Tactic_Omega_lookup_spec__4(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
x_10 = l_Std_DHashMap_Internal_AssocList_foldrM___at___Lean_Elab_Tactic_Omega_lookup_spec__3(x_4, x_9);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_lookup(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_st_ref_get(x_3, x_11);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_30 = x_27;
} else {
 lean_dec_ref(x_27);
 x_30 = lean_box(0);
}
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_31 = l_Lean_Meta_Canonicalizer_canon(x_1, x_5, x_6, x_7, x_8, x_9, x_10, x_29);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint64_t x_38; lean_object* x_39; uint64_t x_40; uint64_t x_41; uint64_t x_42; lean_object* x_43; uint64_t x_44; uint64_t x_45; uint64_t x_46; size_t x_47; size_t x_48; lean_object* x_49; size_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; size_t x_106; size_t x_107; lean_object* x_108; lean_object* x_109; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = lean_ctor_get(x_31, 1);
x_35 = lean_ctor_get(x_28, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_36 = x_28;
} else {
 lean_dec_ref(x_28);
 x_36 = lean_box(0);
}
x_37 = lean_array_get_size(x_35);
x_38 = l_Lean_Expr_hash(x_33);
x_39 = lean_unsigned_to_nat(32u);
x_40 = lean_uint64_of_nat(x_39);
x_41 = lean_uint64_shift_right(x_38, x_40);
x_42 = lean_uint64_xor(x_38, x_41);
x_43 = lean_unsigned_to_nat(16u);
x_44 = lean_uint64_of_nat(x_43);
x_45 = lean_uint64_shift_right(x_42, x_44);
x_46 = lean_uint64_xor(x_42, x_45);
x_47 = lean_uint64_to_usize(x_46);
x_48 = lean_usize_of_nat(x_37);
lean_dec(x_37);
x_49 = lean_unsigned_to_nat(1u);
x_50 = lean_usize_of_nat(x_49);
x_106 = lean_usize_sub(x_48, x_50);
x_107 = lean_usize_land(x_47, x_106);
x_108 = lean_array_uget(x_35, x_107);
lean_dec(x_35);
x_109 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_SynthInstance_findEntry_x3f_spec__0(lean_box(0), x_33, x_108);
lean_dec(x_108);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; uint8_t x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_182; lean_object* x_183; uint8_t x_184; 
lean_free_object(x_31);
x_110 = lean_mk_string_unchecked("omega", 5, 5);
x_111 = l_Lean_Name_mkStr1(x_110);
lean_inc(x_111);
x_182 = l_Lean_isTracingEnabledFor___at___Lean_Elab_Tactic_Omega_lookup_spec__0___redArg(x_111, x_9, x_34);
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
x_184 = lean_unbox(x_183);
lean_dec(x_183);
if (x_184 == 0)
{
lean_object* x_185; 
x_185 = lean_ctor_get(x_182, 1);
lean_inc(x_185);
lean_dec(x_182);
x_144 = x_2;
x_145 = x_3;
x_146 = x_4;
x_147 = x_5;
x_148 = x_6;
x_149 = x_7;
x_150 = x_8;
x_151 = x_9;
x_152 = x_10;
x_153 = x_185;
goto block_181;
}
else
{
uint8_t x_186; 
x_186 = !lean_is_exclusive(x_182);
if (x_186 == 0)
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_187 = lean_ctor_get(x_182, 1);
x_188 = lean_ctor_get(x_182, 0);
lean_dec(x_188);
x_189 = lean_mk_string_unchecked("New atom: ", 10, 10);
x_190 = l_Lean_stringToMessageData(x_189);
lean_dec(x_189);
lean_inc(x_33);
x_191 = l_Lean_MessageData_ofExpr(x_33);
lean_ctor_set_tag(x_182, 7);
lean_ctor_set(x_182, 1, x_191);
lean_ctor_set(x_182, 0, x_190);
x_192 = lean_mk_string_unchecked("", 0, 0);
x_193 = l_Lean_stringToMessageData(x_192);
lean_dec(x_192);
x_194 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_194, 0, x_182);
lean_ctor_set(x_194, 1, x_193);
lean_inc(x_111);
x_195 = l_Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__2___redArg(x_111, x_194, x_7, x_8, x_9, x_10, x_187);
x_196 = lean_ctor_get(x_195, 1);
lean_inc(x_196);
lean_dec(x_195);
x_144 = x_2;
x_145 = x_3;
x_146 = x_4;
x_147 = x_5;
x_148 = x_6;
x_149 = x_7;
x_150 = x_8;
x_151 = x_9;
x_152 = x_10;
x_153 = x_196;
goto block_181;
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_197 = lean_ctor_get(x_182, 1);
lean_inc(x_197);
lean_dec(x_182);
x_198 = lean_mk_string_unchecked("New atom: ", 10, 10);
x_199 = l_Lean_stringToMessageData(x_198);
lean_dec(x_198);
lean_inc(x_33);
x_200 = l_Lean_MessageData_ofExpr(x_33);
x_201 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_201, 0, x_199);
lean_ctor_set(x_201, 1, x_200);
x_202 = lean_mk_string_unchecked("", 0, 0);
x_203 = l_Lean_stringToMessageData(x_202);
lean_dec(x_202);
x_204 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_204, 0, x_201);
lean_ctor_set(x_204, 1, x_203);
lean_inc(x_111);
x_205 = l_Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__2___redArg(x_111, x_204, x_7, x_8, x_9, x_10, x_197);
x_206 = lean_ctor_get(x_205, 1);
lean_inc(x_206);
lean_dec(x_205);
x_144 = x_2;
x_145 = x_3;
x_146 = x_4;
x_147 = x_5;
x_148 = x_6;
x_149 = x_7;
x_150 = x_8;
x_151 = x_9;
x_152 = x_10;
x_153 = x_206;
goto block_181;
}
}
block_143:
{
lean_object* x_124; lean_object* x_125; 
lean_dec(x_122);
lean_dec(x_121);
lean_dec(x_115);
x_124 = lean_box(0);
lean_inc(x_114);
lean_inc(x_117);
lean_inc(x_118);
lean_inc(x_113);
x_125 = l_List_mapM_loop___at___Lean_Elab_Tactic_Omega_lookup_spec__1___redArg(x_123, x_124, x_113, x_118, x_117, x_114, x_116);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
lean_dec(x_125);
x_128 = lean_mk_string_unchecked("New facts: ", 11, 11);
x_129 = l_Lean_stringToMessageData(x_128);
lean_dec(x_128);
x_130 = lean_box(0);
x_131 = l_List_mapTR_loop___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___Lean_Meta_mkAppM_spec__0_spec__0(x_126, x_130);
x_132 = l_Lean_MessageData_ofList(x_131);
if (lean_is_scalar(x_36)) {
 x_133 = lean_alloc_ctor(7, 2, 0);
} else {
 x_133 = x_36;
 lean_ctor_set_tag(x_133, 7);
}
lean_ctor_set(x_133, 0, x_129);
lean_ctor_set(x_133, 1, x_132);
x_134 = lean_mk_string_unchecked("", 0, 0);
x_135 = l_Lean_stringToMessageData(x_134);
lean_dec(x_134);
if (lean_is_scalar(x_30)) {
 x_136 = lean_alloc_ctor(7, 2, 0);
} else {
 x_136 = x_30;
 lean_ctor_set_tag(x_136, 7);
}
lean_ctor_set(x_136, 0, x_133);
lean_ctor_set(x_136, 1, x_135);
x_137 = l_Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__2___redArg(x_111, x_136, x_113, x_118, x_117, x_114, x_127);
lean_dec(x_114);
lean_dec(x_117);
lean_dec(x_118);
lean_dec(x_113);
x_138 = lean_ctor_get(x_137, 1);
lean_inc(x_138);
lean_dec(x_137);
x_51 = x_112;
x_52 = x_119;
x_53 = x_138;
goto block_105;
}
else
{
uint8_t x_139; 
lean_dec(x_119);
lean_dec(x_118);
lean_dec(x_117);
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_112);
lean_dec(x_111);
lean_dec(x_36);
lean_dec(x_33);
lean_dec(x_30);
x_139 = !lean_is_exclusive(x_125);
if (x_139 == 0)
{
return x_125;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = lean_ctor_get(x_125, 0);
x_141 = lean_ctor_get(x_125, 1);
lean_inc(x_141);
lean_inc(x_140);
lean_dec(x_125);
x_142 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set(x_142, 1, x_141);
return x_142;
}
}
}
block_181:
{
lean_object* x_154; 
lean_inc(x_152);
lean_inc(x_151);
lean_inc(x_150);
lean_inc(x_149);
lean_inc(x_148);
lean_inc(x_146);
lean_inc(x_145);
lean_inc(x_144);
lean_inc(x_33);
x_154 = l_Lean_Elab_Tactic_Omega_analyzeAtom(x_33, x_144, x_145, x_146, x_147, x_148, x_149, x_150, x_151, x_152, x_153);
if (lean_obj_tag(x_154) == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; 
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_154, 1);
lean_inc(x_156);
lean_dec(x_154);
lean_inc(x_111);
x_157 = l_Lean_isTracingEnabledFor___at___Lean_Elab_Tactic_Omega_lookup_spec__0___redArg(x_111, x_151, x_156);
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
x_159 = lean_unbox(x_158);
lean_dec(x_158);
if (x_159 == 0)
{
lean_object* x_160; 
lean_dec(x_152);
lean_dec(x_151);
lean_dec(x_150);
lean_dec(x_149);
lean_dec(x_148);
lean_dec(x_146);
lean_dec(x_144);
lean_dec(x_111);
lean_dec(x_36);
lean_dec(x_30);
x_160 = lean_ctor_get(x_157, 1);
lean_inc(x_160);
lean_dec(x_157);
x_51 = x_155;
x_52 = x_145;
x_53 = x_160;
goto block_105;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; uint8_t x_164; 
x_161 = lean_ctor_get(x_157, 1);
lean_inc(x_161);
lean_dec(x_157);
x_162 = lean_ctor_get(x_155, 0);
lean_inc(x_162);
x_163 = lean_unsigned_to_nat(0u);
x_164 = lean_nat_dec_eq(x_162, x_163);
lean_dec(x_162);
if (x_164 == 0)
{
lean_object* x_165; lean_object* x_166; uint8_t x_167; 
lean_inc(x_111);
x_165 = l_Lean_isTracingEnabledFor___at___Lean_Elab_Tactic_Omega_lookup_spec__0___redArg(x_111, x_151, x_161);
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
x_167 = lean_unbox(x_166);
lean_dec(x_166);
if (x_167 == 0)
{
lean_object* x_168; 
lean_dec(x_152);
lean_dec(x_151);
lean_dec(x_150);
lean_dec(x_149);
lean_dec(x_148);
lean_dec(x_146);
lean_dec(x_144);
lean_dec(x_111);
lean_dec(x_36);
lean_dec(x_30);
x_168 = lean_ctor_get(x_165, 1);
lean_inc(x_168);
lean_dec(x_165);
x_51 = x_155;
x_52 = x_145;
x_53 = x_168;
goto block_105;
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; uint8_t x_173; 
x_169 = lean_ctor_get(x_165, 1);
lean_inc(x_169);
lean_dec(x_165);
x_170 = lean_box(0);
x_171 = lean_ctor_get(x_155, 1);
lean_inc(x_171);
x_172 = lean_array_get_size(x_171);
x_173 = lean_nat_dec_lt(x_163, x_172);
if (x_173 == 0)
{
lean_dec(x_172);
lean_dec(x_171);
x_112 = x_155;
x_113 = x_149;
x_114 = x_152;
x_115 = x_144;
x_116 = x_169;
x_117 = x_151;
x_118 = x_150;
x_119 = x_145;
x_120 = x_147;
x_121 = x_146;
x_122 = x_148;
x_123 = x_170;
goto block_143;
}
else
{
size_t x_174; size_t x_175; lean_object* x_176; 
x_174 = lean_usize_of_nat(x_172);
lean_dec(x_172);
x_175 = lean_usize_of_nat(x_163);
x_176 = l_Array_foldrMUnsafe_fold___at___Lean_Elab_Tactic_Omega_lookup_spec__4(x_171, x_174, x_175, x_170);
lean_dec(x_171);
x_112 = x_155;
x_113 = x_149;
x_114 = x_152;
x_115 = x_144;
x_116 = x_169;
x_117 = x_151;
x_118 = x_150;
x_119 = x_145;
x_120 = x_147;
x_121 = x_146;
x_122 = x_148;
x_123 = x_176;
goto block_143;
}
}
}
else
{
lean_dec(x_152);
lean_dec(x_151);
lean_dec(x_150);
lean_dec(x_149);
lean_dec(x_148);
lean_dec(x_146);
lean_dec(x_144);
lean_dec(x_111);
lean_dec(x_36);
lean_dec(x_30);
x_51 = x_155;
x_52 = x_145;
x_53 = x_161;
goto block_105;
}
}
}
else
{
uint8_t x_177; 
lean_dec(x_152);
lean_dec(x_151);
lean_dec(x_150);
lean_dec(x_149);
lean_dec(x_148);
lean_dec(x_146);
lean_dec(x_145);
lean_dec(x_144);
lean_dec(x_111);
lean_dec(x_36);
lean_dec(x_33);
lean_dec(x_30);
x_177 = !lean_is_exclusive(x_154);
if (x_177 == 0)
{
return x_154;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_178 = lean_ctor_get(x_154, 0);
x_179 = lean_ctor_get(x_154, 1);
lean_inc(x_179);
lean_inc(x_178);
lean_dec(x_154);
x_180 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_180, 0, x_178);
lean_ctor_set(x_180, 1, x_179);
return x_180;
}
}
}
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; 
lean_dec(x_33);
lean_dec(x_30);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_207 = lean_ctor_get(x_109, 0);
lean_inc(x_207);
lean_dec(x_109);
x_208 = lean_box(0);
if (lean_is_scalar(x_36)) {
 x_209 = lean_alloc_ctor(0, 2, 0);
} else {
 x_209 = x_36;
}
lean_ctor_set(x_209, 0, x_207);
lean_ctor_set(x_209, 1, x_208);
lean_ctor_set(x_31, 0, x_209);
return x_31;
}
block_105:
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_54 = lean_st_ref_take(x_52, x_53);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = !lean_is_exclusive(x_55);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; size_t x_61; size_t x_62; size_t x_63; lean_object* x_64; uint8_t x_65; 
x_58 = lean_ctor_get(x_55, 0);
x_59 = lean_ctor_get(x_55, 1);
x_60 = lean_array_get_size(x_59);
x_61 = lean_usize_of_nat(x_60);
lean_dec(x_60);
x_62 = lean_usize_sub(x_61, x_50);
x_63 = lean_usize_land(x_47, x_62);
x_64 = lean_array_uget(x_59, x_63);
x_65 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectMVars_visit_spec__0___redArg(x_33, x_64);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_66 = lean_nat_add(x_58, x_49);
lean_inc(x_58);
x_67 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_67, 0, x_33);
lean_ctor_set(x_67, 1, x_58);
lean_ctor_set(x_67, 2, x_64);
x_68 = lean_array_uset(x_59, x_63, x_67);
x_69 = lean_unsigned_to_nat(2u);
x_70 = lean_nat_shiftl(x_66, x_69);
x_71 = lean_unsigned_to_nat(3u);
x_72 = lean_nat_div(x_70, x_71);
lean_dec(x_70);
x_73 = lean_array_get_size(x_68);
x_74 = lean_nat_dec_le(x_72, x_73);
lean_dec(x_73);
lean_dec(x_72);
if (x_74 == 0)
{
lean_object* x_75; 
x_75 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectMVars_visit_spec__1(lean_box(0), x_68);
lean_ctor_set(x_55, 1, x_75);
lean_ctor_set(x_55, 0, x_66);
x_12 = x_51;
x_13 = x_58;
x_14 = x_52;
x_15 = x_56;
x_16 = x_55;
goto block_26;
}
else
{
lean_ctor_set(x_55, 1, x_68);
lean_ctor_set(x_55, 0, x_66);
x_12 = x_51;
x_13 = x_58;
x_14 = x_52;
x_15 = x_56;
x_16 = x_55;
goto block_26;
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_76 = lean_box(0);
x_77 = lean_array_uset(x_59, x_63, x_76);
lean_inc(x_58);
x_78 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_SynthInstance_newSubgoal_spec__0___redArg(x_33, x_58, x_64);
x_79 = lean_array_uset(x_77, x_63, x_78);
lean_inc(x_58);
lean_ctor_set(x_55, 1, x_79);
x_12 = x_51;
x_13 = x_58;
x_14 = x_52;
x_15 = x_56;
x_16 = x_55;
goto block_26;
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; size_t x_83; size_t x_84; size_t x_85; lean_object* x_86; uint8_t x_87; 
x_80 = lean_ctor_get(x_55, 0);
x_81 = lean_ctor_get(x_55, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_55);
x_82 = lean_array_get_size(x_81);
x_83 = lean_usize_of_nat(x_82);
lean_dec(x_82);
x_84 = lean_usize_sub(x_83, x_50);
x_85 = lean_usize_land(x_47, x_84);
x_86 = lean_array_uget(x_81, x_85);
x_87 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectMVars_visit_spec__0___redArg(x_33, x_86);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_88 = lean_nat_add(x_80, x_49);
lean_inc(x_80);
x_89 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_89, 0, x_33);
lean_ctor_set(x_89, 1, x_80);
lean_ctor_set(x_89, 2, x_86);
x_90 = lean_array_uset(x_81, x_85, x_89);
x_91 = lean_unsigned_to_nat(2u);
x_92 = lean_nat_shiftl(x_88, x_91);
x_93 = lean_unsigned_to_nat(3u);
x_94 = lean_nat_div(x_92, x_93);
lean_dec(x_92);
x_95 = lean_array_get_size(x_90);
x_96 = lean_nat_dec_le(x_94, x_95);
lean_dec(x_95);
lean_dec(x_94);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; 
x_97 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectMVars_visit_spec__1(lean_box(0), x_90);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_88);
lean_ctor_set(x_98, 1, x_97);
x_12 = x_51;
x_13 = x_80;
x_14 = x_52;
x_15 = x_56;
x_16 = x_98;
goto block_26;
}
else
{
lean_object* x_99; 
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_88);
lean_ctor_set(x_99, 1, x_90);
x_12 = x_51;
x_13 = x_80;
x_14 = x_52;
x_15 = x_56;
x_16 = x_99;
goto block_26;
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_100 = lean_box(0);
x_101 = lean_array_uset(x_81, x_85, x_100);
lean_inc(x_80);
x_102 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_SynthInstance_newSubgoal_spec__0___redArg(x_33, x_80, x_86);
x_103 = lean_array_uset(x_101, x_85, x_102);
lean_inc(x_80);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_80);
lean_ctor_set(x_104, 1, x_103);
x_12 = x_51;
x_13 = x_80;
x_14 = x_52;
x_15 = x_56;
x_16 = x_104;
goto block_26;
}
}
}
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; uint64_t x_215; lean_object* x_216; uint64_t x_217; uint64_t x_218; uint64_t x_219; lean_object* x_220; uint64_t x_221; uint64_t x_222; uint64_t x_223; size_t x_224; size_t x_225; lean_object* x_226; size_t x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; size_t x_261; size_t x_262; lean_object* x_263; lean_object* x_264; 
x_210 = lean_ctor_get(x_31, 0);
x_211 = lean_ctor_get(x_31, 1);
lean_inc(x_211);
lean_inc(x_210);
lean_dec(x_31);
x_212 = lean_ctor_get(x_28, 1);
lean_inc(x_212);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_213 = x_28;
} else {
 lean_dec_ref(x_28);
 x_213 = lean_box(0);
}
x_214 = lean_array_get_size(x_212);
x_215 = l_Lean_Expr_hash(x_210);
x_216 = lean_unsigned_to_nat(32u);
x_217 = lean_uint64_of_nat(x_216);
x_218 = lean_uint64_shift_right(x_215, x_217);
x_219 = lean_uint64_xor(x_215, x_218);
x_220 = lean_unsigned_to_nat(16u);
x_221 = lean_uint64_of_nat(x_220);
x_222 = lean_uint64_shift_right(x_219, x_221);
x_223 = lean_uint64_xor(x_219, x_222);
x_224 = lean_uint64_to_usize(x_223);
x_225 = lean_usize_of_nat(x_214);
lean_dec(x_214);
x_226 = lean_unsigned_to_nat(1u);
x_227 = lean_usize_of_nat(x_226);
x_261 = lean_usize_sub(x_225, x_227);
x_262 = lean_usize_land(x_224, x_261);
x_263 = lean_array_uget(x_212, x_262);
lean_dec(x_212);
x_264 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_SynthInstance_findEntry_x3f_spec__0(lean_box(0), x_210, x_263);
lean_dec(x_263);
if (lean_obj_tag(x_264) == 0)
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; uint8_t x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_299; lean_object* x_300; lean_object* x_301; uint8_t x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_337; lean_object* x_338; uint8_t x_339; 
x_265 = lean_mk_string_unchecked("omega", 5, 5);
x_266 = l_Lean_Name_mkStr1(x_265);
lean_inc(x_266);
x_337 = l_Lean_isTracingEnabledFor___at___Lean_Elab_Tactic_Omega_lookup_spec__0___redArg(x_266, x_9, x_211);
x_338 = lean_ctor_get(x_337, 0);
lean_inc(x_338);
x_339 = lean_unbox(x_338);
lean_dec(x_338);
if (x_339 == 0)
{
lean_object* x_340; 
x_340 = lean_ctor_get(x_337, 1);
lean_inc(x_340);
lean_dec(x_337);
x_299 = x_2;
x_300 = x_3;
x_301 = x_4;
x_302 = x_5;
x_303 = x_6;
x_304 = x_7;
x_305 = x_8;
x_306 = x_9;
x_307 = x_10;
x_308 = x_340;
goto block_336;
}
else
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; 
x_341 = lean_ctor_get(x_337, 1);
lean_inc(x_341);
if (lean_is_exclusive(x_337)) {
 lean_ctor_release(x_337, 0);
 lean_ctor_release(x_337, 1);
 x_342 = x_337;
} else {
 lean_dec_ref(x_337);
 x_342 = lean_box(0);
}
x_343 = lean_mk_string_unchecked("New atom: ", 10, 10);
x_344 = l_Lean_stringToMessageData(x_343);
lean_dec(x_343);
lean_inc(x_210);
x_345 = l_Lean_MessageData_ofExpr(x_210);
if (lean_is_scalar(x_342)) {
 x_346 = lean_alloc_ctor(7, 2, 0);
} else {
 x_346 = x_342;
 lean_ctor_set_tag(x_346, 7);
}
lean_ctor_set(x_346, 0, x_344);
lean_ctor_set(x_346, 1, x_345);
x_347 = lean_mk_string_unchecked("", 0, 0);
x_348 = l_Lean_stringToMessageData(x_347);
lean_dec(x_347);
x_349 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_349, 0, x_346);
lean_ctor_set(x_349, 1, x_348);
lean_inc(x_266);
x_350 = l_Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__2___redArg(x_266, x_349, x_7, x_8, x_9, x_10, x_341);
x_351 = lean_ctor_get(x_350, 1);
lean_inc(x_351);
lean_dec(x_350);
x_299 = x_2;
x_300 = x_3;
x_301 = x_4;
x_302 = x_5;
x_303 = x_6;
x_304 = x_7;
x_305 = x_8;
x_306 = x_9;
x_307 = x_10;
x_308 = x_351;
goto block_336;
}
block_298:
{
lean_object* x_279; lean_object* x_280; 
lean_dec(x_277);
lean_dec(x_276);
lean_dec(x_270);
x_279 = lean_box(0);
lean_inc(x_269);
lean_inc(x_272);
lean_inc(x_273);
lean_inc(x_268);
x_280 = l_List_mapM_loop___at___Lean_Elab_Tactic_Omega_lookup_spec__1___redArg(x_278, x_279, x_268, x_273, x_272, x_269, x_271);
if (lean_obj_tag(x_280) == 0)
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; 
x_281 = lean_ctor_get(x_280, 0);
lean_inc(x_281);
x_282 = lean_ctor_get(x_280, 1);
lean_inc(x_282);
lean_dec(x_280);
x_283 = lean_mk_string_unchecked("New facts: ", 11, 11);
x_284 = l_Lean_stringToMessageData(x_283);
lean_dec(x_283);
x_285 = lean_box(0);
x_286 = l_List_mapTR_loop___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___Lean_Meta_mkAppM_spec__0_spec__0(x_281, x_285);
x_287 = l_Lean_MessageData_ofList(x_286);
if (lean_is_scalar(x_213)) {
 x_288 = lean_alloc_ctor(7, 2, 0);
} else {
 x_288 = x_213;
 lean_ctor_set_tag(x_288, 7);
}
lean_ctor_set(x_288, 0, x_284);
lean_ctor_set(x_288, 1, x_287);
x_289 = lean_mk_string_unchecked("", 0, 0);
x_290 = l_Lean_stringToMessageData(x_289);
lean_dec(x_289);
if (lean_is_scalar(x_30)) {
 x_291 = lean_alloc_ctor(7, 2, 0);
} else {
 x_291 = x_30;
 lean_ctor_set_tag(x_291, 7);
}
lean_ctor_set(x_291, 0, x_288);
lean_ctor_set(x_291, 1, x_290);
x_292 = l_Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__2___redArg(x_266, x_291, x_268, x_273, x_272, x_269, x_282);
lean_dec(x_269);
lean_dec(x_272);
lean_dec(x_273);
lean_dec(x_268);
x_293 = lean_ctor_get(x_292, 1);
lean_inc(x_293);
lean_dec(x_292);
x_228 = x_267;
x_229 = x_274;
x_230 = x_293;
goto block_260;
}
else
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; 
lean_dec(x_274);
lean_dec(x_273);
lean_dec(x_272);
lean_dec(x_269);
lean_dec(x_268);
lean_dec(x_267);
lean_dec(x_266);
lean_dec(x_213);
lean_dec(x_210);
lean_dec(x_30);
x_294 = lean_ctor_get(x_280, 0);
lean_inc(x_294);
x_295 = lean_ctor_get(x_280, 1);
lean_inc(x_295);
if (lean_is_exclusive(x_280)) {
 lean_ctor_release(x_280, 0);
 lean_ctor_release(x_280, 1);
 x_296 = x_280;
} else {
 lean_dec_ref(x_280);
 x_296 = lean_box(0);
}
if (lean_is_scalar(x_296)) {
 x_297 = lean_alloc_ctor(1, 2, 0);
} else {
 x_297 = x_296;
}
lean_ctor_set(x_297, 0, x_294);
lean_ctor_set(x_297, 1, x_295);
return x_297;
}
}
block_336:
{
lean_object* x_309; 
lean_inc(x_307);
lean_inc(x_306);
lean_inc(x_305);
lean_inc(x_304);
lean_inc(x_303);
lean_inc(x_301);
lean_inc(x_300);
lean_inc(x_299);
lean_inc(x_210);
x_309 = l_Lean_Elab_Tactic_Omega_analyzeAtom(x_210, x_299, x_300, x_301, x_302, x_303, x_304, x_305, x_306, x_307, x_308);
if (lean_obj_tag(x_309) == 0)
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; uint8_t x_314; 
x_310 = lean_ctor_get(x_309, 0);
lean_inc(x_310);
x_311 = lean_ctor_get(x_309, 1);
lean_inc(x_311);
lean_dec(x_309);
lean_inc(x_266);
x_312 = l_Lean_isTracingEnabledFor___at___Lean_Elab_Tactic_Omega_lookup_spec__0___redArg(x_266, x_306, x_311);
x_313 = lean_ctor_get(x_312, 0);
lean_inc(x_313);
x_314 = lean_unbox(x_313);
lean_dec(x_313);
if (x_314 == 0)
{
lean_object* x_315; 
lean_dec(x_307);
lean_dec(x_306);
lean_dec(x_305);
lean_dec(x_304);
lean_dec(x_303);
lean_dec(x_301);
lean_dec(x_299);
lean_dec(x_266);
lean_dec(x_213);
lean_dec(x_30);
x_315 = lean_ctor_get(x_312, 1);
lean_inc(x_315);
lean_dec(x_312);
x_228 = x_310;
x_229 = x_300;
x_230 = x_315;
goto block_260;
}
else
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; uint8_t x_319; 
x_316 = lean_ctor_get(x_312, 1);
lean_inc(x_316);
lean_dec(x_312);
x_317 = lean_ctor_get(x_310, 0);
lean_inc(x_317);
x_318 = lean_unsigned_to_nat(0u);
x_319 = lean_nat_dec_eq(x_317, x_318);
lean_dec(x_317);
if (x_319 == 0)
{
lean_object* x_320; lean_object* x_321; uint8_t x_322; 
lean_inc(x_266);
x_320 = l_Lean_isTracingEnabledFor___at___Lean_Elab_Tactic_Omega_lookup_spec__0___redArg(x_266, x_306, x_316);
x_321 = lean_ctor_get(x_320, 0);
lean_inc(x_321);
x_322 = lean_unbox(x_321);
lean_dec(x_321);
if (x_322 == 0)
{
lean_object* x_323; 
lean_dec(x_307);
lean_dec(x_306);
lean_dec(x_305);
lean_dec(x_304);
lean_dec(x_303);
lean_dec(x_301);
lean_dec(x_299);
lean_dec(x_266);
lean_dec(x_213);
lean_dec(x_30);
x_323 = lean_ctor_get(x_320, 1);
lean_inc(x_323);
lean_dec(x_320);
x_228 = x_310;
x_229 = x_300;
x_230 = x_323;
goto block_260;
}
else
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; uint8_t x_328; 
x_324 = lean_ctor_get(x_320, 1);
lean_inc(x_324);
lean_dec(x_320);
x_325 = lean_box(0);
x_326 = lean_ctor_get(x_310, 1);
lean_inc(x_326);
x_327 = lean_array_get_size(x_326);
x_328 = lean_nat_dec_lt(x_318, x_327);
if (x_328 == 0)
{
lean_dec(x_327);
lean_dec(x_326);
x_267 = x_310;
x_268 = x_304;
x_269 = x_307;
x_270 = x_299;
x_271 = x_324;
x_272 = x_306;
x_273 = x_305;
x_274 = x_300;
x_275 = x_302;
x_276 = x_301;
x_277 = x_303;
x_278 = x_325;
goto block_298;
}
else
{
size_t x_329; size_t x_330; lean_object* x_331; 
x_329 = lean_usize_of_nat(x_327);
lean_dec(x_327);
x_330 = lean_usize_of_nat(x_318);
x_331 = l_Array_foldrMUnsafe_fold___at___Lean_Elab_Tactic_Omega_lookup_spec__4(x_326, x_329, x_330, x_325);
lean_dec(x_326);
x_267 = x_310;
x_268 = x_304;
x_269 = x_307;
x_270 = x_299;
x_271 = x_324;
x_272 = x_306;
x_273 = x_305;
x_274 = x_300;
x_275 = x_302;
x_276 = x_301;
x_277 = x_303;
x_278 = x_331;
goto block_298;
}
}
}
else
{
lean_dec(x_307);
lean_dec(x_306);
lean_dec(x_305);
lean_dec(x_304);
lean_dec(x_303);
lean_dec(x_301);
lean_dec(x_299);
lean_dec(x_266);
lean_dec(x_213);
lean_dec(x_30);
x_228 = x_310;
x_229 = x_300;
x_230 = x_316;
goto block_260;
}
}
}
else
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; 
lean_dec(x_307);
lean_dec(x_306);
lean_dec(x_305);
lean_dec(x_304);
lean_dec(x_303);
lean_dec(x_301);
lean_dec(x_300);
lean_dec(x_299);
lean_dec(x_266);
lean_dec(x_213);
lean_dec(x_210);
lean_dec(x_30);
x_332 = lean_ctor_get(x_309, 0);
lean_inc(x_332);
x_333 = lean_ctor_get(x_309, 1);
lean_inc(x_333);
if (lean_is_exclusive(x_309)) {
 lean_ctor_release(x_309, 0);
 lean_ctor_release(x_309, 1);
 x_334 = x_309;
} else {
 lean_dec_ref(x_309);
 x_334 = lean_box(0);
}
if (lean_is_scalar(x_334)) {
 x_335 = lean_alloc_ctor(1, 2, 0);
} else {
 x_335 = x_334;
}
lean_ctor_set(x_335, 0, x_332);
lean_ctor_set(x_335, 1, x_333);
return x_335;
}
}
}
else
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; 
lean_dec(x_210);
lean_dec(x_30);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_352 = lean_ctor_get(x_264, 0);
lean_inc(x_352);
lean_dec(x_264);
x_353 = lean_box(0);
if (lean_is_scalar(x_213)) {
 x_354 = lean_alloc_ctor(0, 2, 0);
} else {
 x_354 = x_213;
}
lean_ctor_set(x_354, 0, x_352);
lean_ctor_set(x_354, 1, x_353);
x_355 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_355, 0, x_354);
lean_ctor_set(x_355, 1, x_211);
return x_355;
}
block_260:
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; size_t x_238; size_t x_239; size_t x_240; lean_object* x_241; uint8_t x_242; 
x_231 = lean_st_ref_take(x_229, x_230);
x_232 = lean_ctor_get(x_231, 0);
lean_inc(x_232);
x_233 = lean_ctor_get(x_231, 1);
lean_inc(x_233);
lean_dec(x_231);
x_234 = lean_ctor_get(x_232, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_232, 1);
lean_inc(x_235);
if (lean_is_exclusive(x_232)) {
 lean_ctor_release(x_232, 0);
 lean_ctor_release(x_232, 1);
 x_236 = x_232;
} else {
 lean_dec_ref(x_232);
 x_236 = lean_box(0);
}
x_237 = lean_array_get_size(x_235);
x_238 = lean_usize_of_nat(x_237);
lean_dec(x_237);
x_239 = lean_usize_sub(x_238, x_227);
x_240 = lean_usize_land(x_224, x_239);
x_241 = lean_array_uget(x_235, x_240);
x_242 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectMVars_visit_spec__0___redArg(x_210, x_241);
if (x_242 == 0)
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; uint8_t x_251; 
x_243 = lean_nat_add(x_234, x_226);
lean_inc(x_234);
x_244 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_244, 0, x_210);
lean_ctor_set(x_244, 1, x_234);
lean_ctor_set(x_244, 2, x_241);
x_245 = lean_array_uset(x_235, x_240, x_244);
x_246 = lean_unsigned_to_nat(2u);
x_247 = lean_nat_shiftl(x_243, x_246);
x_248 = lean_unsigned_to_nat(3u);
x_249 = lean_nat_div(x_247, x_248);
lean_dec(x_247);
x_250 = lean_array_get_size(x_245);
x_251 = lean_nat_dec_le(x_249, x_250);
lean_dec(x_250);
lean_dec(x_249);
if (x_251 == 0)
{
lean_object* x_252; lean_object* x_253; 
x_252 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectMVars_visit_spec__1(lean_box(0), x_245);
if (lean_is_scalar(x_236)) {
 x_253 = lean_alloc_ctor(0, 2, 0);
} else {
 x_253 = x_236;
}
lean_ctor_set(x_253, 0, x_243);
lean_ctor_set(x_253, 1, x_252);
x_12 = x_228;
x_13 = x_234;
x_14 = x_229;
x_15 = x_233;
x_16 = x_253;
goto block_26;
}
else
{
lean_object* x_254; 
if (lean_is_scalar(x_236)) {
 x_254 = lean_alloc_ctor(0, 2, 0);
} else {
 x_254 = x_236;
}
lean_ctor_set(x_254, 0, x_243);
lean_ctor_set(x_254, 1, x_245);
x_12 = x_228;
x_13 = x_234;
x_14 = x_229;
x_15 = x_233;
x_16 = x_254;
goto block_26;
}
}
else
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; 
x_255 = lean_box(0);
x_256 = lean_array_uset(x_235, x_240, x_255);
lean_inc(x_234);
x_257 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_SynthInstance_newSubgoal_spec__0___redArg(x_210, x_234, x_241);
x_258 = lean_array_uset(x_256, x_240, x_257);
lean_inc(x_234);
if (lean_is_scalar(x_236)) {
 x_259 = lean_alloc_ctor(0, 2, 0);
} else {
 x_259 = x_236;
}
lean_ctor_set(x_259, 0, x_234);
lean_ctor_set(x_259, 1, x_258);
x_12 = x_228;
x_13 = x_234;
x_14 = x_229;
x_15 = x_233;
x_16 = x_259;
goto block_26;
}
}
}
}
else
{
uint8_t x_356; 
lean_dec(x_30);
lean_dec(x_28);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_356 = !lean_is_exclusive(x_31);
if (x_356 == 0)
{
return x_31;
}
else
{
lean_object* x_357; lean_object* x_358; lean_object* x_359; 
x_357 = lean_ctor_get(x_31, 0);
x_358 = lean_ctor_get(x_31, 1);
lean_inc(x_358);
lean_inc(x_357);
lean_dec(x_31);
x_359 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_359, 0, x_357);
lean_ctor_set(x_359, 1, x_358);
return x_359;
}
}
block_26:
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_st_ref_set(x_14, x_16, x_15);
lean_dec(x_14);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_12);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_13);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set(x_17, 0, x_21);
return x_17;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_dec(x_17);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_12);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_13);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_22);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Elab_Tactic_Omega_lookup_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_isTracingEnabledFor___at___Lean_Elab_Tactic_Omega_lookup_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Elab_Tactic_Omega_lookup_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_5);
lean_dec(x_5);
x_13 = l_Lean_isTracingEnabledFor___at___Lean_Elab_Tactic_Omega_lookup_spec__0(x_1, x_2, x_3, x_4, x_12, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Elab_Tactic_Omega_lookup_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_6);
lean_dec(x_6);
x_14 = l_List_mapM_loop___at___Lean_Elab_Tactic_Omega_lookup_spec__1(x_1, x_2, x_3, x_4, x_5, x_13, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_6);
lean_dec(x_6);
x_14 = l_Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__2(x_1, x_2, x_3, x_4, x_5, x_13, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___Lean_Elab_Tactic_Omega_lookup_spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_foldrM___at___Lean_Elab_Tactic_Omega_lookup_spec__3(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_Elab_Tactic_Omega_lookup_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldrMUnsafe_fold___at___Lean_Elab_Tactic_Omega_lookup_spec__4(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_lookup___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_5);
lean_dec(x_5);
x_13 = l_Lean_Elab_Tactic_Omega_lookup(x_1, x_2, x_3, x_4, x_12, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
lean_object* initialize_Init_Omega_LinearCombo(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Omega_Int(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Omega_Logic(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_BitVec_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_AppBuilder(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Canonicalizer(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Data_HashMap_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Data_HashSet_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Omega_OmegaM(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Omega_LinearCombo(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega_Int(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega_Logic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_BitVec_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_AppBuilder(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Canonicalizer(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_HashMap_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_HashSet_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
