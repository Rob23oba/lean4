// Lean compiler output
// Module: Lean.Meta.Tactic.Simp.SimpCongrTheorems
// Imports: Lean.ScopedEnvExtension Lean.Util.Recognizers Lean.Util.CollectMVars Lean.Meta.Basic
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
lean_object* l_Lean_Name_reprPrec(lean_object*, lean_object*);
lean_object* l_Lean_getAttrParamOptPrio(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedSimpCongrTheorem;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkSimpCongrTheorem_spec__7_spec__7___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___Lean_Meta_mkSimpCongrTheorem_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpCongrTheorems_get___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_reprSimpCongrTheorem____x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems___hyg_53_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarIdSet_insert(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_toList___at_____private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_reprSimpCongrTheorems____x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems___hyg_185__spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Std_Format_fill(lean_object*);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getSimpCongrTheorems(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkSimpCongrTheorem_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkSimpCongrTheorem_spec__7_spec__7(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_findConstVal_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at_____private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_reprSimpCongrTheorems____x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems___hyg_185__spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkSimpCongrTheorem_spec__7_spec__7___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___Lean_mkConstWithLevelParams___at___Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at_____private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_reprSimpCongrTheorems____x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems___hyg_185__spec__1___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_addSimpCongrTheorem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkSimpCongrTheorem_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Format_joinSep(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getSimpCongrTheorems___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_find_x3f___at___Lean_addAliasEntry_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_reprSimpCongrTheorem___redArg___lam__0____x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems___hyg_53_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__0____x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems___hyg_1861_(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpCongrTheorems_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedSimpCongrTheorems;
LEAN_EXPORT lean_object* l_List_repr___at_____private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_reprSimpCongrTheorems____x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems___hyg_185__spec__1(lean_object*, lean_object*);
lean_object* l_Lean_SMap_insert___at_____private_Lean_Environment_0__Lean_Kernel_Environment_add_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpCongrTheorem_onlyMVarsAt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkSimpCongrTheorem_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_reprSimpCongrTheorem___redArg____x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems___hyg_53_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___Lean_mkConstWithLevelParams___at___Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___Lean_Meta_addSimpCongrTheorem_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_mkSimpCongrTheorem_onlyMVarsAt___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_addSimpCongrTheorem(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getSimpCongrTheorems___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkSimpCongrTheorem_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___Lean_Meta_addSimpCongrTheorem_spec__0___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at_____private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_reprSimpCongrTheorems____x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems___hyg_185__spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_reprSimpCongrTheorems____x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems___hyg_185____boxed(lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
uint8_t l_Lean_Expr_isMVar(lean_object*);
lean_object* l_Lean_RBNode_findCore___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimApp_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Expr_withAppAux___at___Lean_Meta_mkSimpCongrTheorem_spec__11_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_toList___at_____private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_reprSimpCongrTheorems____x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems___hyg_185__spec__0___redArg(lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Meta_mkSimpCongrTheorem_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkSimpCongrTheorem_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems___hyg_1861_(lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at___Prod_repr___at___List_repr___at_____private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_reprSimpCongrTheorems____x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems___hyg_185__spec__1_spec__1_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_toList___at_____private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_reprSimpCongrTheorems____x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems___hyg_185__spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkSimpCongrTheorem_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_constName_x21(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_reprSimpCongrTheorem____x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems___hyg_53____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Expr_withAppAux___at___Lean_Meta_mkSimpCongrTheorem_spec__9_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__1____x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems___hyg_1861_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__1____x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems___hyg_1861____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__0____x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems___hyg_362_(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkSimpCongrTheorem_spec__5(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_fold___at___Lean_getRevAliases_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___Lean_Meta_mkSimpCongrTheorem_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkSimpCongrTheorem_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at___Prod_repr___at___List_repr___at_____private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_reprSimpCongrTheorems____x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems___hyg_185__spec__1_spec__1_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_reprSimpCongrTheorems___redArg____x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems___hyg_185_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___Lean_Meta_addSimpCongrTheorem_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_repr___at___List_repr___at_____private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_reprSimpCongrTheorems____x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems___hyg_185__spec__1_spec__1___boxed(lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Meta_mkSimpCongrTheorem_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_reprSimpCongrTheorems____x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems___hyg_185_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReprSimpCongrTheorem;
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_toList___at_____private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_reprSimpCongrTheorems____x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems___hyg_185__spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpCongrTheorem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_mkSimpCongrTheorem_onlyMVarsAt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_SMap_switch___at___Lean_initFn____x40_Lean_Namespace___hyg_3__spec__4___redArg(lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkSimpCongrTheorem_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_CollectMVars_visit(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_repr___at___List_repr___at_____private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_reprSimpCongrTheorems____x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems___hyg_185__spec__1_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Expr_withAppAux___at___Lean_Meta_mkSimpCongrTheorem_spec__11_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
uint8_t l_Lean_BinderInfo_isExplicit(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems___hyg_362_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Meta_mkSimpCongrTheorem_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at___Prod_repr___at___List_repr___at_____private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_reprSimpCongrTheorems____x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems___hyg_185__spec__1_spec__1_spec__1___redArg___lam__0(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_repr___at___List_repr___at_____private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_reprSimpCongrTheorems____x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems___hyg_185__spec__1_spec__1(lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_congrExtension;
lean_object* l_List_reverse___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_mkConstWithLevelParams___at___Lean_Meta_mkSimpCongrTheorem_spec__1_spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallMetaTelescopeReducing(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___at___Lean_Meta_getParamNames_spec__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpCongrTheorem_onlyMVarsAt___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getSimpCongrTheorems___redArg___boxed(lean_object*, lean_object*);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_List_repr___at___Prod_repr___at___List_repr___at_____private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_reprSimpCongrTheorems____x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems___hyg_185__spec__1_spec__1_spec__1(lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__0____x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems___hyg_362____boxed(lean_object*);
lean_object* l_Lean_registerBuiltinAttribute(lean_object*, lean_object*);
lean_object* l_Std_Format_joinSep___at___Lean_Syntax_formatStxAux_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkSimpCongrTheorem_spec__7(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkSimpCongrTheorem_spec__7_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_addSimpCongrTheoremEntry(lean_object*, lean_object*);
lean_object* l_Lean_Level_param___override(lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_addSimpCongrTheoremEntry_insert(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_reprSimpCongrTheorems___redArg____x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems___hyg_185____boxed(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Meta_mkSimpCongrTheorem_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___Lean_Meta_addSimpCongrTheorem_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReprSimpCongrTheorems;
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_addCore___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkSimpCongrTheorem_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_find_expr(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpCongrTheorem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Expr_withAppAux___at___Lean_Meta_mkSimpCongrTheorem_spec__9_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConst(lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkSimpCongrTheorem_spec__6(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_toList___at_____private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_reprSimpCongrTheorems____x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems___hyg_185__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__0____x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems___hyg_1861____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Meta_instInhabitedSimpCongrTheorem() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = l_Array_empty(lean_box(0));
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_1);
lean_ctor_set(x_4, 2, x_2);
lean_ctor_set(x_4, 3, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_reprSimpCongrTheorem___redArg___lam__0____x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems___hyg_53_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l___private_Init_Data_Repr_0__Nat_reprFast(x_1);
x_3 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_reprSimpCongrTheorem___redArg____x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems___hyg_53_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_2 = lean_mk_string_unchecked("{ ", 2, 2);
x_3 = lean_box(0);
x_4 = lean_mk_string_unchecked("theoremName", 11, 11);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_mk_string_unchecked(" := ", 4, 4);
x_8 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_8, 0, x_7);
lean_inc(x_8);
x_9 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(15u);
x_11 = lean_nat_to_int(x_10);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Lean_Name_reprPrec(x_12, x_13);
x_15 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_17, 0, x_15);
x_18 = lean_unbox(x_16);
lean_ctor_set_uint8(x_17, sizeof(void*)*1, x_18);
x_19 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_19, 0, x_9);
lean_ctor_set(x_19, 1, x_17);
x_20 = lean_mk_string_unchecked(",", 1, 1);
x_21 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_21, 0, x_20);
lean_inc(x_21);
x_22 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_box(1);
x_24 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_mk_string_unchecked("funName", 7, 7);
x_26 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_26);
lean_inc(x_8);
x_28 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_8);
x_29 = lean_unsigned_to_nat(11u);
x_30 = lean_nat_to_int(x_29);
x_31 = lean_ctor_get(x_1, 1);
lean_inc(x_31);
x_32 = l_Lean_Name_reprPrec(x_31, x_13);
x_33 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_34, 0, x_33);
x_35 = lean_unbox(x_16);
lean_ctor_set_uint8(x_34, sizeof(void*)*1, x_35);
x_36 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_36, 0, x_28);
lean_ctor_set(x_36, 1, x_34);
lean_inc(x_21);
x_37 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_21);
x_38 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_23);
x_39 = lean_mk_string_unchecked("hypothesesPos", 13, 13);
x_40 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_40, 0, x_39);
x_41 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set(x_41, 1, x_40);
lean_inc(x_8);
x_42 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_8);
x_43 = lean_unsigned_to_nat(17u);
x_44 = lean_nat_to_int(x_43);
x_76 = lean_ctor_get(x_1, 2);
lean_inc(x_76);
x_77 = lean_array_get_size(x_76);
x_78 = lean_nat_dec_eq(x_77, x_13);
lean_dec(x_77);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_79 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_reprSimpCongrTheorem___redArg___lam__0____x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems___hyg_53_), 1, 0);
x_80 = lean_mk_string_unchecked("#[", 2, 2);
x_81 = lean_array_to_list(x_76);
lean_inc(x_21);
x_82 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_82, 0, x_21);
lean_ctor_set(x_82, 1, x_23);
x_83 = l_Std_Format_joinSep(lean_box(0), x_79, x_81, x_82);
x_84 = lean_mk_string_unchecked("]", 1, 1);
x_85 = lean_unsigned_to_nat(2u);
x_86 = lean_nat_to_int(x_85);
x_87 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_87, 0, x_80);
x_88 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_83);
x_89 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_89, 0, x_84);
x_90 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
x_91 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_91, 0, x_86);
lean_ctor_set(x_91, 1, x_90);
x_92 = l_Std_Format_fill(x_91);
x_45 = x_92;
goto block_75;
}
else
{
lean_object* x_93; lean_object* x_94; 
lean_dec(x_76);
x_93 = lean_mk_string_unchecked("#[]", 3, 3);
x_94 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_94, 0, x_93);
x_45 = x_94;
goto block_75;
}
block_75:
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_46 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_47, 0, x_46);
x_48 = lean_unbox(x_16);
lean_ctor_set_uint8(x_47, sizeof(void*)*1, x_48);
x_49 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_49, 0, x_42);
lean_ctor_set(x_49, 1, x_47);
x_50 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_21);
x_51 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_23);
x_52 = lean_mk_string_unchecked("priority", 8, 8);
x_53 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_53, 0, x_52);
x_54 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_54, 0, x_51);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_8);
x_56 = lean_unsigned_to_nat(12u);
x_57 = lean_nat_to_int(x_56);
x_58 = lean_ctor_get(x_1, 3);
lean_inc(x_58);
lean_dec(x_1);
x_59 = l___private_Init_Data_Repr_0__Nat_reprFast(x_58);
x_60 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_60, 0, x_59);
x_61 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_61, 0, x_57);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_62, 0, x_61);
x_63 = lean_unbox(x_16);
lean_ctor_set_uint8(x_62, sizeof(void*)*1, x_63);
x_64 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_64, 0, x_55);
lean_ctor_set(x_64, 1, x_62);
x_65 = lean_mk_string_unchecked(" }", 2, 2);
x_66 = lean_unsigned_to_nat(2u);
x_67 = lean_nat_to_int(x_66);
x_68 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_68, 0, x_2);
x_69 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_64);
x_70 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_70, 0, x_65);
x_71 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
x_72 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_72, 0, x_67);
lean_ctor_set(x_72, 1, x_71);
x_73 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_73, 0, x_72);
x_74 = lean_unbox(x_16);
lean_ctor_set_uint8(x_73, sizeof(void*)*1, x_74);
return x_73;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_reprSimpCongrTheorem____x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems___hyg_53_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_reprSimpCongrTheorem___redArg____x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems___hyg_53_(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_reprSimpCongrTheorem____x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems___hyg_53____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_reprSimpCongrTheorem____x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems___hyg_53_(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_instReprSimpCongrTheorem() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_reprSimpCongrTheorem____x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems___hyg_53____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedSimpCongrTheorems() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
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
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_unbox(x_1);
lean_ctor_set_uint8(x_14, sizeof(void*)*2, x_15);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_toList___at_____private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_reprSimpCongrTheorems____x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems___hyg_185__spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_toList___at_____private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_reprSimpCongrTheorems____x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems___hyg_185__spec__0___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_alloc_closure((void*)(l_Lean_SMap_toList___at_____private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_reprSimpCongrTheorems____x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems___hyg_185__spec__0___redArg___lam__0), 3, 0);
x_3 = lean_box(0);
x_4 = l_Lean_SMap_fold___at___Lean_getRevAliases_spec__0(lean_box(0), lean_box(0), x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_toList___at_____private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_reprSimpCongrTheorems____x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems___hyg_185__spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_SMap_toList___at_____private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_reprSimpCongrTheorems____x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems___hyg_185__spec__0___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___Prod_repr___at___List_repr___at_____private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_reprSimpCongrTheorems____x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems___hyg_185__spec__1_spec__1_spec__1___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_reprSimpCongrTheorem___redArg____x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems___hyg_53_(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___Prod_repr___at___List_repr___at_____private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_reprSimpCongrTheorems____x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems___hyg_185__spec__1_spec__1_spec__1___redArg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_mk_string_unchecked("[]", 2, 2);
x_3 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_4 = lean_alloc_closure((void*)(l_List_repr___at___Prod_repr___at___List_repr___at_____private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_reprSimpCongrTheorems____x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems___hyg_185__spec__1_spec__1_spec__1___redArg___lam__0), 1, 0);
x_5 = lean_mk_string_unchecked("[", 1, 1);
x_6 = lean_mk_string_unchecked(",", 1, 1);
x_7 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_box(1);
x_9 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
lean_inc(x_1);
x_10 = l_Std_Format_joinSep(lean_box(0), x_4, x_1, x_9);
x_11 = !lean_is_exclusive(x_1);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_12 = lean_ctor_get(x_1, 1);
lean_dec(x_12);
x_13 = lean_ctor_get(x_1, 0);
lean_dec(x_13);
x_14 = lean_mk_string_unchecked("]", 1, 1);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_to_int(x_15);
x_17 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_17, 0, x_5);
lean_ctor_set_tag(x_1, 5);
lean_ctor_set(x_1, 1, x_10);
lean_ctor_set(x_1, 0, x_17);
x_18 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_18, 0, x_14);
x_19 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_20, 0, x_16);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_22, 0, x_20);
x_23 = lean_unbox(x_21);
lean_ctor_set_uint8(x_22, sizeof(void*)*1, x_23);
return x_22;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
lean_dec(x_1);
x_24 = lean_mk_string_unchecked("]", 1, 1);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_to_int(x_25);
x_27 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_27, 0, x_5);
x_28 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_10);
x_29 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_29, 0, x_24);
x_30 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_31, 0, x_26);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_33, 0, x_31);
x_34 = lean_unbox(x_32);
lean_ctor_set_uint8(x_33, sizeof(void*)*1, x_34);
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l_List_repr___at___Prod_repr___at___List_repr___at_____private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_reprSimpCongrTheorems____x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems___hyg_185__spec__1_spec__1_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_repr___at___Prod_repr___at___List_repr___at_____private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_reprSimpCongrTheorems____x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems___hyg_185__spec__1_spec__1_spec__1___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___List_repr___at_____private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_reprSimpCongrTheorems____x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems___hyg_185__spec__1_spec__1___redArg(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_mk_string_unchecked("(", 1, 1);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Lean_Name_reprPrec(x_3, x_6);
x_8 = lean_box(0);
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 1, x_8);
lean_ctor_set(x_1, 0, x_7);
x_9 = l_List_repr___at___Prod_repr___at___List_repr___at_____private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_reprSimpCongrTheorems____x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems___hyg_185__spec__1_spec__1_spec__1___redArg(x_4);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_1);
x_11 = l_List_reverse___redArg(x_10);
x_12 = lean_mk_string_unchecked(",", 1, 1);
x_13 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_box(1);
x_15 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Std_Format_joinSep___at___Lean_Syntax_formatStxAux_spec__1(x_11, x_15);
x_17 = lean_mk_string_unchecked(")", 1, 1);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_to_int(x_18);
x_20 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_20, 0, x_5);
x_21 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_16);
x_22 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_22, 0, x_17);
x_23 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_24, 0, x_19);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_26, 0, x_24);
x_27 = lean_unbox(x_25);
lean_ctor_set_uint8(x_26, sizeof(void*)*1, x_27);
return x_26;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_28 = lean_ctor_get(x_1, 0);
x_29 = lean_ctor_get(x_1, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_1);
x_30 = lean_mk_string_unchecked("(", 1, 1);
x_31 = lean_unsigned_to_nat(0u);
x_32 = l_Lean_Name_reprPrec(x_28, x_31);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = l_List_repr___at___Prod_repr___at___List_repr___at_____private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_reprSimpCongrTheorems____x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems___hyg_185__spec__1_spec__1_spec__1___redArg(x_29);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
x_37 = l_List_reverse___redArg(x_36);
x_38 = lean_mk_string_unchecked(",", 1, 1);
x_39 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_39, 0, x_38);
x_40 = lean_box(1);
x_41 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Std_Format_joinSep___at___Lean_Syntax_formatStxAux_spec__1(x_37, x_41);
x_43 = lean_mk_string_unchecked(")", 1, 1);
x_44 = lean_unsigned_to_nat(1u);
x_45 = lean_nat_to_int(x_44);
x_46 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_46, 0, x_30);
x_47 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_42);
x_48 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_48, 0, x_43);
x_49 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_50, 0, x_45);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_box(0);
x_52 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_52, 0, x_50);
x_53 = lean_unbox(x_51);
lean_ctor_set_uint8(x_52, sizeof(void*)*1, x_53);
return x_52;
}
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___List_repr___at_____private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_reprSimpCongrTheorems____x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems___hyg_185__spec__1_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Prod_repr___at___List_repr___at_____private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_reprSimpCongrTheorems____x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems___hyg_185__spec__1_spec__1___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_repr___at_____private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_reprSimpCongrTheorems____x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems___hyg_185__spec__1___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Prod_repr___at___List_repr___at_____private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_reprSimpCongrTheorems____x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems___hyg_185__spec__1_spec__1___redArg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_repr___at_____private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_reprSimpCongrTheorems____x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems___hyg_185__spec__1___redArg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_mk_string_unchecked("[]", 2, 2);
x_3 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_4 = lean_alloc_closure((void*)(l_List_repr___at_____private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_reprSimpCongrTheorems____x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems___hyg_185__spec__1___redArg___lam__0), 1, 0);
x_5 = lean_mk_string_unchecked("[", 1, 1);
x_6 = lean_mk_string_unchecked(",", 1, 1);
x_7 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_box(1);
x_9 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
lean_inc(x_1);
x_10 = l_Std_Format_joinSep(lean_box(0), x_4, x_1, x_9);
x_11 = !lean_is_exclusive(x_1);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_12 = lean_ctor_get(x_1, 1);
lean_dec(x_12);
x_13 = lean_ctor_get(x_1, 0);
lean_dec(x_13);
x_14 = lean_mk_string_unchecked("]", 1, 1);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_to_int(x_15);
x_17 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_17, 0, x_5);
lean_ctor_set_tag(x_1, 5);
lean_ctor_set(x_1, 1, x_10);
lean_ctor_set(x_1, 0, x_17);
x_18 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_18, 0, x_14);
x_19 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_20, 0, x_16);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_22, 0, x_20);
x_23 = lean_unbox(x_21);
lean_ctor_set_uint8(x_22, sizeof(void*)*1, x_23);
return x_22;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
lean_dec(x_1);
x_24 = lean_mk_string_unchecked("]", 1, 1);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_to_int(x_25);
x_27 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_27, 0, x_5);
x_28 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_10);
x_29 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_29, 0, x_24);
x_30 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_31, 0, x_26);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_33, 0, x_31);
x_34 = lean_unbox(x_32);
lean_ctor_set_uint8(x_33, sizeof(void*)*1, x_34);
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l_List_repr___at_____private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_reprSimpCongrTheorems____x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems___hyg_185__spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_repr___at_____private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_reprSimpCongrTheorems____x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems___hyg_185__spec__1___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_reprSimpCongrTheorems___redArg____x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems___hyg_185_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_2 = lean_mk_string_unchecked("{ ", 2, 2);
x_3 = lean_box(0);
x_4 = lean_mk_string_unchecked("lemmas", 6, 6);
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
x_10 = lean_unsigned_to_nat(10u);
x_11 = lean_nat_to_int(x_10);
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Lean_SMap_toList___at_____private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_reprSimpCongrTheorems____x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems___hyg_185__spec__0___redArg(x_1);
x_14 = l_List_repr___at_____private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_reprSimpCongrTheorems____x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems___hyg_185__spec__1___redArg(x_13);
x_15 = lean_mk_string_unchecked(".toSMap", 7, 7);
x_16 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Repr_addAppParen(x_17, x_12);
x_19 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_19, 0, x_11);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_21, 0, x_19);
x_22 = lean_unbox(x_20);
lean_ctor_set_uint8(x_21, sizeof(void*)*1, x_22);
x_23 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_23, 0, x_9);
lean_ctor_set(x_23, 1, x_21);
x_24 = lean_mk_string_unchecked(" }", 2, 2);
x_25 = lean_unsigned_to_nat(2u);
x_26 = lean_nat_to_int(x_25);
x_27 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_27, 0, x_2);
x_28 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_23);
x_29 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_29, 0, x_24);
x_30 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_31, 0, x_26);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_32, 0, x_31);
x_33 = lean_unbox(x_20);
lean_ctor_set_uint8(x_32, sizeof(void*)*1, x_33);
return x_32;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_reprSimpCongrTheorems____x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems___hyg_185_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_reprSimpCongrTheorems___redArg____x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems___hyg_185_(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_toList___at_____private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_reprSimpCongrTheorems____x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems___hyg_185__spec__0___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_SMap_toList___at_____private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_reprSimpCongrTheorems____x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems___hyg_185__spec__0___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_toList___at_____private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_reprSimpCongrTheorems____x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems___hyg_185__spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_SMap_toList___at_____private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_reprSimpCongrTheorems____x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems___hyg_185__spec__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___Prod_repr___at___List_repr___at_____private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_reprSimpCongrTheorems____x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems___hyg_185__spec__1_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_repr___at___Prod_repr___at___List_repr___at_____private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_reprSimpCongrTheorems____x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems___hyg_185__spec__1_spec__1_spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___List_repr___at_____private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_reprSimpCongrTheorems____x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems___hyg_185__spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Prod_repr___at___List_repr___at_____private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_reprSimpCongrTheorems____x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems___hyg_185__spec__1_spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_repr___at_____private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_reprSimpCongrTheorems____x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems___hyg_185__spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_repr___at_____private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_reprSimpCongrTheorems____x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems___hyg_185__spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_reprSimpCongrTheorems___redArg____x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems___hyg_185____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_reprSimpCongrTheorems___redArg____x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems___hyg_185_(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_reprSimpCongrTheorems____x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems___hyg_185____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_reprSimpCongrTheorems____x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems___hyg_185_(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_instReprSimpCongrTheorems() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_reprSimpCongrTheorems____x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems___hyg_185____boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpCongrTheorems_get(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_SMap_find_x3f___at___Lean_addAliasEntry_spec__0(lean_box(0), x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpCongrTheorems_get___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_SimpCongrTheorems_get(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addSimpCongrTheoremEntry_insert(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 3);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
x_8 = lean_nat_dec_le(x_6, x_7);
lean_dec(x_7);
lean_dec(x_6);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_2, 1);
lean_dec(x_10);
x_11 = lean_ctor_get(x_2, 0);
lean_dec(x_11);
x_12 = l_Lean_Meta_addSimpCongrTheoremEntry_insert(x_1, x_5);
lean_ctor_set(x_2, 1, x_12);
return x_2;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_2);
x_13 = l_Lean_Meta_addSimpCongrTheoremEntry_insert(x_1, x_5);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
else
{
lean_object* x_15; 
lean_dec(x_5);
lean_dec(x_4);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_2);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addSimpCongrTheoremEntry(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
lean_inc(x_1);
x_4 = l_Lean_SMap_find_x3f___at___Lean_addAliasEntry_spec__0(lean_box(0), x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_5);
x_7 = l_Lean_SMap_insert___at_____private_Lean_Environment_0__Lean_Kernel_Environment_add_spec__0___redArg(x_1, x_3, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
lean_dec(x_4);
x_9 = l_Lean_Meta_addSimpCongrTheoremEntry_insert(x_2, x_8);
x_10 = l_Lean_SMap_insert___at_____private_Lean_Environment_0__Lean_Kernel_Environment_add_spec__0___redArg(x_1, x_3, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__0____x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems___hyg_362_(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_SMap_switch___at___Lean_initFn____x40_Lean_Namespace___hyg_3__spec__4___redArg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems___hyg_362_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_initFn___lam__0____x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems___hyg_362____boxed), 1, 0);
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Meta", 4, 4);
x_5 = lean_mk_string_unchecked("congrExtension", 14, 14);
x_6 = l_Lean_Name_mkStr3(x_3, x_4, x_5);
x_7 = lean_alloc_closure((void*)(l_Lean_Meta_addSimpCongrTheoremEntry), 2, 0);
x_8 = lean_box(1);
x_9 = lean_unsigned_to_nat(8u);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_unsigned_to_nat(2u);
x_12 = lean_nat_shiftl(x_9, x_11);
x_13 = lean_unsigned_to_nat(3u);
x_14 = lean_nat_div(x_12, x_13);
lean_dec(x_12);
x_15 = l_Nat_nextPowerOfTwo(x_14);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = lean_mk_array(x_15, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_10);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_unbox(x_8);
lean_ctor_set_uint8(x_21, sizeof(void*)*2, x_22);
x_23 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_23, 0, x_6);
lean_ctor_set(x_23, 1, x_7);
lean_ctor_set(x_23, 2, x_21);
lean_ctor_set(x_23, 3, x_2);
x_24 = l_Lean_registerSimpleScopedEnvExtension___redArg(x_23, x_1);
return x_24;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__0____x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems___hyg_362____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_initFn___lam__0____x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems___hyg_362_(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_mkSimpCongrTheorem_onlyMVarsAt___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_Expr_isMVar(x_2);
if (x_3 == 0)
{
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Expr_mvarId_x21(x_2);
x_5 = l_Lean_RBNode_findCore___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimApp_spec__1___redArg(x_1, x_4);
lean_dec(x_4);
if (lean_obj_tag(x_5) == 0)
{
return x_3;
}
else
{
lean_object* x_6; uint8_t x_7; 
lean_dec(x_5);
x_6 = lean_box(0);
x_7 = lean_unbox(x_6);
return x_7;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_mkSimpCongrTheorem_onlyMVarsAt(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_mkSimpCongrTheorem_onlyMVarsAt___lam__0___boxed), 2, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = lean_find_expr(x_3, x_1);
lean_dec(x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_box(1);
x_6 = lean_unbox(x_5);
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
lean_dec(x_4);
x_7 = lean_box(0);
x_8 = lean_unbox(x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpCongrTheorem_onlyMVarsAt___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_mkSimpCongrTheorem_onlyMVarsAt___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpCongrTheorem_onlyMVarsAt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_mkSimpCongrTheorem_onlyMVarsAt(x_1, x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkSimpCongrTheorem_spec__0___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; 
x_8 = lean_array_uget(x_1, x_3);
x_9 = l_Lean_MVarIdSet_insert(x_4, x_8);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_usize_of_nat(x_10);
x_12 = lean_usize_add(x_3, x_11);
x_3 = x_12;
x_4 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkSimpCongrTheorem_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkSimpCongrTheorem_spec__0___redArg(x_1, x_2, x_3, x_4, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___Lean_mkConstWithLevelParams___at___Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_box(0);
x_13 = lean_unbox(x_12);
lean_inc(x_1);
x_14 = l_Lean_Environment_findConstVal_x3f(x_11, x_1, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_free_object(x_7);
x_15 = lean_mk_string_unchecked("unknown constant '", 18, 18);
x_16 = l_Lean_stringToMessageData(x_15);
lean_dec(x_15);
x_17 = lean_box(0);
x_18 = l_Lean_Expr_const___override(x_1, x_17);
x_19 = l_Lean_MessageData_ofExpr(x_18);
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_16);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_mk_string_unchecked("'", 1, 1);
x_22 = l_Lean_stringToMessageData(x_21);
lean_dec(x_21);
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_23, x_2, x_3, x_4, x_5, x_10);
return x_24;
}
else
{
lean_object* x_25; 
lean_dec(x_1);
x_25 = lean_ctor_get(x_14, 0);
lean_inc(x_25);
lean_dec(x_14);
lean_ctor_set(x_7, 0, x_25);
return x_7;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_26 = lean_ctor_get(x_7, 0);
x_27 = lean_ctor_get(x_7, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_7);
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_box(0);
x_30 = lean_unbox(x_29);
lean_inc(x_1);
x_31 = l_Lean_Environment_findConstVal_x3f(x_28, x_1, x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_32 = lean_mk_string_unchecked("unknown constant '", 18, 18);
x_33 = l_Lean_stringToMessageData(x_32);
lean_dec(x_32);
x_34 = lean_box(0);
x_35 = l_Lean_Expr_const___override(x_1, x_34);
x_36 = l_Lean_MessageData_ofExpr(x_35);
x_37 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_37, 0, x_33);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_mk_string_unchecked("'", 1, 1);
x_39 = l_Lean_stringToMessageData(x_38);
lean_dec(x_38);
x_40 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_39);
x_41 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_40, x_2, x_3, x_4, x_5, x_27);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_1);
x_42 = lean_ctor_get(x_31, 0);
lean_inc(x_42);
lean_dec(x_31);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_27);
return x_43;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_mkConstWithLevelParams___at___Lean_Meta_mkSimpCongrTheorem_spec__1_spec__2(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Lean_Level_param___override(x_5);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_7);
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_11 = l_Lean_Level_param___override(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_2);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___Lean_Meta_mkSimpCongrTheorem_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_1);
x_7 = l_Lean_getConstVal___at___Lean_mkConstWithLevelParams___at___Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_box(0);
x_12 = l_List_mapTR_loop___at___Lean_mkConstWithLevelParams___at___Lean_Meta_mkSimpCongrTheorem_spec__1_spec__2(x_10, x_11);
x_13 = l_Lean_Expr_const___override(x_1, x_12);
lean_ctor_set(x_7, 0, x_13);
return x_7;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_7, 0);
x_15 = lean_ctor_get(x_7, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_7);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_box(0);
x_18 = l_List_mapTR_loop___at___Lean_mkConstWithLevelParams___at___Lean_Meta_mkSimpCongrTheorem_spec__1_spec__2(x_16, x_17);
x_19 = l_Lean_Expr_const___override(x_1, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_15);
return x_20;
}
}
else
{
uint8_t x_21; 
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_7);
if (x_21 == 0)
{
return x_7;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_7, 0);
x_23 = lean_ctor_get(x_7, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_7);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkSimpCongrTheorem_spec__4(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_3, x_2);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; size_t x_27; size_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; size_t x_33; size_t x_34; 
x_12 = lean_array_uget(x_1, x_3);
x_13 = lean_unsigned_to_nat(8u);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_unsigned_to_nat(2u);
x_16 = lean_nat_shiftl(x_13, x_15);
x_17 = lean_unsigned_to_nat(3u);
x_18 = lean_nat_div(x_16, x_17);
lean_dec(x_16);
x_19 = l_Nat_nextPowerOfTwo(x_18);
lean_dec(x_18);
x_20 = lean_box(0);
x_21 = lean_mk_array(x_19, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_14);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_mk_empty_array_with_capacity(x_14);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_CollectMVars_visit(x_12, x_24);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_array_size(x_26);
x_28 = lean_usize_of_nat(x_14);
x_29 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkSimpCongrTheorem_spec__0___redArg(x_26, x_27, x_28, x_4, x_9);
lean_dec(x_26);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_usize_of_nat(x_32);
x_34 = lean_usize_add(x_3, x_33);
x_3 = x_34;
x_4 = x_30;
x_9 = x_31;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkSimpCongrTheorem_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_19; 
x_19 = lean_usize_dec_lt(x_5, x_4);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_2);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_6);
lean_ctor_set(x_20, 1, x_11);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
lean_dec(x_6);
x_21 = lean_box(0);
x_22 = lean_array_uget(x_3, x_5);
x_23 = l_Lean_Expr_isFVar(x_22);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_24 = lean_mk_string_unchecked("invalid 'congr' theorem, parameter #", 36, 36);
x_25 = l_Lean_stringToMessageData(x_24);
lean_dec(x_24);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_1, x_26);
x_28 = l___private_Init_Data_Repr_0__Nat_reprFast(x_27);
x_29 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = l_Lean_MessageData_ofFormat(x_29);
x_31 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_31, 0, x_25);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_mk_string_unchecked(" is not a valid hypothesis, the right-hand-side argument is not local variable", 78, 78);
x_33 = l_Lean_stringToMessageData(x_32);
lean_dec(x_32);
x_34 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_33);
x_35 = l_Lean_indentExpr(x_2);
x_36 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_mk_string_unchecked("", 0, 0);
x_38 = l_Lean_stringToMessageData(x_37);
lean_dec(x_37);
x_39 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_39, x_7, x_8, x_9, x_10, x_11);
return x_40;
}
else
{
x_12 = x_21;
x_13 = x_11;
goto block_18;
}
}
block_18:
{
lean_object* x_14; size_t x_15; size_t x_16; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_usize_of_nat(x_14);
x_16 = lean_usize_add(x_5, x_15);
x_5 = x_16;
x_6 = x_12;
x_11 = x_13;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkSimpCongrTheorem_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_20; 
x_20 = lean_usize_dec_lt(x_5, x_4);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_6);
lean_ctor_set(x_21, 1, x_11);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_array_uget(x_3, x_5);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_23 = lean_infer_type(x_22, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_1);
x_26 = l_Lean_Meta_mkSimpCongrTheorem_onlyMVarsAt(x_24, x_1);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
lean_dec(x_1);
x_27 = lean_mk_string_unchecked("invalid 'congr' theorem, argument #", 35, 35);
x_28 = l_Lean_stringToMessageData(x_27);
lean_dec(x_27);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_add(x_6, x_29);
lean_dec(x_6);
x_31 = l___private_Init_Data_Repr_0__Nat_reprFast(x_30);
x_32 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = l_Lean_MessageData_ofFormat(x_32);
x_34 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_34, 0, x_28);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_mk_string_unchecked(" of parameter #", 15, 15);
x_36 = l_Lean_stringToMessageData(x_35);
lean_dec(x_35);
x_37 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_nat_add(x_2, x_29);
x_39 = l___private_Init_Data_Repr_0__Nat_reprFast(x_38);
x_40 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_40, 0, x_39);
x_41 = l_Lean_MessageData_ofFormat(x_40);
x_42 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_42, 0, x_37);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_mk_string_unchecked(" contains unresolved parameter", 30, 30);
x_44 = l_Lean_stringToMessageData(x_43);
lean_dec(x_43);
x_45 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_44);
x_46 = l_Lean_indentExpr(x_24);
x_47 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_mk_string_unchecked("", 0, 0);
x_49 = l_Lean_stringToMessageData(x_48);
lean_dec(x_48);
x_50 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_49);
x_51 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_50, x_7, x_8, x_9, x_10, x_25);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
return x_51;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_51, 0);
x_54 = lean_ctor_get(x_51, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_51);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
else
{
lean_dec(x_24);
x_12 = x_6;
x_13 = x_25;
goto block_19;
}
}
else
{
uint8_t x_56; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_56 = !lean_is_exclusive(x_23);
if (x_56 == 0)
{
return x_23;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_23, 0);
x_58 = lean_ctor_get(x_23, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_23);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
block_19:
{
lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_12, x_14);
lean_dec(x_12);
x_16 = lean_usize_of_nat(x_14);
x_17 = lean_usize_add(x_5, x_16);
x_5 = x_17;
x_6 = x_15;
x_11 = x_13;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkSimpCongrTheorem_spec__7_spec__7___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_117; lean_object* x_118; lean_object* x_143; lean_object* x_144; lean_object* x_176; lean_object* x_177; lean_object* x_178; uint8_t x_179; 
x_176 = lean_mk_string_unchecked("Eq", 2, 2);
x_177 = l_Lean_Name_mkStr1(x_176);
x_178 = lean_unsigned_to_nat(3u);
x_179 = l_Lean_Expr_isAppOfArity(x_5, x_177, x_178);
lean_dec(x_177);
if (x_179 == 0)
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; uint8_t x_183; 
x_180 = lean_mk_string_unchecked("Iff", 3, 3);
x_181 = l_Lean_Name_mkStr1(x_180);
x_182 = lean_unsigned_to_nat(2u);
x_183 = l_Lean_Expr_isAppOfArity(x_5, x_181, x_182);
lean_dec(x_181);
if (x_183 == 0)
{
lean_object* x_184; lean_object* x_185; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_184 = lean_box(0);
x_185 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_185, 0, x_184);
lean_ctor_set(x_185, 1, x_10);
return x_185;
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_186 = l_Lean_Expr_appFn_x21(x_5);
x_187 = l_Lean_Expr_appArg_x21(x_186);
lean_dec(x_186);
x_188 = l_Lean_Expr_appArg_x21(x_5);
x_143 = x_187;
x_144 = x_188;
goto block_175;
}
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_189 = l_Lean_Expr_appFn_x21(x_5);
x_190 = l_Lean_Expr_appArg_x21(x_189);
lean_dec(x_189);
x_191 = l_Lean_Expr_appArg_x21(x_5);
x_143 = x_190;
x_144 = x_191;
goto block_175;
}
block_39:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; lean_object* x_28; 
x_18 = lean_box(0);
x_19 = l_Lean_Expr_sort___override(x_18);
x_20 = l_Lean_Expr_getAppNumArgs(x_12);
lean_inc(x_20);
x_21 = lean_mk_array(x_20, x_19);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_sub(x_20, x_22);
lean_dec(x_20);
lean_inc(x_12);
x_24 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_12, x_21, x_23);
x_25 = lean_box(0);
x_26 = lean_array_size(x_24);
x_27 = lean_usize_of_nat(x_1);
lean_dec(x_1);
x_28 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkSimpCongrTheorem_spec__5(x_2, x_12, x_24, x_26, x_27, x_25, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_24);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_28, 0);
lean_dec(x_30);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_11);
lean_ctor_set(x_28, 0, x_31);
return x_28;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_28, 1);
lean_inc(x_32);
lean_dec(x_28);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_11);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
else
{
uint8_t x_35; 
lean_dec(x_11);
x_35 = !lean_is_exclusive(x_28);
if (x_35 == 0)
{
return x_28;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_28, 0);
x_37 = lean_ctor_get(x_28, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_28);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
block_116:
{
lean_object* x_47; lean_object* x_48; 
x_47 = l_Lean_Expr_mvarId_x21(x_40);
x_48 = l_Lean_RBNode_findCore___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimApp_spec__1___redArg(x_3, x_47);
lean_dec(x_47);
lean_dec(x_3);
if (lean_obj_tag(x_48) == 0)
{
x_11 = x_40;
x_12 = x_41;
x_13 = x_42;
x_14 = x_43;
x_15 = x_44;
x_16 = x_45;
x_17 = x_46;
goto block_39;
}
else
{
uint8_t x_49; 
lean_dec(x_40);
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; uint8_t x_51; 
x_50 = lean_ctor_get(x_48, 0);
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_52 = lean_ctor_get(x_50, 1);
lean_dec(x_52);
x_53 = lean_ctor_get(x_50, 0);
lean_dec(x_53);
x_54 = lean_mk_string_unchecked("invalid 'congr' theorem, parameter #", 36, 36);
x_55 = l_Lean_stringToMessageData(x_54);
lean_dec(x_54);
x_56 = lean_unsigned_to_nat(1u);
x_57 = lean_nat_add(x_2, x_56);
x_58 = l___private_Init_Data_Repr_0__Nat_reprFast(x_57);
lean_ctor_set_tag(x_48, 3);
lean_ctor_set(x_48, 0, x_58);
x_59 = l_Lean_MessageData_ofFormat(x_48);
lean_ctor_set_tag(x_50, 7);
lean_ctor_set(x_50, 1, x_59);
lean_ctor_set(x_50, 0, x_55);
x_60 = lean_mk_string_unchecked(" is not a valid hypothesis, the right-hand-side head was already resolved", 73, 73);
x_61 = l_Lean_stringToMessageData(x_60);
lean_dec(x_60);
x_62 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_62, 0, x_50);
lean_ctor_set(x_62, 1, x_61);
x_63 = l_Lean_indentExpr(x_41);
x_64 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
x_65 = lean_mk_string_unchecked("", 0, 0);
x_66 = l_Lean_stringToMessageData(x_65);
lean_dec(x_65);
x_67 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_67, 0, x_64);
lean_ctor_set(x_67, 1, x_66);
x_68 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_67, x_42, x_43, x_44, x_45, x_46);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
x_69 = !lean_is_exclusive(x_68);
if (x_69 == 0)
{
return x_68;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_68, 0);
x_71 = lean_ctor_get(x_68, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_68);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_50);
x_73 = lean_mk_string_unchecked("invalid 'congr' theorem, parameter #", 36, 36);
x_74 = l_Lean_stringToMessageData(x_73);
lean_dec(x_73);
x_75 = lean_unsigned_to_nat(1u);
x_76 = lean_nat_add(x_2, x_75);
x_77 = l___private_Init_Data_Repr_0__Nat_reprFast(x_76);
lean_ctor_set_tag(x_48, 3);
lean_ctor_set(x_48, 0, x_77);
x_78 = l_Lean_MessageData_ofFormat(x_48);
x_79 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_79, 0, x_74);
lean_ctor_set(x_79, 1, x_78);
x_80 = lean_mk_string_unchecked(" is not a valid hypothesis, the right-hand-side head was already resolved", 73, 73);
x_81 = l_Lean_stringToMessageData(x_80);
lean_dec(x_80);
x_82 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_82, 0, x_79);
lean_ctor_set(x_82, 1, x_81);
x_83 = l_Lean_indentExpr(x_41);
x_84 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
x_85 = lean_mk_string_unchecked("", 0, 0);
x_86 = l_Lean_stringToMessageData(x_85);
lean_dec(x_85);
x_87 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_87, 0, x_84);
lean_ctor_set(x_87, 1, x_86);
x_88 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_87, x_42, x_43, x_44, x_45, x_46);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
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
if (lean_is_scalar(x_91)) {
 x_92 = lean_alloc_ctor(1, 2, 0);
} else {
 x_92 = x_91;
}
lean_ctor_set(x_92, 0, x_89);
lean_ctor_set(x_92, 1, x_90);
return x_92;
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_93 = lean_ctor_get(x_48, 0);
lean_inc(x_93);
lean_dec(x_48);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_94 = x_93;
} else {
 lean_dec_ref(x_93);
 x_94 = lean_box(0);
}
x_95 = lean_mk_string_unchecked("invalid 'congr' theorem, parameter #", 36, 36);
x_96 = l_Lean_stringToMessageData(x_95);
lean_dec(x_95);
x_97 = lean_unsigned_to_nat(1u);
x_98 = lean_nat_add(x_2, x_97);
x_99 = l___private_Init_Data_Repr_0__Nat_reprFast(x_98);
x_100 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_100, 0, x_99);
x_101 = l_Lean_MessageData_ofFormat(x_100);
if (lean_is_scalar(x_94)) {
 x_102 = lean_alloc_ctor(7, 2, 0);
} else {
 x_102 = x_94;
 lean_ctor_set_tag(x_102, 7);
}
lean_ctor_set(x_102, 0, x_96);
lean_ctor_set(x_102, 1, x_101);
x_103 = lean_mk_string_unchecked(" is not a valid hypothesis, the right-hand-side head was already resolved", 73, 73);
x_104 = l_Lean_stringToMessageData(x_103);
lean_dec(x_103);
x_105 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_105, 0, x_102);
lean_ctor_set(x_105, 1, x_104);
x_106 = l_Lean_indentExpr(x_41);
x_107 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
x_108 = lean_mk_string_unchecked("", 0, 0);
x_109 = l_Lean_stringToMessageData(x_108);
lean_dec(x_108);
x_110 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_110, 0, x_107);
lean_ctor_set(x_110, 1, x_109);
x_111 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_110, x_42, x_43, x_44, x_45, x_46);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_114 = x_111;
} else {
 lean_dec_ref(x_111);
 x_114 = lean_box(0);
}
if (lean_is_scalar(x_114)) {
 x_115 = lean_alloc_ctor(1, 2, 0);
} else {
 x_115 = x_114;
}
lean_ctor_set(x_115, 0, x_112);
lean_ctor_set(x_115, 1, x_113);
return x_115;
}
}
}
block_142:
{
lean_object* x_119; uint8_t x_120; 
x_119 = l_Lean_Expr_getAppFn(x_117);
x_120 = l_Lean_Expr_isMVar(x_119);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; 
lean_dec(x_119);
lean_dec(x_3);
lean_dec(x_1);
x_121 = lean_mk_string_unchecked("invalid 'congr' theorem, parameter #", 36, 36);
x_122 = l_Lean_stringToMessageData(x_121);
lean_dec(x_121);
x_123 = lean_unsigned_to_nat(1u);
x_124 = lean_nat_add(x_2, x_123);
x_125 = l___private_Init_Data_Repr_0__Nat_reprFast(x_124);
x_126 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_126, 0, x_125);
x_127 = l_Lean_MessageData_ofFormat(x_126);
x_128 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_128, 0, x_122);
lean_ctor_set(x_128, 1, x_127);
x_129 = lean_mk_string_unchecked(" is not a valid hypothesis, the right-hand-side head is not a metavariable", 74, 74);
x_130 = l_Lean_stringToMessageData(x_129);
lean_dec(x_129);
x_131 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_131, 0, x_128);
lean_ctor_set(x_131, 1, x_130);
x_132 = l_Lean_indentExpr(x_117);
x_133 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
x_134 = lean_mk_string_unchecked("", 0, 0);
x_135 = l_Lean_stringToMessageData(x_134);
lean_dec(x_134);
x_136 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_136, 0, x_133);
lean_ctor_set(x_136, 1, x_135);
x_137 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_136, x_6, x_7, x_8, x_9, x_118);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_138 = !lean_is_exclusive(x_137);
if (x_138 == 0)
{
return x_137;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_139 = lean_ctor_get(x_137, 0);
x_140 = lean_ctor_get(x_137, 1);
lean_inc(x_140);
lean_inc(x_139);
lean_dec(x_137);
x_141 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_141, 0, x_139);
lean_ctor_set(x_141, 1, x_140);
return x_141;
}
}
else
{
x_40 = x_119;
x_41 = x_117;
x_42 = x_6;
x_43 = x_7;
x_44 = x_8;
x_45 = x_9;
x_46 = x_118;
goto block_116;
}
}
block_175:
{
size_t x_145; size_t x_146; lean_object* x_147; 
x_145 = lean_array_size(x_4);
x_146 = lean_usize_of_nat(x_1);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
lean_inc(x_3);
x_147 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkSimpCongrTheorem_spec__6(x_3, x_2, x_4, x_145, x_146, x_1, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; uint8_t x_149; 
x_148 = lean_ctor_get(x_147, 1);
lean_inc(x_148);
lean_dec(x_147);
lean_inc(x_3);
x_149 = l_Lean_Meta_mkSimpCongrTheorem_onlyMVarsAt(x_143, x_3);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; uint8_t x_167; 
lean_dec(x_144);
lean_dec(x_3);
lean_dec(x_1);
x_150 = lean_mk_string_unchecked("invalid 'congr' theorem, parameter #", 36, 36);
x_151 = l_Lean_stringToMessageData(x_150);
lean_dec(x_150);
x_152 = lean_unsigned_to_nat(1u);
x_153 = lean_nat_add(x_2, x_152);
x_154 = l___private_Init_Data_Repr_0__Nat_reprFast(x_153);
x_155 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_155, 0, x_154);
x_156 = l_Lean_MessageData_ofFormat(x_155);
x_157 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_157, 0, x_151);
lean_ctor_set(x_157, 1, x_156);
x_158 = lean_mk_string_unchecked(" is not a valid hypothesis, the left-hand-side contains unresolved parameters", 77, 77);
x_159 = l_Lean_stringToMessageData(x_158);
lean_dec(x_158);
x_160 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_160, 0, x_157);
lean_ctor_set(x_160, 1, x_159);
x_161 = l_Lean_indentExpr(x_143);
x_162 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_162, 0, x_160);
lean_ctor_set(x_162, 1, x_161);
x_163 = lean_mk_string_unchecked("", 0, 0);
x_164 = l_Lean_stringToMessageData(x_163);
lean_dec(x_163);
x_165 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_165, 0, x_162);
lean_ctor_set(x_165, 1, x_164);
x_166 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_165, x_6, x_7, x_8, x_9, x_148);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_167 = !lean_is_exclusive(x_166);
if (x_167 == 0)
{
return x_166;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_168 = lean_ctor_get(x_166, 0);
x_169 = lean_ctor_get(x_166, 1);
lean_inc(x_169);
lean_inc(x_168);
lean_dec(x_166);
x_170 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_170, 0, x_168);
lean_ctor_set(x_170, 1, x_169);
return x_170;
}
}
else
{
lean_dec(x_143);
x_117 = x_144;
x_118 = x_148;
goto block_142;
}
}
else
{
uint8_t x_171; 
lean_dec(x_144);
lean_dec(x_143);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_171 = !lean_is_exclusive(x_147);
if (x_171 == 0)
{
return x_147;
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_172 = lean_ctor_get(x_147, 0);
x_173 = lean_ctor_get(x_147, 1);
lean_inc(x_173);
lean_inc(x_172);
lean_dec(x_147);
x_174 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_174, 0, x_172);
lean_ctor_set(x_174, 1, x_173);
return x_174;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkSimpCongrTheorem_spec__7_spec__7(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
lean_dec(x_5);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_12 = lean_ctor_get(x_4, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_4, 1);
lean_inc(x_13);
lean_dec(x_4);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_12, 2);
lean_inc(x_19);
x_20 = lean_nat_dec_lt(x_18, x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_16);
lean_ctor_set(x_21, 1, x_17);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_14);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_12);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_9);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_46; uint8_t x_71; 
x_25 = lean_unsigned_to_nat(0u);
x_26 = lean_array_uget(x_1, x_3);
lean_inc(x_14);
lean_inc(x_17);
x_27 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkSimpCongrTheorem_spec__7_spec__7___lam__0___boxed), 10, 3);
lean_closure_set(x_27, 0, x_25);
lean_closure_set(x_27, 1, x_17);
lean_closure_set(x_27, 2, x_14);
x_28 = lean_ctor_get(x_12, 0);
lean_inc(x_28);
lean_dec(x_12);
x_29 = lean_array_fget(x_28, x_18);
x_30 = lean_unbox(x_29);
lean_dec(x_29);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_add(x_18, x_31);
lean_dec(x_18);
x_33 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_33, 0, x_28);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_33, 2, x_19);
x_71 = l_Lean_BinderInfo_isExplicit(x_30);
if (x_71 == 0)
{
x_46 = x_71;
goto block_70;
}
else
{
lean_object* x_72; lean_object* x_73; 
x_72 = l_Lean_Expr_mvarId_x21(x_26);
x_73 = l_Lean_RBNode_findCore___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimApp_spec__1___redArg(x_14, x_72);
lean_dec(x_72);
if (lean_obj_tag(x_73) == 0)
{
x_46 = x_71;
goto block_70;
}
else
{
lean_dec(x_73);
if (x_71 == 0)
{
x_46 = x_71;
goto block_70;
}
else
{
lean_dec(x_27);
lean_dec(x_26);
x_34 = x_14;
x_35 = x_16;
x_36 = x_17;
x_37 = x_9;
goto block_45;
}
}
}
block_45:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; size_t x_42; size_t x_43; 
x_38 = lean_nat_add(x_36, x_31);
lean_dec(x_36);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_35);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_34);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_33);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_usize_of_nat(x_31);
x_43 = lean_usize_add(x_3, x_42);
x_3 = x_43;
x_4 = x_41;
x_9 = x_37;
goto _start;
}
block_70:
{
if (x_46 == 0)
{
lean_dec(x_27);
lean_dec(x_26);
x_34 = x_14;
x_35 = x_16;
x_36 = x_17;
x_37 = x_9;
goto block_45;
}
else
{
lean_object* x_47; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_26);
x_47 = lean_infer_type(x_26, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = lean_box(0);
x_51 = lean_unbox(x_50);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_52 = l_Lean_Meta_forallTelescopeReducing___at___Lean_Meta_getParamNames_spec__1(lean_box(0), x_48, x_27, x_51, x_5, x_6, x_7, x_8, x_49);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; 
lean_dec(x_26);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_34 = x_14;
x_35 = x_16;
x_36 = x_17;
x_37 = x_54;
goto block_45;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
lean_dec(x_52);
x_56 = lean_ctor_get(x_53, 0);
lean_inc(x_56);
lean_dec(x_53);
x_57 = l_Lean_Expr_mvarId_x21(x_26);
lean_dec(x_26);
x_58 = l_Lean_MVarIdSet_insert(x_14, x_57);
x_59 = l_Lean_Expr_mvarId_x21(x_56);
lean_dec(x_56);
x_60 = l_Lean_MVarIdSet_insert(x_58, x_59);
lean_inc(x_17);
x_61 = lean_array_push(x_16, x_17);
x_34 = x_60;
x_35 = x_61;
x_36 = x_17;
x_37 = x_55;
goto block_45;
}
}
else
{
uint8_t x_62; 
lean_dec(x_33);
lean_dec(x_26);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_62 = !lean_is_exclusive(x_52);
if (x_62 == 0)
{
return x_52;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_52, 0);
x_64 = lean_ctor_get(x_52, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_52);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
else
{
uint8_t x_66; 
lean_dec(x_33);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_66 = !lean_is_exclusive(x_47);
if (x_66 == 0)
{
return x_47;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_47, 0);
x_68 = lean_ctor_get(x_47, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_47);
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
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_117; lean_object* x_118; lean_object* x_143; lean_object* x_144; lean_object* x_176; lean_object* x_177; lean_object* x_178; uint8_t x_179; 
x_176 = lean_mk_string_unchecked("Eq", 2, 2);
x_177 = l_Lean_Name_mkStr1(x_176);
x_178 = lean_unsigned_to_nat(3u);
x_179 = l_Lean_Expr_isAppOfArity(x_5, x_177, x_178);
lean_dec(x_177);
if (x_179 == 0)
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; uint8_t x_183; 
x_180 = lean_mk_string_unchecked("Iff", 3, 3);
x_181 = l_Lean_Name_mkStr1(x_180);
x_182 = lean_unsigned_to_nat(2u);
x_183 = l_Lean_Expr_isAppOfArity(x_5, x_181, x_182);
lean_dec(x_181);
if (x_183 == 0)
{
lean_object* x_184; lean_object* x_185; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_184 = lean_box(0);
x_185 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_185, 0, x_184);
lean_ctor_set(x_185, 1, x_10);
return x_185;
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_186 = l_Lean_Expr_appFn_x21(x_5);
x_187 = l_Lean_Expr_appArg_x21(x_186);
lean_dec(x_186);
x_188 = l_Lean_Expr_appArg_x21(x_5);
x_143 = x_187;
x_144 = x_188;
goto block_175;
}
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_189 = l_Lean_Expr_appFn_x21(x_5);
x_190 = l_Lean_Expr_appArg_x21(x_189);
lean_dec(x_189);
x_191 = l_Lean_Expr_appArg_x21(x_5);
x_143 = x_190;
x_144 = x_191;
goto block_175;
}
block_39:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; lean_object* x_28; 
x_18 = lean_box(0);
x_19 = l_Lean_Expr_sort___override(x_18);
x_20 = l_Lean_Expr_getAppNumArgs(x_11);
lean_inc(x_20);
x_21 = lean_mk_array(x_20, x_19);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_sub(x_20, x_22);
lean_dec(x_20);
lean_inc(x_11);
x_24 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_11, x_21, x_23);
x_25 = lean_box(0);
x_26 = lean_array_size(x_24);
x_27 = lean_usize_of_nat(x_1);
lean_dec(x_1);
x_28 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkSimpCongrTheorem_spec__5(x_2, x_11, x_24, x_26, x_27, x_25, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_24);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_28, 0);
lean_dec(x_30);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_12);
lean_ctor_set(x_28, 0, x_31);
return x_28;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_28, 1);
lean_inc(x_32);
lean_dec(x_28);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_12);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
else
{
uint8_t x_35; 
lean_dec(x_12);
x_35 = !lean_is_exclusive(x_28);
if (x_35 == 0)
{
return x_28;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_28, 0);
x_37 = lean_ctor_get(x_28, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_28);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
block_116:
{
lean_object* x_47; lean_object* x_48; 
x_47 = l_Lean_Expr_mvarId_x21(x_41);
x_48 = l_Lean_RBNode_findCore___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimApp_spec__1___redArg(x_3, x_47);
lean_dec(x_47);
lean_dec(x_3);
if (lean_obj_tag(x_48) == 0)
{
x_11 = x_40;
x_12 = x_41;
x_13 = x_42;
x_14 = x_43;
x_15 = x_44;
x_16 = x_45;
x_17 = x_46;
goto block_39;
}
else
{
uint8_t x_49; 
lean_dec(x_41);
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; uint8_t x_51; 
x_50 = lean_ctor_get(x_48, 0);
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_52 = lean_ctor_get(x_50, 1);
lean_dec(x_52);
x_53 = lean_ctor_get(x_50, 0);
lean_dec(x_53);
x_54 = lean_mk_string_unchecked("invalid 'congr' theorem, parameter #", 36, 36);
x_55 = l_Lean_stringToMessageData(x_54);
lean_dec(x_54);
x_56 = lean_unsigned_to_nat(1u);
x_57 = lean_nat_add(x_2, x_56);
x_58 = l___private_Init_Data_Repr_0__Nat_reprFast(x_57);
lean_ctor_set_tag(x_48, 3);
lean_ctor_set(x_48, 0, x_58);
x_59 = l_Lean_MessageData_ofFormat(x_48);
lean_ctor_set_tag(x_50, 7);
lean_ctor_set(x_50, 1, x_59);
lean_ctor_set(x_50, 0, x_55);
x_60 = lean_mk_string_unchecked(" is not a valid hypothesis, the right-hand-side head was already resolved", 73, 73);
x_61 = l_Lean_stringToMessageData(x_60);
lean_dec(x_60);
x_62 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_62, 0, x_50);
lean_ctor_set(x_62, 1, x_61);
x_63 = l_Lean_indentExpr(x_40);
x_64 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
x_65 = lean_mk_string_unchecked("", 0, 0);
x_66 = l_Lean_stringToMessageData(x_65);
lean_dec(x_65);
x_67 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_67, 0, x_64);
lean_ctor_set(x_67, 1, x_66);
x_68 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_67, x_42, x_43, x_44, x_45, x_46);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
x_69 = !lean_is_exclusive(x_68);
if (x_69 == 0)
{
return x_68;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_68, 0);
x_71 = lean_ctor_get(x_68, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_68);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_50);
x_73 = lean_mk_string_unchecked("invalid 'congr' theorem, parameter #", 36, 36);
x_74 = l_Lean_stringToMessageData(x_73);
lean_dec(x_73);
x_75 = lean_unsigned_to_nat(1u);
x_76 = lean_nat_add(x_2, x_75);
x_77 = l___private_Init_Data_Repr_0__Nat_reprFast(x_76);
lean_ctor_set_tag(x_48, 3);
lean_ctor_set(x_48, 0, x_77);
x_78 = l_Lean_MessageData_ofFormat(x_48);
x_79 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_79, 0, x_74);
lean_ctor_set(x_79, 1, x_78);
x_80 = lean_mk_string_unchecked(" is not a valid hypothesis, the right-hand-side head was already resolved", 73, 73);
x_81 = l_Lean_stringToMessageData(x_80);
lean_dec(x_80);
x_82 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_82, 0, x_79);
lean_ctor_set(x_82, 1, x_81);
x_83 = l_Lean_indentExpr(x_40);
x_84 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
x_85 = lean_mk_string_unchecked("", 0, 0);
x_86 = l_Lean_stringToMessageData(x_85);
lean_dec(x_85);
x_87 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_87, 0, x_84);
lean_ctor_set(x_87, 1, x_86);
x_88 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_87, x_42, x_43, x_44, x_45, x_46);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
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
if (lean_is_scalar(x_91)) {
 x_92 = lean_alloc_ctor(1, 2, 0);
} else {
 x_92 = x_91;
}
lean_ctor_set(x_92, 0, x_89);
lean_ctor_set(x_92, 1, x_90);
return x_92;
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_93 = lean_ctor_get(x_48, 0);
lean_inc(x_93);
lean_dec(x_48);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_94 = x_93;
} else {
 lean_dec_ref(x_93);
 x_94 = lean_box(0);
}
x_95 = lean_mk_string_unchecked("invalid 'congr' theorem, parameter #", 36, 36);
x_96 = l_Lean_stringToMessageData(x_95);
lean_dec(x_95);
x_97 = lean_unsigned_to_nat(1u);
x_98 = lean_nat_add(x_2, x_97);
x_99 = l___private_Init_Data_Repr_0__Nat_reprFast(x_98);
x_100 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_100, 0, x_99);
x_101 = l_Lean_MessageData_ofFormat(x_100);
if (lean_is_scalar(x_94)) {
 x_102 = lean_alloc_ctor(7, 2, 0);
} else {
 x_102 = x_94;
 lean_ctor_set_tag(x_102, 7);
}
lean_ctor_set(x_102, 0, x_96);
lean_ctor_set(x_102, 1, x_101);
x_103 = lean_mk_string_unchecked(" is not a valid hypothesis, the right-hand-side head was already resolved", 73, 73);
x_104 = l_Lean_stringToMessageData(x_103);
lean_dec(x_103);
x_105 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_105, 0, x_102);
lean_ctor_set(x_105, 1, x_104);
x_106 = l_Lean_indentExpr(x_40);
x_107 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
x_108 = lean_mk_string_unchecked("", 0, 0);
x_109 = l_Lean_stringToMessageData(x_108);
lean_dec(x_108);
x_110 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_110, 0, x_107);
lean_ctor_set(x_110, 1, x_109);
x_111 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_110, x_42, x_43, x_44, x_45, x_46);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_114 = x_111;
} else {
 lean_dec_ref(x_111);
 x_114 = lean_box(0);
}
if (lean_is_scalar(x_114)) {
 x_115 = lean_alloc_ctor(1, 2, 0);
} else {
 x_115 = x_114;
}
lean_ctor_set(x_115, 0, x_112);
lean_ctor_set(x_115, 1, x_113);
return x_115;
}
}
}
block_142:
{
lean_object* x_119; uint8_t x_120; 
x_119 = l_Lean_Expr_getAppFn(x_117);
x_120 = l_Lean_Expr_isMVar(x_119);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; 
lean_dec(x_119);
lean_dec(x_3);
lean_dec(x_1);
x_121 = lean_mk_string_unchecked("invalid 'congr' theorem, parameter #", 36, 36);
x_122 = l_Lean_stringToMessageData(x_121);
lean_dec(x_121);
x_123 = lean_unsigned_to_nat(1u);
x_124 = lean_nat_add(x_2, x_123);
x_125 = l___private_Init_Data_Repr_0__Nat_reprFast(x_124);
x_126 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_126, 0, x_125);
x_127 = l_Lean_MessageData_ofFormat(x_126);
x_128 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_128, 0, x_122);
lean_ctor_set(x_128, 1, x_127);
x_129 = lean_mk_string_unchecked(" is not a valid hypothesis, the right-hand-side head is not a metavariable", 74, 74);
x_130 = l_Lean_stringToMessageData(x_129);
lean_dec(x_129);
x_131 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_131, 0, x_128);
lean_ctor_set(x_131, 1, x_130);
x_132 = l_Lean_indentExpr(x_117);
x_133 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
x_134 = lean_mk_string_unchecked("", 0, 0);
x_135 = l_Lean_stringToMessageData(x_134);
lean_dec(x_134);
x_136 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_136, 0, x_133);
lean_ctor_set(x_136, 1, x_135);
x_137 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_136, x_6, x_7, x_8, x_9, x_118);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_138 = !lean_is_exclusive(x_137);
if (x_138 == 0)
{
return x_137;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_139 = lean_ctor_get(x_137, 0);
x_140 = lean_ctor_get(x_137, 1);
lean_inc(x_140);
lean_inc(x_139);
lean_dec(x_137);
x_141 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_141, 0, x_139);
lean_ctor_set(x_141, 1, x_140);
return x_141;
}
}
else
{
x_40 = x_117;
x_41 = x_119;
x_42 = x_6;
x_43 = x_7;
x_44 = x_8;
x_45 = x_9;
x_46 = x_118;
goto block_116;
}
}
block_175:
{
size_t x_145; size_t x_146; lean_object* x_147; 
x_145 = lean_array_size(x_4);
x_146 = lean_usize_of_nat(x_1);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
lean_inc(x_3);
x_147 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkSimpCongrTheorem_spec__6(x_3, x_2, x_4, x_145, x_146, x_1, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; uint8_t x_149; 
x_148 = lean_ctor_get(x_147, 1);
lean_inc(x_148);
lean_dec(x_147);
lean_inc(x_3);
x_149 = l_Lean_Meta_mkSimpCongrTheorem_onlyMVarsAt(x_143, x_3);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; uint8_t x_167; 
lean_dec(x_144);
lean_dec(x_3);
lean_dec(x_1);
x_150 = lean_mk_string_unchecked("invalid 'congr' theorem, parameter #", 36, 36);
x_151 = l_Lean_stringToMessageData(x_150);
lean_dec(x_150);
x_152 = lean_unsigned_to_nat(1u);
x_153 = lean_nat_add(x_2, x_152);
x_154 = l___private_Init_Data_Repr_0__Nat_reprFast(x_153);
x_155 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_155, 0, x_154);
x_156 = l_Lean_MessageData_ofFormat(x_155);
x_157 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_157, 0, x_151);
lean_ctor_set(x_157, 1, x_156);
x_158 = lean_mk_string_unchecked(" is not a valid hypothesis, the left-hand-side contains unresolved parameters", 77, 77);
x_159 = l_Lean_stringToMessageData(x_158);
lean_dec(x_158);
x_160 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_160, 0, x_157);
lean_ctor_set(x_160, 1, x_159);
x_161 = l_Lean_indentExpr(x_143);
x_162 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_162, 0, x_160);
lean_ctor_set(x_162, 1, x_161);
x_163 = lean_mk_string_unchecked("", 0, 0);
x_164 = l_Lean_stringToMessageData(x_163);
lean_dec(x_163);
x_165 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_165, 0, x_162);
lean_ctor_set(x_165, 1, x_164);
x_166 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_165, x_6, x_7, x_8, x_9, x_148);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_167 = !lean_is_exclusive(x_166);
if (x_167 == 0)
{
return x_166;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_168 = lean_ctor_get(x_166, 0);
x_169 = lean_ctor_get(x_166, 1);
lean_inc(x_169);
lean_inc(x_168);
lean_dec(x_166);
x_170 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_170, 0, x_168);
lean_ctor_set(x_170, 1, x_169);
return x_170;
}
}
else
{
lean_dec(x_143);
x_117 = x_144;
x_118 = x_148;
goto block_142;
}
}
else
{
uint8_t x_171; 
lean_dec(x_144);
lean_dec(x_143);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_171 = !lean_is_exclusive(x_147);
if (x_171 == 0)
{
return x_147;
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_172 = lean_ctor_get(x_147, 0);
x_173 = lean_ctor_get(x_147, 1);
lean_inc(x_173);
lean_inc(x_172);
lean_dec(x_147);
x_174 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_174, 0, x_172);
lean_ctor_set(x_174, 1, x_173);
return x_174;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkSimpCongrTheorem_spec__7(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
lean_dec(x_5);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_12 = lean_ctor_get(x_4, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_4, 1);
lean_inc(x_13);
lean_dec(x_4);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_12, 2);
lean_inc(x_19);
x_20 = lean_nat_dec_lt(x_18, x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_16);
lean_ctor_set(x_21, 1, x_17);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_14);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_12);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_9);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_46; uint8_t x_71; 
x_25 = lean_unsigned_to_nat(0u);
x_26 = lean_array_uget(x_1, x_3);
lean_inc(x_14);
lean_inc(x_17);
x_27 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___boxed), 10, 3);
lean_closure_set(x_27, 0, x_25);
lean_closure_set(x_27, 1, x_17);
lean_closure_set(x_27, 2, x_14);
x_28 = lean_ctor_get(x_12, 0);
lean_inc(x_28);
lean_dec(x_12);
x_29 = lean_array_fget(x_28, x_18);
x_30 = lean_unbox(x_29);
lean_dec(x_29);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_add(x_18, x_31);
lean_dec(x_18);
x_33 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_33, 0, x_28);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_33, 2, x_19);
x_71 = l_Lean_BinderInfo_isExplicit(x_30);
if (x_71 == 0)
{
x_46 = x_71;
goto block_70;
}
else
{
lean_object* x_72; lean_object* x_73; 
x_72 = l_Lean_Expr_mvarId_x21(x_26);
x_73 = l_Lean_RBNode_findCore___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimApp_spec__1___redArg(x_14, x_72);
lean_dec(x_72);
if (lean_obj_tag(x_73) == 0)
{
x_46 = x_71;
goto block_70;
}
else
{
lean_dec(x_73);
if (x_71 == 0)
{
x_46 = x_71;
goto block_70;
}
else
{
lean_dec(x_27);
lean_dec(x_26);
x_34 = x_14;
x_35 = x_16;
x_36 = x_17;
x_37 = x_9;
goto block_45;
}
}
}
block_45:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; size_t x_42; size_t x_43; lean_object* x_44; 
x_38 = lean_nat_add(x_36, x_31);
lean_dec(x_36);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_35);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_34);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_33);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_usize_of_nat(x_31);
x_43 = lean_usize_add(x_3, x_42);
x_44 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkSimpCongrTheorem_spec__7_spec__7(x_1, x_2, x_43, x_41, x_5, x_6, x_7, x_8, x_37);
return x_44;
}
block_70:
{
if (x_46 == 0)
{
lean_dec(x_27);
lean_dec(x_26);
x_34 = x_14;
x_35 = x_16;
x_36 = x_17;
x_37 = x_9;
goto block_45;
}
else
{
lean_object* x_47; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_26);
x_47 = lean_infer_type(x_26, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = lean_box(0);
x_51 = lean_unbox(x_50);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_52 = l_Lean_Meta_forallTelescopeReducing___at___Lean_Meta_getParamNames_spec__1(lean_box(0), x_48, x_27, x_51, x_5, x_6, x_7, x_8, x_49);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; 
lean_dec(x_26);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_34 = x_14;
x_35 = x_16;
x_36 = x_17;
x_37 = x_54;
goto block_45;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
lean_dec(x_52);
x_56 = lean_ctor_get(x_53, 0);
lean_inc(x_56);
lean_dec(x_53);
x_57 = l_Lean_Expr_mvarId_x21(x_26);
lean_dec(x_26);
x_58 = l_Lean_MVarIdSet_insert(x_14, x_57);
x_59 = l_Lean_Expr_mvarId_x21(x_56);
lean_dec(x_56);
x_60 = l_Lean_MVarIdSet_insert(x_58, x_59);
lean_inc(x_17);
x_61 = lean_array_push(x_16, x_17);
x_34 = x_60;
x_35 = x_61;
x_36 = x_17;
x_37 = x_55;
goto block_45;
}
}
else
{
uint8_t x_62; 
lean_dec(x_33);
lean_dec(x_26);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_62 = !lean_is_exclusive(x_52);
if (x_62 == 0)
{
return x_52;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_52, 0);
x_64 = lean_ctor_get(x_52, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_52);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
else
{
uint8_t x_66; 
lean_dec(x_33);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_66 = !lean_is_exclusive(x_47);
if (x_66 == 0)
{
return x_47;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_47, 0);
x_68 = lean_ctor_get(x_47, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_47);
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
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Expr_withAppAux___at___Lean_Meta_mkSimpCongrTheorem_spec__9_spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_90; 
if (lean_obj_tag(x_8) == 5)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_98 = lean_ctor_get(x_8, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_8, 1);
lean_inc(x_99);
lean_dec(x_8);
x_100 = lean_array_set(x_9, x_10, x_99);
x_101 = lean_unsigned_to_nat(1u);
x_102 = lean_nat_sub(x_10, x_101);
lean_dec(x_10);
x_8 = x_98;
x_9 = x_100;
x_10 = x_102;
goto _start;
}
else
{
uint8_t x_104; 
lean_dec(x_10);
x_104 = l_Lean_Expr_isConst(x_4);
if (x_104 == 0)
{
x_90 = x_104;
goto block_97;
}
else
{
uint8_t x_105; 
x_105 = l_Lean_Expr_isConst(x_8);
x_90 = x_105;
goto block_97;
}
}
block_76:
{
lean_object* x_21; size_t x_22; lean_object* x_23; size_t x_24; lean_object* x_25; uint8_t x_26; 
x_21 = lean_box(0);
x_22 = lean_array_size(x_1);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_usize_of_nat(x_23);
x_25 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkSimpCongrTheorem_spec__4(x_1, x_22, x_24, x_21, x_16, x_17, x_18, x_19, x_20);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; size_t x_34; lean_object* x_35; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_ctor_get(x_25, 1);
x_29 = lean_mk_empty_array_with_capacity(x_23);
x_30 = lean_array_get_size(x_2);
x_31 = l_Array_toSubarray___redArg(x_2, x_23, x_30);
lean_ctor_set(x_25, 1, x_23);
lean_ctor_set(x_25, 0, x_29);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_27);
lean_ctor_set(x_32, 1, x_25);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_array_size(x_3);
x_35 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkSimpCongrTheorem_spec__7(x_3, x_34, x_24, x_33, x_16, x_17, x_18, x_19, x_28);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_39 = !lean_is_exclusive(x_35);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_35, 0);
lean_dec(x_40);
x_41 = lean_ctor_get(x_38, 0);
lean_inc(x_41);
lean_dec(x_38);
x_42 = l_Lean_Expr_constName_x21(x_4);
x_43 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_43, 0, x_5);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set(x_43, 2, x_41);
lean_ctor_set(x_43, 3, x_6);
lean_ctor_set(x_35, 0, x_43);
return x_35;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_44 = lean_ctor_get(x_35, 1);
lean_inc(x_44);
lean_dec(x_35);
x_45 = lean_ctor_get(x_38, 0);
lean_inc(x_45);
lean_dec(x_38);
x_46 = l_Lean_Expr_constName_x21(x_4);
x_47 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_47, 0, x_5);
lean_ctor_set(x_47, 1, x_46);
lean_ctor_set(x_47, 2, x_45);
lean_ctor_set(x_47, 3, x_6);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_44);
return x_48;
}
}
else
{
uint8_t x_49; 
lean_dec(x_6);
lean_dec(x_5);
x_49 = !lean_is_exclusive(x_35);
if (x_49 == 0)
{
return x_35;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_35, 0);
x_51 = lean_ctor_get(x_35, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_35);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; size_t x_61; lean_object* x_62; 
x_53 = lean_ctor_get(x_25, 0);
x_54 = lean_ctor_get(x_25, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_25);
x_55 = lean_mk_empty_array_with_capacity(x_23);
x_56 = lean_array_get_size(x_2);
x_57 = l_Array_toSubarray___redArg(x_2, x_23, x_56);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_23);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_53);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_array_size(x_3);
x_62 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkSimpCongrTheorem_spec__7(x_3, x_61, x_24, x_60, x_16, x_17, x_18, x_19, x_54);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
lean_dec(x_63);
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
lean_dec(x_64);
x_66 = lean_ctor_get(x_62, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_67 = x_62;
} else {
 lean_dec_ref(x_62);
 x_67 = lean_box(0);
}
x_68 = lean_ctor_get(x_65, 0);
lean_inc(x_68);
lean_dec(x_65);
x_69 = l_Lean_Expr_constName_x21(x_4);
x_70 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_70, 0, x_5);
lean_ctor_set(x_70, 1, x_69);
lean_ctor_set(x_70, 2, x_68);
lean_ctor_set(x_70, 3, x_6);
if (lean_is_scalar(x_67)) {
 x_71 = lean_alloc_ctor(0, 2, 0);
} else {
 x_71 = x_67;
}
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_66);
return x_71;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_6);
lean_dec(x_5);
x_72 = lean_ctor_get(x_62, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_62, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_74 = x_62;
} else {
 lean_dec_ref(x_62);
 x_74 = lean_box(0);
}
if (lean_is_scalar(x_74)) {
 x_75 = lean_alloc_ctor(1, 2, 0);
} else {
 x_75 = x_74;
}
lean_ctor_set(x_75, 0, x_72);
lean_ctor_set(x_75, 1, x_73);
return x_75;
}
}
}
block_89:
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_77 = lean_mk_string_unchecked("invalid 'congr' theorem, equality left/right-hand sides must be applications of the same function", 97, 97);
x_78 = l_Lean_stringToMessageData(x_77);
lean_dec(x_77);
x_79 = l_Lean_indentExpr(x_7);
x_80 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
x_81 = lean_mk_string_unchecked("", 0, 0);
x_82 = l_Lean_stringToMessageData(x_81);
lean_dec(x_81);
x_83 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_83, 0, x_80);
lean_ctor_set(x_83, 1, x_82);
x_84 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_83, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_85 = !lean_is_exclusive(x_84);
if (x_85 == 0)
{
return x_84;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_84, 0);
x_87 = lean_ctor_get(x_84, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_84);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
block_97:
{
if (x_90 == 0)
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
goto block_89;
}
else
{
lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_91 = l_Lean_Expr_constName_x21(x_4);
x_92 = l_Lean_Expr_constName_x21(x_8);
lean_dec(x_8);
x_93 = lean_name_eq(x_91, x_92);
lean_dec(x_92);
lean_dec(x_91);
if (x_93 == 0)
{
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
goto block_89;
}
else
{
lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_94 = lean_array_get_size(x_1);
x_95 = lean_array_get_size(x_9);
lean_dec(x_9);
x_96 = lean_nat_dec_eq(x_94, x_95);
lean_dec(x_95);
lean_dec(x_94);
if (x_96 == 0)
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
goto block_89;
}
else
{
lean_dec(x_7);
x_16 = x_11;
x_17 = x_12;
x_18 = x_13;
x_19 = x_14;
x_20 = x_15;
goto block_76;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Meta_mkSimpCongrTheorem_spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_90; 
if (lean_obj_tag(x_8) == 5)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_98 = lean_ctor_get(x_8, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_8, 1);
lean_inc(x_99);
lean_dec(x_8);
x_100 = lean_array_set(x_9, x_10, x_99);
x_101 = lean_unsigned_to_nat(1u);
x_102 = lean_nat_sub(x_10, x_101);
x_103 = l_Lean_Expr_withAppAux___at___Lean_Expr_withAppAux___at___Lean_Meta_mkSimpCongrTheorem_spec__9_spec__9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_98, x_100, x_102, x_11, x_12, x_13, x_14, x_15);
return x_103;
}
else
{
uint8_t x_104; 
x_104 = l_Lean_Expr_isConst(x_4);
if (x_104 == 0)
{
x_90 = x_104;
goto block_97;
}
else
{
uint8_t x_105; 
x_105 = l_Lean_Expr_isConst(x_8);
x_90 = x_105;
goto block_97;
}
}
block_76:
{
lean_object* x_21; size_t x_22; lean_object* x_23; size_t x_24; lean_object* x_25; uint8_t x_26; 
x_21 = lean_box(0);
x_22 = lean_array_size(x_1);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_usize_of_nat(x_23);
x_25 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkSimpCongrTheorem_spec__4(x_1, x_22, x_24, x_21, x_16, x_17, x_18, x_19, x_20);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; size_t x_34; lean_object* x_35; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_ctor_get(x_25, 1);
x_29 = lean_mk_empty_array_with_capacity(x_23);
x_30 = lean_array_get_size(x_2);
x_31 = l_Array_toSubarray___redArg(x_2, x_23, x_30);
lean_ctor_set(x_25, 1, x_23);
lean_ctor_set(x_25, 0, x_29);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_27);
lean_ctor_set(x_32, 1, x_25);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_array_size(x_3);
x_35 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkSimpCongrTheorem_spec__7(x_3, x_34, x_24, x_33, x_16, x_17, x_18, x_19, x_28);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_39 = !lean_is_exclusive(x_35);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_35, 0);
lean_dec(x_40);
x_41 = lean_ctor_get(x_38, 0);
lean_inc(x_41);
lean_dec(x_38);
x_42 = l_Lean_Expr_constName_x21(x_4);
x_43 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_43, 0, x_5);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set(x_43, 2, x_41);
lean_ctor_set(x_43, 3, x_6);
lean_ctor_set(x_35, 0, x_43);
return x_35;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_44 = lean_ctor_get(x_35, 1);
lean_inc(x_44);
lean_dec(x_35);
x_45 = lean_ctor_get(x_38, 0);
lean_inc(x_45);
lean_dec(x_38);
x_46 = l_Lean_Expr_constName_x21(x_4);
x_47 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_47, 0, x_5);
lean_ctor_set(x_47, 1, x_46);
lean_ctor_set(x_47, 2, x_45);
lean_ctor_set(x_47, 3, x_6);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_44);
return x_48;
}
}
else
{
uint8_t x_49; 
lean_dec(x_6);
lean_dec(x_5);
x_49 = !lean_is_exclusive(x_35);
if (x_49 == 0)
{
return x_35;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_35, 0);
x_51 = lean_ctor_get(x_35, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_35);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; size_t x_61; lean_object* x_62; 
x_53 = lean_ctor_get(x_25, 0);
x_54 = lean_ctor_get(x_25, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_25);
x_55 = lean_mk_empty_array_with_capacity(x_23);
x_56 = lean_array_get_size(x_2);
x_57 = l_Array_toSubarray___redArg(x_2, x_23, x_56);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_23);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_53);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_array_size(x_3);
x_62 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkSimpCongrTheorem_spec__7(x_3, x_61, x_24, x_60, x_16, x_17, x_18, x_19, x_54);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
lean_dec(x_63);
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
lean_dec(x_64);
x_66 = lean_ctor_get(x_62, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_67 = x_62;
} else {
 lean_dec_ref(x_62);
 x_67 = lean_box(0);
}
x_68 = lean_ctor_get(x_65, 0);
lean_inc(x_68);
lean_dec(x_65);
x_69 = l_Lean_Expr_constName_x21(x_4);
x_70 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_70, 0, x_5);
lean_ctor_set(x_70, 1, x_69);
lean_ctor_set(x_70, 2, x_68);
lean_ctor_set(x_70, 3, x_6);
if (lean_is_scalar(x_67)) {
 x_71 = lean_alloc_ctor(0, 2, 0);
} else {
 x_71 = x_67;
}
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_66);
return x_71;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_6);
lean_dec(x_5);
x_72 = lean_ctor_get(x_62, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_62, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_74 = x_62;
} else {
 lean_dec_ref(x_62);
 x_74 = lean_box(0);
}
if (lean_is_scalar(x_74)) {
 x_75 = lean_alloc_ctor(1, 2, 0);
} else {
 x_75 = x_74;
}
lean_ctor_set(x_75, 0, x_72);
lean_ctor_set(x_75, 1, x_73);
return x_75;
}
}
}
block_89:
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_77 = lean_mk_string_unchecked("invalid 'congr' theorem, equality left/right-hand sides must be applications of the same function", 97, 97);
x_78 = l_Lean_stringToMessageData(x_77);
lean_dec(x_77);
x_79 = l_Lean_indentExpr(x_7);
x_80 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
x_81 = lean_mk_string_unchecked("", 0, 0);
x_82 = l_Lean_stringToMessageData(x_81);
lean_dec(x_81);
x_83 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_83, 0, x_80);
lean_ctor_set(x_83, 1, x_82);
x_84 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_83, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_85 = !lean_is_exclusive(x_84);
if (x_85 == 0)
{
return x_84;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_84, 0);
x_87 = lean_ctor_get(x_84, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_84);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
block_97:
{
if (x_90 == 0)
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
goto block_89;
}
else
{
lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_91 = l_Lean_Expr_constName_x21(x_4);
x_92 = l_Lean_Expr_constName_x21(x_8);
lean_dec(x_8);
x_93 = lean_name_eq(x_91, x_92);
lean_dec(x_92);
lean_dec(x_91);
if (x_93 == 0)
{
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
goto block_89;
}
else
{
lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_94 = lean_array_get_size(x_1);
x_95 = lean_array_get_size(x_9);
lean_dec(x_9);
x_96 = lean_nat_dec_eq(x_94, x_95);
lean_dec(x_95);
lean_dec(x_94);
if (x_96 == 0)
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
goto block_89;
}
else
{
lean_dec(x_7);
x_16 = x_11;
x_17 = x_12;
x_18 = x_13;
x_19 = x_14;
x_20 = x_15;
goto block_76;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Expr_withAppAux___at___Lean_Meta_mkSimpCongrTheorem_spec__11_spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
if (lean_obj_tag(x_7) == 5)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_7, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_7, 1);
lean_inc(x_16);
lean_dec(x_7);
x_17 = lean_array_set(x_8, x_9, x_16);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_sub(x_9, x_18);
lean_dec(x_9);
x_7 = x_15;
x_8 = x_17;
x_9 = x_19;
goto _start;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_9);
x_21 = lean_box(0);
x_22 = l_Lean_Expr_sort___override(x_21);
x_23 = l_Lean_Expr_getAppNumArgs(x_1);
lean_inc(x_23);
x_24 = lean_mk_array(x_23, x_22);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_sub(x_23, x_25);
lean_dec(x_23);
x_27 = l_Lean_Expr_withAppAux___at___Lean_Meta_mkSimpCongrTheorem_spec__9(x_8, x_2, x_3, x_7, x_4, x_5, x_6, x_1, x_24, x_26, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_26);
lean_dec(x_7);
lean_dec(x_8);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Meta_mkSimpCongrTheorem_spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
if (lean_obj_tag(x_7) == 5)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_7, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_7, 1);
lean_inc(x_16);
lean_dec(x_7);
x_17 = lean_array_set(x_8, x_9, x_16);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_sub(x_9, x_18);
x_20 = l_Lean_Expr_withAppAux___at___Lean_Expr_withAppAux___at___Lean_Meta_mkSimpCongrTheorem_spec__11_spec__11(x_6, x_1, x_2, x_3, x_4, x_5, x_15, x_17, x_19, x_10, x_11, x_12, x_13, x_14);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_21 = lean_box(0);
x_22 = l_Lean_Expr_sort___override(x_21);
x_23 = l_Lean_Expr_getAppNumArgs(x_6);
lean_inc(x_23);
x_24 = lean_mk_array(x_23, x_22);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_sub(x_23, x_25);
lean_dec(x_23);
x_27 = l_Lean_Expr_withAppAux___at___Lean_Meta_mkSimpCongrTheorem_spec__9(x_8, x_1, x_2, x_7, x_3, x_4, x_5, x_6, x_24, x_26, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_26);
lean_dec(x_7);
lean_dec(x_8);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpCongrTheorem(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; lean_object* x_27; uint8_t x_28; uint64_t x_29; lean_object* x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; uint8_t x_34; uint64_t x_35; uint64_t x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; 
x_8 = lean_box(2);
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get_uint8(x_9, 0);
x_11 = lean_ctor_get_uint8(x_9, 1);
x_12 = lean_ctor_get_uint8(x_9, 2);
x_13 = lean_ctor_get_uint8(x_9, 3);
x_14 = lean_ctor_get_uint8(x_9, 4);
x_15 = lean_ctor_get_uint8(x_9, 5);
x_16 = lean_ctor_get_uint8(x_9, 6);
x_17 = lean_ctor_get_uint8(x_9, 7);
x_18 = lean_ctor_get_uint8(x_9, 8);
x_19 = lean_ctor_get_uint8(x_9, 10);
x_20 = lean_ctor_get_uint8(x_9, 11);
x_21 = lean_ctor_get_uint8(x_9, 12);
x_22 = lean_ctor_get_uint8(x_9, 13);
x_23 = lean_ctor_get_uint8(x_9, 14);
x_24 = lean_ctor_get_uint8(x_9, 15);
x_25 = lean_ctor_get_uint8(x_9, 16);
x_26 = lean_ctor_get_uint8(x_9, 17);
x_27 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_27, 0, x_10);
lean_ctor_set_uint8(x_27, 1, x_11);
lean_ctor_set_uint8(x_27, 2, x_12);
lean_ctor_set_uint8(x_27, 3, x_13);
lean_ctor_set_uint8(x_27, 4, x_14);
lean_ctor_set_uint8(x_27, 5, x_15);
lean_ctor_set_uint8(x_27, 6, x_16);
lean_ctor_set_uint8(x_27, 7, x_17);
lean_ctor_set_uint8(x_27, 8, x_18);
x_28 = lean_unbox(x_8);
lean_ctor_set_uint8(x_27, 9, x_28);
lean_ctor_set_uint8(x_27, 10, x_19);
lean_ctor_set_uint8(x_27, 11, x_20);
lean_ctor_set_uint8(x_27, 12, x_21);
lean_ctor_set_uint8(x_27, 13, x_22);
lean_ctor_set_uint8(x_27, 14, x_23);
lean_ctor_set_uint8(x_27, 15, x_24);
lean_ctor_set_uint8(x_27, 16, x_25);
lean_ctor_set_uint8(x_27, 17, x_26);
x_29 = lean_ctor_get_uint64(x_3, sizeof(void*)*7);
x_30 = lean_unsigned_to_nat(2u);
x_31 = lean_uint64_of_nat(x_30);
x_32 = lean_uint64_shift_right(x_29, x_31);
x_33 = lean_uint64_shift_left(x_32, x_31);
x_34 = lean_unbox(x_8);
x_35 = l_Lean_Meta_TransparencyMode_toUInt64(x_34);
x_36 = lean_uint64_lor(x_33, x_35);
x_37 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 8);
x_38 = lean_ctor_get(x_3, 1);
x_39 = lean_ctor_get(x_3, 2);
x_40 = lean_ctor_get(x_3, 3);
x_41 = lean_ctor_get(x_3, 4);
x_42 = lean_ctor_get(x_3, 5);
x_43 = lean_ctor_get(x_3, 6);
x_44 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 9);
x_45 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 10);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
x_46 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_46, 0, x_27);
lean_ctor_set(x_46, 1, x_38);
lean_ctor_set(x_46, 2, x_39);
lean_ctor_set(x_46, 3, x_40);
lean_ctor_set(x_46, 4, x_41);
lean_ctor_set(x_46, 5, x_42);
lean_ctor_set(x_46, 6, x_43);
lean_ctor_set_uint64(x_46, sizeof(void*)*7, x_36);
lean_ctor_set_uint8(x_46, sizeof(void*)*7 + 8, x_37);
lean_ctor_set_uint8(x_46, sizeof(void*)*7 + 9, x_44);
lean_ctor_set_uint8(x_46, sizeof(void*)*7 + 10, x_45);
lean_inc(x_1);
x_47 = l_Lean_mkConstWithLevelParams___at___Lean_Meta_mkSimpCongrTheorem_spec__1(x_1, x_46, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_46);
x_50 = lean_infer_type(x_48, x_46, x_4, x_5, x_6, x_49);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_box(0);
x_54 = lean_box(0);
x_55 = lean_unbox(x_54);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_46);
x_56 = l_Lean_Meta_forallMetaTelescopeReducing(x_51, x_53, x_55, x_46, x_4, x_5, x_6, x_52);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
x_59 = lean_ctor_get(x_56, 1);
lean_inc(x_59);
lean_dec(x_56);
x_60 = !lean_is_exclusive(x_57);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_61 = lean_ctor_get(x_57, 0);
x_62 = lean_ctor_get(x_57, 1);
lean_dec(x_62);
x_63 = !lean_is_exclusive(x_58);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_64 = lean_ctor_get(x_58, 0);
x_65 = lean_ctor_get(x_58, 1);
x_76 = lean_mk_string_unchecked("Eq", 2, 2);
x_77 = l_Lean_Name_mkStr1(x_76);
x_78 = lean_unsigned_to_nat(3u);
x_79 = l_Lean_Expr_isAppOfArity(x_65, x_77, x_78);
lean_dec(x_77);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_80 = lean_mk_string_unchecked("Iff", 3, 3);
x_81 = l_Lean_Name_mkStr1(x_80);
x_82 = l_Lean_Expr_isAppOfArity(x_65, x_81, x_30);
lean_dec(x_81);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_64);
lean_dec(x_61);
lean_dec(x_2);
lean_dec(x_1);
x_83 = lean_mk_string_unchecked("invalid 'congr' theorem, equality expected", 42, 42);
x_84 = l_Lean_stringToMessageData(x_83);
lean_dec(x_83);
x_85 = l_Lean_indentExpr(x_65);
lean_ctor_set_tag(x_58, 7);
lean_ctor_set(x_58, 1, x_85);
lean_ctor_set(x_58, 0, x_84);
x_86 = lean_mk_string_unchecked("", 0, 0);
x_87 = l_Lean_stringToMessageData(x_86);
lean_dec(x_86);
lean_ctor_set_tag(x_57, 7);
lean_ctor_set(x_57, 1, x_87);
lean_ctor_set(x_57, 0, x_58);
x_88 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_57, x_46, x_4, x_5, x_6, x_59);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_46);
return x_88;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_free_object(x_58);
lean_free_object(x_57);
x_89 = l_Lean_Expr_appFn_x21(x_65);
x_90 = l_Lean_Expr_appArg_x21(x_89);
lean_dec(x_89);
x_91 = l_Lean_Expr_appArg_x21(x_65);
x_66 = x_90;
x_67 = x_91;
goto block_75;
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_free_object(x_58);
lean_free_object(x_57);
x_92 = l_Lean_Expr_appFn_x21(x_65);
x_93 = l_Lean_Expr_appArg_x21(x_92);
lean_dec(x_92);
x_94 = l_Lean_Expr_appArg_x21(x_65);
x_66 = x_93;
x_67 = x_94;
goto block_75;
}
block_75:
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_68 = lean_box(0);
x_69 = l_Lean_Expr_sort___override(x_68);
x_70 = l_Lean_Expr_getAppNumArgs(x_66);
lean_inc(x_70);
x_71 = lean_mk_array(x_70, x_69);
x_72 = lean_unsigned_to_nat(1u);
x_73 = lean_nat_sub(x_70, x_72);
lean_dec(x_70);
x_74 = l_Lean_Expr_withAppAux___at___Lean_Meta_mkSimpCongrTheorem_spec__11(x_64, x_61, x_1, x_2, x_65, x_67, x_66, x_71, x_73, x_46, x_4, x_5, x_6, x_59);
lean_dec(x_73);
lean_dec(x_61);
return x_74;
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; 
x_95 = lean_ctor_get(x_58, 0);
x_96 = lean_ctor_get(x_58, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_58);
x_107 = lean_mk_string_unchecked("Eq", 2, 2);
x_108 = l_Lean_Name_mkStr1(x_107);
x_109 = lean_unsigned_to_nat(3u);
x_110 = l_Lean_Expr_isAppOfArity(x_96, x_108, x_109);
lean_dec(x_108);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; uint8_t x_113; 
x_111 = lean_mk_string_unchecked("Iff", 3, 3);
x_112 = l_Lean_Name_mkStr1(x_111);
x_113 = l_Lean_Expr_isAppOfArity(x_96, x_112, x_30);
lean_dec(x_112);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
lean_dec(x_95);
lean_dec(x_61);
lean_dec(x_2);
lean_dec(x_1);
x_114 = lean_mk_string_unchecked("invalid 'congr' theorem, equality expected", 42, 42);
x_115 = l_Lean_stringToMessageData(x_114);
lean_dec(x_114);
x_116 = l_Lean_indentExpr(x_96);
x_117 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
x_118 = lean_mk_string_unchecked("", 0, 0);
x_119 = l_Lean_stringToMessageData(x_118);
lean_dec(x_118);
lean_ctor_set_tag(x_57, 7);
lean_ctor_set(x_57, 1, x_119);
lean_ctor_set(x_57, 0, x_117);
x_120 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_57, x_46, x_4, x_5, x_6, x_59);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_46);
return x_120;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_free_object(x_57);
x_121 = l_Lean_Expr_appFn_x21(x_96);
x_122 = l_Lean_Expr_appArg_x21(x_121);
lean_dec(x_121);
x_123 = l_Lean_Expr_appArg_x21(x_96);
x_97 = x_122;
x_98 = x_123;
goto block_106;
}
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
lean_free_object(x_57);
x_124 = l_Lean_Expr_appFn_x21(x_96);
x_125 = l_Lean_Expr_appArg_x21(x_124);
lean_dec(x_124);
x_126 = l_Lean_Expr_appArg_x21(x_96);
x_97 = x_125;
x_98 = x_126;
goto block_106;
}
block_106:
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_99 = lean_box(0);
x_100 = l_Lean_Expr_sort___override(x_99);
x_101 = l_Lean_Expr_getAppNumArgs(x_97);
lean_inc(x_101);
x_102 = lean_mk_array(x_101, x_100);
x_103 = lean_unsigned_to_nat(1u);
x_104 = lean_nat_sub(x_101, x_103);
lean_dec(x_101);
x_105 = l_Lean_Expr_withAppAux___at___Lean_Meta_mkSimpCongrTheorem_spec__11(x_95, x_61, x_1, x_2, x_96, x_98, x_97, x_102, x_104, x_46, x_4, x_5, x_6, x_59);
lean_dec(x_104);
lean_dec(x_61);
return x_105;
}
}
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_141; lean_object* x_142; lean_object* x_143; uint8_t x_144; 
x_127 = lean_ctor_get(x_57, 0);
lean_inc(x_127);
lean_dec(x_57);
x_128 = lean_ctor_get(x_58, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_58, 1);
lean_inc(x_129);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_130 = x_58;
} else {
 lean_dec_ref(x_58);
 x_130 = lean_box(0);
}
x_141 = lean_mk_string_unchecked("Eq", 2, 2);
x_142 = l_Lean_Name_mkStr1(x_141);
x_143 = lean_unsigned_to_nat(3u);
x_144 = l_Lean_Expr_isAppOfArity(x_129, x_142, x_143);
lean_dec(x_142);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; uint8_t x_147; 
x_145 = lean_mk_string_unchecked("Iff", 3, 3);
x_146 = l_Lean_Name_mkStr1(x_145);
x_147 = l_Lean_Expr_isAppOfArity(x_129, x_146, x_30);
lean_dec(x_146);
if (x_147 == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
lean_dec(x_128);
lean_dec(x_127);
lean_dec(x_2);
lean_dec(x_1);
x_148 = lean_mk_string_unchecked("invalid 'congr' theorem, equality expected", 42, 42);
x_149 = l_Lean_stringToMessageData(x_148);
lean_dec(x_148);
x_150 = l_Lean_indentExpr(x_129);
if (lean_is_scalar(x_130)) {
 x_151 = lean_alloc_ctor(7, 2, 0);
} else {
 x_151 = x_130;
 lean_ctor_set_tag(x_151, 7);
}
lean_ctor_set(x_151, 0, x_149);
lean_ctor_set(x_151, 1, x_150);
x_152 = lean_mk_string_unchecked("", 0, 0);
x_153 = l_Lean_stringToMessageData(x_152);
lean_dec(x_152);
x_154 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_154, 0, x_151);
lean_ctor_set(x_154, 1, x_153);
x_155 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_154, x_46, x_4, x_5, x_6, x_59);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_46);
return x_155;
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; 
lean_dec(x_130);
x_156 = l_Lean_Expr_appFn_x21(x_129);
x_157 = l_Lean_Expr_appArg_x21(x_156);
lean_dec(x_156);
x_158 = l_Lean_Expr_appArg_x21(x_129);
x_131 = x_157;
x_132 = x_158;
goto block_140;
}
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; 
lean_dec(x_130);
x_159 = l_Lean_Expr_appFn_x21(x_129);
x_160 = l_Lean_Expr_appArg_x21(x_159);
lean_dec(x_159);
x_161 = l_Lean_Expr_appArg_x21(x_129);
x_131 = x_160;
x_132 = x_161;
goto block_140;
}
block_140:
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_133 = lean_box(0);
x_134 = l_Lean_Expr_sort___override(x_133);
x_135 = l_Lean_Expr_getAppNumArgs(x_131);
lean_inc(x_135);
x_136 = lean_mk_array(x_135, x_134);
x_137 = lean_unsigned_to_nat(1u);
x_138 = lean_nat_sub(x_135, x_137);
lean_dec(x_135);
x_139 = l_Lean_Expr_withAppAux___at___Lean_Meta_mkSimpCongrTheorem_spec__11(x_128, x_127, x_1, x_2, x_129, x_132, x_131, x_136, x_138, x_46, x_4, x_5, x_6, x_59);
lean_dec(x_138);
lean_dec(x_127);
return x_139;
}
}
}
else
{
uint8_t x_162; 
lean_dec(x_46);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_162 = !lean_is_exclusive(x_56);
if (x_162 == 0)
{
return x_56;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_163 = lean_ctor_get(x_56, 0);
x_164 = lean_ctor_get(x_56, 1);
lean_inc(x_164);
lean_inc(x_163);
lean_dec(x_56);
x_165 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_165, 0, x_163);
lean_ctor_set(x_165, 1, x_164);
return x_165;
}
}
}
else
{
uint8_t x_166; 
lean_dec(x_46);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_166 = !lean_is_exclusive(x_50);
if (x_166 == 0)
{
return x_50;
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_167 = lean_ctor_get(x_50, 0);
x_168 = lean_ctor_get(x_50, 1);
lean_inc(x_168);
lean_inc(x_167);
lean_dec(x_50);
x_169 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_169, 0, x_167);
lean_ctor_set(x_169, 1, x_168);
return x_169;
}
}
}
else
{
uint8_t x_170; 
lean_dec(x_46);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_170 = !lean_is_exclusive(x_47);
if (x_170 == 0)
{
return x_47;
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_171 = lean_ctor_get(x_47, 0);
x_172 = lean_ctor_get(x_47, 1);
lean_inc(x_172);
lean_inc(x_171);
lean_dec(x_47);
x_173 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_173, 0, x_171);
lean_ctor_set(x_173, 1, x_172);
return x_173;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkSimpCongrTheorem_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkSimpCongrTheorem_spec__0___redArg(x_1, x_6, x_7, x_4, x_5);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkSimpCongrTheorem_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkSimpCongrTheorem_spec__0(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___Lean_mkConstWithLevelParams___at___Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_getConstVal___at___Lean_mkConstWithLevelParams___at___Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___Lean_Meta_mkSimpCongrTheorem_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_mkConstWithLevelParams___at___Lean_Meta_mkSimpCongrTheorem_spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkSimpCongrTheorem_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkSimpCongrTheorem_spec__4(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkSimpCongrTheorem_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkSimpCongrTheorem_spec__5(x_1, x_2, x_3, x_12, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkSimpCongrTheorem_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkSimpCongrTheorem_spec__6(x_1, x_2, x_3, x_12, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkSimpCongrTheorem_spec__7_spec__7___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkSimpCongrTheorem_spec__7_spec__7___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkSimpCongrTheorem_spec__7_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkSimpCongrTheorem_spec__7_spec__7(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkSimpCongrTheorem_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkSimpCongrTheorem_spec__7(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Expr_withAppAux___at___Lean_Meta_mkSimpCongrTheorem_spec__9_spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_Expr_withAppAux___at___Lean_Expr_withAppAux___at___Lean_Meta_mkSimpCongrTheorem_spec__9_spec__9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Meta_mkSimpCongrTheorem_spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_Expr_withAppAux___at___Lean_Meta_mkSimpCongrTheorem_spec__9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Expr_withAppAux___at___Lean_Meta_mkSimpCongrTheorem_spec__11_spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Expr_withAppAux___at___Lean_Expr_withAppAux___at___Lean_Meta_mkSimpCongrTheorem_spec__11_spec__11(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_3);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Meta_mkSimpCongrTheorem_spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Expr_withAppAux___at___Lean_Meta_mkSimpCongrTheorem_spec__11(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_9);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpCongrTheorem___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_mkSimpCongrTheorem(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___Lean_Meta_addSimpCongrTheorem_spec__0___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_st_ref_take(x_6, x_7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_12 = lean_ctor_get(x_5, 6);
lean_inc(x_12);
lean_dec(x_5);
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
x_14 = l_Lean_ScopedEnvExtension_addCore___redArg(x_13, x_1, x_2, x_3, x_12);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_10, 2);
lean_inc(x_16);
x_17 = lean_ctor_get(x_10, 3);
lean_inc(x_17);
x_18 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_18);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
lean_inc(x_19);
lean_ctor_set(x_8, 1, x_19);
lean_ctor_set(x_8, 0, x_19);
x_20 = lean_ctor_get(x_10, 5);
lean_inc(x_20);
x_21 = lean_ctor_get(x_10, 6);
lean_inc(x_21);
x_22 = lean_ctor_get(x_10, 7);
lean_inc(x_22);
lean_dec(x_10);
x_23 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_23, 0, x_14);
lean_ctor_set(x_23, 1, x_15);
lean_ctor_set(x_23, 2, x_16);
lean_ctor_set(x_23, 3, x_17);
lean_ctor_set(x_23, 4, x_8);
lean_ctor_set(x_23, 5, x_20);
lean_ctor_set(x_23, 6, x_21);
lean_ctor_set(x_23, 7, x_22);
x_24 = lean_st_ref_set(x_6, x_23, x_11);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_st_ref_take(x_4, x_25);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
lean_inc(x_18);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_18);
lean_inc(x_18);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_18);
lean_inc(x_18);
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_18);
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_18);
lean_inc(x_33);
lean_inc(x_30);
x_34 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_34, 0, x_30);
lean_ctor_set(x_34, 1, x_31);
lean_ctor_set(x_34, 2, x_32);
lean_ctor_set(x_34, 3, x_30);
lean_ctor_set(x_34, 4, x_33);
lean_ctor_set(x_34, 5, x_33);
x_35 = lean_ctor_get(x_27, 2);
lean_inc(x_35);
x_36 = lean_ctor_get(x_27, 3);
lean_inc(x_36);
x_37 = lean_ctor_get(x_27, 4);
lean_inc(x_37);
lean_dec(x_27);
x_38 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_38, 0, x_29);
lean_ctor_set(x_38, 1, x_34);
lean_ctor_set(x_38, 2, x_35);
lean_ctor_set(x_38, 3, x_36);
lean_ctor_set(x_38, 4, x_37);
x_39 = lean_st_ref_set(x_4, x_38, x_28);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_39, 0);
lean_dec(x_41);
x_42 = lean_box(0);
lean_ctor_set(x_39, 0, x_42);
return x_39;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_39, 1);
lean_inc(x_43);
lean_dec(x_39);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_46 = lean_ctor_get(x_8, 0);
x_47 = lean_ctor_get(x_8, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_8);
x_48 = lean_ctor_get(x_5, 6);
lean_inc(x_48);
lean_dec(x_5);
x_49 = lean_ctor_get(x_46, 0);
lean_inc(x_49);
x_50 = l_Lean_ScopedEnvExtension_addCore___redArg(x_49, x_1, x_2, x_3, x_48);
x_51 = lean_ctor_get(x_46, 1);
lean_inc(x_51);
x_52 = lean_ctor_get(x_46, 2);
lean_inc(x_52);
x_53 = lean_ctor_get(x_46, 3);
lean_inc(x_53);
x_54 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_54);
x_55 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_55, 0, x_54);
lean_inc(x_55);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_55);
x_57 = lean_ctor_get(x_46, 5);
lean_inc(x_57);
x_58 = lean_ctor_get(x_46, 6);
lean_inc(x_58);
x_59 = lean_ctor_get(x_46, 7);
lean_inc(x_59);
lean_dec(x_46);
x_60 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_60, 0, x_50);
lean_ctor_set(x_60, 1, x_51);
lean_ctor_set(x_60, 2, x_52);
lean_ctor_set(x_60, 3, x_53);
lean_ctor_set(x_60, 4, x_56);
lean_ctor_set(x_60, 5, x_57);
lean_ctor_set(x_60, 6, x_58);
lean_ctor_set(x_60, 7, x_59);
x_61 = lean_st_ref_set(x_6, x_60, x_47);
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
lean_dec(x_61);
x_63 = lean_st_ref_take(x_4, x_62);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = lean_ctor_get(x_64, 0);
lean_inc(x_66);
lean_inc(x_54);
x_67 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_67, 0, x_54);
lean_inc(x_54);
x_68 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_68, 0, x_54);
lean_inc(x_54);
x_69 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_69, 0, x_54);
x_70 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_70, 0, x_54);
lean_inc(x_70);
lean_inc(x_67);
x_71 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_71, 0, x_67);
lean_ctor_set(x_71, 1, x_68);
lean_ctor_set(x_71, 2, x_69);
lean_ctor_set(x_71, 3, x_67);
lean_ctor_set(x_71, 4, x_70);
lean_ctor_set(x_71, 5, x_70);
x_72 = lean_ctor_get(x_64, 2);
lean_inc(x_72);
x_73 = lean_ctor_get(x_64, 3);
lean_inc(x_73);
x_74 = lean_ctor_get(x_64, 4);
lean_inc(x_74);
lean_dec(x_64);
x_75 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_75, 0, x_66);
lean_ctor_set(x_75, 1, x_71);
lean_ctor_set(x_75, 2, x_72);
lean_ctor_set(x_75, 3, x_73);
lean_ctor_set(x_75, 4, x_74);
x_76 = lean_st_ref_set(x_4, x_75, x_65);
x_77 = lean_ctor_get(x_76, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_78 = x_76;
} else {
 lean_dec_ref(x_76);
 x_78 = lean_box(0);
}
x_79 = lean_box(0);
if (lean_is_scalar(x_78)) {
 x_80 = lean_alloc_ctor(0, 2, 0);
} else {
 x_80 = x_78;
}
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_77);
return x_80;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___Lean_Meta_addSimpCongrTheorem_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_ScopedEnvExtension_add___at___Lean_Meta_addSimpCongrTheorem_spec__0___redArg(x_4, x_5, x_6, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addSimpCongrTheorem(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_9 = l_Lean_Meta_mkSimpCongrTheorem(x_1, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Meta_congrExtension;
x_13 = l_Lean_ScopedEnvExtension_add___at___Lean_Meta_addSimpCongrTheorem_spec__0___redArg(x_12, x_10, x_2, x_5, x_6, x_7, x_11);
lean_dec(x_7);
lean_dec(x_5);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_14 = !lean_is_exclusive(x_9);
if (x_14 == 0)
{
return x_9;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_9, 0);
x_16 = lean_ctor_get(x_9, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_9);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___Lean_Meta_addSimpCongrTheorem_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_3);
lean_dec(x_3);
x_9 = l_Lean_ScopedEnvExtension_add___at___Lean_Meta_addSimpCongrTheorem_spec__0___redArg(x_1, x_2, x_8, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___Lean_Meta_addSimpCongrTheorem_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_6);
lean_dec(x_6);
x_13 = l_Lean_ScopedEnvExtension_add___at___Lean_Meta_addSimpCongrTheorem_spec__0(x_1, x_2, x_3, x_4, x_5, x_12, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addSimpCongrTheorem___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_Lean_Meta_addSimpCongrTheorem(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__0____x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems___hyg_1861_(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = l_Lean_Syntax_getArg(x_2, x_7);
x_9 = l_Lean_getAttrParamOptPrio(x_8, x_4, x_5, x_6);
lean_dec(x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; lean_object* x_17; lean_object* x_18; size_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; uint8_t x_53; uint8_t x_54; uint8_t x_55; uint8_t x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; uint8_t x_60; uint8_t x_61; uint8_t x_62; uint8_t x_63; uint8_t x_64; uint8_t x_65; uint8_t x_66; uint8_t x_67; uint8_t x_68; uint8_t x_69; uint64_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; uint8_t x_77; uint8_t x_78; lean_object* x_79; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_box(0);
x_13 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
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
x_23 = lean_unsigned_to_nat(0u);
lean_inc(x_13);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_13);
lean_inc(x_13);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_13);
lean_inc(x_13);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_13);
lean_inc(x_13);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_13);
lean_inc(x_13);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_13);
lean_inc(x_13);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_13);
lean_inc(x_24);
x_30 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_30, 0, x_23);
lean_ctor_set(x_30, 1, x_23);
lean_ctor_set(x_30, 2, x_23);
lean_ctor_set(x_30, 3, x_24);
lean_ctor_set(x_30, 4, x_25);
lean_ctor_set(x_30, 5, x_26);
lean_ctor_set(x_30, 6, x_27);
lean_ctor_set(x_30, 7, x_28);
lean_ctor_set(x_30, 8, x_29);
lean_inc(x_13);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_13);
lean_inc(x_13);
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_13);
lean_inc(x_13);
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_13);
lean_inc(x_13);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_13);
lean_inc(x_34);
lean_inc(x_31);
x_35 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_35, 0, x_31);
lean_ctor_set(x_35, 1, x_32);
lean_ctor_set(x_35, 2, x_33);
lean_ctor_set(x_35, 3, x_31);
lean_ctor_set(x_35, 4, x_34);
lean_ctor_set(x_35, 5, x_34);
lean_inc(x_21);
x_36 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_36, 0, x_21);
lean_inc(x_21);
x_37 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_21);
lean_ctor_set(x_37, 2, x_23);
lean_ctor_set(x_37, 3, x_23);
lean_ctor_set_usize(x_37, 4, x_16);
lean_inc(x_13);
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_13);
lean_inc_n(x_24, 2);
x_39 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_39, 0, x_24);
lean_ctor_set(x_39, 1, x_24);
lean_ctor_set(x_39, 2, x_24);
lean_ctor_set(x_39, 3, x_38);
x_40 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_40, 0, x_30);
lean_ctor_set(x_40, 1, x_35);
lean_ctor_set(x_40, 2, x_12);
lean_ctor_set(x_40, 3, x_37);
lean_ctor_set(x_40, 4, x_39);
x_41 = lean_st_mk_ref(x_40, x_11);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_box(1);
x_45 = lean_box(1);
x_46 = lean_box(0);
x_47 = lean_box(2);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_13);
x_49 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_49, 0, x_22);
lean_ctor_set(x_49, 1, x_21);
lean_ctor_set(x_49, 2, x_23);
lean_ctor_set(x_49, 3, x_23);
lean_ctor_set_usize(x_49, 4, x_16);
x_50 = lean_box(0);
x_51 = lean_alloc_ctor(0, 0, 18);
x_52 = lean_unbox(x_50);
lean_ctor_set_uint8(x_51, 0, x_52);
x_53 = lean_unbox(x_50);
lean_ctor_set_uint8(x_51, 1, x_53);
x_54 = lean_unbox(x_50);
lean_ctor_set_uint8(x_51, 2, x_54);
x_55 = lean_unbox(x_50);
lean_ctor_set_uint8(x_51, 3, x_55);
x_56 = lean_unbox(x_50);
lean_ctor_set_uint8(x_51, 4, x_56);
x_57 = lean_unbox(x_44);
lean_ctor_set_uint8(x_51, 5, x_57);
x_58 = lean_unbox(x_44);
lean_ctor_set_uint8(x_51, 6, x_58);
x_59 = lean_unbox(x_50);
lean_ctor_set_uint8(x_51, 7, x_59);
x_60 = lean_unbox(x_44);
lean_ctor_set_uint8(x_51, 8, x_60);
x_61 = lean_unbox(x_45);
lean_ctor_set_uint8(x_51, 9, x_61);
x_62 = lean_unbox(x_46);
lean_ctor_set_uint8(x_51, 10, x_62);
x_63 = lean_unbox(x_44);
lean_ctor_set_uint8(x_51, 11, x_63);
x_64 = lean_unbox(x_44);
lean_ctor_set_uint8(x_51, 12, x_64);
x_65 = lean_unbox(x_44);
lean_ctor_set_uint8(x_51, 13, x_65);
x_66 = lean_unbox(x_47);
lean_ctor_set_uint8(x_51, 14, x_66);
x_67 = lean_unbox(x_44);
lean_ctor_set_uint8(x_51, 15, x_67);
x_68 = lean_unbox(x_44);
lean_ctor_set_uint8(x_51, 16, x_68);
x_69 = lean_unbox(x_44);
lean_ctor_set_uint8(x_51, 17, x_69);
x_70 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_51);
x_71 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_71, 0, x_48);
lean_ctor_set(x_71, 1, x_49);
lean_ctor_set(x_71, 2, x_12);
x_72 = lean_mk_empty_array_with_capacity(x_23);
x_73 = lean_box(0);
x_74 = lean_box(0);
x_75 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_75, 0, x_51);
lean_ctor_set(x_75, 1, x_12);
lean_ctor_set(x_75, 2, x_71);
lean_ctor_set(x_75, 3, x_72);
lean_ctor_set(x_75, 4, x_73);
lean_ctor_set(x_75, 5, x_23);
lean_ctor_set(x_75, 6, x_74);
lean_ctor_set_uint64(x_75, sizeof(void*)*7, x_70);
x_76 = lean_unbox(x_50);
lean_ctor_set_uint8(x_75, sizeof(void*)*7 + 8, x_76);
x_77 = lean_unbox(x_50);
lean_ctor_set_uint8(x_75, sizeof(void*)*7 + 9, x_77);
x_78 = lean_unbox(x_50);
lean_ctor_set_uint8(x_75, sizeof(void*)*7 + 10, x_78);
lean_inc(x_42);
x_79 = l_Lean_Meta_addSimpCongrTheorem(x_1, x_3, x_10, x_75, x_42, x_4, x_5, x_43);
lean_dec(x_75);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_80 = lean_ctor_get(x_79, 1);
lean_inc(x_80);
lean_dec(x_79);
x_81 = lean_st_ref_get(x_42, x_80);
lean_dec(x_42);
x_82 = !lean_is_exclusive(x_81);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_81, 0);
lean_dec(x_83);
x_84 = lean_box(0);
lean_ctor_set(x_81, 0, x_84);
return x_81;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_81, 1);
lean_inc(x_85);
lean_dec(x_81);
x_86 = lean_box(0);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_85);
return x_87;
}
}
else
{
lean_dec(x_42);
return x_79;
}
}
else
{
uint8_t x_88; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_88 = !lean_is_exclusive(x_9);
if (x_88 == 0)
{
return x_9;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_9, 0);
x_90 = lean_ctor_get(x_9, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_9);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__1____x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems___hyg_1861_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems___hyg_1861_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_initFn___lam__0____x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems___hyg_1861____boxed), 6, 0);
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_initFn___lam__1____x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems___hyg_1861____boxed), 4, 0);
x_4 = lean_box(0);
x_5 = lean_mk_string_unchecked("Lean", 4, 4);
lean_inc(x_5);
x_6 = l_Lean_Name_str___override(x_4, x_5);
x_7 = lean_mk_string_unchecked("Meta", 4, 4);
lean_inc(x_7);
x_8 = l_Lean_Name_str___override(x_6, x_7);
x_9 = lean_mk_string_unchecked("initFn", 6, 6);
x_10 = l_Lean_Name_str___override(x_8, x_9);
x_11 = lean_mk_string_unchecked("_@", 2, 2);
x_12 = l_Lean_Name_str___override(x_10, x_11);
x_13 = l_Lean_Name_str___override(x_12, x_5);
x_14 = l_Lean_Name_str___override(x_13, x_7);
x_15 = lean_mk_string_unchecked("Tactic", 6, 6);
x_16 = l_Lean_Name_str___override(x_14, x_15);
x_17 = lean_mk_string_unchecked("Simp", 4, 4);
x_18 = l_Lean_Name_str___override(x_16, x_17);
x_19 = lean_mk_string_unchecked("SimpCongrTheorems", 17, 17);
x_20 = l_Lean_Name_str___override(x_18, x_19);
x_21 = lean_mk_string_unchecked("_hyg", 4, 4);
x_22 = l_Lean_Name_str___override(x_20, x_21);
x_23 = lean_unsigned_to_nat(1861u);
x_24 = l_Lean_Name_num___override(x_22, x_23);
x_25 = lean_mk_string_unchecked("congr", 5, 5);
x_26 = l_Lean_Name_mkStr1(x_25);
x_27 = lean_mk_string_unchecked("congruence theorem", 18, 18);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_29, 0, x_24);
lean_ctor_set(x_29, 1, x_26);
lean_ctor_set(x_29, 2, x_27);
x_30 = lean_unbox(x_28);
lean_ctor_set_uint8(x_29, sizeof(void*)*3, x_30);
x_31 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_2);
lean_ctor_set(x_31, 2, x_3);
x_32 = l_Lean_registerBuiltinAttribute(x_31, x_1);
return x_32;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__0____x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems___hyg_1861____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l_Lean_Meta_initFn___lam__0____x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems___hyg_1861_(x_1, x_2, x_7, x_4, x_5, x_6);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__1____x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems___hyg_1861____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_initFn___lam__1____x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems___hyg_1861_(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getSimpCongrTheorems___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_st_ref_get(x_1, x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = l_Lean_Meta_instInhabitedSimpCongrTheorems;
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_Lean_Meta_congrExtension;
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get_uint8(x_10, sizeof(void*)*3);
lean_dec(x_10);
x_12 = l_Lean_ScopedEnvExtension_getState___redArg(x_6, x_8, x_7, x_11);
lean_ctor_set(x_3, 0, x_12);
return x_3;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_13 = lean_ctor_get(x_3, 0);
x_14 = lean_ctor_get(x_3, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_3);
x_15 = l_Lean_Meta_instInhabitedSimpCongrTheorems;
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
lean_dec(x_13);
x_17 = l_Lean_Meta_congrExtension;
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_ctor_get_uint8(x_19, sizeof(void*)*3);
lean_dec(x_19);
x_21 = l_Lean_ScopedEnvExtension_getState___redArg(x_15, x_17, x_16, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_14);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getSimpCongrTheorems(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_getSimpCongrTheorems___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getSimpCongrTheorems___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_getSimpCongrTheorems___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getSimpCongrTheorems___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_getSimpCongrTheorems(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* initialize_Lean_ScopedEnvExtension(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_Recognizers(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_CollectMVars(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Simp_SimpCongrTheorems(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_ScopedEnvExtension(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_Recognizers(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_CollectMVars(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_instInhabitedSimpCongrTheorem = _init_l_Lean_Meta_instInhabitedSimpCongrTheorem();
lean_mark_persistent(l_Lean_Meta_instInhabitedSimpCongrTheorem);
l_Lean_Meta_instReprSimpCongrTheorem = _init_l_Lean_Meta_instReprSimpCongrTheorem();
lean_mark_persistent(l_Lean_Meta_instReprSimpCongrTheorem);
l_Lean_Meta_instInhabitedSimpCongrTheorems = _init_l_Lean_Meta_instInhabitedSimpCongrTheorems();
lean_mark_persistent(l_Lean_Meta_instInhabitedSimpCongrTheorems);
l_Lean_Meta_instReprSimpCongrTheorems = _init_l_Lean_Meta_instReprSimpCongrTheorems();
lean_mark_persistent(l_Lean_Meta_instReprSimpCongrTheorems);
if (builtin) {res = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems___hyg_362_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_congrExtension = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_congrExtension);
lean_dec_ref(res);
}if (builtin) {res = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems___hyg_1861_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
