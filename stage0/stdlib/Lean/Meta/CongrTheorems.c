// Lean compiler output
// Module: Lean.Meta.CongrTheorems
// Imports: Lean.AddDecl Lean.ReservedNameAction Lean.ResolveName Lean.Meta.AppBuilder Lean.Class
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
lean_object* l_Lean_Expr_bindingName_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArity_withNewEqs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerReservedNameAction(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_hcongrThmSuffixBasePrefix;
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArity_withNewEqs___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__0(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Meta_getCongrSimpKinds_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_setBinderInfosD(lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpForConst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_setBinderInfosD_spec__0(lean_object*, size_t, size_t, lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimp_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_noConfusion___redArg___boxed(lean_object*, lean_object*);
lean_object* l_String_toNat_x21(lean_object*);
lean_object* lean_name_append_after(lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MapDeclarationExtension_insert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkHCongrWithArity_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
lean_object* l_Lean_Meta_withLCtx___at_____private_Lean_Meta_Basic_0__Lean_Meta_mkLevelErrorMessageCore_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_addPrimeToFVarUserNames___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpCore_x3f(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArity_mkProof___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_CongrTheorems___hyg_5298_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_CongrTheorems___hyg_5266_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArity_mkProof___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Meta_getCongrSimpKindsForArgZero_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_FunInfo_getArity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isHCongrReservedNameSuffix___boxed(lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
uint8_t l_Array_contains___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_congrSimpSuffix;
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArity_withNewEqs_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_mkMapDeclarationExtension___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_name_append_before(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_hcongrThmSuffixBase;
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Meta_getCongrSimpKinds_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__0____x40_Lean_Meta_CongrTheorems___hyg_5298____boxed(lean_object*, lean_object*);
extern lean_object* l_instInhabitedNat;
uint8_t l_Lean_Expr_hasMVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__0____x40_Lean_Meta_CongrTheorems___hyg_5266____boxed(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_isHCongrReservedNameSuffix(lean_object*);
lean_object* l_Lean_LocalContext_getFVar_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_go_spec__0___redArg___lam__1___boxed(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_isSubobjectField_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at___Lean_Meta_withLocalDeclD___at___Lean_Meta_addPPExplicitToExposeDiff_visit_spec__3_spec__3___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_getCongrSimpKinds_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArity_mkProof___lam__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_noConfusion___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___at___Lean_Meta_whnfCore_go_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_executeReservedNameAction(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* l_Lean_Meta_getFunInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_noConfusion(lean_object*, uint8_t, uint8_t, lean_object*);
uint32_t lean_uint32_of_nat(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_beqCongrArgKind____x40_Lean_Meta_CongrTheorems___hyg_230_(uint8_t, uint8_t);
uint8_t l___private_Lean_Expr_0__Lean_beqFVarId____x40_Lean_Expr___hyg_1672_(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_arrowDomainsN_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_initFn___lam__0____x40_Lean_Meta_CongrTheorems___hyg_5298_(lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_toCtorIdx___boxed(lean_object*);
lean_object* l_Lean_Meta_mkEqNDRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_setBinderInfo(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_mkHEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArityForConst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBMap_toArray___at___Lean_mkMapDeclarationExtension_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArity_mkProof___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_getCongrSimpKinds_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate(lean_object*, lean_object*);
lean_object* l_Lean_MapDeclarationExtension_find_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewBinderInfos___at___Lean_Meta_withInstImplicitAsImplict_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_getCongrSimpKindsForArgZero_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l_Lean_Expr_replaceFVar(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkHEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArity___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getCongrSimpKindsForArgZero___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpForConst_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_getCongrSimpKinds_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_ofSubarray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_go_spec__0___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_addPrimeToFVarUserNames(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_hasCastLike_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_mkCongrSimpCore_x3f_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArity_mkProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_addPrimeToFVarUserNames_spec__0(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArity(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Meta_getCongrSimpKinds_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_setUserName(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_ParamInfo_isInstImplicit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_noConfusion___redArg(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_congrKindsExt;
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpCore_x3f_mk_x3f(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__0____x40_Lean_Meta_CongrTheorems___hyg_5351_(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerReservedNamePredicate(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_instInhabited(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArity_mkProof___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpCore_x3f_mkProof_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Meta_mkHCongrWithArityForConst_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Meta_getCongrSimpKinds_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_CongrTheorems___hyg_5351_(lean_object*);
lean_object* l_Substring_nextn(lean_object*, lean_object*, lean_object*);
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArity_mkProof___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArity___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_go_spec__0___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instBEqCongrArgKind;
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingDomain_x21(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_getCongrSimpKinds_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_mkCongrSimpCore_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_replaceFVars(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_getCongrSimpKindsForArgZero_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_noConfusion___redArg___lam__0(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_instInhabitedCongrArgKind;
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArity___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArity___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDeclD___at___Lean_Meta_addPPExplicitToExposeDiff_visit_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_hasCastLike_spec__0(lean_object*, size_t, size_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpCore_x3f_mkProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___lam__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpCore_x3f_mk_x3f___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
uint8_t l_Lean_Expr_isHEq(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReprCongrArgKind;
uint8_t l_String_isPrefixOf(lean_object*, lean_object*);
uint8_t l_Lean_Environment_isSafeDefinition(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_getCongrSimpKindsForArgZero_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArity___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkHCongrWithArity_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getCongrSimpKindsForArgZero(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___at___Lean_Meta_getParamNames_spec__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimp_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_setBinderInfosD___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Meta_getCongrSimpKindsForArgZero_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpCore_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_go_spec__0___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Meta_getCongrSimpKindsForArgZero_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_anyAux___at___Lean_Meta_isHCongrReservedNameSuffix_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_binderInfo(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_reprCongrArgKind____x40_Lean_Meta_CongrTheorems___hyg_18_(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkHCongrWithArity_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Meta_getCongrSimpKindsForArgZero_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__2(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpCore_x3f_mk_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_instInhabitedParamInfo;
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqOfHEq(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_reprCongrArgKind____x40_Lean_Meta_CongrTheorems___hyg_18____boxed(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_hasCastLike___boxed(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Expr_bindingBody_x21(lean_object*);
lean_object* l_Lean_Meta_getLocalInstances___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_setBinderInfosD_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__0____x40_Lean_Meta_CongrTheorems___hyg_5266_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_noConfusion___redArg___lam__0___boxed(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_getCongrSimpKindsForArgZero_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__3(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_getCongrSimpKinds(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__1(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkHCongrWithArity_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_instDecidableEqPos(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_go_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_anyAux___at___Lean_Meta_isHCongrReservedNameSuffix_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_is_class(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_hasCastLike(lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArity___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getCongrSimpKinds___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArity_withNewEqs_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_addPrimeToFVarUserNames_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___at___Lean_mkConstWithLevelParams___at___Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__2(lean_object*, lean_object*);
lean_object* l_Lean_addDecl(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpCore_x3f_mk_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_beqCongrArgKind____x40_Lean_Meta_CongrTheorems___hyg_230____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpForConst_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_toCtorIdx(uint8_t x_1) {
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
case 2:
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
case 3:
{
lean_object* x_5; 
x_5 = lean_unsigned_to_nat(3u);
return x_5;
}
case 4:
{
lean_object* x_6; 
x_6 = lean_unsigned_to_nat(4u);
return x_6;
}
default: 
{
lean_object* x_7; 
x_7 = lean_unsigned_to_nat(5u);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Meta_CongrArgKind_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_noConfusion___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_noConfusion___redArg(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_CongrArgKind_noConfusion___redArg___lam__0___boxed), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_noConfusion(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_CongrArgKind_noConfusion___redArg(x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_noConfusion___redArg___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_CongrArgKind_noConfusion___redArg___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_noConfusion___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lean_Meta_CongrArgKind_noConfusion___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_noConfusion___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l_Lean_Meta_CongrArgKind_noConfusion(x_1, x_5, x_6, x_4);
return x_7;
}
}
static uint8_t _init_l_Lean_Meta_instInhabitedCongrArgKind() {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = lean_box(0);
x_2 = lean_unbox(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_reprCongrArgKind____x40_Lean_Meta_CongrTheorems___hyg_18_(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_12; lean_object* x_21; lean_object* x_30; lean_object* x_39; lean_object* x_48; 
switch (x_1) {
case 0:
{
lean_object* x_57; uint8_t x_58; 
x_57 = lean_unsigned_to_nat(1024u);
x_58 = lean_nat_dec_le(x_57, x_2);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_unsigned_to_nat(2u);
x_60 = lean_nat_to_int(x_59);
x_3 = x_60;
goto block_11;
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_unsigned_to_nat(1u);
x_62 = lean_nat_to_int(x_61);
x_3 = x_62;
goto block_11;
}
}
case 1:
{
lean_object* x_63; uint8_t x_64; 
x_63 = lean_unsigned_to_nat(1024u);
x_64 = lean_nat_dec_le(x_63, x_2);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_unsigned_to_nat(2u);
x_66 = lean_nat_to_int(x_65);
x_12 = x_66;
goto block_20;
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_unsigned_to_nat(1u);
x_68 = lean_nat_to_int(x_67);
x_12 = x_68;
goto block_20;
}
}
case 2:
{
lean_object* x_69; uint8_t x_70; 
x_69 = lean_unsigned_to_nat(1024u);
x_70 = lean_nat_dec_le(x_69, x_2);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_unsigned_to_nat(2u);
x_72 = lean_nat_to_int(x_71);
x_21 = x_72;
goto block_29;
}
else
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_unsigned_to_nat(1u);
x_74 = lean_nat_to_int(x_73);
x_21 = x_74;
goto block_29;
}
}
case 3:
{
lean_object* x_75; uint8_t x_76; 
x_75 = lean_unsigned_to_nat(1024u);
x_76 = lean_nat_dec_le(x_75, x_2);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_unsigned_to_nat(2u);
x_78 = lean_nat_to_int(x_77);
x_30 = x_78;
goto block_38;
}
else
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_unsigned_to_nat(1u);
x_80 = lean_nat_to_int(x_79);
x_30 = x_80;
goto block_38;
}
}
case 4:
{
lean_object* x_81; uint8_t x_82; 
x_81 = lean_unsigned_to_nat(1024u);
x_82 = lean_nat_dec_le(x_81, x_2);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_unsigned_to_nat(2u);
x_84 = lean_nat_to_int(x_83);
x_39 = x_84;
goto block_47;
}
else
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_unsigned_to_nat(1u);
x_86 = lean_nat_to_int(x_85);
x_39 = x_86;
goto block_47;
}
}
default: 
{
lean_object* x_87; uint8_t x_88; 
x_87 = lean_unsigned_to_nat(1024u);
x_88 = lean_nat_dec_le(x_87, x_2);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_unsigned_to_nat(2u);
x_90 = lean_nat_to_int(x_89);
x_48 = x_90;
goto block_56;
}
else
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_unsigned_to_nat(1u);
x_92 = lean_nat_to_int(x_91);
x_48 = x_92;
goto block_56;
}
}
}
block_11:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_4 = lean_mk_string_unchecked("Lean.Meta.CongrArgKind.fixed", 28, 28);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_8, 0, x_6);
x_9 = lean_unbox(x_7);
lean_ctor_set_uint8(x_8, sizeof(void*)*1, x_9);
x_10 = l_Repr_addAppParen(x_8, x_2);
return x_10;
}
block_20:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_13 = lean_mk_string_unchecked("Lean.Meta.CongrArgKind.fixedNoParam", 35, 35);
x_14 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_17, 0, x_15);
x_18 = lean_unbox(x_16);
lean_ctor_set_uint8(x_17, sizeof(void*)*1, x_18);
x_19 = l_Repr_addAppParen(x_17, x_2);
return x_19;
}
block_29:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; 
x_22 = lean_mk_string_unchecked("Lean.Meta.CongrArgKind.eq", 25, 25);
x_23 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_26, 0, x_24);
x_27 = lean_unbox(x_25);
lean_ctor_set_uint8(x_26, sizeof(void*)*1, x_27);
x_28 = l_Repr_addAppParen(x_26, x_2);
return x_28;
}
block_38:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; 
x_31 = lean_mk_string_unchecked("Lean.Meta.CongrArgKind.cast", 27, 27);
x_32 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_35, 0, x_33);
x_36 = lean_unbox(x_34);
lean_ctor_set_uint8(x_35, sizeof(void*)*1, x_36);
x_37 = l_Repr_addAppParen(x_35, x_2);
return x_37;
}
block_47:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; 
x_40 = lean_mk_string_unchecked("Lean.Meta.CongrArgKind.heq", 26, 26);
x_41 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_42 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_44, 0, x_42);
x_45 = lean_unbox(x_43);
lean_ctor_set_uint8(x_44, sizeof(void*)*1, x_45);
x_46 = l_Repr_addAppParen(x_44, x_2);
return x_46;
}
block_56:
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; 
x_49 = lean_mk_string_unchecked("Lean.Meta.CongrArgKind.subsingletonInst", 39, 39);
x_50 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_50, 0, x_49);
x_51 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_51, 0, x_48);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_53, 0, x_51);
x_54 = lean_unbox(x_52);
lean_ctor_set_uint8(x_53, sizeof(void*)*1, x_54);
x_55 = l_Repr_addAppParen(x_53, x_2);
return x_55;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_reprCongrArgKind____x40_Lean_Meta_CongrTheorems___hyg_18____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_reprCongrArgKind____x40_Lean_Meta_CongrTheorems___hyg_18_(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_instReprCongrArgKind() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_reprCongrArgKind____x40_Lean_Meta_CongrTheorems___hyg_18____boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_beqCongrArgKind____x40_Lean_Meta_CongrTheorems___hyg_230_(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_Meta_CongrArgKind_toCtorIdx(x_1);
x_4 = l_Lean_Meta_CongrArgKind_toCtorIdx(x_2);
x_5 = lean_nat_dec_eq(x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_beqCongrArgKind____x40_Lean_Meta_CongrTheorems___hyg_230____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_beqCongrArgKind____x40_Lean_Meta_CongrTheorems___hyg_230_(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_instBEqCongrArgKind() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_beqCongrArgKind____x40_Lean_Meta_CongrTheorems___hyg_230____boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_addPrimeToFVarUserNames_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_15; 
x_15 = lean_usize_dec_lt(x_3, x_2);
if (x_15 == 0)
{
return x_4;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_21; 
x_16 = lean_array_uget(x_1, x_3);
lean_inc(x_4);
x_17 = l_Lean_LocalContext_getFVar_x21(x_4, x_16);
lean_dec(x_16);
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
x_18 = x_21;
goto block_20;
block_20:
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 2);
lean_inc(x_19);
lean_dec(x_17);
x_5 = x_18;
x_6 = x_19;
goto block_14;
}
}
block_14:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; 
x_7 = lean_mk_string_unchecked("'", 1, 1);
x_8 = lean_name_append_after(x_6, x_7);
x_9 = l_Lean_LocalContext_setUserName(x_4, x_5, x_8);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_usize_of_nat(x_10);
x_12 = lean_usize_add(x_3, x_11);
x_3 = x_12;
x_4 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_addPrimeToFVarUserNames(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; lean_object* x_4; size_t x_5; lean_object* x_6; 
x_3 = lean_array_size(x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_usize_of_nat(x_4);
x_6 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_addPrimeToFVarUserNames_spec__0(x_1, x_3, x_5, x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_addPrimeToFVarUserNames_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_addPrimeToFVarUserNames_spec__0(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_addPrimeToFVarUserNames___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_addPrimeToFVarUserNames(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_setBinderInfosD_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_3, x_2);
if (x_14 == 0)
{
return x_4;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_array_uget(x_1, x_3);
lean_inc(x_4);
x_16 = l_Lean_LocalContext_getFVar_x21(x_4, x_15);
lean_dec(x_15);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_5 = x_17;
goto block_13;
}
block_13:
{
lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; 
x_6 = lean_box(0);
x_7 = lean_unbox(x_6);
x_8 = l_Lean_LocalContext_setBinderInfo(x_4, x_5, x_7);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_usize_of_nat(x_9);
x_11 = lean_usize_add(x_3, x_10);
x_3 = x_11;
x_4 = x_8;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_setBinderInfosD(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; lean_object* x_4; size_t x_5; lean_object* x_6; 
x_3 = lean_array_size(x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_usize_of_nat(x_4);
x_6 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_setBinderInfosD_spec__0(x_1, x_3, x_5, x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_setBinderInfosD_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_setBinderInfosD_spec__0(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_setBinderInfosD___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_setBinderInfosD(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_array_push(x_1, x_7);
x_14 = lean_box(4);
x_15 = lean_array_push(x_2, x_14);
x_16 = l_Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg(x_3, x_4, x_5, x_6, x_13, x_15, x_8, x_9, x_10, x_11, x_12);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_array_push(x_1, x_7);
x_14 = lean_box(2);
x_15 = lean_array_push(x_2, x_14);
x_16 = l_Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg(x_3, x_4, x_5, x_6, x_13, x_15, x_8, x_9, x_10, x_11, x_12);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_1);
x_13 = lean_nat_dec_lt(x_4, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_apply_7(x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = l_Lean_instInhabitedExpr;
x_16 = lean_array_get(x_15, x_1, x_4);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_16);
x_17 = lean_infer_type(x_16, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_array_get(x_15, x_2, x_4);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_20);
x_21 = lean_infer_type(x_20, x_7, x_8, x_9, x_10, x_19);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_Expr_cleanupAnnotations(x_18);
x_25 = l_Lean_Expr_cleanupAnnotations(x_22);
x_26 = lean_expr_eqv(x_24, x_25);
lean_dec(x_25);
lean_dec(x_24);
if (x_26 == 0)
{
lean_object* x_27; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_27 = l_Lean_Meta_mkHEq(x_16, x_20, x_7, x_8, x_9, x_10, x_23);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_mk_string_unchecked("e", 1, 1);
x_31 = l_Lean_Name_mkStr1(x_30);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_add(x_4, x_32);
lean_inc(x_33);
x_34 = lean_alloc_closure((void*)(l_Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg___lam__0___boxed), 12, 6);
lean_closure_set(x_34, 0, x_5);
lean_closure_set(x_34, 1, x_6);
lean_closure_set(x_34, 2, x_1);
lean_closure_set(x_34, 3, x_2);
lean_closure_set(x_34, 4, x_3);
lean_closure_set(x_34, 5, x_33);
x_35 = lean_name_append_index_after(x_31, x_33);
x_36 = l_Lean_Meta_withLocalDeclD___at___Lean_Meta_addPPExplicitToExposeDiff_visit_spec__3(lean_box(0), x_35, x_28, x_34, x_7, x_8, x_9, x_10, x_29);
return x_36;
}
else
{
uint8_t x_37; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_27);
if (x_37 == 0)
{
return x_27;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_27, 0);
x_39 = lean_ctor_get(x_27, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_27);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
lean_object* x_41; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_41 = l_Lean_Meta_mkEq(x_16, x_20, x_7, x_8, x_9, x_10, x_23);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_mk_string_unchecked("e", 1, 1);
x_45 = l_Lean_Name_mkStr1(x_44);
x_46 = lean_unsigned_to_nat(1u);
x_47 = lean_nat_add(x_4, x_46);
lean_inc(x_47);
x_48 = lean_alloc_closure((void*)(l_Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg___lam__1___boxed), 12, 6);
lean_closure_set(x_48, 0, x_5);
lean_closure_set(x_48, 1, x_6);
lean_closure_set(x_48, 2, x_1);
lean_closure_set(x_48, 3, x_2);
lean_closure_set(x_48, 4, x_3);
lean_closure_set(x_48, 5, x_47);
x_49 = lean_name_append_index_after(x_45, x_47);
x_50 = l_Lean_Meta_withLocalDeclD___at___Lean_Meta_addPPExplicitToExposeDiff_visit_spec__3(lean_box(0), x_49, x_42, x_48, x_7, x_8, x_9, x_10, x_43);
return x_50;
}
else
{
uint8_t x_51; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_41);
if (x_51 == 0)
{
return x_41;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_41, 0);
x_53 = lean_ctor_get(x_41, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_41);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
else
{
uint8_t x_55; 
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_55 = !lean_is_exclusive(x_21);
if (x_55 == 0)
{
return x_21;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_21, 0);
x_57 = lean_ctor_get(x_21, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_21);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
uint8_t x_59; 
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_59 = !lean_is_exclusive(x_17);
if (x_59 == 0)
{
return x_17;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_17, 0);
x_61 = lean_ctor_get(x_17, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_17);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArity_withNewEqs_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_6);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_6);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArity_withNewEqs_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_mkHCongrWithArity_withNewEqs_loop(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_5);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArity_withNewEqs___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_mk_empty_array_with_capacity(x_9);
lean_inc(x_10);
x_11 = l_Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg(x_1, x_2, x_3, x_9, x_10, x_10, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArity_withNewEqs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_mkHCongrWithArity_withNewEqs___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArity_mkProof___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Lean_Expr_bindingBody_x21(x_1);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_15 = l_Lean_Meta_mkHCongrWithArity_mkProof(x_14, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_18 = lean_infer_type(x_8, x_9, x_10, x_11, x_12, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_21 = lean_whnf(x_19, x_9, x_10, x_11, x_12, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_51; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_Expr_bindingBody_x21(x_2);
x_51 = l_Lean_Expr_isHEq(x_22);
lean_dec(x_22);
if (x_51 == 0)
{
lean_inc(x_8);
x_25 = x_8;
x_26 = x_9;
x_27 = x_10;
x_28 = x_11;
x_29 = x_12;
x_30 = x_23;
goto block_50;
}
else
{
lean_object* x_52; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_52 = l_Lean_Meta_mkEqOfHEq(x_8, x_51, x_9, x_10, x_11, x_12, x_23);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_25 = x_53;
x_26 = x_9;
x_27 = x_10;
x_28 = x_11;
x_29 = x_12;
x_30 = x_54;
goto block_50;
}
else
{
lean_dec(x_24);
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
return x_52;
}
}
block_50:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_36; lean_object* x_37; 
x_31 = lean_mk_empty_array_with_capacity(x_3);
lean_inc(x_4);
x_32 = lean_array_push(x_31, x_4);
x_33 = lean_box(1);
x_34 = lean_box(1);
x_35 = lean_unbox(x_33);
x_36 = lean_unbox(x_34);
x_37 = l_Lean_Meta_mkLambdaFVars(x_32, x_24, x_5, x_35, x_5, x_36, x_26, x_27, x_28, x_29, x_30);
lean_dec(x_32);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
x_40 = l_Lean_Meta_mkEqNDRec(x_38, x_16, x_25, x_26, x_27, x_28, x_29, x_39);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; uint8_t x_48; lean_object* x_49; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_mk_empty_array_with_capacity(x_6);
x_44 = lean_array_push(x_43, x_7);
x_45 = lean_array_push(x_44, x_4);
x_46 = lean_array_push(x_45, x_8);
x_47 = lean_unbox(x_33);
x_48 = lean_unbox(x_34);
x_49 = l_Lean_Meta_mkLambdaFVars(x_46, x_41, x_5, x_47, x_5, x_48, x_26, x_27, x_28, x_29, x_42);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_46);
return x_49;
}
else
{
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
return x_40;
}
}
else
{
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
return x_37;
}
}
}
else
{
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
return x_21;
}
}
else
{
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
return x_18;
}
}
else
{
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArity_mkProof___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_15 = lean_array_get(x_1, x_8, x_2);
x_16 = l_Lean_Expr_bindingBody_x21(x_3);
x_17 = lean_expr_instantiate1(x_16, x_4);
lean_dec(x_16);
x_18 = lean_box(x_6);
lean_inc(x_9);
x_19 = lean_alloc_closure((void*)(l_Lean_Meta_mkHCongrWithArity_mkProof___lam__0___boxed), 13, 7);
lean_closure_set(x_19, 0, x_17);
lean_closure_set(x_19, 1, x_9);
lean_closure_set(x_19, 2, x_5);
lean_closure_set(x_19, 3, x_15);
lean_closure_set(x_19, 4, x_18);
lean_closure_set(x_19, 5, x_7);
lean_closure_set(x_19, 6, x_4);
x_20 = l_Lean_Expr_bindingName_x21(x_9);
x_21 = l_Lean_Expr_bindingDomain_x21(x_9);
lean_dec(x_9);
x_22 = l_Lean_Meta_withLocalDeclD___at___Lean_Meta_addPPExplicitToExposeDiff_visit_spec__3(lean_box(0), x_20, x_21, x_19, x_10, x_11, x_12, x_13, x_14);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArity_mkProof___lam__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_13 = lean_unsigned_to_nat(0u);
lean_inc(x_1);
x_14 = lean_array_get(x_1, x_6, x_13);
x_15 = lean_box(x_3);
lean_inc(x_7);
x_16 = lean_alloc_closure((void*)(l_Lean_Meta_mkHCongrWithArity_mkProof___lam__1___boxed), 14, 7);
lean_closure_set(x_16, 0, x_1);
lean_closure_set(x_16, 1, x_13);
lean_closure_set(x_16, 2, x_7);
lean_closure_set(x_16, 3, x_14);
lean_closure_set(x_16, 4, x_2);
lean_closure_set(x_16, 5, x_15);
lean_closure_set(x_16, 6, x_4);
x_17 = lean_box(1);
x_18 = lean_unbox(x_17);
x_19 = l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_arrowDomainsN_spec__6(lean_box(0), x_7, x_5, x_16, x_18, x_8, x_9, x_10, x_11, x_12);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArity_mkProof(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_mk_string_unchecked("Eq", 2, 2);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_unsigned_to_nat(3u);
x_10 = l_Lean_Expr_isAppOfArity(x_1, x_8, x_9);
lean_dec(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_mk_string_unchecked("HEq", 3, 3);
x_12 = l_Lean_Name_mkStr1(x_11);
x_13 = lean_unsigned_to_nat(4u);
x_14 = l_Lean_Expr_isAppOfArity(x_1, x_12, x_13);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_15 = l_Lean_instInhabitedExpr;
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_box(x_14);
lean_inc(x_17);
x_19 = lean_alloc_closure((void*)(l_Lean_Meta_mkHCongrWithArity_mkProof___lam__2___boxed), 12, 5);
lean_closure_set(x_19, 0, x_15);
lean_closure_set(x_19, 1, x_16);
lean_closure_set(x_19, 2, x_18);
lean_closure_set(x_19, 3, x_9);
lean_closure_set(x_19, 4, x_17);
x_20 = lean_box(1);
x_21 = lean_unbox(x_20);
x_22 = l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_arrowDomainsN_spec__6(lean_box(0), x_1, x_17, x_19, x_21, x_2, x_3, x_4, x_5, x_6);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = l_Lean_Expr_appFn_x21(x_1);
lean_dec(x_1);
x_24 = l_Lean_Expr_appFn_x21(x_23);
lean_dec(x_23);
x_25 = l_Lean_Expr_appArg_x21(x_24);
lean_dec(x_24);
x_26 = l_Lean_Meta_mkHEqRefl(x_25, x_2, x_3, x_4, x_5, x_6);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = l_Lean_Expr_appFn_x21(x_1);
lean_dec(x_1);
x_28 = l_Lean_Expr_appArg_x21(x_27);
lean_dec(x_27);
x_29 = l_Lean_Meta_mkEqRefl(x_28, x_2, x_3, x_4, x_5, x_6);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArity_mkProof___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_5);
lean_dec(x_5);
x_15 = l_Lean_Meta_mkHCongrWithArity_mkProof___lam__0(x_1, x_2, x_3, x_4, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArity_mkProof___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_6);
lean_dec(x_6);
x_16 = l_Lean_Meta_mkHCongrWithArity_mkProof___lam__1(x_1, x_2, x_3, x_4, x_5, x_15, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArity_mkProof___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_3);
lean_dec(x_3);
x_14 = l_Lean_Meta_mkHCongrWithArity_mkProof___lam__2(x_1, x_2, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_6);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkHCongrWithArity_spec__0___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
lean_dec(x_4);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 2);
lean_inc(x_13);
x_14 = lean_nat_dec_lt(x_12, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_13);
lean_dec(x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_11);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_8);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_5);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_18 = lean_ctor_get(x_10, 0);
lean_inc(x_18);
lean_dec(x_10);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_12, x_19);
lean_inc(x_18);
x_21 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set(x_21, 2, x_13);
x_22 = lean_ctor_get(x_8, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_8, 2);
lean_inc(x_23);
x_24 = lean_nat_dec_lt(x_22, x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_18);
lean_dec(x_12);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_21);
lean_ctor_set(x_25, 1, x_11);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_8);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_5);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; size_t x_39; size_t x_40; 
x_28 = lean_array_uget(x_1, x_3);
x_29 = lean_array_fget(x_18, x_12);
lean_dec(x_12);
lean_dec(x_18);
x_30 = lean_ctor_get(x_8, 0);
lean_inc(x_30);
lean_dec(x_8);
x_31 = lean_array_fget(x_30, x_22);
x_32 = lean_nat_add(x_22, x_19);
lean_dec(x_22);
x_33 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_33, 2, x_23);
x_34 = lean_array_push(x_11, x_28);
x_35 = lean_array_push(x_34, x_31);
x_36 = lean_array_push(x_35, x_29);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_21);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_33);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_usize_of_nat(x_19);
x_40 = lean_usize_add(x_3, x_39);
x_3 = x_40;
x_4 = x_38;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkHCongrWithArity_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkHCongrWithArity_spec__0___redArg(x_1, x_2, x_3, x_4, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArity___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_mk_empty_array_with_capacity(x_13);
x_15 = lean_array_get_size(x_1);
lean_inc(x_1);
x_16 = l_Array_toSubarray___redArg(x_1, x_13, x_15);
x_17 = lean_array_get_size(x_6);
x_18 = l_Array_toSubarray___redArg(x_6, x_13, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_14);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_16);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_array_size(x_2);
x_22 = lean_usize_of_nat(x_13);
x_23 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkHCongrWithArity_spec__0___redArg(x_2, x_21, x_22, x_20, x_12);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
lean_inc(x_3);
x_28 = l_Lean_mkAppN(x_3, x_2);
x_29 = l_Lean_mkAppN(x_3, x_1);
lean_dec(x_1);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_30 = l_Lean_Meta_mkHEq(x_28, x_29, x_8, x_9, x_10, x_11, x_26);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_box(1);
x_34 = lean_unbox(x_33);
x_35 = l_Lean_Meta_mkForallFVars(x_27, x_31, x_4, x_5, x_34, x_8, x_9, x_10, x_11, x_32);
lean_dec(x_27);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
lean_inc(x_36);
x_38 = l_Lean_Meta_mkHCongrWithArity_mkProof(x_36, x_8, x_9, x_10, x_11, x_37);
if (lean_obj_tag(x_38) == 0)
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_38, 0);
x_41 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_41, 0, x_36);
lean_ctor_set(x_41, 1, x_40);
lean_ctor_set(x_41, 2, x_7);
lean_ctor_set(x_38, 0, x_41);
return x_38;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_38, 0);
x_43 = lean_ctor_get(x_38, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_38);
x_44 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_44, 0, x_36);
lean_ctor_set(x_44, 1, x_42);
lean_ctor_set(x_44, 2, x_7);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
else
{
uint8_t x_46; 
lean_dec(x_36);
lean_dec(x_7);
x_46 = !lean_is_exclusive(x_38);
if (x_46 == 0)
{
return x_38;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_38, 0);
x_48 = lean_ctor_get(x_38, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_38);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_50 = !lean_is_exclusive(x_35);
if (x_50 == 0)
{
return x_35;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_35, 0);
x_52 = lean_ctor_get(x_35, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_35);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_27);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_54 = !lean_is_exclusive(x_30);
if (x_54 == 0)
{
return x_30;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_30, 0);
x_56 = lean_ctor_get(x_30, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_30);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArity___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_array_get_size(x_1);
x_12 = lean_nat_dec_eq(x_11, x_2);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_4);
lean_dec(x_1);
x_13 = lean_mk_string_unchecked("failed to generate `hcongr` theorem: expected ", 46, 46);
x_14 = l_Lean_stringToMessageData(x_13);
lean_dec(x_13);
x_15 = l___private_Init_Data_Repr_0__Nat_reprFast(x_2);
x_16 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = l_Lean_MessageData_ofFormat(x_16);
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_14);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_mk_string_unchecked(" arguments, but got ", 20, 20);
x_20 = l_Lean_stringToMessageData(x_19);
lean_dec(x_19);
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
x_22 = l___private_Init_Data_Repr_0__Nat_reprFast(x_11);
x_23 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = l_Lean_MessageData_ofFormat(x_23);
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_21);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_mk_string_unchecked(" for", 4, 4);
x_27 = l_Lean_stringToMessageData(x_26);
lean_dec(x_26);
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_indentExpr(x_3);
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_mk_string_unchecked("", 0, 0);
x_32 = l_Lean_stringToMessageData(x_31);
lean_dec(x_31);
x_33 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_32);
x_34 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_33, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_11);
lean_dec(x_2);
x_35 = lean_ctor_get(x_6, 2);
lean_inc(x_35);
x_36 = l_Lean_Meta_getLocalInstances___redArg(x_6, x_10);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_addPrimeToFVarUserNames(x_4, x_35);
x_40 = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_setBinderInfosD(x_4, x_39);
x_41 = lean_box(0);
x_42 = lean_box(x_12);
lean_inc(x_1);
lean_inc(x_4);
x_43 = lean_alloc_closure((void*)(l_Lean_Meta_mkHCongrWithArity___lam__0___boxed), 12, 5);
lean_closure_set(x_43, 0, x_4);
lean_closure_set(x_43, 1, x_1);
lean_closure_set(x_43, 2, x_3);
lean_closure_set(x_43, 3, x_41);
lean_closure_set(x_43, 4, x_42);
x_44 = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_setBinderInfosD(x_1, x_40);
x_45 = lean_alloc_closure((void*)(l_Lean_Meta_mkHCongrWithArity_withNewEqs), 9, 4);
lean_closure_set(x_45, 0, lean_box(0));
lean_closure_set(x_45, 1, x_1);
lean_closure_set(x_45, 2, x_4);
lean_closure_set(x_45, 3, x_43);
x_46 = l_Lean_Meta_withLCtx___at_____private_Lean_Meta_Basic_0__Lean_Meta_mkLevelErrorMessageCore_spec__1(lean_box(0), x_44, x_37, x_45, x_6, x_7, x_8, x_9, x_38);
lean_dec(x_6);
return x_46;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArity___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_mkHCongrWithArity___lam__1___boxed), 10, 3);
lean_closure_set(x_12, 0, x_5);
lean_closure_set(x_12, 1, x_1);
lean_closure_set(x_12, 2, x_2);
x_13 = lean_box(1);
x_14 = lean_unbox(x_13);
x_15 = l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_arrowDomainsN_spec__6(lean_box(0), x_3, x_4, x_12, x_14, x_7, x_8, x_9, x_10, x_11);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArity(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_8 = lean_infer_type(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_2);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_2);
lean_inc(x_11);
lean_inc(x_9);
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_mkHCongrWithArity___lam__2___boxed), 11, 4);
lean_closure_set(x_12, 0, x_2);
lean_closure_set(x_12, 1, x_1);
lean_closure_set(x_12, 2, x_9);
lean_closure_set(x_12, 3, x_11);
x_13 = lean_box(1);
x_14 = lean_unbox(x_13);
x_15 = l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_arrowDomainsN_spec__6(lean_box(0), x_9, x_11, x_12, x_14, x_3, x_4, x_5, x_6, x_10);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_8);
if (x_16 == 0)
{
return x_8;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_8, 0);
x_18 = lean_ctor_get(x_8, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_8);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkHCongrWithArity_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkHCongrWithArity_spec__0___redArg(x_1, x_6, x_7, x_4, x_5);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkHCongrWithArity_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkHCongrWithArity_spec__0(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArity___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_unbox(x_4);
lean_dec(x_4);
x_14 = lean_unbox(x_5);
lean_dec(x_5);
x_15 = l_Lean_Meta_mkHCongrWithArity___lam__0(x_1, x_2, x_3, x_13, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArity___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_mkHCongrWithArity___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArity___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_mkHCongrWithArity___lam__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_7 = l_Lean_Meta_getFunInfo(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Meta_FunInfo_getArity(x_8);
lean_dec(x_8);
x_11 = l_Lean_Meta_mkHCongrWithArity(x_1, x_10, x_2, x_3, x_4, x_5, x_9);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = !lean_is_exclusive(x_7);
if (x_12 == 0)
{
return x_7;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_7, 0);
x_14 = lean_ctor_get(x_7, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_7);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_3, 1);
x_20 = lean_nat_dec_lt(x_5, x_19);
if (x_20 == 0)
{
lean_dec(x_5);
return x_4;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_ctor_get(x_2, 0);
x_22 = lean_array_fget(x_21, x_5);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec(x_22);
x_24 = l_Array_contains___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__3(x_23, x_1);
lean_dec(x_23);
if (x_24 == 0)
{
x_6 = x_4;
goto block_10;
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; 
x_25 = lean_box(0);
x_26 = lean_array_get(x_25, x_4, x_5);
x_27 = lean_unbox(x_26);
lean_dec(x_26);
x_28 = lean_box(x_27);
if (lean_obj_tag(x_28) == 2)
{
if (x_24 == 0)
{
goto block_18;
}
else
{
lean_dec(x_5);
goto block_13;
}
}
else
{
lean_dec(x_28);
goto block_18;
}
}
}
block_10:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_3, 2);
x_8 = lean_nat_add(x_5, x_7);
lean_dec(x_5);
x_4 = x_6;
x_5 = x_8;
goto _start;
}
block_13:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
x_12 = lean_array_set(x_4, x_1, x_11);
return x_12;
}
block_18:
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_14 = lean_box(0);
x_15 = lean_array_get(x_14, x_4, x_5);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
x_17 = lean_box(x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_dec(x_5);
goto block_13;
}
else
{
lean_dec(x_17);
x_6 = x_4;
goto block_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_3, 1);
x_20 = lean_nat_dec_lt(x_5, x_19);
if (x_20 == 0)
{
return x_4;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_ctor_get(x_2, 0);
x_22 = lean_array_fget(x_21, x_5);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec(x_22);
x_24 = l_Array_contains___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__3(x_23, x_1);
lean_dec(x_23);
if (x_24 == 0)
{
x_6 = x_4;
goto block_10;
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; 
x_25 = lean_box(0);
x_26 = lean_array_get(x_25, x_4, x_5);
x_27 = lean_unbox(x_26);
lean_dec(x_26);
x_28 = lean_box(x_27);
if (lean_obj_tag(x_28) == 2)
{
if (x_24 == 0)
{
goto block_18;
}
else
{
goto block_13;
}
}
else
{
lean_dec(x_28);
goto block_18;
}
}
}
block_10:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_3, 2);
x_8 = lean_nat_add(x_5, x_7);
x_9 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0_spec__0___redArg(x_1, x_2, x_3, x_6, x_8);
return x_9;
}
block_13:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
x_12 = lean_array_set(x_4, x_1, x_11);
return x_12;
}
block_18:
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_14 = lean_box(0);
x_15 = lean_array_get(x_14, x_4, x_5);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
x_17 = lean_box(x_16);
if (lean_obj_tag(x_17) == 0)
{
goto block_13;
}
else
{
lean_dec(x_17);
x_6 = x_4;
goto block_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0___redArg(x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__2_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_nat_dec_lt(x_4, x_5);
if (x_6 == 0)
{
lean_dec(x_4);
return x_3;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_array_get_size(x_7);
x_10 = lean_nat_add(x_4, x_8);
lean_inc(x_10);
x_11 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
lean_ctor_set(x_11, 2, x_8);
x_12 = l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0___redArg(x_4, x_1, x_11, x_3, x_10);
lean_dec(x_10);
lean_dec(x_11);
x_13 = lean_ctor_get(x_2, 2);
x_14 = lean_nat_add(x_4, x_13);
lean_dec(x_4);
x_3 = x_12;
x_4 = x_14;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__2_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__2_spec__2___redArg(x_1, x_2, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_nat_dec_lt(x_4, x_5);
if (x_6 == 0)
{
return x_3;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_array_get_size(x_7);
x_10 = lean_nat_add(x_4, x_8);
lean_inc(x_10);
x_11 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
lean_ctor_set(x_11, 2, x_8);
x_12 = l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0___redArg(x_4, x_1, x_11, x_3, x_10);
lean_dec(x_10);
lean_dec(x_11);
x_13 = lean_ctor_get(x_2, 2);
x_14 = lean_nat_add(x_4, x_13);
x_15 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__2_spec__2___redArg(x_1, x_2, x_12, x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__2___redArg(x_1, x_2, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_array_get_size(x_4);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_5);
lean_ctor_set(x_7, 2, x_6);
x_8 = l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__2___redArg(x_1, x_7, x_2, x_3);
lean_dec(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__2_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__2_spec__2___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__2_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__2_spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__2___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_go_spec__0___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_go_spec__0___redArg___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l___private_Lean_Expr_0__Lean_beqFVarId____x40_Lean_Expr___hyg_1672_(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_go_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_27; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_33 = lean_alloc_closure((void*)(l_Lean_exprDependsOn___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_go_spec__0___redArg___lam__0___boxed), 1, 0);
x_34 = lean_alloc_closure((void*)(l_Lean_exprDependsOn___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_go_spec__0___redArg___lam__1___boxed), 2, 1);
lean_closure_set(x_34, 0, x_2);
x_35 = lean_ctor_get(x_7, 0);
lean_inc(x_35);
lean_dec(x_7);
x_36 = lean_unsigned_to_nat(8u);
x_37 = lean_unsigned_to_nat(0u);
x_38 = lean_unsigned_to_nat(2u);
x_39 = lean_nat_shiftl(x_36, x_38);
x_40 = lean_unsigned_to_nat(3u);
x_41 = lean_nat_div(x_39, x_40);
lean_dec(x_39);
x_42 = l_Nat_nextPowerOfTwo(x_41);
lean_dec(x_41);
x_43 = lean_box(0);
x_44 = lean_mk_array(x_42, x_43);
lean_ctor_set(x_5, 1, x_44);
lean_ctor_set(x_5, 0, x_37);
lean_inc(x_35);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_5);
lean_ctor_set(x_45, 1, x_35);
x_46 = l_Lean_Expr_hasFVar(x_1);
if (x_46 == 0)
{
uint8_t x_47; 
x_47 = l_Lean_Expr_hasMVar(x_1);
if (x_47 == 0)
{
lean_dec(x_45);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_1);
x_9 = x_47;
x_10 = x_35;
goto block_26;
}
else
{
lean_object* x_48; 
lean_dec(x_35);
x_48 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_34, x_33, x_1, x_45);
x_27 = x_48;
goto block_32;
}
}
else
{
lean_object* x_49; 
lean_dec(x_35);
x_49 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_34, x_33, x_1, x_45);
x_27 = x_49;
goto block_32;
}
block_26:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_11 = lean_st_ref_take(x_3, x_8);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 2);
lean_inc(x_15);
x_16 = lean_ctor_get(x_12, 3);
lean_inc(x_16);
x_17 = lean_ctor_get(x_12, 4);
lean_inc(x_17);
lean_dec(x_12);
x_18 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_18, 0, x_10);
lean_ctor_set(x_18, 1, x_14);
lean_ctor_set(x_18, 2, x_15);
lean_ctor_set(x_18, 3, x_16);
lean_ctor_set(x_18, 4, x_17);
x_19 = lean_st_ref_set(x_3, x_18, x_13);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
x_22 = lean_box(x_9);
lean_ctor_set(x_19, 0, x_22);
return x_19;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_dec(x_19);
x_24 = lean_box(x_9);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
block_32:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_unbox(x_29);
lean_dec(x_29);
x_9 = x_31;
x_10 = x_30;
goto block_26;
}
}
else
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_68; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_50 = lean_ctor_get(x_5, 0);
x_51 = lean_ctor_get(x_5, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_5);
x_74 = lean_alloc_closure((void*)(l_Lean_exprDependsOn___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_go_spec__0___redArg___lam__0___boxed), 1, 0);
x_75 = lean_alloc_closure((void*)(l_Lean_exprDependsOn___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_go_spec__0___redArg___lam__1___boxed), 2, 1);
lean_closure_set(x_75, 0, x_2);
x_76 = lean_ctor_get(x_50, 0);
lean_inc(x_76);
lean_dec(x_50);
x_77 = lean_unsigned_to_nat(8u);
x_78 = lean_unsigned_to_nat(0u);
x_79 = lean_unsigned_to_nat(2u);
x_80 = lean_nat_shiftl(x_77, x_79);
x_81 = lean_unsigned_to_nat(3u);
x_82 = lean_nat_div(x_80, x_81);
lean_dec(x_80);
x_83 = l_Nat_nextPowerOfTwo(x_82);
lean_dec(x_82);
x_84 = lean_box(0);
x_85 = lean_mk_array(x_83, x_84);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_78);
lean_ctor_set(x_86, 1, x_85);
lean_inc(x_76);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_76);
x_88 = l_Lean_Expr_hasFVar(x_1);
if (x_88 == 0)
{
uint8_t x_89; 
x_89 = l_Lean_Expr_hasMVar(x_1);
if (x_89 == 0)
{
lean_dec(x_87);
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_1);
x_52 = x_89;
x_53 = x_76;
goto block_67;
}
else
{
lean_object* x_90; 
lean_dec(x_76);
x_90 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_75, x_74, x_1, x_87);
x_68 = x_90;
goto block_73;
}
}
else
{
lean_object* x_91; 
lean_dec(x_76);
x_91 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_75, x_74, x_1, x_87);
x_68 = x_91;
goto block_73;
}
block_67:
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_54 = lean_st_ref_take(x_3, x_51);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
x_58 = lean_ctor_get(x_55, 2);
lean_inc(x_58);
x_59 = lean_ctor_get(x_55, 3);
lean_inc(x_59);
x_60 = lean_ctor_get(x_55, 4);
lean_inc(x_60);
lean_dec(x_55);
x_61 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_61, 0, x_53);
lean_ctor_set(x_61, 1, x_57);
lean_ctor_set(x_61, 2, x_58);
lean_ctor_set(x_61, 3, x_59);
lean_ctor_set(x_61, 4, x_60);
x_62 = lean_st_ref_set(x_3, x_61, x_56);
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_64 = x_62;
} else {
 lean_dec_ref(x_62);
 x_64 = lean_box(0);
}
x_65 = lean_box(x_52);
if (lean_is_scalar(x_64)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_64;
}
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_63);
return x_66;
}
block_73:
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 0);
lean_inc(x_70);
lean_dec(x_68);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = lean_unbox(x_70);
lean_dec(x_70);
x_52 = x_72;
x_53 = x_71;
goto block_67;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_go_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_exprDependsOn___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_go_spec__0___redArg(x_1, x_2, x_4, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_array_get_size(x_2);
x_12 = lean_nat_dec_lt(x_4, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_box(0);
x_15 = l_instInhabitedNat;
x_16 = lean_array_get(x_15, x_2, x_4);
x_17 = lean_array_get(x_14, x_3, x_16);
lean_dec(x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_4, x_18);
lean_dec(x_4);
x_4 = x_19;
goto _start;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_17, 0);
lean_inc(x_21);
lean_dec(x_17);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_21);
x_22 = lean_infer_type(x_21, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_mk_string_unchecked("Eq", 2, 2);
x_26 = l_Lean_Name_mkStr1(x_25);
x_27 = lean_unsigned_to_nat(3u);
x_28 = l_Lean_Expr_isAppOfArity(x_23, x_26, x_27);
lean_dec(x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_29 = lean_mk_string_unchecked("Lean.Meta.CongrTheorems", 23, 23);
x_30 = lean_mk_string_unchecked("_private.Lean.Meta.CongrTheorems.0.Lean.Meta.mkCast.go", 54, 54);
x_31 = lean_unsigned_to_nat(146u);
x_32 = lean_unsigned_to_nat(61u);
x_33 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_34 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_29, x_30, x_31, x_32, x_33);
lean_dec(x_33);
lean_dec(x_30);
lean_dec(x_29);
x_35 = l_panic___at___Lean_Meta_whnfCore_go_spec__1(x_34, x_6, x_7, x_8, x_9, x_24);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_36 = l_Lean_Expr_fvarId_x21(x_21);
lean_inc(x_5);
x_37 = l_Lean_exprDependsOn___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_go_spec__0___redArg(x_5, x_36, x_7, x_24);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = l_Lean_Expr_appFn_x21(x_23);
x_41 = l_Lean_Expr_appArg_x21(x_40);
lean_dec(x_40);
x_42 = l_Lean_Expr_appArg_x21(x_23);
lean_dec(x_23);
x_43 = lean_unbox(x_38);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; uint8_t x_49; uint8_t x_50; lean_object* x_51; 
x_44 = lean_unsigned_to_nat(1u);
x_45 = lean_mk_empty_array_with_capacity(x_44);
lean_inc(x_42);
x_46 = lean_array_push(x_45, x_42);
x_47 = lean_box(1);
x_48 = lean_unbox(x_38);
x_49 = lean_unbox(x_38);
lean_dec(x_38);
x_50 = lean_unbox(x_47);
lean_inc(x_5);
x_51 = l_Lean_Meta_mkLambdaFVars(x_46, x_5, x_48, x_28, x_49, x_50, x_6, x_7, x_8, x_9, x_39);
lean_dec(x_46);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = l_Lean_Expr_replaceFVar(x_5, x_42, x_41);
lean_dec(x_41);
lean_dec(x_5);
x_55 = lean_nat_add(x_4, x_44);
lean_dec(x_4);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_56 = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_go(x_1, x_2, x_3, x_55, x_54, x_6, x_7, x_8, x_9, x_53);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = l_Lean_Meta_mkEqNDRec(x_52, x_57, x_21, x_6, x_7, x_8, x_9, x_58);
return x_59;
}
else
{
lean_dec(x_52);
lean_dec(x_21);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_56;
}
}
else
{
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_21);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_51;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; uint8_t x_67; uint8_t x_68; lean_object* x_69; 
lean_dec(x_38);
x_60 = lean_unsigned_to_nat(2u);
x_61 = lean_mk_empty_array_with_capacity(x_60);
lean_inc(x_42);
x_62 = lean_array_push(x_61, x_42);
lean_inc(x_21);
x_63 = lean_array_push(x_62, x_21);
x_64 = lean_box(0);
x_65 = lean_box(1);
x_66 = lean_unbox(x_64);
x_67 = lean_unbox(x_64);
x_68 = lean_unbox(x_65);
lean_inc(x_5);
x_69 = l_Lean_Meta_mkLambdaFVars(x_63, x_5, x_66, x_28, x_67, x_68, x_6, x_7, x_8, x_9, x_39);
lean_dec(x_63);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_41);
x_72 = l_Lean_Meta_mkEqRefl(x_41, x_6, x_7, x_8, x_9, x_71);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = l_Lean_Expr_replaceFVar(x_5, x_42, x_41);
lean_dec(x_41);
lean_dec(x_5);
lean_inc(x_21);
x_76 = l_Lean_Expr_replaceFVar(x_75, x_21, x_73);
lean_dec(x_73);
lean_dec(x_75);
x_77 = lean_unsigned_to_nat(1u);
x_78 = lean_nat_add(x_4, x_77);
lean_dec(x_4);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_79 = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_go(x_1, x_2, x_3, x_78, x_76, x_6, x_7, x_8, x_9, x_74);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
x_82 = l_Lean_Meta_mkEqRec(x_70, x_80, x_21, x_6, x_7, x_8, x_9, x_81);
return x_82;
}
else
{
lean_dec(x_70);
lean_dec(x_21);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_79;
}
}
else
{
lean_dec(x_70);
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_21);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_72;
}
}
else
{
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_21);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_69;
}
}
}
}
else
{
lean_dec(x_21);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_22;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_go_spec__0___redArg___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_exprDependsOn___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_go_spec__0___redArg___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_go_spec__0___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_exprDependsOn___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_go_spec__0___redArg___lam__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_go_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_exprDependsOn___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_go_spec__0___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_go_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_exprDependsOn___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_go_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_go(x_1, x_3, x_4, x_10, x_2, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_hasCastLike_spec__0(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_box(1);
x_6 = lean_array_uget(x_1, x_2);
x_7 = lean_unbox(x_6);
lean_dec(x_6);
x_8 = lean_box(x_7);
if (lean_obj_tag(x_8) == 3)
{
uint8_t x_9; 
x_9 = lean_unbox(x_5);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_8);
x_10 = lean_box(x_7);
if (lean_obj_tag(x_10) == 5)
{
uint8_t x_11; 
x_11 = lean_unbox(x_5);
return x_11;
}
else
{
lean_dec(x_10);
if (x_4 == 0)
{
lean_object* x_12; size_t x_13; size_t x_14; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_usize_of_nat(x_12);
x_14 = lean_usize_add(x_2, x_13);
x_2 = x_14;
goto _start;
}
else
{
uint8_t x_16; 
x_16 = lean_unbox(x_5);
return x_16;
}
}
}
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_box(0);
x_18 = lean_unbox(x_17);
return x_18;
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_hasCastLike(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_array_get_size(x_1);
x_4 = lean_nat_dec_lt(x_2, x_3);
if (x_4 == 0)
{
lean_dec(x_3);
return x_4;
}
else
{
if (x_4 == 0)
{
lean_dec(x_3);
return x_4;
}
else
{
size_t x_5; size_t x_6; uint8_t x_7; 
x_5 = lean_usize_of_nat(x_2);
x_6 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_7 = l_Array_anyMUnsafe_any___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_hasCastLike_spec__0(x_1, x_5, x_6);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_hasCastLike_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Array_anyMUnsafe_any___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_hasCastLike_spec__0(x_1, x_4, x_5);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_hasCastLike___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_hasCastLike(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_array_get(x_1, x_3, x_10);
x_12 = lean_apply_7(x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_8 = l_Lean_instInhabitedExpr;
x_9 = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg___lam__0___boxed), 9, 2);
lean_closure_set(x_9, 0, x_8);
lean_closure_set(x_9, 1, x_2);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_box(1);
x_13 = lean_unbox(x_12);
x_14 = l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_arrowDomainsN_spec__6(lean_box(0), x_1, x_11, x_9, x_13, x_3, x_4, x_5, x_6, x_7);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = l_Lean_Meta_instInhabitedParamInfo;
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_usize_dec_lt(x_6, x_5);
if (x_10 == 0)
{
return x_7;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
lean_dec(x_7);
x_11 = lean_box(0);
x_12 = lean_array_uget(x_4, x_6);
x_13 = lean_box(0);
x_14 = lean_array_get(x_13, x_1, x_12);
lean_dec(x_12);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
x_16 = lean_box(x_15);
if (lean_obj_tag(x_16) == 2)
{
lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_array_get(x_8, x_9, x_3);
x_18 = lean_ctor_get_uint8(x_17, sizeof(void*)*1 + 3);
lean_dec(x_17);
x_19 = lean_box(x_18);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_11);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; 
lean_dec(x_16);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_11);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_usize_of_nat(x_24);
x_26 = lean_usize_add(x_6, x_25);
x_6 = x_26;
x_7 = x_23;
goto _start;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = l_Lean_Meta_instInhabitedParamInfo;
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_array_get(x_4, x_5, x_3);
x_7 = lean_ctor_get_uint8(x_6, sizeof(void*)*1 + 3);
if (x_7 == 0)
{
lean_dec(x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; lean_object* x_13; size_t x_14; lean_object* x_15; lean_object* x_16; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_box(0);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_array_size(x_8);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_usize_of_nat(x_13);
x_15 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst_spec__0(x_2, x_1, x_3, x_8, x_12, x_14, x_11);
lean_dec(x_8);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_box(0);
x_18 = lean_unbox(x_17);
return x_18;
}
else
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_16, 0);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_unbox(x_19);
lean_dec(x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst_spec__0(x_1, x_2, x_3, x_4, x_8, x_9, x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_5, 1);
x_19 = lean_nat_dec_lt(x_7, x_18);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_6);
lean_ctor_set(x_20, 1, x_11);
return x_20;
}
else
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_1, 3);
lean_inc(x_21);
x_22 = lean_nat_dec_lt(x_7, x_21);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_array_fget(x_2, x_7);
x_24 = l_Lean_Expr_fvarId_x21(x_23);
lean_dec(x_23);
lean_inc(x_8);
x_25 = l_Lean_FVarId_getDecl___redArg(x_24, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_32; lean_object* x_33; lean_object* x_36; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_32 = lean_ctor_get(x_1, 1);
lean_inc(x_32);
x_36 = lean_ctor_get(x_26, 2);
lean_inc(x_36);
lean_dec(x_26);
x_33 = x_36;
goto block_35;
block_31:
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_box(x_28);
x_30 = lean_array_push(x_6, x_29);
x_12 = x_30;
x_13 = x_27;
goto block_17;
}
block_35:
{
lean_object* x_34; 
lean_inc(x_3);
x_34 = l_Lean_isSubobjectField_x3f(x_3, x_32, x_33);
if (lean_obj_tag(x_34) == 0)
{
x_28 = x_22;
goto block_31;
}
else
{
lean_dec(x_34);
x_28 = x_4;
goto block_31;
}
}
}
else
{
uint8_t x_37; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_25);
if (x_37 == 0)
{
return x_25;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_25, 0);
x_39 = lean_ctor_get(x_25, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_25);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_box(0);
x_42 = lean_array_push(x_6, x_41);
x_12 = x_42;
x_13 = x_11;
goto block_17;
}
}
block_17:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_5, 2);
x_15 = lean_nat_add(x_7, x_14);
lean_dec(x_7);
x_6 = x_12;
x_7 = x_15;
x_11 = x_13;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_10, x_12, x_13, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_10 = lean_st_ref_get(x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_mk_empty_array_with_capacity(x_14);
x_16 = lean_array_get_size(x_3);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_18, 0, x_14);
lean_ctor_set(x_18, 1, x_16);
lean_ctor_set(x_18, 2, x_17);
x_19 = l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0___redArg(x_1, x_3, x_13, x_2, x_18, x_15, x_14, x_5, x_7, x_8, x_12);
lean_dec(x_18);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_19, 0, x_22);
return x_19;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_19, 0);
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_19);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_23);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_19);
if (x_27 == 0)
{
return x_19;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_19, 0);
x_29 = lean_ctor_get(x_19, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_19);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 4)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = l_Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0(x_7, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 6)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_st_ref_get(x_5, x_10);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
x_18 = lean_is_class(x_16, x_17);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_19 = lean_box(0);
lean_ctor_set(x_12, 0, x_19);
return x_12;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_free_object(x_12);
x_20 = lean_box(x_18);
lean_inc(x_11);
x_21 = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f___lam__0___boxed), 9, 2);
lean_closure_set(x_21, 0, x_11);
lean_closure_set(x_21, 1, x_20);
x_22 = lean_ctor_get(x_11, 0);
lean_inc(x_22);
lean_dec(x_11);
x_23 = lean_ctor_get(x_22, 2);
lean_inc(x_23);
lean_dec(x_22);
x_24 = l_Lean_Meta_forallTelescopeReducing___at___Lean_Meta_getParamNames_spec__1(lean_box(0), x_23, x_21, x_18, x_2, x_3, x_4, x_5, x_15);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_25 = lean_ctor_get(x_12, 0);
x_26 = lean_ctor_get(x_12, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_12);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_ctor_get(x_11, 1);
lean_inc(x_28);
x_29 = lean_is_class(x_27, x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_26);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_box(x_29);
lean_inc(x_11);
x_33 = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f___lam__0___boxed), 9, 2);
lean_closure_set(x_33, 0, x_11);
lean_closure_set(x_33, 1, x_32);
x_34 = lean_ctor_get(x_11, 0);
lean_inc(x_34);
lean_dec(x_11);
x_35 = lean_ctor_get(x_34, 2);
lean_inc(x_35);
lean_dec(x_34);
x_36 = l_Lean_Meta_forallTelescopeReducing___at___Lean_Meta_getParamNames_spec__1(lean_box(0), x_35, x_33, x_29, x_2, x_3, x_4, x_5, x_26);
return x_36;
}
}
}
else
{
uint8_t x_37; 
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_37 = !lean_is_exclusive(x_8);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_8, 0);
lean_dec(x_38);
x_39 = lean_box(0);
lean_ctor_set(x_8, 0, x_39);
return x_8;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_8, 1);
lean_inc(x_40);
lean_dec(x_8);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_43 = !lean_is_exclusive(x_8);
if (x_43 == 0)
{
return x_8;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_8, 0);
x_45 = lean_ctor_get(x_8, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_8);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_6);
return x_48;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_4);
lean_dec(x_4);
x_13 = l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0___redArg(x_1, x_2, x_3, x_12, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_4);
lean_dec(x_4);
x_16 = l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0(x_1, x_2, x_3, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_2);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
lean_dec(x_2);
x_11 = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f___lam__0(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Meta_getCongrSimpKinds_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_13; lean_object* x_14; lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_3, 1);
x_22 = lean_nat_dec_lt(x_5, x_21);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_5);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_4);
lean_ctor_set(x_23, 1, x_6);
return x_23;
}
else
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_1, 1);
x_25 = l_Array_contains___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__3(x_24, x_5);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_1, 0);
x_27 = lean_array_fget(x_26, x_5);
x_28 = lean_ctor_get_uint8(x_27, sizeof(void*)*1 + 2);
if (x_28 == 0)
{
uint8_t x_29; 
x_29 = l_Lean_Meta_ParamInfo_isInstImplicit(x_27);
lean_dec(x_27);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_box(2);
x_31 = lean_array_push(x_4, x_30);
x_7 = x_31;
x_8 = x_6;
goto block_12;
}
else
{
if (lean_obj_tag(x_2) == 0)
{
x_13 = x_4;
x_14 = x_6;
goto block_20;
}
else
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = lean_ctor_get(x_2, 0);
x_33 = lean_array_get_size(x_32);
x_34 = lean_nat_dec_lt(x_5, x_33);
lean_dec(x_33);
if (x_34 == 0)
{
x_13 = x_4;
x_14 = x_6;
goto block_20;
}
else
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_array_fget(x_32, x_5);
x_36 = lean_unbox(x_35);
lean_dec(x_35);
if (x_36 == 0)
{
x_13 = x_4;
x_14 = x_6;
goto block_20;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_box(2);
x_38 = lean_array_push(x_4, x_37);
x_7 = x_38;
x_8 = x_6;
goto block_12;
}
}
}
}
}
else
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_27);
x_39 = lean_box(3);
x_40 = lean_array_push(x_4, x_39);
x_7 = x_40;
x_8 = x_6;
goto block_12;
}
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_box(0);
x_42 = lean_array_push(x_4, x_41);
x_7 = x_42;
x_8 = x_6;
goto block_12;
}
}
block_12:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_3, 2);
x_10 = lean_nat_add(x_5, x_9);
lean_dec(x_5);
x_4 = x_7;
x_5 = x_10;
x_6 = x_8;
goto _start;
}
block_20:
{
uint8_t x_15; 
x_15 = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst(x_1, x_13, x_5);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_box(0);
x_17 = lean_array_push(x_13, x_16);
x_7 = x_17;
x_8 = x_14;
goto block_12;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_box(5);
x_19 = lean_array_push(x_13, x_18);
x_7 = x_19;
x_8 = x_14;
goto block_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Meta_getCongrSimpKinds_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Meta_getCongrSimpKinds_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_getCongrSimpKinds_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_17; lean_object* x_18; lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_3, 1);
x_26 = lean_nat_dec_lt(x_5, x_25);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_4);
lean_ctor_set(x_27, 1, x_10);
return x_27;
}
else
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_1, 1);
x_29 = l_Array_contains___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__3(x_28, x_5);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = lean_ctor_get(x_1, 0);
x_31 = lean_array_fget(x_30, x_5);
x_32 = lean_ctor_get_uint8(x_31, sizeof(void*)*1 + 2);
if (x_32 == 0)
{
uint8_t x_33; 
x_33 = l_Lean_Meta_ParamInfo_isInstImplicit(x_31);
lean_dec(x_31);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_box(2);
x_35 = lean_array_push(x_4, x_34);
x_11 = x_35;
x_12 = x_10;
goto block_16;
}
else
{
if (lean_obj_tag(x_2) == 0)
{
x_17 = x_4;
x_18 = x_10;
goto block_24;
}
else
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_36 = lean_ctor_get(x_2, 0);
x_37 = lean_array_get_size(x_36);
x_38 = lean_nat_dec_lt(x_5, x_37);
lean_dec(x_37);
if (x_38 == 0)
{
x_17 = x_4;
x_18 = x_10;
goto block_24;
}
else
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_array_fget(x_36, x_5);
x_40 = lean_unbox(x_39);
lean_dec(x_39);
if (x_40 == 0)
{
x_17 = x_4;
x_18 = x_10;
goto block_24;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_box(2);
x_42 = lean_array_push(x_4, x_41);
x_11 = x_42;
x_12 = x_10;
goto block_16;
}
}
}
}
}
else
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_31);
x_43 = lean_box(3);
x_44 = lean_array_push(x_4, x_43);
x_11 = x_44;
x_12 = x_10;
goto block_16;
}
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_box(0);
x_46 = lean_array_push(x_4, x_45);
x_11 = x_46;
x_12 = x_10;
goto block_16;
}
}
block_16:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_3, 2);
x_14 = lean_nat_add(x_5, x_13);
x_15 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Meta_getCongrSimpKinds_spec__0_spec__0___redArg(x_1, x_2, x_3, x_11, x_14, x_12);
return x_15;
}
block_24:
{
uint8_t x_19; 
x_19 = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst(x_1, x_17, x_5);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_box(0);
x_21 = lean_array_push(x_17, x_20);
x_11 = x_21;
x_12 = x_18;
goto block_16;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_box(5);
x_23 = lean_array_push(x_17, x_22);
x_11 = x_23;
x_12 = x_18;
goto block_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_getCongrSimpKinds_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_getCongrSimpKinds_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCongrSimpKinds(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_8 = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_mk_empty_array_with_capacity(x_11);
x_13 = lean_ctor_get(x_2, 0);
x_14 = lean_array_get_size(x_13);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_14);
lean_ctor_set(x_16, 2, x_15);
x_17 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_getCongrSimpKinds_spec__0___redArg(x_2, x_9, x_16, x_12, x_11, x_3, x_4, x_5, x_6, x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_16);
lean_dec(x_9);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies(x_2, x_19);
lean_ctor_set(x_17, 0, x_20);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_17, 0);
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_17);
x_23 = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies(x_2, x_21);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_25 = !lean_is_exclusive(x_8);
if (x_25 == 0)
{
return x_8;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_8, 0);
x_27 = lean_ctor_get(x_8, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_8);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Meta_getCongrSimpKinds_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Meta_getCongrSimpKinds_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Meta_getCongrSimpKinds_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Meta_getCongrSimpKinds_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_getCongrSimpKinds_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_getCongrSimpKinds_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_getCongrSimpKinds_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_getCongrSimpKinds_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCongrSimpKinds___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_getCongrSimpKinds(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Meta_getCongrSimpKindsForArgZero_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_2, 1);
x_13 = lean_nat_dec_lt(x_4, x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_4);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_3);
lean_ctor_set(x_14, 1, x_5);
return x_14;
}
else
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_1, 1);
x_16 = l_Array_contains___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__3(x_15, x_4);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_dec_eq(x_4, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_1, 0);
x_20 = lean_array_fget(x_19, x_4);
x_21 = lean_ctor_get_uint8(x_20, sizeof(void*)*1 + 2);
if (x_21 == 0)
{
uint8_t x_22; 
x_22 = l_Lean_Meta_ParamInfo_isInstImplicit(x_20);
lean_dec(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_box(0);
x_24 = lean_array_push(x_3, x_23);
x_6 = x_24;
x_7 = x_5;
goto block_11;
}
else
{
uint8_t x_25; 
x_25 = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst(x_1, x_3, x_4);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_box(0);
x_27 = lean_array_push(x_3, x_26);
x_6 = x_27;
x_7 = x_5;
goto block_11;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_box(5);
x_29 = lean_array_push(x_3, x_28);
x_6 = x_29;
x_7 = x_5;
goto block_11;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_20);
x_30 = lean_box(3);
x_31 = lean_array_push(x_3, x_30);
x_6 = x_31;
x_7 = x_5;
goto block_11;
}
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_box(2);
x_33 = lean_array_push(x_3, x_32);
x_6 = x_33;
x_7 = x_5;
goto block_11;
}
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_box(0);
x_35 = lean_array_push(x_3, x_34);
x_6 = x_35;
x_7 = x_5;
goto block_11;
}
}
block_11:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_2, 2);
x_9 = lean_nat_add(x_4, x_8);
lean_dec(x_4);
x_3 = x_6;
x_4 = x_9;
x_5 = x_7;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Meta_getCongrSimpKindsForArgZero_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Meta_getCongrSimpKindsForArgZero_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_getCongrSimpKindsForArgZero_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_2, 1);
x_17 = lean_nat_dec_lt(x_4, x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_3);
lean_ctor_set(x_18, 1, x_9);
return x_18;
}
else
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_1, 1);
x_20 = l_Array_contains___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__3(x_19, x_4);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_nat_dec_eq(x_4, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_1, 0);
x_24 = lean_array_fget(x_23, x_4);
x_25 = lean_ctor_get_uint8(x_24, sizeof(void*)*1 + 2);
if (x_25 == 0)
{
uint8_t x_26; 
x_26 = l_Lean_Meta_ParamInfo_isInstImplicit(x_24);
lean_dec(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_box(0);
x_28 = lean_array_push(x_3, x_27);
x_10 = x_28;
x_11 = x_9;
goto block_15;
}
else
{
uint8_t x_29; 
x_29 = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst(x_1, x_3, x_4);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_box(0);
x_31 = lean_array_push(x_3, x_30);
x_10 = x_31;
x_11 = x_9;
goto block_15;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_box(5);
x_33 = lean_array_push(x_3, x_32);
x_10 = x_33;
x_11 = x_9;
goto block_15;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_24);
x_34 = lean_box(3);
x_35 = lean_array_push(x_3, x_34);
x_10 = x_35;
x_11 = x_9;
goto block_15;
}
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_box(2);
x_37 = lean_array_push(x_3, x_36);
x_10 = x_37;
x_11 = x_9;
goto block_15;
}
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_box(0);
x_39 = lean_array_push(x_3, x_38);
x_10 = x_39;
x_11 = x_9;
goto block_15;
}
}
block_15:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_2, 2);
x_13 = lean_nat_add(x_4, x_12);
x_14 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Meta_getCongrSimpKindsForArgZero_spec__0_spec__0___redArg(x_1, x_2, x_10, x_13, x_11);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_getCongrSimpKindsForArgZero_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_getCongrSimpKindsForArgZero_spec__0___redArg(x_1, x_2, x_3, x_4, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCongrSimpKindsForArgZero(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_mk_empty_array_with_capacity(x_7);
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_array_get_size(x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set(x_12, 1, x_10);
lean_ctor_set(x_12, 2, x_11);
x_13 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_getCongrSimpKindsForArgZero_spec__0___redArg(x_1, x_12, x_8, x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_12);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies(x_1, x_15);
lean_ctor_set(x_13, 0, x_16);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_13, 0);
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_13);
x_19 = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies(x_1, x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Meta_getCongrSimpKindsForArgZero_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Meta_getCongrSimpKindsForArgZero_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Meta_getCongrSimpKindsForArgZero_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Meta_getCongrSimpKindsForArgZero_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_getCongrSimpKindsForArgZero_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_getCongrSimpKindsForArgZero_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_getCongrSimpKindsForArgZero_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_getCongrSimpKindsForArgZero_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCongrSimpKindsForArgZero___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_getCongrSimpKindsForArgZero(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
lean_inc(x_2);
x_16 = lean_array_push(x_1, x_2);
lean_inc(x_9);
x_17 = lean_array_push(x_16, x_9);
x_18 = lean_box(1);
x_19 = lean_unbox(x_18);
x_20 = l_Lean_Meta_mkLambdaFVars(x_17, x_10, x_3, x_4, x_3, x_19, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_17);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_5, x_23);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_25 = l_Lean_Meta_mkCongrSimpCore_x3f_mkProof_go(x_6, x_24, x_7, x_11, x_12, x_13, x_14, x_22);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_9);
x_28 = l_Lean_Meta_mkEqRec(x_21, x_26, x_9, x_11, x_12, x_13, x_14, x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_unsigned_to_nat(3u);
x_32 = lean_mk_empty_array_with_capacity(x_31);
x_33 = lean_array_push(x_32, x_8);
x_34 = lean_array_push(x_33, x_2);
x_35 = lean_array_push(x_34, x_9);
x_36 = lean_unbox(x_18);
x_37 = l_Lean_Meta_mkLambdaFVars(x_35, x_29, x_3, x_4, x_3, x_36, x_11, x_12, x_13, x_14, x_30);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_35);
return x_37;
}
else
{
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
return x_28;
}
}
else
{
lean_dec(x_21);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
return x_25;
}
}
else
{
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__1(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_box(x_2);
x_16 = lean_box(x_3);
x_17 = lean_alloc_closure((void*)(l_Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__0___boxed), 15, 8);
lean_closure_set(x_17, 0, x_1);
lean_closure_set(x_17, 1, x_8);
lean_closure_set(x_17, 2, x_15);
lean_closure_set(x_17, 3, x_16);
lean_closure_set(x_17, 4, x_4);
lean_closure_set(x_17, 5, x_5);
lean_closure_set(x_17, 6, x_6);
lean_closure_set(x_17, 7, x_7);
x_18 = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg(x_9, x_17, x_10, x_11, x_12, x_13, x_14);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__2(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
lean_inc(x_9);
x_16 = lean_array_push(x_1, x_9);
x_17 = lean_box(1);
x_18 = lean_unbox(x_17);
x_19 = l_Lean_Meta_mkLambdaFVars(x_16, x_10, x_2, x_3, x_2, x_18, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_16);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_nat_add(x_4, x_5);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_23 = l_Lean_Meta_mkCongrSimpCore_x3f_mkProof_go(x_6, x_22, x_7, x_11, x_12, x_13, x_14, x_21);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_mk_string_unchecked("Subsingleton", 12, 12);
x_27 = lean_mk_string_unchecked("elim", 4, 4);
x_28 = l_Lean_Name_mkStr2(x_26, x_27);
x_29 = lean_unsigned_to_nat(2u);
x_30 = lean_mk_empty_array_with_capacity(x_29);
x_31 = lean_array_push(x_30, x_8);
x_32 = lean_array_push(x_31, x_9);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_32);
x_33 = l_Lean_Meta_mkAppM(x_28, x_32, x_11, x_12, x_13, x_14, x_25);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_36 = l_Lean_Meta_mkEqNDRec(x_20, x_24, x_34, x_11, x_12, x_13, x_14, x_35);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_unbox(x_17);
x_40 = l_Lean_Meta_mkLambdaFVars(x_32, x_37, x_2, x_3, x_2, x_39, x_11, x_12, x_13, x_14, x_38);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_32);
return x_40;
}
else
{
lean_dec(x_32);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
return x_36;
}
}
else
{
lean_dec(x_32);
lean_dec(x_24);
lean_dec(x_20);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
return x_33;
}
}
else
{
lean_dec(x_20);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
return x_23;
}
}
else
{
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__3(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_20 = lean_box(0);
x_21 = lean_array_get(x_20, x_1, x_2);
x_22 = lean_unbox(x_21);
lean_dec(x_21);
x_23 = lean_box(x_22);
switch (lean_obj_tag(x_23)) {
case 1:
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
goto block_19;
}
case 2:
{
lean_object* x_24; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_5);
x_24 = l_Lean_Meta_mkEqRefl(x_5, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_Expr_bindingBody_x21(x_6);
x_28 = l_Lean_Expr_bindingBody_x21(x_27);
lean_dec(x_27);
x_29 = lean_unsigned_to_nat(2u);
x_30 = lean_mk_empty_array_with_capacity(x_29);
lean_inc(x_30);
x_31 = lean_array_push(x_30, x_25);
lean_inc(x_5);
x_32 = lean_array_push(x_31, x_5);
x_33 = lean_expr_instantiate(x_28, x_32);
lean_dec(x_32);
lean_dec(x_28);
x_34 = lean_box(x_3);
x_35 = lean_box(x_4);
x_36 = lean_alloc_closure((void*)(l_Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__1___boxed), 14, 7);
lean_closure_set(x_36, 0, x_30);
lean_closure_set(x_36, 1, x_34);
lean_closure_set(x_36, 2, x_35);
lean_closure_set(x_36, 3, x_2);
lean_closure_set(x_36, 4, x_1);
lean_closure_set(x_36, 5, x_33);
lean_closure_set(x_36, 6, x_5);
x_37 = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg(x_6, x_36, x_7, x_8, x_9, x_10, x_26);
return x_37;
}
else
{
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_24;
}
}
case 4:
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
goto block_19;
}
case 5:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_38 = l_Lean_Expr_bindingBody_x21(x_6);
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_mk_empty_array_with_capacity(x_39);
lean_inc(x_5);
lean_inc(x_40);
x_41 = lean_array_push(x_40, x_5);
x_42 = lean_expr_instantiate(x_38, x_41);
lean_dec(x_41);
lean_dec(x_38);
x_43 = lean_box(x_3);
x_44 = lean_box(x_4);
x_45 = lean_alloc_closure((void*)(l_Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__2___boxed), 15, 8);
lean_closure_set(x_45, 0, x_40);
lean_closure_set(x_45, 1, x_43);
lean_closure_set(x_45, 2, x_44);
lean_closure_set(x_45, 3, x_2);
lean_closure_set(x_45, 4, x_39);
lean_closure_set(x_45, 5, x_1);
lean_closure_set(x_45, 6, x_42);
lean_closure_set(x_45, 7, x_5);
x_46 = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg(x_6, x_45, x_7, x_8, x_9, x_10, x_11);
return x_46;
}
default: 
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_23);
x_47 = lean_unsigned_to_nat(1u);
x_48 = lean_nat_add(x_2, x_47);
lean_dec(x_2);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_49 = l_Lean_Meta_mkCongrSimpCore_x3f_mkProof_go(x_1, x_48, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = lean_mk_empty_array_with_capacity(x_47);
x_53 = lean_array_push(x_52, x_5);
x_54 = lean_box(1);
x_55 = lean_unbox(x_54);
x_56 = l_Lean_Meta_mkLambdaFVars(x_53, x_50, x_3, x_4, x_3, x_55, x_7, x_8, x_9, x_10, x_51);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_53);
return x_56;
}
else
{
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
return x_49;
}
}
}
block_19:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_mk_string_unchecked("Lean.Meta.CongrTheorems", 23, 23);
x_13 = lean_mk_string_unchecked("Lean.Meta.mkCongrSimpCore\?.mkProof.go", 37, 37);
x_14 = lean_unsigned_to_nat(326u);
x_15 = lean_unsigned_to_nat(34u);
x_16 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_17 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_12, x_13, x_14, x_15, x_16);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_12);
x_18 = l_panic___at___Lean_Meta_whnfCore_go_spec__1(x_17, x_7, x_8, x_9, x_10, x_11);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpCore_x3f_mkProof_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_get_size(x_1);
x_10 = lean_nat_dec_eq(x_2, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_box(1);
x_12 = lean_box(x_10);
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__3___boxed), 11, 4);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_2);
lean_closure_set(x_13, 2, x_12);
lean_closure_set(x_13, 3, x_11);
x_14 = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg(x_3, x_13, x_4, x_5, x_6, x_7, x_8);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_mk_string_unchecked("Eq", 2, 2);
x_16 = l_Lean_Name_mkStr1(x_15);
x_17 = lean_unsigned_to_nat(3u);
x_18 = l_Lean_Expr_isAppOfArity(x_3, x_16, x_17);
lean_dec(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_3);
x_19 = lean_mk_string_unchecked("Lean.Meta.CongrTheorems", 23, 23);
x_20 = lean_mk_string_unchecked("Lean.Meta.mkCongrSimpCore\?.mkProof.go", 37, 37);
x_21 = lean_unsigned_to_nat(321u);
x_22 = lean_unsigned_to_nat(43u);
x_23 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_24 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_19, x_20, x_21, x_22, x_23);
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_19);
x_25 = l_panic___at___Lean_Meta_whnfCore_go_spec__1(x_24, x_4, x_5, x_6, x_7, x_8);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = l_Lean_Expr_appFn_x21(x_3);
lean_dec(x_3);
x_27 = l_Lean_Expr_appArg_x21(x_26);
lean_dec(x_26);
x_28 = l_Lean_Meta_mkEqRefl(x_27, x_4, x_5, x_6, x_7, x_8);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_16 = lean_unbox(x_3);
lean_dec(x_3);
x_17 = lean_unbox(x_4);
lean_dec(x_4);
x_18 = l_Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__0(x_1, x_2, x_16, x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_5);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; uint8_t x_16; lean_object* x_17; 
x_15 = lean_unbox(x_2);
lean_dec(x_2);
x_16 = lean_unbox(x_3);
lean_dec(x_3);
x_17 = l_Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__1(x_1, x_15, x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_16 = lean_unbox(x_2);
lean_dec(x_2);
x_17 = lean_unbox(x_3);
lean_dec(x_3);
x_18 = l_Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__2(x_1, x_16, x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_5);
lean_dec(x_4);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_unbox(x_3);
lean_dec(x_3);
x_13 = lean_unbox(x_4);
lean_dec(x_4);
x_14 = l_Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__3(x_1, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpCore_x3f_mkProof(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_Meta_mkCongrSimpCore_x3f_mkProof_go(x_2, x_8, x_1, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_alloc_closure((void*)(l_Lean_Meta_instInhabitedMetaM___lam__0___boxed), 5, 0);
x_8 = lean_panic_fn(x_7, x_1);
x_9 = lean_apply_5(x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_1, x_17);
lean_inc(x_3);
x_19 = lean_array_push(x_2, x_3);
lean_inc(x_11);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_11);
x_21 = lean_array_push(x_4, x_20);
x_22 = lean_array_push(x_5, x_3);
x_23 = lean_array_push(x_22, x_11);
x_24 = l_Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go(x_6, x_7, x_8, x_9, x_10, x_18, x_19, x_21, x_23, x_12, x_13, x_14, x_15, x_16);
return x_24;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; 
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_18 = l_Lean_Meta_mkEq(x_1, x_12, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_box(x_6);
x_22 = lean_alloc_closure((void*)(l_Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___lam__0___boxed), 16, 10);
lean_closure_set(x_22, 0, x_2);
lean_closure_set(x_22, 1, x_3);
lean_closure_set(x_22, 2, x_12);
lean_closure_set(x_22, 3, x_4);
lean_closure_set(x_22, 4, x_5);
lean_closure_set(x_22, 5, x_21);
lean_closure_set(x_22, 6, x_7);
lean_closure_set(x_22, 7, x_8);
lean_closure_set(x_22, 8, x_9);
lean_closure_set(x_22, 9, x_10);
x_23 = lean_mk_string_unchecked("e_", 2, 2);
x_24 = lean_name_append_before(x_11, x_23);
x_25 = l_Lean_Meta_withLocalDeclD___at___Lean_Meta_addPPExplicitToExposeDiff_visit_spec__3(lean_box(0), x_24, x_19, x_22, x_13, x_14, x_15, x_16, x_20);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_26 = !lean_is_exclusive(x_18);
if (x_26 == 0)
{
return x_18;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_18, 0);
x_28 = lean_ctor_get(x_18, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_18);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_1, x_16);
lean_inc(x_10);
x_18 = lean_array_push(x_2, x_10);
x_19 = lean_box(0);
x_20 = lean_array_push(x_3, x_19);
x_21 = lean_array_push(x_4, x_10);
x_22 = l_Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go(x_5, x_6, x_7, x_8, x_9, x_17, x_18, x_20, x_21, x_11, x_12, x_13, x_14, x_15);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_13 = lean_infer_type(x_1, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; uint8_t x_28; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_get_size(x_2);
x_18 = l_Array_toSubarray___redArg(x_3, x_16, x_17);
x_19 = l_Array_ofSubarray___redArg(x_18);
lean_dec(x_18);
x_20 = l_Lean_Expr_replaceFVars(x_14, x_19, x_2);
lean_dec(x_19);
lean_dec(x_14);
if (x_6 == 0)
{
x_28 = x_7;
goto block_37;
}
else
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_box(3);
x_39 = lean_unbox(x_38);
x_28 = x_39;
goto block_37;
}
block_27:
{
lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_24 = lean_box(0);
x_25 = lean_unbox(x_24);
x_26 = l_Lean_Meta_withLocalDecl___at___Lean_Meta_withLocalDeclD___at___Lean_Meta_addPPExplicitToExposeDiff_visit_spec__3_spec__3___redArg(x_23, x_21, x_20, x_4, x_25, x_8, x_9, x_10, x_11, x_22);
return x_26;
}
block_37:
{
lean_object* x_29; 
lean_inc(x_8);
x_29 = l_Lean_FVarId_getDecl___redArg(x_5, x_8, x_10, x_11, x_15);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_ctor_get(x_30, 2);
lean_inc(x_32);
lean_dec(x_30);
x_21 = x_28;
x_22 = x_31;
x_23 = x_32;
goto block_27;
}
else
{
uint8_t x_33; 
lean_dec(x_20);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_33 = !lean_is_exclusive(x_29);
if (x_33 == 0)
{
return x_29;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_29, 0);
x_35 = lean_ctor_get(x_29, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_29);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_40 = !lean_is_exclusive(x_13);
if (x_40 == 0)
{
return x_13;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_13, 0);
x_42 = lean_ctor_get(x_13, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_13);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_array_get_size(x_4);
x_16 = lean_nat_dec_eq(x_6, x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_17 = l_Lean_instInhabitedExpr;
x_18 = lean_array_get(x_17, x_5, x_6);
lean_inc(x_18);
x_19 = lean_array_push(x_9, x_18);
x_20 = lean_box(0);
x_21 = lean_array_get(x_20, x_4, x_6);
x_22 = lean_unbox(x_21);
lean_dec(x_21);
x_23 = lean_box(x_22);
switch (lean_obj_tag(x_23)) {
case 0:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_6, x_24);
lean_dec(x_6);
x_26 = lean_array_push(x_7, x_18);
x_27 = lean_box(0);
x_28 = lean_array_push(x_8, x_27);
x_6 = x_25;
x_7 = x_26;
x_8 = x_28;
x_9 = x_19;
goto _start;
}
case 2:
{
lean_object* x_30; lean_object* x_31; 
x_30 = l_Lean_Expr_fvarId_x21(x_18);
lean_inc(x_10);
x_31 = l_Lean_FVarId_getDecl___redArg(x_30, x_10, x_12, x_13, x_14);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_42; lean_object* x_48; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_48 = lean_ctor_get(x_32, 2);
lean_inc(x_48);
x_42 = x_48;
goto block_47;
block_41:
{
lean_object* x_38; uint8_t x_39; lean_object* x_40; 
x_38 = lean_box(0);
x_39 = lean_unbox(x_38);
x_40 = l_Lean_Meta_withLocalDecl___at___Lean_Meta_withLocalDeclD___at___Lean_Meta_addPPExplicitToExposeDiff_visit_spec__3_spec__3___redArg(x_34, x_36, x_37, x_35, x_39, x_10, x_11, x_12, x_13, x_33);
return x_40;
}
block_47:
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; 
x_43 = lean_box(x_1);
lean_inc(x_42);
x_44 = lean_alloc_closure((void*)(l_Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___lam__1___boxed), 17, 11);
lean_closure_set(x_44, 0, x_18);
lean_closure_set(x_44, 1, x_6);
lean_closure_set(x_44, 2, x_7);
lean_closure_set(x_44, 3, x_8);
lean_closure_set(x_44, 4, x_19);
lean_closure_set(x_44, 5, x_43);
lean_closure_set(x_44, 6, x_2);
lean_closure_set(x_44, 7, x_3);
lean_closure_set(x_44, 8, x_4);
lean_closure_set(x_44, 9, x_5);
lean_closure_set(x_44, 10, x_42);
x_45 = l_Lean_LocalDecl_binderInfo(x_32);
x_46 = lean_ctor_get(x_32, 3);
lean_inc(x_46);
lean_dec(x_32);
x_34 = x_42;
x_35 = x_44;
x_36 = x_45;
x_37 = x_46;
goto block_41;
}
}
else
{
uint8_t x_49; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_49 = !lean_is_exclusive(x_31);
if (x_49 == 0)
{
return x_31;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_31, 0);
x_51 = lean_ctor_get(x_31, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_31);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
case 3:
{
lean_object* x_53; 
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_18);
x_53 = lean_infer_type(x_18, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_unsigned_to_nat(0u);
x_57 = lean_array_get_size(x_7);
lean_inc(x_5);
x_58 = l_Array_toSubarray___redArg(x_5, x_56, x_57);
x_59 = l_Array_ofSubarray___redArg(x_58);
lean_dec(x_58);
x_60 = l_Lean_Expr_replaceFVars(x_54, x_59, x_7);
lean_dec(x_59);
lean_dec(x_54);
x_61 = l_Lean_Meta_instInhabitedParamInfo;
x_62 = lean_ctor_get(x_3, 0);
lean_inc(x_62);
x_63 = lean_array_get(x_61, x_62, x_6);
lean_dec(x_62);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
lean_dec(x_63);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_65 = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast(x_18, x_60, x_64, x_8, x_10, x_11, x_12, x_13, x_55);
lean_dec(x_64);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = lean_unsigned_to_nat(1u);
x_69 = lean_nat_add(x_6, x_68);
lean_dec(x_6);
x_70 = lean_array_push(x_7, x_66);
x_71 = lean_box(0);
x_72 = lean_array_push(x_8, x_71);
x_6 = x_69;
x_7 = x_70;
x_8 = x_72;
x_9 = x_19;
x_14 = x_67;
goto _start;
}
else
{
uint8_t x_74; 
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_74 = !lean_is_exclusive(x_65);
if (x_74 == 0)
{
return x_65;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_65, 0);
x_76 = lean_ctor_get(x_65, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_65);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
else
{
uint8_t x_78; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_78 = !lean_is_exclusive(x_53);
if (x_78 == 0)
{
return x_53;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_53, 0);
x_80 = lean_ctor_get(x_53, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_53);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
case 5:
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_82 = lean_box(x_1);
lean_inc(x_5);
lean_inc(x_7);
x_83 = lean_alloc_closure((void*)(l_Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___lam__2___boxed), 15, 9);
lean_closure_set(x_83, 0, x_6);
lean_closure_set(x_83, 1, x_7);
lean_closure_set(x_83, 2, x_8);
lean_closure_set(x_83, 3, x_19);
lean_closure_set(x_83, 4, x_82);
lean_closure_set(x_83, 5, x_2);
lean_closure_set(x_83, 6, x_3);
lean_closure_set(x_83, 7, x_4);
lean_closure_set(x_83, 8, x_5);
x_84 = l_Lean_Expr_fvarId_x21(x_18);
x_85 = lean_box(1);
x_86 = lean_box(x_1);
lean_inc(x_84);
x_87 = lean_alloc_closure((void*)(l_Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___lam__3___boxed), 12, 7);
lean_closure_set(x_87, 0, x_18);
lean_closure_set(x_87, 1, x_7);
lean_closure_set(x_87, 2, x_5);
lean_closure_set(x_87, 3, x_83);
lean_closure_set(x_87, 4, x_84);
lean_closure_set(x_87, 5, x_86);
lean_closure_set(x_87, 6, x_85);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_84);
lean_ctor_set(x_88, 1, x_85);
x_89 = lean_unsigned_to_nat(1u);
x_90 = lean_mk_empty_array_with_capacity(x_89);
x_91 = lean_array_push(x_90, x_88);
x_92 = l_Lean_Meta_withNewBinderInfos___at___Lean_Meta_withInstImplicitAsImplict_spec__2___redArg(x_91, x_87, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_91);
return x_92;
}
default: 
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_23);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_93 = lean_mk_string_unchecked("Lean.Meta.CongrTheorems", 23, 23);
x_94 = lean_mk_string_unchecked("Lean.Meta.mkCongrSimpCore\?.mk\?.go", 33, 33);
x_95 = lean_unsigned_to_nat(296u);
x_96 = lean_unsigned_to_nat(38u);
x_97 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_98 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_93, x_94, x_95, x_96, x_97);
lean_dec(x_97);
lean_dec(x_94);
lean_dec(x_93);
x_99 = l_panic___at___Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0(x_98, x_10, x_11, x_12, x_13, x_14);
return x_99;
}
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
lean_inc(x_2);
x_100 = l_Lean_mkAppN(x_2, x_5);
lean_dec(x_5);
x_101 = l_Lean_mkAppN(x_2, x_7);
lean_dec(x_7);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_102 = l_Lean_Meta_mkEq(x_100, x_101, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; uint8_t x_108; lean_object* x_109; 
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec(x_102);
x_105 = lean_box(0);
x_106 = lean_box(1);
x_107 = lean_unbox(x_105);
x_108 = lean_unbox(x_106);
x_109 = l_Lean_Meta_mkForallFVars(x_9, x_103, x_107, x_16, x_108, x_10, x_11, x_12, x_13, x_104);
lean_dec(x_9);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
lean_dec(x_109);
lean_inc(x_4);
lean_inc(x_110);
x_112 = l_Lean_Meta_mkCongrSimpCore_x3f_mkProof(x_110, x_4, x_10, x_11, x_12, x_13, x_111);
if (lean_obj_tag(x_112) == 0)
{
uint8_t x_113; 
x_113 = !lean_is_exclusive(x_112);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; 
x_114 = lean_ctor_get(x_112, 0);
x_115 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_115, 0, x_110);
lean_ctor_set(x_115, 1, x_114);
lean_ctor_set(x_115, 2, x_4);
lean_ctor_set(x_112, 0, x_115);
return x_112;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_116 = lean_ctor_get(x_112, 0);
x_117 = lean_ctor_get(x_112, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_112);
x_118 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_118, 0, x_110);
lean_ctor_set(x_118, 1, x_116);
lean_ctor_set(x_118, 2, x_4);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_117);
return x_119;
}
}
else
{
uint8_t x_120; 
lean_dec(x_110);
lean_dec(x_4);
x_120 = !lean_is_exclusive(x_112);
if (x_120 == 0)
{
return x_112;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_112, 0);
x_122 = lean_ctor_get(x_112, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_112);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
return x_123;
}
}
}
else
{
uint8_t x_124; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_4);
x_124 = !lean_is_exclusive(x_109);
if (x_124 == 0)
{
return x_109;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_109, 0);
x_126 = lean_ctor_get(x_109, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_109);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
return x_127;
}
}
}
else
{
uint8_t x_128; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
x_128 = !lean_is_exclusive(x_102);
if (x_128 == 0)
{
return x_102;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_102, 0);
x_130 = lean_ctor_get(x_102, 1);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_102);
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
return x_131;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; lean_object* x_18; 
x_17 = lean_unbox(x_6);
lean_dec(x_6);
x_18 = l_Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___lam__0(x_1, x_2, x_3, x_4, x_5, x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_1);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___lam__1___boxed(lean_object** _args) {
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
x_18 = lean_unbox(x_6);
lean_dec(x_6);
x_19 = l_Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___lam__1(x_1, x_2, x_3, x_4, x_5, x_18, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_5);
lean_dec(x_5);
x_17 = l_Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___lam__2(x_1, x_2, x_3, x_4, x_16, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_1);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_unbox(x_6);
lean_dec(x_6);
x_14 = lean_unbox(x_7);
lean_dec(x_7);
x_15 = l_Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___lam__3(x_1, x_2, x_3, x_4, x_5, x_13, x_14, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_1);
lean_dec(x_1);
x_16 = l_Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go(x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpCore_x3f_mk_x3f___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_array_get_size(x_6);
x_14 = lean_nat_dec_eq(x_13, x_1);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_12);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_mk_empty_array_with_capacity(x_17);
lean_inc_n(x_18, 2);
x_19 = l_Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go(x_2, x_3, x_4, x_5, x_6, x_17, x_18, x_18, x_18, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_19, 0, x_22);
return x_19;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_19, 0);
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_19);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_23);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_19);
if (x_27 == 0)
{
return x_19;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_19, 0);
x_29 = lean_ctor_get(x_19, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_19);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpCore_x3f_mk_x3f(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_17; lean_object* x_18; lean_object* x_22; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_2);
x_22 = lean_infer_type(x_2, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_array_get_size(x_4);
x_26 = lean_box(x_1);
lean_inc(x_25);
x_27 = lean_alloc_closure((void*)(l_Lean_Meta_mkCongrSimpCore_x3f_mk_x3f___lam__0___boxed), 12, 5);
lean_closure_set(x_27, 0, x_25);
lean_closure_set(x_27, 1, x_26);
lean_closure_set(x_27, 2, x_2);
lean_closure_set(x_27, 3, x_3);
lean_closure_set(x_27, 4, x_4);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_25);
x_29 = lean_box(1);
x_30 = lean_unbox(x_29);
x_31 = l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_arrowDomainsN_spec__6(lean_box(0), x_23, x_28, x_27, x_30, x_5, x_6, x_7, x_8, x_24);
if (lean_obj_tag(x_31) == 0)
{
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_17 = x_32;
x_18 = x_33;
goto block_21;
}
}
else
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_34 = lean_ctor_get(x_22, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_22, 1);
lean_inc(x_35);
lean_dec(x_22);
x_17 = x_34;
x_18 = x_35;
goto block_21;
}
block_16:
{
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_11);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_10);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_10);
return x_15;
}
}
block_21:
{
uint8_t x_19; 
x_19 = l_Lean_Exception_isInterrupt(x_17);
if (x_19 == 0)
{
uint8_t x_20; 
x_20 = l_Lean_Exception_isRuntime(x_17);
x_10 = x_18;
x_11 = x_17;
x_12 = x_20;
goto block_16;
}
else
{
x_10 = x_18;
x_11 = x_17;
x_12 = x_19;
goto block_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpCore_x3f_mk_x3f___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_2);
lean_dec(x_2);
x_14 = l_Lean_Meta_mkCongrSimpCore_x3f_mk_x3f___lam__0(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpCore_x3f_mk_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_1);
lean_dec(x_1);
x_11 = l_Lean_Meta_mkCongrSimpCore_x3f_mk_x3f(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_mkCongrSimpCore_x3f_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_box(0);
x_7 = lean_array_uset(x_3, x_2, x_6);
if (lean_obj_tag(x_5) == 3)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_box(0);
x_17 = lean_unbox(x_16);
x_8 = x_17;
goto block_15;
}
else
{
if (lean_obj_tag(x_5) == 5)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_box(0);
x_19 = lean_unbox(x_18);
x_8 = x_19;
goto block_15;
}
else
{
uint8_t x_20; 
x_20 = lean_unbox(x_5);
lean_dec(x_5);
x_8 = x_20;
goto block_15;
}
}
block_15:
{
lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_usize_of_nat(x_9);
x_11 = lean_usize_add(x_2, x_10);
x_12 = lean_box(x_8);
x_13 = lean_array_uset(x_7, x_2, x_12);
x_2 = x_11;
x_3 = x_13;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpCore_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_10 = l_Lean_Meta_mkCongrSimpCore_x3f_mk_x3f(x_4, x_1, x_2, x_3, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
x_13 = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_hasCastLike(x_3);
if (x_13 == 0)
{
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
else
{
size_t x_14; lean_object* x_15; size_t x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_10);
x_14 = lean_array_size(x_3);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_usize_of_nat(x_15);
x_17 = l_Array_mapMUnsafe_map___at___Lean_Meta_mkCongrSimpCore_x3f_spec__0(x_14, x_16, x_3);
x_18 = l_Lean_Meta_mkCongrSimpCore_x3f_mk_x3f(x_4, x_1, x_2, x_17, x_5, x_6, x_7, x_8, x_12);
return x_18;
}
}
else
{
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
else
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_mkCongrSimpCore_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Lean_Meta_mkCongrSimpCore_x3f_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpCore_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
lean_dec(x_4);
x_11 = l_Lean_Meta_mkCongrSimpCore_x3f(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimp_x3f(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(x_1, x_4, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Expr_cleanupAnnotations(x_9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_11);
x_12 = l_Lean_Meta_getFunInfo(x_11, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_11);
x_15 = l_Lean_Meta_getCongrSimpKinds(x_11, x_13, x_3, x_4, x_5, x_6, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_Meta_mkCongrSimpCore_x3f(x_11, x_13, x_16, x_2, x_3, x_4, x_5, x_6, x_17);
return x_18;
}
else
{
uint8_t x_19; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_19 = !lean_is_exclusive(x_15);
if (x_19 == 0)
{
return x_15;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_15, 0);
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_15);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
else
{
uint8_t x_23; 
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_23 = !lean_is_exclusive(x_12);
if (x_23 == 0)
{
return x_12;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_12, 0);
x_25 = lean_ctor_get(x_12, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_12);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimp_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l_Lean_Meta_mkCongrSimp_x3f(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
static lean_object* _init_l_Lean_Meta_hcongrThmSuffixBase() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hcongr", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_hcongrThmSuffixBasePrefix() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hcongr_", 7, 7);
return x_1;
}
}
LEAN_EXPORT uint8_t l_String_anyAux___at___Lean_Meta_isHCongrReservedNameSuffix_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_string_utf8_byte_size(x_1);
lean_inc(x_10);
lean_inc(x_1);
x_11 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_9);
lean_ctor_set(x_11, 2, x_10);
x_12 = lean_unsigned_to_nat(7u);
x_13 = l_Substring_nextn(x_11, x_12, x_9);
lean_dec(x_11);
x_14 = lean_string_utf8_extract(x_1, x_13, x_10);
lean_dec(x_10);
lean_dec(x_13);
x_15 = lean_nat_dec_lt(x_4, x_3);
if (x_15 == 0)
{
lean_dec(x_14);
lean_dec(x_4);
lean_dec(x_1);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_19; lean_object* x_20; uint32_t x_21; uint32_t x_22; uint8_t x_23; 
x_16 = lean_mk_string_unchecked("hcongr_", 7, 7);
x_17 = lean_string_utf8_byte_size(x_14);
lean_dec(x_14);
x_18 = l_String_isPrefixOf(x_16, x_1);
lean_dec(x_16);
x_19 = l_instDecidableEqPos(x_17, x_9);
lean_dec(x_17);
x_20 = lean_unsigned_to_nat(48u);
x_21 = lean_uint32_of_nat(x_20);
x_22 = lean_string_utf8_get(x_2, x_4);
x_23 = lean_uint32_dec_le(x_21, x_22);
if (x_23 == 0)
{
if (x_23 == 0)
{
x_5 = x_18;
goto block_8;
}
else
{
x_5 = x_19;
goto block_8;
}
}
else
{
lean_object* x_24; uint32_t x_25; uint8_t x_26; 
x_24 = lean_unsigned_to_nat(57u);
x_25 = lean_uint32_of_nat(x_24);
x_26 = lean_uint32_dec_le(x_22, x_25);
if (x_26 == 0)
{
x_5 = x_18;
goto block_8;
}
else
{
x_5 = x_19;
goto block_8;
}
}
}
block_8:
{
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_string_utf8_next(x_2, x_4);
lean_dec(x_4);
x_4 = x_6;
goto _start;
}
else
{
lean_dec(x_4);
lean_dec(x_1);
return x_5;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_isHCongrReservedNameSuffix(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_mk_string_unchecked("hcongr_", 7, 7);
x_3 = l_String_isPrefixOf(x_2, x_1);
lean_dec(x_2);
if (x_3 == 0)
{
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_4 = lean_unsigned_to_nat(7u);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_string_utf8_byte_size(x_1);
lean_inc(x_6);
lean_inc(x_1);
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_5);
lean_ctor_set(x_7, 2, x_6);
x_8 = l_Substring_nextn(x_7, x_4, x_5);
lean_dec(x_7);
x_9 = lean_string_utf8_extract(x_1, x_8, x_6);
lean_dec(x_6);
lean_dec(x_8);
x_10 = lean_string_utf8_byte_size(x_9);
x_11 = l_instDecidableEqPos(x_10, x_5);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = l_String_anyAux___at___Lean_Meta_isHCongrReservedNameSuffix_spec__0(x_1, x_9, x_10, x_5);
lean_dec(x_10);
lean_dec(x_9);
if (x_12 == 0)
{
return x_3;
}
else
{
return x_11;
}
}
else
{
lean_object* x_13; uint8_t x_14; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_13 = lean_box(0);
x_14 = lean_unbox(x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_String_anyAux___at___Lean_Meta_isHCongrReservedNameSuffix_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_String_anyAux___at___Lean_Meta_isHCongrReservedNameSuffix_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isHCongrReservedNameSuffix___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_isHCongrReservedNameSuffix(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_congrSimpSuffix() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("congr_simp", 10, 10);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__0____x40_Lean_Meta_CongrTheorems___hyg_5266_(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_RBMap_toArray___at___Lean_mkMapDeclarationExtension_spec__1___redArg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_CongrTheorems___hyg_5266_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_initFn___lam__0____x40_Lean_Meta_CongrTheorems___hyg_5266____boxed), 1, 0);
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Meta", 4, 4);
x_5 = lean_mk_string_unchecked("congrKindsExt", 13, 13);
x_6 = l_Lean_Name_mkStr3(x_3, x_4, x_5);
x_7 = l_Lean_mkMapDeclarationExtension___redArg(x_6, x_2, x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__0____x40_Lean_Meta_CongrTheorems___hyg_5266____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_initFn___lam__0____x40_Lean_Meta_CongrTheorems___hyg_5266_(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_initFn___lam__0____x40_Lean_Meta_CongrTheorems___hyg_5298_(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_8; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
lean_inc(x_4);
x_8 = l_Lean_Meta_isHCongrReservedNameSuffix(x_4);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_mk_string_unchecked("congr_simp", 10, 10);
x_10 = lean_string_dec_eq(x_4, x_9);
lean_dec(x_9);
lean_dec(x_4);
x_5 = x_10;
goto block_7;
}
else
{
lean_dec(x_4);
x_5 = x_8;
goto block_7;
}
block_7:
{
if (x_5 == 0)
{
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = l_Lean_Environment_isSafeDefinition(x_1, x_3);
return x_6;
}
}
}
else
{
lean_object* x_11; uint8_t x_12; 
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_box(0);
x_12 = lean_unbox(x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_CongrTheorems___hyg_5298_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_initFn___lam__0____x40_Lean_Meta_CongrTheorems___hyg_5298____boxed), 2, 0);
x_3 = l_Lean_registerReservedNamePredicate(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__0____x40_Lean_Meta_CongrTheorems___hyg_5298____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_initFn___lam__0____x40_Lean_Meta_CongrTheorems___hyg_5298_(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__0____x40_Lean_Meta_CongrTheorems___hyg_5351_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_st_ref_get(x_3, x_4);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_10 = x_7;
} else {
 lean_dec_ref(x_7);
 x_10 = lean_box(0);
}
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
lean_dec(x_8);
lean_inc(x_5);
x_12 = l_Lean_Environment_isSafeDefinition(x_11, x_5);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_13 = lean_box(x_12);
if (lean_is_scalar(x_10)) {
 x_14 = lean_alloc_ctor(0, 2, 0);
} else {
 x_14 = x_10;
}
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_9);
return x_14;
}
else
{
uint8_t x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_23; lean_object* x_24; 
lean_inc(x_6);
x_15 = l_Lean_Meta_isHCongrReservedNameSuffix(x_6);
if (x_15 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_mk_string_unchecked("congr_simp", 10, 10);
x_29 = lean_string_dec_eq(x_6, x_28);
lean_dec(x_28);
lean_dec(x_6);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_30 = lean_box(x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_9);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; size_t x_36; lean_object* x_37; lean_object* x_38; size_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; uint8_t x_81; uint8_t x_82; uint64_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_32 = lean_box(0);
x_33 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_34 = lean_unsigned_to_nat(2u);
x_35 = lean_unsigned_to_nat(5u);
x_36 = lean_usize_of_nat(x_35);
x_37 = lean_usize_to_nat(x_36);
x_38 = lean_nat_pow(x_34, x_37);
lean_dec(x_37);
x_39 = lean_usize_of_nat(x_38);
lean_dec(x_38);
x_40 = lean_usize_to_nat(x_39);
x_41 = lean_mk_empty_array_with_capacity(x_40);
lean_dec(x_40);
lean_inc(x_41);
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_41);
x_43 = lean_unsigned_to_nat(0u);
lean_inc(x_33);
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_33);
lean_inc(x_33);
x_45 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_45, 0, x_33);
lean_inc(x_33);
x_46 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_46, 0, x_33);
lean_inc(x_33);
x_47 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_47, 0, x_33);
lean_inc(x_33);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_33);
lean_inc(x_33);
x_49 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_49, 0, x_33);
lean_inc(x_44);
x_50 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_50, 0, x_43);
lean_ctor_set(x_50, 1, x_43);
lean_ctor_set(x_50, 2, x_43);
lean_ctor_set(x_50, 3, x_44);
lean_ctor_set(x_50, 4, x_45);
lean_ctor_set(x_50, 5, x_46);
lean_ctor_set(x_50, 6, x_47);
lean_ctor_set(x_50, 7, x_48);
lean_ctor_set(x_50, 8, x_49);
lean_inc(x_33);
x_51 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_51, 0, x_33);
lean_inc(x_33);
x_52 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_52, 0, x_33);
lean_inc(x_33);
x_53 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_53, 0, x_33);
lean_inc(x_33);
x_54 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_54, 0, x_33);
lean_inc(x_54);
lean_inc(x_51);
x_55 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_55, 0, x_51);
lean_ctor_set(x_55, 1, x_52);
lean_ctor_set(x_55, 2, x_53);
lean_ctor_set(x_55, 3, x_51);
lean_ctor_set(x_55, 4, x_54);
lean_ctor_set(x_55, 5, x_54);
lean_inc(x_41);
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_41);
lean_inc(x_41);
x_57 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_41);
lean_ctor_set(x_57, 2, x_43);
lean_ctor_set(x_57, 3, x_43);
lean_ctor_set_usize(x_57, 4, x_36);
lean_inc(x_33);
x_58 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_58, 0, x_33);
lean_inc_n(x_44, 2);
x_59 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_59, 0, x_44);
lean_ctor_set(x_59, 1, x_44);
lean_ctor_set(x_59, 2, x_44);
lean_ctor_set(x_59, 3, x_58);
lean_inc(x_55);
x_60 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_60, 0, x_50);
lean_ctor_set(x_60, 1, x_55);
lean_ctor_set(x_60, 2, x_32);
lean_ctor_set(x_60, 3, x_57);
lean_ctor_set(x_60, 4, x_59);
x_61 = lean_st_mk_ref(x_60, x_9);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_74 = lean_box(1);
x_75 = lean_box(0);
x_76 = lean_box(2);
lean_inc(x_33);
x_77 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_77, 0, x_33);
x_78 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_78, 0, x_42);
lean_ctor_set(x_78, 1, x_41);
lean_ctor_set(x_78, 2, x_43);
lean_ctor_set(x_78, 3, x_43);
lean_ctor_set_usize(x_78, 4, x_36);
x_79 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_79, 0, x_15);
lean_ctor_set_uint8(x_79, 1, x_15);
lean_ctor_set_uint8(x_79, 2, x_15);
lean_ctor_set_uint8(x_79, 3, x_15);
lean_ctor_set_uint8(x_79, 4, x_15);
lean_ctor_set_uint8(x_79, 5, x_12);
lean_ctor_set_uint8(x_79, 6, x_12);
lean_ctor_set_uint8(x_79, 7, x_15);
lean_ctor_set_uint8(x_79, 8, x_12);
x_80 = lean_unbox(x_74);
lean_ctor_set_uint8(x_79, 9, x_80);
x_81 = lean_unbox(x_75);
lean_ctor_set_uint8(x_79, 10, x_81);
lean_ctor_set_uint8(x_79, 11, x_12);
lean_ctor_set_uint8(x_79, 12, x_12);
lean_ctor_set_uint8(x_79, 13, x_12);
x_82 = lean_unbox(x_76);
lean_ctor_set_uint8(x_79, 14, x_82);
lean_ctor_set_uint8(x_79, 15, x_12);
lean_ctor_set_uint8(x_79, 16, x_12);
lean_ctor_set_uint8(x_79, 17, x_12);
x_83 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_79);
x_84 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_84, 0, x_77);
lean_ctor_set(x_84, 1, x_78);
lean_ctor_set(x_84, 2, x_32);
x_85 = lean_mk_empty_array_with_capacity(x_43);
x_86 = lean_box(0);
x_87 = lean_box(0);
x_88 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_88, 0, x_79);
lean_ctor_set(x_88, 1, x_32);
lean_ctor_set(x_88, 2, x_84);
lean_ctor_set(x_88, 3, x_85);
lean_ctor_set(x_88, 4, x_86);
lean_ctor_set(x_88, 5, x_43);
lean_ctor_set(x_88, 6, x_87);
lean_ctor_set_uint64(x_88, sizeof(void*)*7, x_83);
lean_ctor_set_uint8(x_88, sizeof(void*)*7 + 8, x_15);
lean_ctor_set_uint8(x_88, sizeof(void*)*7 + 9, x_15);
lean_ctor_set_uint8(x_88, sizeof(void*)*7 + 10, x_15);
lean_inc(x_5);
x_89 = l_Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0(x_5, x_88, x_62, x_2, x_3, x_63);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
x_92 = l_Lean_ConstantInfo_levelParams(x_90);
lean_dec(x_90);
x_93 = lean_box(0);
lean_inc(x_92);
x_94 = l_List_mapTR_loop___at___Lean_mkConstWithLevelParams___at___Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__2(x_92, x_93);
x_95 = l_Lean_Expr_const___override(x_5, x_94);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_62);
lean_inc(x_88);
lean_inc(x_95);
x_96 = l_Lean_Meta_getFunInfo(x_95, x_88, x_62, x_2, x_3, x_91);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
lean_dec(x_96);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_62);
lean_inc(x_88);
lean_inc(x_95);
x_99 = l_Lean_Meta_getCongrSimpKinds(x_95, x_97, x_88, x_62, x_2, x_3, x_98);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
lean_dec(x_99);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_62);
x_102 = l_Lean_Meta_mkCongrSimpCore_x3f(x_95, x_97, x_100, x_12, x_88, x_62, x_2, x_3, x_101);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; 
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; 
lean_dec(x_92);
lean_dec(x_55);
lean_dec(x_33);
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec(x_102);
x_64 = x_15;
x_65 = x_104;
goto block_73;
}
else
{
uint8_t x_105; 
x_105 = !lean_is_exclusive(x_102);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; uint8_t x_108; 
x_106 = lean_ctor_get(x_102, 1);
x_107 = lean_ctor_get(x_102, 0);
lean_dec(x_107);
x_108 = !lean_is_exclusive(x_103);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_109 = lean_ctor_get(x_103, 0);
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
lean_inc(x_1);
x_111 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_111, 0, x_1);
lean_ctor_set(x_111, 1, x_92);
lean_ctor_set(x_111, 2, x_110);
x_112 = lean_ctor_get(x_109, 1);
lean_inc(x_112);
x_113 = lean_box(0);
lean_inc(x_1);
lean_ctor_set_tag(x_102, 1);
lean_ctor_set(x_102, 1, x_113);
lean_ctor_set(x_102, 0, x_1);
x_114 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_114, 0, x_111);
lean_ctor_set(x_114, 1, x_112);
lean_ctor_set(x_114, 2, x_102);
lean_ctor_set_tag(x_103, 2);
lean_ctor_set(x_103, 0, x_114);
lean_inc(x_3);
x_115 = l_Lean_addDecl(x_103, x_2, x_3, x_106);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; lean_object* x_117; uint8_t x_118; 
lean_dec(x_10);
x_116 = lean_ctor_get(x_115, 1);
lean_inc(x_116);
lean_dec(x_115);
x_117 = lean_st_ref_take(x_3, x_116);
x_118 = !lean_is_exclusive(x_117);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_119 = lean_ctor_get(x_117, 0);
x_120 = lean_ctor_get(x_117, 1);
x_121 = lean_ctor_get(x_119, 0);
lean_inc(x_121);
x_122 = l_Lean_Meta_congrKindsExt;
x_123 = lean_ctor_get(x_109, 2);
lean_inc(x_123);
lean_dec(x_109);
x_124 = l_Lean_MapDeclarationExtension_insert(lean_box(0), x_122, x_121, x_1, x_123);
x_125 = lean_ctor_get(x_119, 1);
lean_inc(x_125);
x_126 = lean_ctor_get(x_119, 2);
lean_inc(x_126);
x_127 = lean_ctor_get(x_119, 3);
lean_inc(x_127);
x_128 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_128, 0, x_33);
lean_inc(x_128);
lean_ctor_set(x_117, 1, x_128);
lean_ctor_set(x_117, 0, x_128);
x_129 = lean_ctor_get(x_119, 5);
lean_inc(x_129);
x_130 = lean_ctor_get(x_119, 6);
lean_inc(x_130);
x_131 = lean_ctor_get(x_119, 7);
lean_inc(x_131);
lean_dec(x_119);
x_132 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_132, 0, x_124);
lean_ctor_set(x_132, 1, x_125);
lean_ctor_set(x_132, 2, x_126);
lean_ctor_set(x_132, 3, x_127);
lean_ctor_set(x_132, 4, x_117);
lean_ctor_set(x_132, 5, x_129);
lean_ctor_set(x_132, 6, x_130);
lean_ctor_set(x_132, 7, x_131);
x_133 = lean_st_ref_set(x_3, x_132, x_120);
lean_dec(x_3);
x_134 = lean_ctor_get(x_133, 1);
lean_inc(x_134);
lean_dec(x_133);
x_135 = lean_st_ref_take(x_62, x_134);
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_135, 1);
lean_inc(x_137);
lean_dec(x_135);
x_138 = lean_ctor_get(x_136, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_136, 2);
lean_inc(x_139);
x_140 = lean_ctor_get(x_136, 3);
lean_inc(x_140);
x_141 = lean_ctor_get(x_136, 4);
lean_inc(x_141);
lean_dec(x_136);
x_142 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_142, 0, x_138);
lean_ctor_set(x_142, 1, x_55);
lean_ctor_set(x_142, 2, x_139);
lean_ctor_set(x_142, 3, x_140);
lean_ctor_set(x_142, 4, x_141);
x_143 = lean_st_ref_set(x_62, x_142, x_137);
x_144 = lean_ctor_get(x_143, 1);
lean_inc(x_144);
lean_dec(x_143);
x_64 = x_12;
x_65 = x_144;
goto block_73;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_145 = lean_ctor_get(x_117, 0);
x_146 = lean_ctor_get(x_117, 1);
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_117);
x_147 = lean_ctor_get(x_145, 0);
lean_inc(x_147);
x_148 = l_Lean_Meta_congrKindsExt;
x_149 = lean_ctor_get(x_109, 2);
lean_inc(x_149);
lean_dec(x_109);
x_150 = l_Lean_MapDeclarationExtension_insert(lean_box(0), x_148, x_147, x_1, x_149);
x_151 = lean_ctor_get(x_145, 1);
lean_inc(x_151);
x_152 = lean_ctor_get(x_145, 2);
lean_inc(x_152);
x_153 = lean_ctor_get(x_145, 3);
lean_inc(x_153);
x_154 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_154, 0, x_33);
lean_inc(x_154);
x_155 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_155, 1, x_154);
x_156 = lean_ctor_get(x_145, 5);
lean_inc(x_156);
x_157 = lean_ctor_get(x_145, 6);
lean_inc(x_157);
x_158 = lean_ctor_get(x_145, 7);
lean_inc(x_158);
lean_dec(x_145);
x_159 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_159, 0, x_150);
lean_ctor_set(x_159, 1, x_151);
lean_ctor_set(x_159, 2, x_152);
lean_ctor_set(x_159, 3, x_153);
lean_ctor_set(x_159, 4, x_155);
lean_ctor_set(x_159, 5, x_156);
lean_ctor_set(x_159, 6, x_157);
lean_ctor_set(x_159, 7, x_158);
x_160 = lean_st_ref_set(x_3, x_159, x_146);
lean_dec(x_3);
x_161 = lean_ctor_get(x_160, 1);
lean_inc(x_161);
lean_dec(x_160);
x_162 = lean_st_ref_take(x_62, x_161);
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_162, 1);
lean_inc(x_164);
lean_dec(x_162);
x_165 = lean_ctor_get(x_163, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_163, 2);
lean_inc(x_166);
x_167 = lean_ctor_get(x_163, 3);
lean_inc(x_167);
x_168 = lean_ctor_get(x_163, 4);
lean_inc(x_168);
lean_dec(x_163);
x_169 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_169, 0, x_165);
lean_ctor_set(x_169, 1, x_55);
lean_ctor_set(x_169, 2, x_166);
lean_ctor_set(x_169, 3, x_167);
lean_ctor_set(x_169, 4, x_168);
x_170 = lean_st_ref_set(x_62, x_169, x_164);
x_171 = lean_ctor_get(x_170, 1);
lean_inc(x_171);
lean_dec(x_170);
x_64 = x_12;
x_65 = x_171;
goto block_73;
}
}
else
{
lean_object* x_172; lean_object* x_173; 
lean_dec(x_109);
lean_dec(x_62);
lean_dec(x_55);
lean_dec(x_33);
lean_dec(x_3);
lean_dec(x_1);
x_172 = lean_ctor_get(x_115, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_115, 1);
lean_inc(x_173);
lean_dec(x_115);
x_23 = x_172;
x_24 = x_173;
goto block_27;
}
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_174 = lean_ctor_get(x_103, 0);
lean_inc(x_174);
lean_dec(x_103);
x_175 = lean_ctor_get(x_174, 0);
lean_inc(x_175);
lean_inc(x_1);
x_176 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_176, 0, x_1);
lean_ctor_set(x_176, 1, x_92);
lean_ctor_set(x_176, 2, x_175);
x_177 = lean_ctor_get(x_174, 1);
lean_inc(x_177);
x_178 = lean_box(0);
lean_inc(x_1);
lean_ctor_set_tag(x_102, 1);
lean_ctor_set(x_102, 1, x_178);
lean_ctor_set(x_102, 0, x_1);
x_179 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_179, 0, x_176);
lean_ctor_set(x_179, 1, x_177);
lean_ctor_set(x_179, 2, x_102);
x_180 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_180, 0, x_179);
lean_inc(x_3);
x_181 = l_Lean_addDecl(x_180, x_2, x_3, x_106);
if (lean_obj_tag(x_181) == 0)
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
lean_dec(x_10);
x_182 = lean_ctor_get(x_181, 1);
lean_inc(x_182);
lean_dec(x_181);
x_183 = lean_st_ref_take(x_3, x_182);
x_184 = lean_ctor_get(x_183, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_183, 1);
lean_inc(x_185);
if (lean_is_exclusive(x_183)) {
 lean_ctor_release(x_183, 0);
 lean_ctor_release(x_183, 1);
 x_186 = x_183;
} else {
 lean_dec_ref(x_183);
 x_186 = lean_box(0);
}
x_187 = lean_ctor_get(x_184, 0);
lean_inc(x_187);
x_188 = l_Lean_Meta_congrKindsExt;
x_189 = lean_ctor_get(x_174, 2);
lean_inc(x_189);
lean_dec(x_174);
x_190 = l_Lean_MapDeclarationExtension_insert(lean_box(0), x_188, x_187, x_1, x_189);
x_191 = lean_ctor_get(x_184, 1);
lean_inc(x_191);
x_192 = lean_ctor_get(x_184, 2);
lean_inc(x_192);
x_193 = lean_ctor_get(x_184, 3);
lean_inc(x_193);
x_194 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_194, 0, x_33);
lean_inc(x_194);
if (lean_is_scalar(x_186)) {
 x_195 = lean_alloc_ctor(0, 2, 0);
} else {
 x_195 = x_186;
}
lean_ctor_set(x_195, 0, x_194);
lean_ctor_set(x_195, 1, x_194);
x_196 = lean_ctor_get(x_184, 5);
lean_inc(x_196);
x_197 = lean_ctor_get(x_184, 6);
lean_inc(x_197);
x_198 = lean_ctor_get(x_184, 7);
lean_inc(x_198);
lean_dec(x_184);
x_199 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_199, 0, x_190);
lean_ctor_set(x_199, 1, x_191);
lean_ctor_set(x_199, 2, x_192);
lean_ctor_set(x_199, 3, x_193);
lean_ctor_set(x_199, 4, x_195);
lean_ctor_set(x_199, 5, x_196);
lean_ctor_set(x_199, 6, x_197);
lean_ctor_set(x_199, 7, x_198);
x_200 = lean_st_ref_set(x_3, x_199, x_185);
lean_dec(x_3);
x_201 = lean_ctor_get(x_200, 1);
lean_inc(x_201);
lean_dec(x_200);
x_202 = lean_st_ref_take(x_62, x_201);
x_203 = lean_ctor_get(x_202, 0);
lean_inc(x_203);
x_204 = lean_ctor_get(x_202, 1);
lean_inc(x_204);
lean_dec(x_202);
x_205 = lean_ctor_get(x_203, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_203, 2);
lean_inc(x_206);
x_207 = lean_ctor_get(x_203, 3);
lean_inc(x_207);
x_208 = lean_ctor_get(x_203, 4);
lean_inc(x_208);
lean_dec(x_203);
x_209 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_209, 0, x_205);
lean_ctor_set(x_209, 1, x_55);
lean_ctor_set(x_209, 2, x_206);
lean_ctor_set(x_209, 3, x_207);
lean_ctor_set(x_209, 4, x_208);
x_210 = lean_st_ref_set(x_62, x_209, x_204);
x_211 = lean_ctor_get(x_210, 1);
lean_inc(x_211);
lean_dec(x_210);
x_64 = x_12;
x_65 = x_211;
goto block_73;
}
else
{
lean_object* x_212; lean_object* x_213; 
lean_dec(x_174);
lean_dec(x_62);
lean_dec(x_55);
lean_dec(x_33);
lean_dec(x_3);
lean_dec(x_1);
x_212 = lean_ctor_get(x_181, 0);
lean_inc(x_212);
x_213 = lean_ctor_get(x_181, 1);
lean_inc(x_213);
lean_dec(x_181);
x_23 = x_212;
x_24 = x_213;
goto block_27;
}
}
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_214 = lean_ctor_get(x_102, 1);
lean_inc(x_214);
lean_dec(x_102);
x_215 = lean_ctor_get(x_103, 0);
lean_inc(x_215);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 x_216 = x_103;
} else {
 lean_dec_ref(x_103);
 x_216 = lean_box(0);
}
x_217 = lean_ctor_get(x_215, 0);
lean_inc(x_217);
lean_inc(x_1);
x_218 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_218, 0, x_1);
lean_ctor_set(x_218, 1, x_92);
lean_ctor_set(x_218, 2, x_217);
x_219 = lean_ctor_get(x_215, 1);
lean_inc(x_219);
x_220 = lean_box(0);
lean_inc(x_1);
x_221 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_221, 0, x_1);
lean_ctor_set(x_221, 1, x_220);
x_222 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_222, 0, x_218);
lean_ctor_set(x_222, 1, x_219);
lean_ctor_set(x_222, 2, x_221);
if (lean_is_scalar(x_216)) {
 x_223 = lean_alloc_ctor(2, 1, 0);
} else {
 x_223 = x_216;
 lean_ctor_set_tag(x_223, 2);
}
lean_ctor_set(x_223, 0, x_222);
lean_inc(x_3);
x_224 = l_Lean_addDecl(x_223, x_2, x_3, x_214);
if (lean_obj_tag(x_224) == 0)
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; 
lean_dec(x_10);
x_225 = lean_ctor_get(x_224, 1);
lean_inc(x_225);
lean_dec(x_224);
x_226 = lean_st_ref_take(x_3, x_225);
x_227 = lean_ctor_get(x_226, 0);
lean_inc(x_227);
x_228 = lean_ctor_get(x_226, 1);
lean_inc(x_228);
if (lean_is_exclusive(x_226)) {
 lean_ctor_release(x_226, 0);
 lean_ctor_release(x_226, 1);
 x_229 = x_226;
} else {
 lean_dec_ref(x_226);
 x_229 = lean_box(0);
}
x_230 = lean_ctor_get(x_227, 0);
lean_inc(x_230);
x_231 = l_Lean_Meta_congrKindsExt;
x_232 = lean_ctor_get(x_215, 2);
lean_inc(x_232);
lean_dec(x_215);
x_233 = l_Lean_MapDeclarationExtension_insert(lean_box(0), x_231, x_230, x_1, x_232);
x_234 = lean_ctor_get(x_227, 1);
lean_inc(x_234);
x_235 = lean_ctor_get(x_227, 2);
lean_inc(x_235);
x_236 = lean_ctor_get(x_227, 3);
lean_inc(x_236);
x_237 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_237, 0, x_33);
lean_inc(x_237);
if (lean_is_scalar(x_229)) {
 x_238 = lean_alloc_ctor(0, 2, 0);
} else {
 x_238 = x_229;
}
lean_ctor_set(x_238, 0, x_237);
lean_ctor_set(x_238, 1, x_237);
x_239 = lean_ctor_get(x_227, 5);
lean_inc(x_239);
x_240 = lean_ctor_get(x_227, 6);
lean_inc(x_240);
x_241 = lean_ctor_get(x_227, 7);
lean_inc(x_241);
lean_dec(x_227);
x_242 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_242, 0, x_233);
lean_ctor_set(x_242, 1, x_234);
lean_ctor_set(x_242, 2, x_235);
lean_ctor_set(x_242, 3, x_236);
lean_ctor_set(x_242, 4, x_238);
lean_ctor_set(x_242, 5, x_239);
lean_ctor_set(x_242, 6, x_240);
lean_ctor_set(x_242, 7, x_241);
x_243 = lean_st_ref_set(x_3, x_242, x_228);
lean_dec(x_3);
x_244 = lean_ctor_get(x_243, 1);
lean_inc(x_244);
lean_dec(x_243);
x_245 = lean_st_ref_take(x_62, x_244);
x_246 = lean_ctor_get(x_245, 0);
lean_inc(x_246);
x_247 = lean_ctor_get(x_245, 1);
lean_inc(x_247);
lean_dec(x_245);
x_248 = lean_ctor_get(x_246, 0);
lean_inc(x_248);
x_249 = lean_ctor_get(x_246, 2);
lean_inc(x_249);
x_250 = lean_ctor_get(x_246, 3);
lean_inc(x_250);
x_251 = lean_ctor_get(x_246, 4);
lean_inc(x_251);
lean_dec(x_246);
x_252 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_252, 0, x_248);
lean_ctor_set(x_252, 1, x_55);
lean_ctor_set(x_252, 2, x_249);
lean_ctor_set(x_252, 3, x_250);
lean_ctor_set(x_252, 4, x_251);
x_253 = lean_st_ref_set(x_62, x_252, x_247);
x_254 = lean_ctor_get(x_253, 1);
lean_inc(x_254);
lean_dec(x_253);
x_64 = x_12;
x_65 = x_254;
goto block_73;
}
else
{
lean_object* x_255; lean_object* x_256; 
lean_dec(x_215);
lean_dec(x_62);
lean_dec(x_55);
lean_dec(x_33);
lean_dec(x_3);
lean_dec(x_1);
x_255 = lean_ctor_get(x_224, 0);
lean_inc(x_255);
x_256 = lean_ctor_get(x_224, 1);
lean_inc(x_256);
lean_dec(x_224);
x_23 = x_255;
x_24 = x_256;
goto block_27;
}
}
}
}
else
{
lean_object* x_257; lean_object* x_258; 
lean_dec(x_92);
lean_dec(x_62);
lean_dec(x_55);
lean_dec(x_33);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_257 = lean_ctor_get(x_102, 0);
lean_inc(x_257);
x_258 = lean_ctor_get(x_102, 1);
lean_inc(x_258);
lean_dec(x_102);
x_23 = x_257;
x_24 = x_258;
goto block_27;
}
}
else
{
lean_object* x_259; lean_object* x_260; 
lean_dec(x_97);
lean_dec(x_95);
lean_dec(x_92);
lean_dec(x_88);
lean_dec(x_62);
lean_dec(x_55);
lean_dec(x_33);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_259 = lean_ctor_get(x_99, 0);
lean_inc(x_259);
x_260 = lean_ctor_get(x_99, 1);
lean_inc(x_260);
lean_dec(x_99);
x_23 = x_259;
x_24 = x_260;
goto block_27;
}
}
else
{
lean_object* x_261; lean_object* x_262; 
lean_dec(x_95);
lean_dec(x_92);
lean_dec(x_88);
lean_dec(x_62);
lean_dec(x_55);
lean_dec(x_33);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_261 = lean_ctor_get(x_96, 0);
lean_inc(x_261);
x_262 = lean_ctor_get(x_96, 1);
lean_inc(x_262);
lean_dec(x_96);
x_23 = x_261;
x_24 = x_262;
goto block_27;
}
}
else
{
lean_object* x_263; lean_object* x_264; 
lean_dec(x_88);
lean_dec(x_62);
lean_dec(x_55);
lean_dec(x_33);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_263 = lean_ctor_get(x_89, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_89, 1);
lean_inc(x_264);
lean_dec(x_89);
x_23 = x_263;
x_24 = x_264;
goto block_27;
}
block_73:
{
lean_object* x_66; uint8_t x_67; 
x_66 = lean_st_ref_get(x_62, x_65);
lean_dec(x_62);
x_67 = !lean_is_exclusive(x_66);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_66, 0);
lean_dec(x_68);
x_69 = lean_box(x_64);
lean_ctor_set(x_66, 0, x_69);
return x_66;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_66, 1);
lean_inc(x_70);
lean_dec(x_66);
x_71 = lean_box(x_64);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_70);
return x_72;
}
}
}
}
else
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; size_t x_273; lean_object* x_274; lean_object* x_275; size_t x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; uint8_t x_304; lean_object* x_308; lean_object* x_309; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; uint8_t x_319; uint8_t x_320; uint8_t x_321; uint8_t x_322; uint8_t x_323; uint8_t x_324; uint8_t x_325; uint8_t x_326; uint8_t x_327; uint64_t x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; uint8_t x_334; uint8_t x_335; uint8_t x_336; lean_object* x_337; 
lean_dec(x_10);
x_265 = lean_unsigned_to_nat(7u);
x_266 = lean_unsigned_to_nat(0u);
x_267 = lean_string_utf8_byte_size(x_6);
lean_inc(x_267);
lean_inc(x_6);
x_268 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_268, 0, x_6);
lean_ctor_set(x_268, 1, x_266);
lean_ctor_set(x_268, 2, x_267);
x_269 = lean_box(0);
x_270 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_271 = lean_unsigned_to_nat(2u);
x_272 = lean_unsigned_to_nat(5u);
x_273 = lean_usize_of_nat(x_272);
x_274 = lean_usize_to_nat(x_273);
x_275 = lean_nat_pow(x_271, x_274);
lean_dec(x_274);
x_276 = lean_usize_of_nat(x_275);
lean_dec(x_275);
x_277 = lean_usize_to_nat(x_276);
x_278 = lean_mk_empty_array_with_capacity(x_277);
lean_dec(x_277);
lean_inc(x_278);
x_279 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_279, 0, x_278);
lean_inc(x_270);
x_280 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_280, 0, x_270);
lean_inc(x_270);
x_281 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_281, 0, x_270);
lean_inc(x_270);
x_282 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_282, 0, x_270);
lean_inc(x_270);
x_283 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_283, 0, x_270);
lean_inc(x_270);
x_284 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_284, 0, x_270);
lean_inc(x_270);
x_285 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_285, 0, x_270);
lean_inc(x_280);
x_286 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_286, 0, x_266);
lean_ctor_set(x_286, 1, x_266);
lean_ctor_set(x_286, 2, x_266);
lean_ctor_set(x_286, 3, x_280);
lean_ctor_set(x_286, 4, x_281);
lean_ctor_set(x_286, 5, x_282);
lean_ctor_set(x_286, 6, x_283);
lean_ctor_set(x_286, 7, x_284);
lean_ctor_set(x_286, 8, x_285);
lean_inc(x_270);
x_287 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_287, 0, x_270);
lean_inc(x_270);
x_288 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_288, 0, x_270);
lean_inc(x_270);
x_289 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_289, 0, x_270);
lean_inc(x_270);
x_290 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_290, 0, x_270);
lean_inc(x_290);
lean_inc(x_287);
x_291 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_291, 0, x_287);
lean_ctor_set(x_291, 1, x_288);
lean_ctor_set(x_291, 2, x_289);
lean_ctor_set(x_291, 3, x_287);
lean_ctor_set(x_291, 4, x_290);
lean_ctor_set(x_291, 5, x_290);
lean_inc(x_278);
x_292 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_292, 0, x_278);
lean_inc(x_278);
x_293 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_293, 0, x_292);
lean_ctor_set(x_293, 1, x_278);
lean_ctor_set(x_293, 2, x_266);
lean_ctor_set(x_293, 3, x_266);
lean_ctor_set_usize(x_293, 4, x_273);
lean_inc(x_270);
x_294 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_294, 0, x_270);
lean_inc_n(x_280, 2);
x_295 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_295, 0, x_280);
lean_ctor_set(x_295, 1, x_280);
lean_ctor_set(x_295, 2, x_280);
lean_ctor_set(x_295, 3, x_294);
lean_inc(x_291);
x_296 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_296, 0, x_286);
lean_ctor_set(x_296, 1, x_291);
lean_ctor_set(x_296, 2, x_269);
lean_ctor_set(x_296, 3, x_293);
lean_ctor_set(x_296, 4, x_295);
x_297 = lean_st_mk_ref(x_296, x_9);
x_298 = lean_ctor_get(x_297, 0);
lean_inc(x_298);
x_299 = lean_ctor_get(x_297, 1);
lean_inc(x_299);
if (lean_is_exclusive(x_297)) {
 lean_ctor_release(x_297, 0);
 lean_ctor_release(x_297, 1);
 x_300 = x_297;
} else {
 lean_dec_ref(x_297);
 x_300 = lean_box(0);
}
x_301 = lean_box(0);
x_313 = lean_box(1);
x_314 = lean_box(0);
x_315 = lean_box(2);
lean_inc(x_270);
x_316 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_316, 0, x_270);
x_317 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_317, 0, x_279);
lean_ctor_set(x_317, 1, x_278);
lean_ctor_set(x_317, 2, x_266);
lean_ctor_set(x_317, 3, x_266);
lean_ctor_set_usize(x_317, 4, x_273);
x_318 = lean_alloc_ctor(0, 0, 18);
x_319 = lean_unbox(x_301);
lean_ctor_set_uint8(x_318, 0, x_319);
x_320 = lean_unbox(x_301);
lean_ctor_set_uint8(x_318, 1, x_320);
x_321 = lean_unbox(x_301);
lean_ctor_set_uint8(x_318, 2, x_321);
x_322 = lean_unbox(x_301);
lean_ctor_set_uint8(x_318, 3, x_322);
x_323 = lean_unbox(x_301);
lean_ctor_set_uint8(x_318, 4, x_323);
lean_ctor_set_uint8(x_318, 5, x_12);
lean_ctor_set_uint8(x_318, 6, x_12);
x_324 = lean_unbox(x_301);
lean_ctor_set_uint8(x_318, 7, x_324);
lean_ctor_set_uint8(x_318, 8, x_12);
x_325 = lean_unbox(x_313);
lean_ctor_set_uint8(x_318, 9, x_325);
x_326 = lean_unbox(x_314);
lean_ctor_set_uint8(x_318, 10, x_326);
lean_ctor_set_uint8(x_318, 11, x_12);
lean_ctor_set_uint8(x_318, 12, x_12);
lean_ctor_set_uint8(x_318, 13, x_12);
x_327 = lean_unbox(x_315);
lean_ctor_set_uint8(x_318, 14, x_327);
lean_ctor_set_uint8(x_318, 15, x_12);
lean_ctor_set_uint8(x_318, 16, x_12);
lean_ctor_set_uint8(x_318, 17, x_12);
x_328 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_318);
x_329 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_329, 0, x_316);
lean_ctor_set(x_329, 1, x_317);
lean_ctor_set(x_329, 2, x_269);
x_330 = lean_mk_empty_array_with_capacity(x_266);
x_331 = lean_box(0);
x_332 = lean_box(0);
x_333 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_333, 0, x_318);
lean_ctor_set(x_333, 1, x_269);
lean_ctor_set(x_333, 2, x_329);
lean_ctor_set(x_333, 3, x_330);
lean_ctor_set(x_333, 4, x_331);
lean_ctor_set(x_333, 5, x_266);
lean_ctor_set(x_333, 6, x_332);
lean_ctor_set_uint64(x_333, sizeof(void*)*7, x_328);
x_334 = lean_unbox(x_301);
lean_ctor_set_uint8(x_333, sizeof(void*)*7 + 8, x_334);
x_335 = lean_unbox(x_301);
lean_ctor_set_uint8(x_333, sizeof(void*)*7 + 9, x_335);
x_336 = lean_unbox(x_301);
lean_ctor_set_uint8(x_333, sizeof(void*)*7 + 10, x_336);
lean_inc(x_5);
x_337 = l_Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0(x_5, x_333, x_298, x_2, x_3, x_299);
if (lean_obj_tag(x_337) == 0)
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; 
x_338 = lean_ctor_get(x_337, 0);
lean_inc(x_338);
x_339 = lean_ctor_get(x_337, 1);
lean_inc(x_339);
lean_dec(x_337);
x_340 = l_Substring_nextn(x_268, x_265, x_266);
lean_dec(x_268);
x_341 = lean_string_utf8_extract(x_6, x_340, x_267);
lean_dec(x_267);
lean_dec(x_340);
lean_dec(x_6);
x_342 = l_String_toNat_x21(x_341);
lean_dec(x_341);
x_343 = l_Lean_ConstantInfo_levelParams(x_338);
lean_dec(x_338);
x_344 = lean_box(0);
lean_inc(x_343);
x_345 = l_List_mapTR_loop___at___Lean_mkConstWithLevelParams___at___Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__2(x_343, x_344);
x_346 = l_Lean_Expr_const___override(x_5, x_345);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_298);
x_347 = l_Lean_Meta_mkHCongrWithArity(x_346, x_342, x_333, x_298, x_2, x_3, x_339);
if (lean_obj_tag(x_347) == 0)
{
uint8_t x_348; 
x_348 = !lean_is_exclusive(x_347);
if (x_348 == 0)
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; 
x_349 = lean_ctor_get(x_347, 0);
x_350 = lean_ctor_get(x_347, 1);
x_351 = lean_ctor_get(x_349, 0);
lean_inc(x_351);
lean_inc(x_1);
x_352 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_352, 0, x_1);
lean_ctor_set(x_352, 1, x_343);
lean_ctor_set(x_352, 2, x_351);
x_353 = lean_ctor_get(x_349, 1);
lean_inc(x_353);
x_354 = lean_box(0);
lean_inc(x_1);
lean_ctor_set_tag(x_347, 1);
lean_ctor_set(x_347, 1, x_354);
lean_ctor_set(x_347, 0, x_1);
x_355 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_355, 0, x_352);
lean_ctor_set(x_355, 1, x_353);
lean_ctor_set(x_355, 2, x_347);
x_356 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_356, 0, x_355);
lean_inc(x_3);
x_357 = l_Lean_addDecl(x_356, x_2, x_3, x_350);
if (lean_obj_tag(x_357) == 0)
{
lean_object* x_358; lean_object* x_359; uint8_t x_360; 
lean_dec(x_300);
x_358 = lean_ctor_get(x_357, 1);
lean_inc(x_358);
lean_dec(x_357);
x_359 = lean_st_ref_take(x_3, x_358);
x_360 = !lean_is_exclusive(x_359);
if (x_360 == 0)
{
lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; uint8_t x_388; 
x_361 = lean_ctor_get(x_359, 0);
x_362 = lean_ctor_get(x_359, 1);
x_363 = lean_ctor_get(x_361, 0);
lean_inc(x_363);
x_364 = l_Lean_Meta_congrKindsExt;
x_365 = lean_ctor_get(x_349, 2);
lean_inc(x_365);
lean_dec(x_349);
x_366 = l_Lean_MapDeclarationExtension_insert(lean_box(0), x_364, x_363, x_1, x_365);
x_367 = lean_ctor_get(x_361, 1);
lean_inc(x_367);
x_368 = lean_ctor_get(x_361, 2);
lean_inc(x_368);
x_369 = lean_ctor_get(x_361, 3);
lean_inc(x_369);
x_370 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_370, 0, x_270);
lean_inc(x_370);
lean_ctor_set(x_359, 1, x_370);
lean_ctor_set(x_359, 0, x_370);
x_371 = lean_ctor_get(x_361, 5);
lean_inc(x_371);
x_372 = lean_ctor_get(x_361, 6);
lean_inc(x_372);
x_373 = lean_ctor_get(x_361, 7);
lean_inc(x_373);
lean_dec(x_361);
x_374 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_374, 0, x_366);
lean_ctor_set(x_374, 1, x_367);
lean_ctor_set(x_374, 2, x_368);
lean_ctor_set(x_374, 3, x_369);
lean_ctor_set(x_374, 4, x_359);
lean_ctor_set(x_374, 5, x_371);
lean_ctor_set(x_374, 6, x_372);
lean_ctor_set(x_374, 7, x_373);
x_375 = lean_st_ref_set(x_3, x_374, x_362);
lean_dec(x_3);
x_376 = lean_ctor_get(x_375, 1);
lean_inc(x_376);
lean_dec(x_375);
x_377 = lean_st_ref_take(x_298, x_376);
x_378 = lean_ctor_get(x_377, 0);
lean_inc(x_378);
x_379 = lean_ctor_get(x_377, 1);
lean_inc(x_379);
lean_dec(x_377);
x_380 = lean_ctor_get(x_378, 0);
lean_inc(x_380);
x_381 = lean_ctor_get(x_378, 2);
lean_inc(x_381);
x_382 = lean_ctor_get(x_378, 3);
lean_inc(x_382);
x_383 = lean_ctor_get(x_378, 4);
lean_inc(x_383);
lean_dec(x_378);
x_384 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_384, 0, x_380);
lean_ctor_set(x_384, 1, x_291);
lean_ctor_set(x_384, 2, x_381);
lean_ctor_set(x_384, 3, x_382);
lean_ctor_set(x_384, 4, x_383);
x_385 = lean_st_ref_set(x_298, x_384, x_379);
x_386 = lean_ctor_get(x_385, 1);
lean_inc(x_386);
lean_dec(x_385);
x_387 = lean_st_ref_get(x_298, x_386);
lean_dec(x_298);
x_388 = !lean_is_exclusive(x_387);
if (x_388 == 0)
{
lean_object* x_389; lean_object* x_390; 
x_389 = lean_ctor_get(x_387, 0);
lean_dec(x_389);
x_390 = lean_box(x_12);
lean_ctor_set(x_387, 0, x_390);
return x_387;
}
else
{
lean_object* x_391; lean_object* x_392; lean_object* x_393; 
x_391 = lean_ctor_get(x_387, 1);
lean_inc(x_391);
lean_dec(x_387);
x_392 = lean_box(x_12);
x_393 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_393, 0, x_392);
lean_ctor_set(x_393, 1, x_391);
return x_393;
}
}
else
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; 
x_394 = lean_ctor_get(x_359, 0);
x_395 = lean_ctor_get(x_359, 1);
lean_inc(x_395);
lean_inc(x_394);
lean_dec(x_359);
x_396 = lean_ctor_get(x_394, 0);
lean_inc(x_396);
x_397 = l_Lean_Meta_congrKindsExt;
x_398 = lean_ctor_get(x_349, 2);
lean_inc(x_398);
lean_dec(x_349);
x_399 = l_Lean_MapDeclarationExtension_insert(lean_box(0), x_397, x_396, x_1, x_398);
x_400 = lean_ctor_get(x_394, 1);
lean_inc(x_400);
x_401 = lean_ctor_get(x_394, 2);
lean_inc(x_401);
x_402 = lean_ctor_get(x_394, 3);
lean_inc(x_402);
x_403 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_403, 0, x_270);
lean_inc(x_403);
x_404 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_404, 0, x_403);
lean_ctor_set(x_404, 1, x_403);
x_405 = lean_ctor_get(x_394, 5);
lean_inc(x_405);
x_406 = lean_ctor_get(x_394, 6);
lean_inc(x_406);
x_407 = lean_ctor_get(x_394, 7);
lean_inc(x_407);
lean_dec(x_394);
x_408 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_408, 0, x_399);
lean_ctor_set(x_408, 1, x_400);
lean_ctor_set(x_408, 2, x_401);
lean_ctor_set(x_408, 3, x_402);
lean_ctor_set(x_408, 4, x_404);
lean_ctor_set(x_408, 5, x_405);
lean_ctor_set(x_408, 6, x_406);
lean_ctor_set(x_408, 7, x_407);
x_409 = lean_st_ref_set(x_3, x_408, x_395);
lean_dec(x_3);
x_410 = lean_ctor_get(x_409, 1);
lean_inc(x_410);
lean_dec(x_409);
x_411 = lean_st_ref_take(x_298, x_410);
x_412 = lean_ctor_get(x_411, 0);
lean_inc(x_412);
x_413 = lean_ctor_get(x_411, 1);
lean_inc(x_413);
lean_dec(x_411);
x_414 = lean_ctor_get(x_412, 0);
lean_inc(x_414);
x_415 = lean_ctor_get(x_412, 2);
lean_inc(x_415);
x_416 = lean_ctor_get(x_412, 3);
lean_inc(x_416);
x_417 = lean_ctor_get(x_412, 4);
lean_inc(x_417);
lean_dec(x_412);
x_418 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_418, 0, x_414);
lean_ctor_set(x_418, 1, x_291);
lean_ctor_set(x_418, 2, x_415);
lean_ctor_set(x_418, 3, x_416);
lean_ctor_set(x_418, 4, x_417);
x_419 = lean_st_ref_set(x_298, x_418, x_413);
x_420 = lean_ctor_get(x_419, 1);
lean_inc(x_420);
lean_dec(x_419);
x_421 = lean_st_ref_get(x_298, x_420);
lean_dec(x_298);
x_422 = lean_ctor_get(x_421, 1);
lean_inc(x_422);
if (lean_is_exclusive(x_421)) {
 lean_ctor_release(x_421, 0);
 lean_ctor_release(x_421, 1);
 x_423 = x_421;
} else {
 lean_dec_ref(x_421);
 x_423 = lean_box(0);
}
x_424 = lean_box(x_12);
if (lean_is_scalar(x_423)) {
 x_425 = lean_alloc_ctor(0, 2, 0);
} else {
 x_425 = x_423;
}
lean_ctor_set(x_425, 0, x_424);
lean_ctor_set(x_425, 1, x_422);
return x_425;
}
}
else
{
lean_object* x_426; lean_object* x_427; 
lean_dec(x_349);
lean_dec(x_298);
lean_dec(x_291);
lean_dec(x_270);
lean_dec(x_3);
lean_dec(x_1);
x_426 = lean_ctor_get(x_357, 0);
lean_inc(x_426);
x_427 = lean_ctor_get(x_357, 1);
lean_inc(x_427);
lean_dec(x_357);
x_308 = x_426;
x_309 = x_427;
goto block_312;
}
}
else
{
lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; 
x_428 = lean_ctor_get(x_347, 0);
x_429 = lean_ctor_get(x_347, 1);
lean_inc(x_429);
lean_inc(x_428);
lean_dec(x_347);
x_430 = lean_ctor_get(x_428, 0);
lean_inc(x_430);
lean_inc(x_1);
x_431 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_431, 0, x_1);
lean_ctor_set(x_431, 1, x_343);
lean_ctor_set(x_431, 2, x_430);
x_432 = lean_ctor_get(x_428, 1);
lean_inc(x_432);
x_433 = lean_box(0);
lean_inc(x_1);
x_434 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_434, 0, x_1);
lean_ctor_set(x_434, 1, x_433);
x_435 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_435, 0, x_431);
lean_ctor_set(x_435, 1, x_432);
lean_ctor_set(x_435, 2, x_434);
x_436 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_436, 0, x_435);
lean_inc(x_3);
x_437 = l_Lean_addDecl(x_436, x_2, x_3, x_429);
if (lean_obj_tag(x_437) == 0)
{
lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; 
lean_dec(x_300);
x_438 = lean_ctor_get(x_437, 1);
lean_inc(x_438);
lean_dec(x_437);
x_439 = lean_st_ref_take(x_3, x_438);
x_440 = lean_ctor_get(x_439, 0);
lean_inc(x_440);
x_441 = lean_ctor_get(x_439, 1);
lean_inc(x_441);
if (lean_is_exclusive(x_439)) {
 lean_ctor_release(x_439, 0);
 lean_ctor_release(x_439, 1);
 x_442 = x_439;
} else {
 lean_dec_ref(x_439);
 x_442 = lean_box(0);
}
x_443 = lean_ctor_get(x_440, 0);
lean_inc(x_443);
x_444 = l_Lean_Meta_congrKindsExt;
x_445 = lean_ctor_get(x_428, 2);
lean_inc(x_445);
lean_dec(x_428);
x_446 = l_Lean_MapDeclarationExtension_insert(lean_box(0), x_444, x_443, x_1, x_445);
x_447 = lean_ctor_get(x_440, 1);
lean_inc(x_447);
x_448 = lean_ctor_get(x_440, 2);
lean_inc(x_448);
x_449 = lean_ctor_get(x_440, 3);
lean_inc(x_449);
x_450 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_450, 0, x_270);
lean_inc(x_450);
if (lean_is_scalar(x_442)) {
 x_451 = lean_alloc_ctor(0, 2, 0);
} else {
 x_451 = x_442;
}
lean_ctor_set(x_451, 0, x_450);
lean_ctor_set(x_451, 1, x_450);
x_452 = lean_ctor_get(x_440, 5);
lean_inc(x_452);
x_453 = lean_ctor_get(x_440, 6);
lean_inc(x_453);
x_454 = lean_ctor_get(x_440, 7);
lean_inc(x_454);
lean_dec(x_440);
x_455 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_455, 0, x_446);
lean_ctor_set(x_455, 1, x_447);
lean_ctor_set(x_455, 2, x_448);
lean_ctor_set(x_455, 3, x_449);
lean_ctor_set(x_455, 4, x_451);
lean_ctor_set(x_455, 5, x_452);
lean_ctor_set(x_455, 6, x_453);
lean_ctor_set(x_455, 7, x_454);
x_456 = lean_st_ref_set(x_3, x_455, x_441);
lean_dec(x_3);
x_457 = lean_ctor_get(x_456, 1);
lean_inc(x_457);
lean_dec(x_456);
x_458 = lean_st_ref_take(x_298, x_457);
x_459 = lean_ctor_get(x_458, 0);
lean_inc(x_459);
x_460 = lean_ctor_get(x_458, 1);
lean_inc(x_460);
lean_dec(x_458);
x_461 = lean_ctor_get(x_459, 0);
lean_inc(x_461);
x_462 = lean_ctor_get(x_459, 2);
lean_inc(x_462);
x_463 = lean_ctor_get(x_459, 3);
lean_inc(x_463);
x_464 = lean_ctor_get(x_459, 4);
lean_inc(x_464);
lean_dec(x_459);
x_465 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_465, 0, x_461);
lean_ctor_set(x_465, 1, x_291);
lean_ctor_set(x_465, 2, x_462);
lean_ctor_set(x_465, 3, x_463);
lean_ctor_set(x_465, 4, x_464);
x_466 = lean_st_ref_set(x_298, x_465, x_460);
x_467 = lean_ctor_get(x_466, 1);
lean_inc(x_467);
lean_dec(x_466);
x_468 = lean_st_ref_get(x_298, x_467);
lean_dec(x_298);
x_469 = lean_ctor_get(x_468, 1);
lean_inc(x_469);
if (lean_is_exclusive(x_468)) {
 lean_ctor_release(x_468, 0);
 lean_ctor_release(x_468, 1);
 x_470 = x_468;
} else {
 lean_dec_ref(x_468);
 x_470 = lean_box(0);
}
x_471 = lean_box(x_12);
if (lean_is_scalar(x_470)) {
 x_472 = lean_alloc_ctor(0, 2, 0);
} else {
 x_472 = x_470;
}
lean_ctor_set(x_472, 0, x_471);
lean_ctor_set(x_472, 1, x_469);
return x_472;
}
else
{
lean_object* x_473; lean_object* x_474; 
lean_dec(x_428);
lean_dec(x_298);
lean_dec(x_291);
lean_dec(x_270);
lean_dec(x_3);
lean_dec(x_1);
x_473 = lean_ctor_get(x_437, 0);
lean_inc(x_473);
x_474 = lean_ctor_get(x_437, 1);
lean_inc(x_474);
lean_dec(x_437);
x_308 = x_473;
x_309 = x_474;
goto block_312;
}
}
}
else
{
lean_object* x_475; lean_object* x_476; 
lean_dec(x_343);
lean_dec(x_298);
lean_dec(x_291);
lean_dec(x_270);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_475 = lean_ctor_get(x_347, 0);
lean_inc(x_475);
x_476 = lean_ctor_get(x_347, 1);
lean_inc(x_476);
lean_dec(x_347);
x_308 = x_475;
x_309 = x_476;
goto block_312;
}
}
else
{
lean_object* x_477; lean_object* x_478; 
lean_dec(x_333);
lean_dec(x_298);
lean_dec(x_291);
lean_dec(x_270);
lean_dec(x_268);
lean_dec(x_267);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_477 = lean_ctor_get(x_337, 0);
lean_inc(x_477);
x_478 = lean_ctor_get(x_337, 1);
lean_inc(x_478);
lean_dec(x_337);
x_308 = x_477;
x_309 = x_478;
goto block_312;
}
block_307:
{
if (x_304 == 0)
{
lean_object* x_305; 
lean_dec(x_303);
if (lean_is_scalar(x_300)) {
 x_305 = lean_alloc_ctor(0, 2, 0);
} else {
 x_305 = x_300;
}
lean_ctor_set(x_305, 0, x_301);
lean_ctor_set(x_305, 1, x_302);
return x_305;
}
else
{
lean_object* x_306; 
if (lean_is_scalar(x_300)) {
 x_306 = lean_alloc_ctor(1, 2, 0);
} else {
 x_306 = x_300;
 lean_ctor_set_tag(x_306, 1);
}
lean_ctor_set(x_306, 0, x_303);
lean_ctor_set(x_306, 1, x_302);
return x_306;
}
}
block_312:
{
uint8_t x_310; 
x_310 = l_Lean_Exception_isInterrupt(x_308);
if (x_310 == 0)
{
uint8_t x_311; 
x_311 = l_Lean_Exception_isRuntime(x_308);
x_302 = x_309;
x_303 = x_308;
x_304 = x_311;
goto block_307;
}
else
{
x_302 = x_309;
x_303 = x_308;
x_304 = x_310;
goto block_307;
}
}
}
block_22:
{
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_16);
x_19 = lean_box(x_15);
if (lean_is_scalar(x_10)) {
 x_20 = lean_alloc_ctor(0, 2, 0);
} else {
 x_20 = x_10;
}
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_17);
return x_20;
}
else
{
lean_object* x_21; 
if (lean_is_scalar(x_10)) {
 x_21 = lean_alloc_ctor(1, 2, 0);
} else {
 x_21 = x_10;
 lean_ctor_set_tag(x_21, 1);
}
lean_ctor_set(x_21, 0, x_16);
lean_ctor_set(x_21, 1, x_17);
return x_21;
}
}
block_27:
{
uint8_t x_25; 
x_25 = l_Lean_Exception_isInterrupt(x_23);
if (x_25 == 0)
{
uint8_t x_26; 
x_26 = l_Lean_Exception_isRuntime(x_23);
x_16 = x_23;
x_17 = x_24;
x_18 = x_26;
goto block_22;
}
else
{
x_16 = x_23;
x_17 = x_24;
x_18 = x_25;
goto block_22;
}
}
}
}
else
{
lean_object* x_479; lean_object* x_480; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_479 = lean_box(0);
x_480 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_480, 0, x_479);
lean_ctor_set(x_480, 1, x_4);
return x_480;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_CongrTheorems___hyg_5351_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_initFn___lam__0____x40_Lean_Meta_CongrTheorems___hyg_5351_), 4, 0);
x_3 = l_Lean_registerReservedNameAction(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Meta_mkHCongrWithArityForConst_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_alloc_closure((void*)(l_Lean_Meta_instInhabitedMetaM___lam__0___boxed), 5, 0);
x_8 = lean_panic_fn(x_7, x_1);
x_9 = lean_apply_5(x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
lean_inc(x_1);
x_10 = l_Lean_Expr_const___override(x_1, x_2);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_10);
x_11 = lean_infer_type(x_10, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_st_ref_get(x_8, x_13);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Meta_congrKindsExt;
x_20 = lean_box(0);
x_21 = lean_unbox(x_20);
x_22 = l_Lean_MapDeclarationExtension_find_x3f(lean_box(0), x_3, x_19, x_18, x_1, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_free_object(x_14);
lean_dec(x_12);
lean_dec(x_10);
x_23 = lean_mk_string_unchecked("Lean.Meta.CongrTheorems", 23, 23);
x_24 = lean_mk_string_unchecked("Lean.Meta.mkHCongrWithArityForConst\?", 36, 36);
x_25 = lean_unsigned_to_nat(421u);
x_26 = lean_unsigned_to_nat(8u);
x_27 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_28 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_23, x_24, x_25, x_26, x_27);
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_23);
x_29 = l_panic___at___Lean_Meta_mkHCongrWithArityForConst_x3f_spec__0(x_28, x_5, x_6, x_7, x_8, x_17);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_29, 0, x_33);
return x_29;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_34 = lean_ctor_get(x_29, 0);
x_35 = lean_ctor_get(x_29, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_29);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_35);
return x_38;
}
}
else
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_29);
if (x_39 == 0)
{
return x_29;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_29, 0);
x_41 = lean_ctor_get(x_29, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_29);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_43 = !lean_is_exclusive(x_22);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_44 = lean_ctor_get(x_22, 0);
x_45 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_45, 0, x_12);
lean_ctor_set(x_45, 1, x_10);
lean_ctor_set(x_45, 2, x_44);
lean_ctor_set(x_22, 0, x_45);
x_46 = lean_box(0);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_22);
lean_ctor_set(x_47, 1, x_46);
lean_ctor_set(x_14, 0, x_47);
return x_14;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_48 = lean_ctor_get(x_22, 0);
lean_inc(x_48);
lean_dec(x_22);
x_49 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_49, 0, x_12);
lean_ctor_set(x_49, 1, x_10);
lean_ctor_set(x_49, 2, x_48);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_49);
x_51 = lean_box(0);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
lean_ctor_set(x_14, 0, x_52);
return x_14;
}
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; 
x_53 = lean_ctor_get(x_14, 0);
x_54 = lean_ctor_get(x_14, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_14);
x_55 = lean_ctor_get(x_53, 0);
lean_inc(x_55);
lean_dec(x_53);
x_56 = l_Lean_Meta_congrKindsExt;
x_57 = lean_box(0);
x_58 = lean_unbox(x_57);
x_59 = l_Lean_MapDeclarationExtension_find_x3f(lean_box(0), x_3, x_56, x_55, x_1, x_58);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_12);
lean_dec(x_10);
x_60 = lean_mk_string_unchecked("Lean.Meta.CongrTheorems", 23, 23);
x_61 = lean_mk_string_unchecked("Lean.Meta.mkHCongrWithArityForConst\?", 36, 36);
x_62 = lean_unsigned_to_nat(421u);
x_63 = lean_unsigned_to_nat(8u);
x_64 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_65 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_60, x_61, x_62, x_63, x_64);
lean_dec(x_64);
lean_dec(x_61);
lean_dec(x_60);
x_66 = l_panic___at___Lean_Meta_mkHCongrWithArityForConst_x3f_spec__0(x_65, x_5, x_6, x_7, x_8, x_54);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_69 = x_66;
} else {
 lean_dec_ref(x_66);
 x_69 = lean_box(0);
}
x_70 = lean_box(0);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_67);
lean_ctor_set(x_71, 1, x_70);
if (lean_is_scalar(x_69)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_69;
}
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_68);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_73 = lean_ctor_get(x_66, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_66, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_75 = x_66;
} else {
 lean_dec_ref(x_66);
 x_75 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_76 = lean_alloc_ctor(1, 2, 0);
} else {
 x_76 = x_75;
}
lean_ctor_set(x_76, 0, x_73);
lean_ctor_set(x_76, 1, x_74);
return x_76;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_77 = lean_ctor_get(x_59, 0);
lean_inc(x_77);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 x_78 = x_59;
} else {
 lean_dec_ref(x_59);
 x_78 = lean_box(0);
}
x_79 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_79, 0, x_12);
lean_ctor_set(x_79, 1, x_10);
lean_ctor_set(x_79, 2, x_77);
if (lean_is_scalar(x_78)) {
 x_80 = lean_alloc_ctor(1, 1, 0);
} else {
 x_80 = x_78;
}
lean_ctor_set(x_80, 0, x_79);
x_81 = lean_box(0);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_54);
return x_83;
}
}
}
else
{
uint8_t x_84; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_84 = !lean_is_exclusive(x_11);
if (x_84 == 0)
{
return x_11;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_11, 0);
x_86 = lean_ctor_get(x_11, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_11);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArityForConst_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_16; lean_object* x_17; lean_object* x_21; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; uint8_t x_43; 
x_32 = lean_st_ref_get(x_7, x_8);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_mk_string_unchecked("hcongr_", 7, 7);
x_36 = l___private_Init_Data_Repr_0__Nat_reprFast(x_3);
x_37 = l_Array_instInhabited(lean_box(0));
x_38 = lean_string_append(x_35, x_36);
lean_dec(x_36);
x_39 = l_Lean_Name_str___override(x_1, x_38);
x_40 = lean_ctor_get(x_33, 0);
lean_inc(x_40);
lean_dec(x_33);
x_41 = lean_box(1);
x_42 = lean_unbox(x_41);
lean_inc(x_39);
x_43 = l_Lean_Environment_contains(x_40, x_39, x_42);
if (x_43 == 0)
{
lean_object* x_44; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_39);
x_44 = l_Lean_executeReservedNameAction(x_39, x_6, x_7, x_34);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_46 = lean_box(0);
x_47 = l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0(x_39, x_2, x_37, x_46, x_4, x_5, x_6, x_7, x_45);
x_21 = x_47;
goto block_31;
}
else
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_39);
lean_dec(x_37);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_48 = lean_ctor_get(x_44, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_44, 1);
lean_inc(x_49);
lean_dec(x_44);
x_16 = x_48;
x_17 = x_49;
goto block_20;
}
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_box(0);
x_51 = l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0(x_39, x_2, x_37, x_50, x_4, x_5, x_6, x_7, x_34);
x_21 = x_51;
goto block_31;
}
block_15:
{
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_9);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
else
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_9);
lean_ctor_set(x_14, 1, x_10);
return x_14;
}
}
block_20:
{
uint8_t x_18; 
x_18 = l_Lean_Exception_isInterrupt(x_16);
if (x_18 == 0)
{
uint8_t x_19; 
x_19 = l_Lean_Exception_isRuntime(x_16);
x_9 = x_16;
x_10 = x_17;
x_11 = x_19;
goto block_15;
}
else
{
x_9 = x_16;
x_10 = x_17;
x_11 = x_18;
goto block_15;
}
}
block_31:
{
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec(x_23);
lean_ctor_set(x_21, 0, x_24);
return x_21;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_21, 0);
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_21);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_21, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_21, 1);
lean_inc(x_30);
lean_dec(x_21);
x_16 = x_29;
x_17 = x_30;
goto block_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpForConst_x3f___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
lean_inc(x_1);
x_10 = l_Lean_Expr_const___override(x_1, x_2);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_10);
x_11 = lean_infer_type(x_10, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_st_ref_get(x_8, x_13);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Meta_congrKindsExt;
x_20 = lean_box(0);
x_21 = lean_unbox(x_20);
x_22 = l_Lean_MapDeclarationExtension_find_x3f(lean_box(0), x_3, x_19, x_18, x_1, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_free_object(x_14);
lean_dec(x_12);
lean_dec(x_10);
x_23 = lean_mk_string_unchecked("Lean.Meta.CongrTheorems", 23, 23);
x_24 = lean_mk_string_unchecked("Lean.Meta.mkCongrSimpForConst\?", 30, 30);
x_25 = lean_unsigned_to_nat(438u);
x_26 = lean_unsigned_to_nat(8u);
x_27 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_28 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_23, x_24, x_25, x_26, x_27);
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_23);
x_29 = l_panic___at___Lean_Meta_mkHCongrWithArityForConst_x3f_spec__0(x_28, x_5, x_6, x_7, x_8, x_17);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_29, 0, x_33);
return x_29;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_34 = lean_ctor_get(x_29, 0);
x_35 = lean_ctor_get(x_29, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_29);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_35);
return x_38;
}
}
else
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_29);
if (x_39 == 0)
{
return x_29;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_29, 0);
x_41 = lean_ctor_get(x_29, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_29);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_43 = !lean_is_exclusive(x_22);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_44 = lean_ctor_get(x_22, 0);
x_45 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_45, 0, x_12);
lean_ctor_set(x_45, 1, x_10);
lean_ctor_set(x_45, 2, x_44);
lean_ctor_set(x_22, 0, x_45);
x_46 = lean_box(0);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_22);
lean_ctor_set(x_47, 1, x_46);
lean_ctor_set(x_14, 0, x_47);
return x_14;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_48 = lean_ctor_get(x_22, 0);
lean_inc(x_48);
lean_dec(x_22);
x_49 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_49, 0, x_12);
lean_ctor_set(x_49, 1, x_10);
lean_ctor_set(x_49, 2, x_48);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_49);
x_51 = lean_box(0);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
lean_ctor_set(x_14, 0, x_52);
return x_14;
}
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; 
x_53 = lean_ctor_get(x_14, 0);
x_54 = lean_ctor_get(x_14, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_14);
x_55 = lean_ctor_get(x_53, 0);
lean_inc(x_55);
lean_dec(x_53);
x_56 = l_Lean_Meta_congrKindsExt;
x_57 = lean_box(0);
x_58 = lean_unbox(x_57);
x_59 = l_Lean_MapDeclarationExtension_find_x3f(lean_box(0), x_3, x_56, x_55, x_1, x_58);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_12);
lean_dec(x_10);
x_60 = lean_mk_string_unchecked("Lean.Meta.CongrTheorems", 23, 23);
x_61 = lean_mk_string_unchecked("Lean.Meta.mkCongrSimpForConst\?", 30, 30);
x_62 = lean_unsigned_to_nat(438u);
x_63 = lean_unsigned_to_nat(8u);
x_64 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_65 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_60, x_61, x_62, x_63, x_64);
lean_dec(x_64);
lean_dec(x_61);
lean_dec(x_60);
x_66 = l_panic___at___Lean_Meta_mkHCongrWithArityForConst_x3f_spec__0(x_65, x_5, x_6, x_7, x_8, x_54);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_69 = x_66;
} else {
 lean_dec_ref(x_66);
 x_69 = lean_box(0);
}
x_70 = lean_box(0);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_67);
lean_ctor_set(x_71, 1, x_70);
if (lean_is_scalar(x_69)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_69;
}
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_68);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_73 = lean_ctor_get(x_66, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_66, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_75 = x_66;
} else {
 lean_dec_ref(x_66);
 x_75 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_76 = lean_alloc_ctor(1, 2, 0);
} else {
 x_76 = x_75;
}
lean_ctor_set(x_76, 0, x_73);
lean_ctor_set(x_76, 1, x_74);
return x_76;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_77 = lean_ctor_get(x_59, 0);
lean_inc(x_77);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 x_78 = x_59;
} else {
 lean_dec_ref(x_59);
 x_78 = lean_box(0);
}
x_79 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_79, 0, x_12);
lean_ctor_set(x_79, 1, x_10);
lean_ctor_set(x_79, 2, x_77);
if (lean_is_scalar(x_78)) {
 x_80 = lean_alloc_ctor(1, 1, 0);
} else {
 x_80 = x_78;
}
lean_ctor_set(x_80, 0, x_79);
x_81 = lean_box(0);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_54);
return x_83;
}
}
}
else
{
uint8_t x_84; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_84 = !lean_is_exclusive(x_11);
if (x_84 == 0)
{
return x_11;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_11, 0);
x_86 = lean_ctor_get(x_11, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_11);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpForConst_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_15; lean_object* x_16; lean_object* x_20; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_40; 
x_31 = lean_st_ref_get(x_6, x_7);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_Array_instInhabited(lean_box(0));
x_35 = lean_mk_string_unchecked("congr_simp", 10, 10);
x_36 = l_Lean_Name_str___override(x_1, x_35);
x_37 = lean_ctor_get(x_32, 0);
lean_inc(x_37);
lean_dec(x_32);
x_38 = lean_box(1);
x_39 = lean_unbox(x_38);
lean_inc(x_36);
x_40 = l_Lean_Environment_contains(x_37, x_36, x_39);
if (x_40 == 0)
{
lean_object* x_41; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_36);
x_41 = l_Lean_executeReservedNameAction(x_36, x_5, x_6, x_33);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
x_43 = lean_box(0);
x_44 = l_Lean_Meta_mkCongrSimpForConst_x3f___lam__0(x_36, x_2, x_34, x_43, x_3, x_4, x_5, x_6, x_42);
x_20 = x_44;
goto block_30;
}
else
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_36);
lean_dec(x_34);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_45 = lean_ctor_get(x_41, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_41, 1);
lean_inc(x_46);
lean_dec(x_41);
x_15 = x_45;
x_16 = x_46;
goto block_19;
}
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_box(0);
x_48 = l_Lean_Meta_mkCongrSimpForConst_x3f___lam__0(x_36, x_2, x_34, x_47, x_3, x_4, x_5, x_6, x_33);
x_20 = x_48;
goto block_30;
}
block_14:
{
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_9);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_8);
return x_12;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_8);
return x_13;
}
}
block_19:
{
uint8_t x_17; 
x_17 = l_Lean_Exception_isInterrupt(x_15);
if (x_17 == 0)
{
uint8_t x_18; 
x_18 = l_Lean_Exception_isRuntime(x_15);
x_8 = x_16;
x_9 = x_15;
x_10 = x_18;
goto block_14;
}
else
{
x_8 = x_16;
x_9 = x_15;
x_10 = x_17;
goto block_14;
}
}
block_30:
{
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec(x_22);
lean_ctor_set(x_20, 0, x_23);
return x_20;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_20, 0);
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_20);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_20, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_20, 1);
lean_inc(x_29);
lean_dec(x_20);
x_15 = x_28;
x_16 = x_29;
goto block_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpForConst_x3f___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_mkCongrSimpForConst_x3f___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
return x_10;
}
}
lean_object* initialize_Lean_AddDecl(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_ReservedNameAction(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_ResolveName(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_AppBuilder(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Class(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_CongrTheorems(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_AddDecl(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ReservedNameAction(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ResolveName(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_AppBuilder(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Class(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_instInhabitedCongrArgKind = _init_l_Lean_Meta_instInhabitedCongrArgKind();
l_Lean_Meta_instReprCongrArgKind = _init_l_Lean_Meta_instReprCongrArgKind();
lean_mark_persistent(l_Lean_Meta_instReprCongrArgKind);
l_Lean_Meta_instBEqCongrArgKind = _init_l_Lean_Meta_instBEqCongrArgKind();
lean_mark_persistent(l_Lean_Meta_instBEqCongrArgKind);
l_Lean_Meta_hcongrThmSuffixBase = _init_l_Lean_Meta_hcongrThmSuffixBase();
lean_mark_persistent(l_Lean_Meta_hcongrThmSuffixBase);
l_Lean_Meta_hcongrThmSuffixBasePrefix = _init_l_Lean_Meta_hcongrThmSuffixBasePrefix();
lean_mark_persistent(l_Lean_Meta_hcongrThmSuffixBasePrefix);
l_Lean_Meta_congrSimpSuffix = _init_l_Lean_Meta_congrSimpSuffix();
lean_mark_persistent(l_Lean_Meta_congrSimpSuffix);
if (builtin) {res = l_Lean_Meta_initFn____x40_Lean_Meta_CongrTheorems___hyg_5266_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_congrKindsExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_congrKindsExt);
lean_dec_ref(res);
}if (builtin) {res = l_Lean_Meta_initFn____x40_Lean_Meta_CongrTheorems___hyg_5298_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l_Lean_Meta_initFn____x40_Lean_Meta_CongrTheorems___hyg_5351_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
