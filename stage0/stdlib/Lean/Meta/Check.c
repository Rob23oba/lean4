// Lean compiler output
// Module: Lean.Meta.Check
// Imports: Lean.Meta.InferType Lean.Meta.Sorry
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
lean_object* l_Lean_Meta_throwIncorrectNumberOfLevels___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_addPPExplicitToExposeDiff___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkLambdaLet_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Meta_throwLetTypeMismatchMessage_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_addPPExplicitToExposeDiff_visit___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkForall_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentD(lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_addPPExplicitToExposeDiff_visit_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkConstant(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_lit___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_addPPExplicitToExposeDiff_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___Lean_Meta_withLocalDeclD___at___Lean_Meta_addPPExplicitToExposeDiff_visit_spec__3_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_addPPExplicitToExposeDiff_visit___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_addPPExplicitToExposeDiff_visit___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at_____private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkForall_spec__1___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_check(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at_____private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkLambdaLet_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at_____private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkLambdaLet_spec__1___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_setAppPPExplicit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_addPPExplicitToExposeDiff_visit___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_addPPExplicitToExposeDiff_visit___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkLambdaLet_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Expr_mvar___override(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkForall_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_addPPExplicitToExposeDiff_visit___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_addPPExplicitToExposeDiff_visit_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_addPPExplicitToExposeDiff_visit_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Check___hyg_4727_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_addPPExplicitToExposeDiff_visit___lam__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at___Lean_Meta_addPPExplicitToExposeDiff_visit_spec__1(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeCorrect(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___Lean_Meta_withLocalDeclD___at___Lean_Meta_addPPExplicitToExposeDiff_visit_spec__3_spec__3___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_abstract(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_throwAppTypeMismatch___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkLambdaLet___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_ensureType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_find(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at___Lean_Meta_addPPExplicitToExposeDiff_visit_spec__2(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Meta_addPPExplicitToExposeDiff_visit___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkForall___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_addPPExplicitToExposeDiff_visit___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_throwLetTypeMismatchMessage(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_addPPExplicitToExposeDiff_visit___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Expr_setPPExplicit(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_addPPExplicitToExposeDiff_visit___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_addPPExplicitToExposeDiff_visit___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwFunctionExpected___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___Lean_Meta_withLocalDeclD___at___Lean_Meta_addPPExplicitToExposeDiff_visit_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___at___Lean_Expr_appFn_x21_spec__0(lean_object*);
uint8_t l_Lean_Expr_isMVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_check(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_addPPExplicitToExposeDiff_visit___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_throwAppTypeMismatch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_addPPExplicitToExposeDiff_visit___lam__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_addPPExplicitToExposeDiff_visit___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_setOption___at___Lean_Expr_setPPExplicit_spec__0(lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux___redArg(uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___Lean_Meta_addPPExplicitToExposeDiff_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_addPPExplicitToExposeDiff_visit___lam__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
lean_object* l_Lean_Meta_isLabeledSorry_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_addPPExplicitToExposeDiff_visit_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at___Lean_Meta_addPPExplicitToExposeDiff_visit_spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_addPPExplicitToExposeDiff_visit___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at_____private_Lean_Meta_Basic_0__Lean_Meta_beqInfoCacheKey____x40_Lean_Meta_Basic___hyg_1324__spec__0(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at_____private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkLambdaLet_spec__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at_____private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkForall_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_check___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at_____private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkLambdaLet_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_addPPExplicitToExposeDiff_visit___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_addPPExplicitToExposeDiff_visit___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_addPPExplicitToExposeDiff_visit___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Meta_throwLetTypeMismatchMessage_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_addPPExplicitToExposeDiff_visit___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at_____private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkForall_spec__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkLambdaLet___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_addPPExplicitToExposeDiff(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_addPPExplicitToExposeDiff_visit___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_check___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at___Lean_Meta_addPPExplicitToExposeDiff_visit_spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkLambdaLet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___Lean_Meta_addPPExplicitToExposeDiff_visit_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___Lean_Meta_addPPExplicitToExposeDiff_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
uint8_t l_Lean_BinderInfo_isExplicit(uint8_t);
lean_object* l_Lean_Meta_getFVarLocalDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Data_DeclarationRange_0__Lean_decEqDeclarationLocation____x40_Lean_Data_DeclarationRange___hyg_600_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkHasTypeButIsExpectedMsg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SavedState_restore___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn_x27(lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_KVMap_getBool(lean_object*, lean_object*, uint8_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_Meta_saveState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_addPPExplicitToExposeDiff_visit___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Meta_check___lam__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___Lean_Meta_addPPExplicitToExposeDiff_visit_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkConstant___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_setPPNumericTypes(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_checkApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_getFunctionDomain(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at_____private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkLambdaLet_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_throwLetTypeMismatchMessage___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_setPPFunBinderTypes(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_withTraceNode___at___Lean_Meta_processPostponed_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkForall___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_addPPExplicitToExposeDiff_visit___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_addPPExplicitToExposeDiff_visit___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_setPPPiBinderTypes(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_check___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_checkProj(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_lengthTR(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at_____private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkForall_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___Lean_Meta_withLocalDeclD___at___Lean_Meta_addPPExplicitToExposeDiff_visit_spec__3_spec__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___Lean_Meta_withLocalDeclD___at___Lean_Meta_addPPExplicitToExposeDiff_visit_spec__3_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_addPPExplicitToExposeDiff_visit___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_ensureType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_getLevel(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
lean_dec(x_9);
x_10 = lean_box(0);
lean_ctor_set(x_7, 0, x_10);
return x_7;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_7, 1);
lean_inc(x_11);
lean_dec(x_7);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_7);
if (x_14 == 0)
{
return x_7;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_7, 0);
x_16 = lean_ctor_get(x_7, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_7);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkConstant(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_1);
x_8 = l_Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_12 = l_List_lengthTR(lean_box(0), x_2);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = l_List_lengthTR(lean_box(0), x_13);
lean_dec(x_13);
x_15 = lean_nat_dec_eq(x_12, x_14);
lean_dec(x_14);
lean_dec(x_12);
if (x_15 == 0)
{
lean_object* x_16; 
lean_free_object(x_8);
x_16 = l_Lean_Meta_throwIncorrectNumberOfLevels___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_11);
return x_16;
}
else
{
lean_object* x_17; 
lean_dec(x_2);
lean_dec(x_1);
x_17 = lean_box(0);
lean_ctor_set(x_8, 0, x_17);
return x_8;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_18 = lean_ctor_get(x_8, 0);
x_19 = lean_ctor_get(x_8, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_8);
x_20 = l_List_lengthTR(lean_box(0), x_2);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = l_List_lengthTR(lean_box(0), x_21);
lean_dec(x_21);
x_23 = lean_nat_dec_eq(x_20, x_22);
lean_dec(x_22);
lean_dec(x_20);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = l_Lean_Meta_throwIncorrectNumberOfLevels___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_19);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_2);
lean_dec(x_1);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_19);
return x_26;
}
}
}
else
{
uint8_t x_27; 
lean_dec(x_2);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_8);
if (x_27 == 0)
{
return x_8;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_8, 0);
x_29 = lean_ctor_get(x_8, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_8);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkConstant___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Check_0__Lean_Meta_checkConstant(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_getFunctionDomain(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_7 = lean_infer_type(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_10 = l_Lean_Meta_whnfD(x_8, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 7)
{
uint8_t x_12; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_10, 0);
lean_dec(x_13);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
x_15 = lean_ctor_get_uint8(x_11, sizeof(void*)*3 + 8);
lean_dec(x_11);
x_16 = lean_box(x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set(x_10, 0, x_17);
return x_10;
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_10, 1);
lean_inc(x_18);
lean_dec(x_10);
x_19 = lean_ctor_get(x_11, 1);
lean_inc(x_19);
x_20 = lean_ctor_get_uint8(x_11, sizeof(void*)*3 + 8);
lean_dec(x_11);
x_21 = lean_box(x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_18);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_11);
x_24 = lean_ctor_get(x_10, 1);
lean_inc(x_24);
lean_dec(x_10);
x_25 = l_Lean_Meta_throwFunctionExpected___redArg(x_1, x_2, x_3, x_4, x_5, x_24);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_10);
if (x_26 == 0)
{
return x_10;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_10, 0);
x_28 = lean_ctor_get(x_10, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_10);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
uint8_t x_30; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_7);
if (x_30 == 0)
{
return x_7;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_7, 0);
x_32 = lean_ctor_get(x_7, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_7);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_addPPExplicitToExposeDiff_visit_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_162; uint8_t x_163; 
x_17 = l_Lean_Expr_getAppNumArgs(x_1);
x_18 = lean_box(0);
x_19 = l_Lean_Expr_sort___override(x_18);
lean_inc(x_19);
lean_inc(x_17);
x_20 = lean_mk_array(x_17, x_19);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_sub(x_17, x_21);
lean_dec(x_17);
lean_inc(x_1);
x_23 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_20, x_22);
x_24 = l_Lean_Expr_getAppNumArgs(x_2);
lean_inc(x_24);
x_25 = lean_mk_array(x_24, x_19);
x_26 = lean_nat_sub(x_24, x_21);
lean_dec(x_24);
lean_inc(x_2);
x_27 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_2, x_25, x_26);
x_28 = lean_box(0);
x_162 = lean_ctor_get(x_3, 1);
x_163 = lean_nat_dec_lt(x_5, x_162);
if (x_163 == 0)
{
lean_object* x_164; 
lean_dec(x_27);
lean_dec(x_23);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_164 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_164, 0, x_4);
lean_ctor_set(x_164, 1, x_10);
return x_164;
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; uint8_t x_172; 
x_165 = lean_ctor_get(x_4, 1);
lean_inc(x_165);
lean_dec(x_4);
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_165, 1);
lean_inc(x_167);
lean_dec(x_165);
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_167, 1);
lean_inc(x_169);
lean_dec(x_167);
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_169, 1);
lean_inc(x_171);
lean_dec(x_169);
x_172 = l_Lean_Expr_isForall(x_166);
if (x_172 == 0)
{
lean_object* x_173; lean_object* x_174; uint8_t x_175; uint8_t x_176; uint8_t x_177; uint8_t x_178; uint8_t x_179; uint8_t x_180; uint8_t x_181; uint8_t x_182; uint8_t x_183; uint8_t x_184; uint8_t x_185; uint8_t x_186; uint8_t x_187; uint8_t x_188; uint8_t x_189; uint8_t x_190; uint8_t x_191; lean_object* x_192; uint8_t x_193; uint64_t x_194; lean_object* x_195; uint64_t x_196; uint64_t x_197; uint64_t x_198; uint8_t x_199; uint64_t x_200; uint64_t x_201; uint8_t x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; uint8_t x_209; uint8_t x_210; lean_object* x_211; lean_object* x_212; 
x_173 = lean_box(0);
x_174 = lean_ctor_get(x_6, 0);
x_175 = lean_ctor_get_uint8(x_174, 0);
x_176 = lean_ctor_get_uint8(x_174, 1);
x_177 = lean_ctor_get_uint8(x_174, 2);
x_178 = lean_ctor_get_uint8(x_174, 3);
x_179 = lean_ctor_get_uint8(x_174, 4);
x_180 = lean_ctor_get_uint8(x_174, 5);
x_181 = lean_ctor_get_uint8(x_174, 6);
x_182 = lean_ctor_get_uint8(x_174, 7);
x_183 = lean_ctor_get_uint8(x_174, 8);
x_184 = lean_ctor_get_uint8(x_174, 10);
x_185 = lean_ctor_get_uint8(x_174, 11);
x_186 = lean_ctor_get_uint8(x_174, 12);
x_187 = lean_ctor_get_uint8(x_174, 13);
x_188 = lean_ctor_get_uint8(x_174, 14);
x_189 = lean_ctor_get_uint8(x_174, 15);
x_190 = lean_ctor_get_uint8(x_174, 16);
x_191 = lean_ctor_get_uint8(x_174, 17);
x_192 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_192, 0, x_175);
lean_ctor_set_uint8(x_192, 1, x_176);
lean_ctor_set_uint8(x_192, 2, x_177);
lean_ctor_set_uint8(x_192, 3, x_178);
lean_ctor_set_uint8(x_192, 4, x_179);
lean_ctor_set_uint8(x_192, 5, x_180);
lean_ctor_set_uint8(x_192, 6, x_181);
lean_ctor_set_uint8(x_192, 7, x_182);
lean_ctor_set_uint8(x_192, 8, x_183);
x_193 = lean_unbox(x_173);
lean_ctor_set_uint8(x_192, 9, x_193);
lean_ctor_set_uint8(x_192, 10, x_184);
lean_ctor_set_uint8(x_192, 11, x_185);
lean_ctor_set_uint8(x_192, 12, x_186);
lean_ctor_set_uint8(x_192, 13, x_187);
lean_ctor_set_uint8(x_192, 14, x_188);
lean_ctor_set_uint8(x_192, 15, x_189);
lean_ctor_set_uint8(x_192, 16, x_190);
lean_ctor_set_uint8(x_192, 17, x_191);
x_194 = lean_ctor_get_uint64(x_6, sizeof(void*)*7);
x_195 = lean_unsigned_to_nat(2u);
x_196 = lean_uint64_of_nat(x_195);
x_197 = lean_uint64_shift_right(x_194, x_196);
x_198 = lean_uint64_shift_left(x_197, x_196);
x_199 = lean_unbox(x_173);
x_200 = l_Lean_Meta_TransparencyMode_toUInt64(x_199);
x_201 = lean_uint64_lor(x_198, x_200);
x_202 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 8);
x_203 = lean_ctor_get(x_6, 1);
x_204 = lean_ctor_get(x_6, 2);
x_205 = lean_ctor_get(x_6, 3);
x_206 = lean_ctor_get(x_6, 4);
x_207 = lean_ctor_get(x_6, 5);
x_208 = lean_ctor_get(x_6, 6);
x_209 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 9);
x_210 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 10);
lean_inc(x_208);
lean_inc(x_207);
lean_inc(x_206);
lean_inc(x_205);
lean_inc(x_204);
lean_inc(x_203);
x_211 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_211, 0, x_192);
lean_ctor_set(x_211, 1, x_203);
lean_ctor_set(x_211, 2, x_204);
lean_ctor_set(x_211, 3, x_205);
lean_ctor_set(x_211, 4, x_206);
lean_ctor_set(x_211, 5, x_207);
lean_ctor_set(x_211, 6, x_208);
lean_ctor_set_uint64(x_211, sizeof(void*)*7, x_201);
lean_ctor_set_uint8(x_211, sizeof(void*)*7 + 8, x_202);
lean_ctor_set_uint8(x_211, sizeof(void*)*7 + 9, x_209);
lean_ctor_set_uint8(x_211, sizeof(void*)*7 + 10, x_210);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_212 = lean_whnf(x_166, x_211, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_212) == 0)
{
lean_object* x_213; lean_object* x_214; 
x_213 = lean_ctor_get(x_212, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_212, 1);
lean_inc(x_214);
lean_dec(x_212);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_105 = x_213;
x_106 = x_168;
x_107 = x_170;
x_108 = x_171;
x_109 = x_6;
x_110 = x_7;
x_111 = x_8;
x_112 = x_9;
x_113 = x_214;
goto block_161;
}
else
{
uint8_t x_215; 
lean_dec(x_171);
lean_dec(x_170);
lean_dec(x_168);
lean_dec(x_27);
lean_dec(x_23);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_215 = !lean_is_exclusive(x_212);
if (x_215 == 0)
{
return x_212;
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_216 = lean_ctor_get(x_212, 0);
x_217 = lean_ctor_get(x_212, 1);
lean_inc(x_217);
lean_inc(x_216);
lean_dec(x_212);
x_218 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_218, 0, x_216);
lean_ctor_set(x_218, 1, x_217);
return x_218;
}
}
}
else
{
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_105 = x_166;
x_106 = x_168;
x_107 = x_170;
x_108 = x_171;
x_109 = x_6;
x_110 = x_7;
x_111 = x_8;
x_112 = x_9;
x_113 = x_10;
goto block_161;
}
}
block_16:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_3, 2);
x_14 = lean_nat_add(x_5, x_13);
lean_dec(x_5);
x_4 = x_11;
x_5 = x_14;
x_10 = x_12;
goto _start;
}
block_38:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_29);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_31);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_32);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_28);
lean_ctor_set(x_37, 1, x_36);
x_11 = x_37;
x_12 = x_30;
goto block_16;
}
block_48:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_40);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_41);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_28);
lean_ctor_set(x_47, 1, x_46);
x_11 = x_47;
x_12 = x_39;
goto block_16;
}
block_57:
{
if (x_54 == 0)
{
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_55; 
lean_inc(x_5);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_5);
x_39 = x_50;
x_40 = x_51;
x_41 = x_52;
x_42 = x_53;
x_43 = x_55;
goto block_48;
}
else
{
x_39 = x_50;
x_40 = x_51;
x_41 = x_52;
x_42 = x_53;
x_43 = x_49;
goto block_48;
}
}
else
{
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_56; 
lean_inc(x_5);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_5);
x_29 = x_49;
x_30 = x_50;
x_31 = x_51;
x_32 = x_52;
x_33 = x_56;
goto block_38;
}
else
{
x_29 = x_49;
x_30 = x_50;
x_31 = x_51;
x_32 = x_52;
x_33 = x_53;
goto block_38;
}
}
}
block_104:
{
if (lean_obj_tag(x_58) == 7)
{
if (lean_obj_tag(x_59) == 7)
{
lean_object* x_67; uint8_t x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_67 = lean_ctor_get(x_58, 2);
lean_inc(x_67);
x_68 = lean_ctor_get_uint8(x_58, sizeof(void*)*3 + 8);
lean_dec(x_58);
x_69 = lean_ctor_get(x_59, 2);
lean_inc(x_69);
x_70 = lean_ctor_get_uint8(x_59, sizeof(void*)*3 + 8);
lean_dec(x_59);
x_71 = l_Lean_instInhabitedExpr;
x_72 = lean_array_get(x_71, x_23, x_5);
lean_dec(x_23);
x_73 = lean_array_get(x_71, x_27, x_5);
lean_dec(x_27);
lean_inc(x_73);
lean_inc(x_72);
x_74 = l_Lean_Meta_isExprDefEq(x_72, x_73, x_62, x_63, x_64, x_65, x_66);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_77 = lean_expr_instantiate1(x_67, x_72);
lean_dec(x_72);
lean_dec(x_67);
x_78 = lean_expr_instantiate1(x_69, x_73);
lean_dec(x_73);
lean_dec(x_69);
x_79 = lean_unbox(x_75);
lean_dec(x_75);
if (x_79 == 0)
{
uint8_t x_80; 
x_80 = l_Lean_BinderInfo_isExplicit(x_68);
if (x_80 == 0)
{
x_49 = x_61;
x_50 = x_76;
x_51 = x_78;
x_52 = x_77;
x_53 = x_60;
x_54 = x_80;
goto block_57;
}
else
{
uint8_t x_81; 
x_81 = l_Lean_BinderInfo_isExplicit(x_70);
x_49 = x_61;
x_50 = x_76;
x_51 = x_78;
x_52 = x_77;
x_53 = x_60;
x_54 = x_81;
goto block_57;
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_60);
lean_ctor_set(x_82, 1, x_61);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_78);
lean_ctor_set(x_83, 1, x_82);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_77);
lean_ctor_set(x_84, 1, x_83);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_28);
lean_ctor_set(x_85, 1, x_84);
x_11 = x_85;
x_12 = x_76;
goto block_16;
}
}
else
{
uint8_t x_86; 
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_69);
lean_dec(x_67);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_86 = !lean_is_exclusive(x_74);
if (x_86 == 0)
{
return x_74;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_74, 0);
x_88 = lean_ctor_get(x_74, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_74);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_27);
lean_dec(x_23);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_1);
lean_ctor_set(x_90, 1, x_2);
x_91 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_91, 0, x_90);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_60);
lean_ctor_set(x_92, 1, x_61);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_59);
lean_ctor_set(x_93, 1, x_92);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_58);
lean_ctor_set(x_94, 1, x_93);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_91);
lean_ctor_set(x_95, 1, x_94);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_66);
return x_96;
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_27);
lean_dec(x_23);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_1);
lean_ctor_set(x_97, 1, x_2);
x_98 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_98, 0, x_97);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_60);
lean_ctor_set(x_99, 1, x_61);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_59);
lean_ctor_set(x_100, 1, x_99);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_58);
lean_ctor_set(x_101, 1, x_100);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_98);
lean_ctor_set(x_102, 1, x_101);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_66);
return x_103;
}
}
block_161:
{
uint8_t x_114; 
x_114 = l_Lean_Expr_isForall(x_106);
if (x_114 == 0)
{
lean_object* x_115; lean_object* x_116; uint8_t x_117; uint8_t x_118; uint8_t x_119; uint8_t x_120; uint8_t x_121; uint8_t x_122; uint8_t x_123; uint8_t x_124; uint8_t x_125; uint8_t x_126; uint8_t x_127; uint8_t x_128; uint8_t x_129; uint8_t x_130; uint8_t x_131; uint8_t x_132; uint8_t x_133; lean_object* x_134; uint8_t x_135; uint64_t x_136; lean_object* x_137; uint64_t x_138; uint64_t x_139; uint64_t x_140; uint8_t x_141; uint64_t x_142; uint64_t x_143; uint8_t x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; uint8_t x_152; lean_object* x_153; lean_object* x_154; 
x_115 = lean_box(0);
x_116 = lean_ctor_get(x_109, 0);
x_117 = lean_ctor_get_uint8(x_116, 0);
x_118 = lean_ctor_get_uint8(x_116, 1);
x_119 = lean_ctor_get_uint8(x_116, 2);
x_120 = lean_ctor_get_uint8(x_116, 3);
x_121 = lean_ctor_get_uint8(x_116, 4);
x_122 = lean_ctor_get_uint8(x_116, 5);
x_123 = lean_ctor_get_uint8(x_116, 6);
x_124 = lean_ctor_get_uint8(x_116, 7);
x_125 = lean_ctor_get_uint8(x_116, 8);
x_126 = lean_ctor_get_uint8(x_116, 10);
x_127 = lean_ctor_get_uint8(x_116, 11);
x_128 = lean_ctor_get_uint8(x_116, 12);
x_129 = lean_ctor_get_uint8(x_116, 13);
x_130 = lean_ctor_get_uint8(x_116, 14);
x_131 = lean_ctor_get_uint8(x_116, 15);
x_132 = lean_ctor_get_uint8(x_116, 16);
x_133 = lean_ctor_get_uint8(x_116, 17);
x_134 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_134, 0, x_117);
lean_ctor_set_uint8(x_134, 1, x_118);
lean_ctor_set_uint8(x_134, 2, x_119);
lean_ctor_set_uint8(x_134, 3, x_120);
lean_ctor_set_uint8(x_134, 4, x_121);
lean_ctor_set_uint8(x_134, 5, x_122);
lean_ctor_set_uint8(x_134, 6, x_123);
lean_ctor_set_uint8(x_134, 7, x_124);
lean_ctor_set_uint8(x_134, 8, x_125);
x_135 = lean_unbox(x_115);
lean_ctor_set_uint8(x_134, 9, x_135);
lean_ctor_set_uint8(x_134, 10, x_126);
lean_ctor_set_uint8(x_134, 11, x_127);
lean_ctor_set_uint8(x_134, 12, x_128);
lean_ctor_set_uint8(x_134, 13, x_129);
lean_ctor_set_uint8(x_134, 14, x_130);
lean_ctor_set_uint8(x_134, 15, x_131);
lean_ctor_set_uint8(x_134, 16, x_132);
lean_ctor_set_uint8(x_134, 17, x_133);
x_136 = lean_ctor_get_uint64(x_109, sizeof(void*)*7);
x_137 = lean_unsigned_to_nat(2u);
x_138 = lean_uint64_of_nat(x_137);
x_139 = lean_uint64_shift_right(x_136, x_138);
x_140 = lean_uint64_shift_left(x_139, x_138);
x_141 = lean_unbox(x_115);
x_142 = l_Lean_Meta_TransparencyMode_toUInt64(x_141);
x_143 = lean_uint64_lor(x_140, x_142);
x_144 = lean_ctor_get_uint8(x_109, sizeof(void*)*7 + 8);
x_145 = lean_ctor_get(x_109, 1);
x_146 = lean_ctor_get(x_109, 2);
x_147 = lean_ctor_get(x_109, 3);
x_148 = lean_ctor_get(x_109, 4);
x_149 = lean_ctor_get(x_109, 5);
x_150 = lean_ctor_get(x_109, 6);
x_151 = lean_ctor_get_uint8(x_109, sizeof(void*)*7 + 9);
x_152 = lean_ctor_get_uint8(x_109, sizeof(void*)*7 + 10);
lean_inc(x_150);
lean_inc(x_149);
lean_inc(x_148);
lean_inc(x_147);
lean_inc(x_146);
lean_inc(x_145);
x_153 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_153, 0, x_134);
lean_ctor_set(x_153, 1, x_145);
lean_ctor_set(x_153, 2, x_146);
lean_ctor_set(x_153, 3, x_147);
lean_ctor_set(x_153, 4, x_148);
lean_ctor_set(x_153, 5, x_149);
lean_ctor_set(x_153, 6, x_150);
lean_ctor_set_uint64(x_153, sizeof(void*)*7, x_143);
lean_ctor_set_uint8(x_153, sizeof(void*)*7 + 8, x_144);
lean_ctor_set_uint8(x_153, sizeof(void*)*7 + 9, x_151);
lean_ctor_set_uint8(x_153, sizeof(void*)*7 + 10, x_152);
lean_inc(x_112);
lean_inc(x_111);
lean_inc(x_110);
x_154 = lean_whnf(x_106, x_153, x_110, x_111, x_112, x_113);
if (lean_obj_tag(x_154) == 0)
{
lean_object* x_155; lean_object* x_156; 
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_154, 1);
lean_inc(x_156);
lean_dec(x_154);
x_58 = x_105;
x_59 = x_155;
x_60 = x_107;
x_61 = x_108;
x_62 = x_109;
x_63 = x_110;
x_64 = x_111;
x_65 = x_112;
x_66 = x_156;
goto block_104;
}
else
{
uint8_t x_157; 
lean_dec(x_112);
lean_dec(x_111);
lean_dec(x_110);
lean_dec(x_108);
lean_dec(x_107);
lean_dec(x_105);
lean_dec(x_27);
lean_dec(x_23);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_157 = !lean_is_exclusive(x_154);
if (x_157 == 0)
{
return x_154;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_158 = lean_ctor_get(x_154, 0);
x_159 = lean_ctor_get(x_154, 1);
lean_inc(x_159);
lean_inc(x_158);
lean_dec(x_154);
x_160 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_160, 0, x_158);
lean_ctor_set(x_160, 1, x_159);
return x_160;
}
}
}
else
{
x_58 = x_105;
x_59 = x_106;
x_60 = x_107;
x_61 = x_108;
x_62 = x_109;
x_63 = x_110;
x_64 = x_111;
x_65 = x_112;
x_66 = x_113;
goto block_104;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_addPPExplicitToExposeDiff_visit_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_addPPExplicitToExposeDiff_visit_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at___Lean_Meta_addPPExplicitToExposeDiff_visit_spec__1(lean_object* x_1, lean_object* x_2) {
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
x_11 = lean_name_eq(x_9, x_10);
return x_11;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at___Lean_Meta_addPPExplicitToExposeDiff_visit_spec__2(lean_object* x_1, lean_object* x_2) {
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
x_11 = l___private_Lean_Data_DeclarationRange_0__Lean_decEqDeclarationLocation____x40_Lean_Data_DeclarationRange___hyg_600_(x_9, x_10);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___Lean_Meta_withLocalDeclD___at___Lean_Meta_addPPExplicitToExposeDiff_visit_spec__3_spec__3___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_apply_6(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___Lean_Meta_withLocalDeclD___at___Lean_Meta_addPPExplicitToExposeDiff_visit_spec__3_spec__3___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___Lean_Meta_withLocalDeclD___at___Lean_Meta_addPPExplicitToExposeDiff_visit_spec__3_spec__3___redArg___lam__0), 7, 1);
lean_closure_set(x_11, 0, x_4);
x_12 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
return x_12;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_12);
if (x_17 == 0)
{
return x_12;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_12, 0);
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_12);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___Lean_Meta_withLocalDeclD___at___Lean_Meta_addPPExplicitToExposeDiff_visit_spec__3_spec__3(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_withLocalDecl___at___Lean_Meta_withLocalDeclD___at___Lean_Meta_addPPExplicitToExposeDiff_visit_spec__3_spec__3___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___Lean_Meta_addPPExplicitToExposeDiff_visit_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_9 = lean_box(0);
x_10 = lean_box(0);
x_11 = lean_unbox(x_9);
x_12 = lean_unbox(x_10);
x_13 = l_Lean_Meta_withLocalDecl___at___Lean_Meta_withLocalDeclD___at___Lean_Meta_addPPExplicitToExposeDiff_visit_spec__3_spec__3___redArg(x_1, x_11, x_2, x_3, x_12, x_4, x_5, x_6, x_7, x_8);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___Lean_Meta_addPPExplicitToExposeDiff_visit_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_withLocalDeclD___at___Lean_Meta_addPPExplicitToExposeDiff_visit_spec__3___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addPPExplicitToExposeDiff_visit___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_2);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addPPExplicitToExposeDiff_visit___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_addPPExplicitToExposeDiff_visit(x_1, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_14 = x_11;
} else {
 lean_dec_ref(x_11);
 x_14 = lean_box(0);
}
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_17 = x_12;
} else {
 lean_dec_ref(x_12);
 x_17 = lean_box(0);
}
if (lean_obj_tag(x_2) == 10)
{
lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; uint8_t x_28; 
x_24 = lean_ctor_get(x_2, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_2, 1);
lean_inc(x_25);
x_26 = lean_ptr_addr(x_25);
lean_dec(x_25);
x_27 = lean_ptr_addr(x_16);
x_28 = lean_usize_dec_eq(x_26, x_27);
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec(x_2);
x_29 = l_Lean_Expr_mdata___override(x_24, x_16);
x_18 = x_29;
goto block_23;
}
else
{
lean_dec(x_24);
lean_dec(x_16);
x_18 = x_2;
goto block_23;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_16);
lean_dec(x_2);
x_30 = lean_mk_string_unchecked("Lean.Expr", 9, 9);
x_31 = lean_mk_string_unchecked("_private.Lean.Expr.0.Lean.Expr.updateMData!Impl", 47, 47);
x_32 = lean_unsigned_to_nat(1802u);
x_33 = lean_unsigned_to_nat(17u);
x_34 = lean_mk_string_unchecked("mdata expected", 14, 14);
x_35 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_30, x_31, x_32, x_33, x_34);
lean_dec(x_34);
lean_dec(x_31);
lean_dec(x_30);
x_36 = l_panic___at___Lean_Expr_appFn_x21_spec__0(x_35);
x_18 = x_36;
goto block_23;
}
block_23:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
if (lean_is_scalar(x_17)) {
 x_19 = lean_alloc_ctor(0, 2, 0);
} else {
 x_19 = x_17;
}
lean_ctor_set(x_19, 0, x_15);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
if (lean_is_scalar(x_14)) {
 x_22 = lean_alloc_ctor(0, 2, 0);
} else {
 x_22 = x_14;
}
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_13);
return x_22;
}
}
else
{
uint8_t x_37; 
lean_dec(x_2);
x_37 = !lean_is_exclusive(x_11);
if (x_37 == 0)
{
return x_11;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_11, 0);
x_39 = lean_ctor_get(x_11, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_11);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addPPExplicitToExposeDiff_visit___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = l_Lean_Expr_bvar___override(x_1);
x_14 = lean_apply_7(x_2, x_13, x_3, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addPPExplicitToExposeDiff_visit___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = l_Lean_Expr_fvar___override(x_1);
x_14 = lean_apply_7(x_2, x_13, x_3, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addPPExplicitToExposeDiff_visit___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = l_Lean_Expr_mvar___override(x_1);
x_14 = lean_apply_7(x_2, x_13, x_3, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addPPExplicitToExposeDiff_visit___lam__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = l_Lean_Expr_sort___override(x_1);
x_14 = lean_apply_7(x_2, x_13, x_3, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addPPExplicitToExposeDiff_visit___lam__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Lean_Expr_const___override(x_1, x_2);
x_15 = lean_apply_7(x_3, x_14, x_4, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addPPExplicitToExposeDiff_visit___lam__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Lean_Expr_app___override(x_1, x_2);
x_15 = lean_apply_7(x_3, x_14, x_4, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addPPExplicitToExposeDiff_visit___lam__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_expr_instantiate1(x_1, x_9);
x_16 = lean_expr_instantiate1(x_2, x_9);
x_17 = l_Lean_Meta_addPPExplicitToExposeDiff_visit(x_15, x_16, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_19, 1);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_mk_empty_array_with_capacity(x_23);
x_25 = lean_array_push(x_24, x_9);
x_26 = lean_expr_abstract(x_21, x_25);
lean_dec(x_21);
x_27 = l_Lean_Expr_lam___override(x_3, x_4, x_26, x_5);
x_28 = lean_expr_abstract(x_22, x_25);
lean_dec(x_25);
lean_dec(x_22);
x_29 = l_Lean_Expr_lam___override(x_6, x_7, x_28, x_8);
lean_ctor_set(x_19, 1, x_29);
lean_ctor_set(x_19, 0, x_27);
return x_17;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_30 = lean_ctor_get(x_19, 0);
x_31 = lean_ctor_get(x_19, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_19);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_mk_empty_array_with_capacity(x_32);
x_34 = lean_array_push(x_33, x_9);
x_35 = lean_expr_abstract(x_30, x_34);
lean_dec(x_30);
x_36 = l_Lean_Expr_lam___override(x_3, x_4, x_35, x_5);
x_37 = lean_expr_abstract(x_31, x_34);
lean_dec(x_34);
lean_dec(x_31);
x_38 = l_Lean_Expr_lam___override(x_6, x_7, x_37, x_8);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_38);
lean_ctor_set(x_17, 0, x_39);
return x_17;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_40 = lean_ctor_get(x_17, 0);
x_41 = lean_ctor_get(x_17, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_17);
x_42 = lean_ctor_get(x_40, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_44 = x_40;
} else {
 lean_dec_ref(x_40);
 x_44 = lean_box(0);
}
x_45 = lean_unsigned_to_nat(1u);
x_46 = lean_mk_empty_array_with_capacity(x_45);
x_47 = lean_array_push(x_46, x_9);
x_48 = lean_expr_abstract(x_42, x_47);
lean_dec(x_42);
x_49 = l_Lean_Expr_lam___override(x_3, x_4, x_48, x_5);
x_50 = lean_expr_abstract(x_43, x_47);
lean_dec(x_47);
lean_dec(x_43);
x_51 = l_Lean_Expr_lam___override(x_6, x_7, x_50, x_8);
if (lean_is_scalar(x_44)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_44;
}
lean_ctor_set(x_52, 0, x_49);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_41);
return x_53;
}
}
else
{
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addPPExplicitToExposeDiff_visit___lam__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_expr_instantiate1(x_1, x_9);
x_16 = lean_expr_instantiate1(x_2, x_9);
x_17 = l_Lean_Meta_addPPExplicitToExposeDiff_visit(x_15, x_16, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_19, 1);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_mk_empty_array_with_capacity(x_23);
x_25 = lean_array_push(x_24, x_9);
x_26 = lean_expr_abstract(x_21, x_25);
lean_dec(x_21);
x_27 = l_Lean_Expr_forallE___override(x_3, x_4, x_26, x_5);
x_28 = lean_expr_abstract(x_22, x_25);
lean_dec(x_25);
lean_dec(x_22);
x_29 = l_Lean_Expr_forallE___override(x_6, x_7, x_28, x_8);
lean_ctor_set(x_19, 1, x_29);
lean_ctor_set(x_19, 0, x_27);
return x_17;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_30 = lean_ctor_get(x_19, 0);
x_31 = lean_ctor_get(x_19, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_19);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_mk_empty_array_with_capacity(x_32);
x_34 = lean_array_push(x_33, x_9);
x_35 = lean_expr_abstract(x_30, x_34);
lean_dec(x_30);
x_36 = l_Lean_Expr_forallE___override(x_3, x_4, x_35, x_5);
x_37 = lean_expr_abstract(x_31, x_34);
lean_dec(x_34);
lean_dec(x_31);
x_38 = l_Lean_Expr_forallE___override(x_6, x_7, x_37, x_8);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_38);
lean_ctor_set(x_17, 0, x_39);
return x_17;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_40 = lean_ctor_get(x_17, 0);
x_41 = lean_ctor_get(x_17, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_17);
x_42 = lean_ctor_get(x_40, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_44 = x_40;
} else {
 lean_dec_ref(x_40);
 x_44 = lean_box(0);
}
x_45 = lean_unsigned_to_nat(1u);
x_46 = lean_mk_empty_array_with_capacity(x_45);
x_47 = lean_array_push(x_46, x_9);
x_48 = lean_expr_abstract(x_42, x_47);
lean_dec(x_42);
x_49 = l_Lean_Expr_forallE___override(x_3, x_4, x_48, x_5);
x_50 = lean_expr_abstract(x_43, x_47);
lean_dec(x_47);
lean_dec(x_43);
x_51 = l_Lean_Expr_forallE___override(x_6, x_7, x_50, x_8);
if (lean_is_scalar(x_44)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_44;
}
lean_ctor_set(x_52, 0, x_49);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_41);
return x_53;
}
}
else
{
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addPPExplicitToExposeDiff_visit___lam__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, uint8_t x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; 
x_17 = l_Lean_Expr_letE___override(x_1, x_2, x_3, x_4, x_5);
x_18 = lean_apply_7(x_6, x_17, x_7, x_12, x_13, x_14, x_15, x_16);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addPPExplicitToExposeDiff_visit___lam__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = l_Lean_Expr_lit___override(x_1);
x_14 = lean_apply_7(x_2, x_13, x_3, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addPPExplicitToExposeDiff_visit___lam__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, uint8_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; 
x_15 = l_Lean_Expr_proj___override(x_1, x_2, x_3);
x_16 = lean_apply_7(x_4, x_15, x_5, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addPPExplicitToExposeDiff_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_18; lean_object* x_19; lean_object* x_23; lean_object* x_34; 
lean_inc(x_2);
lean_inc(x_1);
x_34 = lean_alloc_closure((void*)(l_Lean_Meta_addPPExplicitToExposeDiff_visit___lam__0___boxed), 9, 2);
lean_closure_set(x_34, 0, x_1);
lean_closure_set(x_34, 1, x_2);
switch (lean_obj_tag(x_1)) {
case 0:
{
switch (lean_obj_tag(x_2)) {
case 6:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; 
x_35 = lean_ctor_get(x_1, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_2, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_2, 1);
lean_inc(x_37);
x_38 = lean_ctor_get(x_2, 2);
lean_inc(x_38);
x_39 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_inc(x_2);
x_40 = l_Lean_Meta_addPPExplicitToExposeDiff_visit___lam__2(x_35, x_34, x_2, x_36, x_37, x_38, x_39, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
x_23 = x_40;
goto block_33;
}
case 7:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; 
x_41 = lean_ctor_get(x_1, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_2, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_2, 1);
lean_inc(x_43);
x_44 = lean_ctor_get(x_2, 2);
lean_inc(x_44);
x_45 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_inc(x_2);
x_46 = l_Lean_Meta_addPPExplicitToExposeDiff_visit___lam__2(x_41, x_34, x_2, x_42, x_43, x_44, x_45, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
x_23 = x_46;
goto block_33;
}
case 10:
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_34);
x_47 = lean_ctor_get(x_1, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_2, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_2, 1);
lean_inc(x_49);
x_50 = l_Lean_Expr_bvar___override(x_47);
lean_inc(x_2);
lean_inc(x_1);
x_51 = l_Lean_Meta_addPPExplicitToExposeDiff_visit___lam__1(x_1, x_2, x_50, x_48, x_49, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_48);
lean_dec(x_50);
x_23 = x_51;
goto block_33;
}
default: 
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_34);
x_52 = lean_ctor_get(x_1, 0);
lean_inc(x_52);
x_53 = l_Lean_Expr_bvar___override(x_52);
lean_inc(x_2);
lean_inc(x_1);
x_54 = l_Lean_Meta_addPPExplicitToExposeDiff_visit___lam__0(x_1, x_2, x_53, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_53);
x_23 = x_54;
goto block_33;
}
}
}
case 1:
{
switch (lean_obj_tag(x_2)) {
case 6:
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; 
x_55 = lean_ctor_get(x_1, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_2, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_2, 1);
lean_inc(x_57);
x_58 = lean_ctor_get(x_2, 2);
lean_inc(x_58);
x_59 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_inc(x_2);
x_60 = l_Lean_Meta_addPPExplicitToExposeDiff_visit___lam__3(x_55, x_34, x_2, x_56, x_57, x_58, x_59, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_56);
x_23 = x_60;
goto block_33;
}
case 7:
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; 
x_61 = lean_ctor_get(x_1, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_2, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_2, 1);
lean_inc(x_63);
x_64 = lean_ctor_get(x_2, 2);
lean_inc(x_64);
x_65 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_inc(x_2);
x_66 = l_Lean_Meta_addPPExplicitToExposeDiff_visit___lam__3(x_61, x_34, x_2, x_62, x_63, x_64, x_65, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_62);
x_23 = x_66;
goto block_33;
}
case 10:
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_34);
x_67 = lean_ctor_get(x_1, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_2, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_2, 1);
lean_inc(x_69);
x_70 = l_Lean_Expr_fvar___override(x_67);
lean_inc(x_2);
lean_inc(x_1);
x_71 = l_Lean_Meta_addPPExplicitToExposeDiff_visit___lam__1(x_1, x_2, x_70, x_68, x_69, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_68);
lean_dec(x_70);
x_23 = x_71;
goto block_33;
}
default: 
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_34);
x_72 = lean_ctor_get(x_1, 0);
lean_inc(x_72);
x_73 = l_Lean_Expr_fvar___override(x_72);
lean_inc(x_2);
lean_inc(x_1);
x_74 = l_Lean_Meta_addPPExplicitToExposeDiff_visit___lam__0(x_1, x_2, x_73, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_73);
x_23 = x_74;
goto block_33;
}
}
}
case 2:
{
switch (lean_obj_tag(x_2)) {
case 6:
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; lean_object* x_80; 
x_75 = lean_ctor_get(x_1, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_2, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_2, 1);
lean_inc(x_77);
x_78 = lean_ctor_get(x_2, 2);
lean_inc(x_78);
x_79 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_inc(x_2);
x_80 = l_Lean_Meta_addPPExplicitToExposeDiff_visit___lam__4(x_75, x_34, x_2, x_76, x_77, x_78, x_79, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_76);
x_23 = x_80;
goto block_33;
}
case 7:
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; lean_object* x_86; 
x_81 = lean_ctor_get(x_1, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_2, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_2, 1);
lean_inc(x_83);
x_84 = lean_ctor_get(x_2, 2);
lean_inc(x_84);
x_85 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_inc(x_2);
x_86 = l_Lean_Meta_addPPExplicitToExposeDiff_visit___lam__4(x_81, x_34, x_2, x_82, x_83, x_84, x_85, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_82);
x_23 = x_86;
goto block_33;
}
case 10:
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_34);
x_87 = lean_ctor_get(x_1, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_2, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_2, 1);
lean_inc(x_89);
x_90 = l_Lean_Expr_mvar___override(x_87);
lean_inc(x_2);
lean_inc(x_1);
x_91 = l_Lean_Meta_addPPExplicitToExposeDiff_visit___lam__1(x_1, x_2, x_90, x_88, x_89, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_88);
lean_dec(x_90);
x_23 = x_91;
goto block_33;
}
default: 
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_34);
x_92 = lean_ctor_get(x_1, 0);
lean_inc(x_92);
x_93 = l_Lean_Expr_mvar___override(x_92);
lean_inc(x_2);
lean_inc(x_1);
x_94 = l_Lean_Meta_addPPExplicitToExposeDiff_visit___lam__0(x_1, x_2, x_93, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_93);
x_23 = x_94;
goto block_33;
}
}
}
case 3:
{
switch (lean_obj_tag(x_2)) {
case 6:
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; lean_object* x_100; 
x_95 = lean_ctor_get(x_1, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_2, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_2, 1);
lean_inc(x_97);
x_98 = lean_ctor_get(x_2, 2);
lean_inc(x_98);
x_99 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_inc(x_2);
x_100 = l_Lean_Meta_addPPExplicitToExposeDiff_visit___lam__5(x_95, x_34, x_2, x_96, x_97, x_98, x_99, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_96);
x_23 = x_100;
goto block_33;
}
case 7:
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; lean_object* x_106; 
x_101 = lean_ctor_get(x_1, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_2, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_2, 1);
lean_inc(x_103);
x_104 = lean_ctor_get(x_2, 2);
lean_inc(x_104);
x_105 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_inc(x_2);
x_106 = l_Lean_Meta_addPPExplicitToExposeDiff_visit___lam__5(x_101, x_34, x_2, x_102, x_103, x_104, x_105, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_104);
lean_dec(x_103);
lean_dec(x_102);
x_23 = x_106;
goto block_33;
}
case 10:
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
lean_dec(x_34);
x_107 = lean_ctor_get(x_1, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_2, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_2, 1);
lean_inc(x_109);
x_110 = l_Lean_Expr_sort___override(x_107);
lean_inc(x_2);
lean_inc(x_1);
x_111 = l_Lean_Meta_addPPExplicitToExposeDiff_visit___lam__1(x_1, x_2, x_110, x_108, x_109, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_108);
lean_dec(x_110);
x_23 = x_111;
goto block_33;
}
default: 
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
lean_dec(x_34);
x_112 = lean_ctor_get(x_1, 0);
lean_inc(x_112);
x_113 = l_Lean_Expr_sort___override(x_112);
lean_inc(x_2);
lean_inc(x_1);
x_114 = l_Lean_Meta_addPPExplicitToExposeDiff_visit___lam__0(x_1, x_2, x_113, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_113);
x_23 = x_114;
goto block_33;
}
}
}
case 4:
{
switch (lean_obj_tag(x_2)) {
case 6:
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; uint8_t x_120; lean_object* x_121; 
x_115 = lean_ctor_get(x_1, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_1, 1);
lean_inc(x_116);
x_117 = lean_ctor_get(x_2, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_2, 1);
lean_inc(x_118);
x_119 = lean_ctor_get(x_2, 2);
lean_inc(x_119);
x_120 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_inc(x_2);
x_121 = l_Lean_Meta_addPPExplicitToExposeDiff_visit___lam__6(x_115, x_116, x_34, x_2, x_117, x_118, x_119, x_120, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_119);
lean_dec(x_118);
lean_dec(x_117);
x_23 = x_121;
goto block_33;
}
case 7:
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; lean_object* x_128; 
x_122 = lean_ctor_get(x_1, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_1, 1);
lean_inc(x_123);
x_124 = lean_ctor_get(x_2, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_2, 1);
lean_inc(x_125);
x_126 = lean_ctor_get(x_2, 2);
lean_inc(x_126);
x_127 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_inc(x_2);
x_128 = l_Lean_Meta_addPPExplicitToExposeDiff_visit___lam__6(x_122, x_123, x_34, x_2, x_124, x_125, x_126, x_127, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_126);
lean_dec(x_125);
lean_dec(x_124);
x_23 = x_128;
goto block_33;
}
case 10:
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
lean_dec(x_34);
x_129 = lean_ctor_get(x_1, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_1, 1);
lean_inc(x_130);
x_131 = lean_ctor_get(x_2, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_2, 1);
lean_inc(x_132);
x_133 = l_Lean_Expr_const___override(x_129, x_130);
lean_inc(x_2);
lean_inc(x_1);
x_134 = l_Lean_Meta_addPPExplicitToExposeDiff_visit___lam__1(x_1, x_2, x_133, x_131, x_132, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_131);
lean_dec(x_133);
x_23 = x_134;
goto block_33;
}
default: 
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
lean_dec(x_34);
x_135 = lean_ctor_get(x_1, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_1, 1);
lean_inc(x_136);
x_137 = l_Lean_Expr_const___override(x_135, x_136);
lean_inc(x_2);
lean_inc(x_1);
x_138 = l_Lean_Meta_addPPExplicitToExposeDiff_visit___lam__0(x_1, x_2, x_137, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_137);
x_23 = x_138;
goto block_33;
}
}
}
case 5:
{
switch (lean_obj_tag(x_2)) {
case 5:
{
lean_object* x_139; lean_object* x_140; uint8_t x_141; 
lean_dec(x_34);
x_139 = l_Lean_Expr_getAppNumArgs(x_1);
x_140 = l_Lean_Expr_getAppNumArgs(x_2);
x_141 = lean_nat_dec_eq(x_139, x_140);
if (x_141 == 0)
{
lean_object* x_142; lean_object* x_143; 
lean_dec(x_140);
lean_dec(x_139);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_1);
lean_ctor_set(x_142, 1, x_2);
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_7);
return x_143;
}
else
{
lean_object* x_144; uint8_t x_145; 
x_144 = l_Lean_Expr_getAppFn_x27(x_1);
x_145 = l_Lean_Expr_isMVar(x_144);
lean_dec(x_144);
if (x_145 == 0)
{
lean_object* x_146; uint8_t x_147; 
x_146 = l_Lean_Expr_getAppFn_x27(x_2);
x_147 = l_Lean_Expr_isMVar(x_146);
lean_dec(x_146);
if (x_147 == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_148 = l_Lean_Expr_getAppFn(x_1);
x_149 = l_Lean_Expr_getAppFn(x_2);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_149);
lean_inc(x_148);
x_150 = l_Lean_Meta_isExprDefEq(x_148, x_149, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; uint8_t x_152; 
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
x_152 = lean_unbox(x_151);
lean_dec(x_151);
if (x_152 == 0)
{
lean_object* x_153; lean_object* x_154; 
x_153 = lean_ctor_get(x_150, 1);
lean_inc(x_153);
lean_dec(x_150);
x_154 = l_Lean_Meta_addPPExplicitToExposeDiff_visit(x_148, x_149, x_3, x_4, x_5, x_6, x_153);
if (lean_obj_tag(x_154) == 0)
{
uint8_t x_155; 
x_155 = !lean_is_exclusive(x_154);
if (x_155 == 0)
{
lean_object* x_156; uint8_t x_157; 
x_156 = lean_ctor_get(x_154, 0);
x_157 = !lean_is_exclusive(x_156);
if (x_157 == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_158 = lean_ctor_get(x_156, 0);
x_159 = lean_ctor_get(x_156, 1);
x_160 = lean_box(0);
x_161 = l_Lean_Expr_sort___override(x_160);
lean_inc(x_161);
lean_inc(x_139);
x_162 = lean_mk_array(x_139, x_161);
x_163 = lean_unsigned_to_nat(1u);
x_164 = lean_nat_sub(x_139, x_163);
lean_dec(x_139);
x_165 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_162, x_164);
x_166 = l_Lean_mkAppN(x_158, x_165);
lean_dec(x_165);
lean_inc(x_140);
x_167 = lean_mk_array(x_140, x_161);
x_168 = lean_nat_sub(x_140, x_163);
lean_dec(x_140);
x_169 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_2, x_167, x_168);
x_170 = l_Lean_mkAppN(x_159, x_169);
lean_dec(x_169);
lean_ctor_set(x_156, 1, x_170);
lean_ctor_set(x_156, 0, x_166);
return x_154;
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_171 = lean_ctor_get(x_156, 0);
x_172 = lean_ctor_get(x_156, 1);
lean_inc(x_172);
lean_inc(x_171);
lean_dec(x_156);
x_173 = lean_box(0);
x_174 = l_Lean_Expr_sort___override(x_173);
lean_inc(x_174);
lean_inc(x_139);
x_175 = lean_mk_array(x_139, x_174);
x_176 = lean_unsigned_to_nat(1u);
x_177 = lean_nat_sub(x_139, x_176);
lean_dec(x_139);
x_178 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_175, x_177);
x_179 = l_Lean_mkAppN(x_171, x_178);
lean_dec(x_178);
lean_inc(x_140);
x_180 = lean_mk_array(x_140, x_174);
x_181 = lean_nat_sub(x_140, x_176);
lean_dec(x_140);
x_182 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_2, x_180, x_181);
x_183 = l_Lean_mkAppN(x_172, x_182);
lean_dec(x_182);
x_184 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_184, 0, x_179);
lean_ctor_set(x_184, 1, x_183);
lean_ctor_set(x_154, 0, x_184);
return x_154;
}
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_185 = lean_ctor_get(x_154, 0);
x_186 = lean_ctor_get(x_154, 1);
lean_inc(x_186);
lean_inc(x_185);
lean_dec(x_154);
x_187 = lean_ctor_get(x_185, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_185, 1);
lean_inc(x_188);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 lean_ctor_release(x_185, 1);
 x_189 = x_185;
} else {
 lean_dec_ref(x_185);
 x_189 = lean_box(0);
}
x_190 = lean_box(0);
x_191 = l_Lean_Expr_sort___override(x_190);
lean_inc(x_191);
lean_inc(x_139);
x_192 = lean_mk_array(x_139, x_191);
x_193 = lean_unsigned_to_nat(1u);
x_194 = lean_nat_sub(x_139, x_193);
lean_dec(x_139);
x_195 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_192, x_194);
x_196 = l_Lean_mkAppN(x_187, x_195);
lean_dec(x_195);
lean_inc(x_140);
x_197 = lean_mk_array(x_140, x_191);
x_198 = lean_nat_sub(x_140, x_193);
lean_dec(x_140);
x_199 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_2, x_197, x_198);
x_200 = l_Lean_mkAppN(x_188, x_199);
lean_dec(x_199);
if (lean_is_scalar(x_189)) {
 x_201 = lean_alloc_ctor(0, 2, 0);
} else {
 x_201 = x_189;
}
lean_ctor_set(x_201, 0, x_196);
lean_ctor_set(x_201, 1, x_200);
x_202 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_202, 0, x_201);
lean_ctor_set(x_202, 1, x_186);
return x_202;
}
}
else
{
lean_object* x_203; lean_object* x_204; 
lean_dec(x_140);
lean_dec(x_139);
x_203 = lean_ctor_get(x_154, 0);
lean_inc(x_203);
x_204 = lean_ctor_get(x_154, 1);
lean_inc(x_204);
lean_dec(x_154);
x_18 = x_203;
x_19 = x_204;
goto block_22;
}
}
else
{
uint8_t x_205; 
x_205 = !lean_is_exclusive(x_150);
if (x_205 == 0)
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_206 = lean_ctor_get(x_150, 1);
x_207 = lean_ctor_get(x_150, 0);
lean_dec(x_207);
x_208 = lean_box(0);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_148);
x_209 = lean_infer_type(x_148, x_3, x_4, x_5, x_6, x_206);
if (lean_obj_tag(x_209) == 0)
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_210 = lean_ctor_get(x_209, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_209, 1);
lean_inc(x_211);
if (lean_is_exclusive(x_209)) {
 lean_ctor_release(x_209, 0);
 lean_ctor_release(x_209, 1);
 x_212 = x_209;
} else {
 lean_dec_ref(x_209);
 x_212 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_149);
x_213 = lean_infer_type(x_149, x_3, x_4, x_5, x_6, x_211);
if (lean_obj_tag(x_213) == 0)
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_214 = lean_ctor_get(x_213, 0);
lean_inc(x_214);
x_215 = lean_ctor_get(x_213, 1);
lean_inc(x_215);
if (lean_is_exclusive(x_213)) {
 lean_ctor_release(x_213, 0);
 lean_ctor_release(x_213, 1);
 x_216 = x_213;
} else {
 lean_dec_ref(x_213);
 x_216 = lean_box(0);
}
x_217 = l_Lean_Expr_sort___override(x_208);
lean_inc(x_217);
lean_inc(x_139);
x_218 = lean_mk_array(x_139, x_217);
x_219 = lean_unsigned_to_nat(1u);
x_220 = lean_nat_sub(x_139, x_219);
lean_dec(x_139);
lean_inc(x_1);
x_221 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_218, x_220);
x_222 = lean_box(0);
x_223 = lean_unsigned_to_nat(0u);
x_224 = lean_array_get_size(x_221);
lean_inc(x_224);
x_225 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_225, 0, x_223);
lean_ctor_set(x_225, 1, x_224);
lean_ctor_set(x_225, 2, x_219);
x_226 = lean_box(0);
x_227 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_227, 0, x_222);
lean_ctor_set(x_227, 1, x_222);
x_228 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_228, 0, x_214);
lean_ctor_set(x_228, 1, x_227);
x_229 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_229, 0, x_210);
lean_ctor_set(x_229, 1, x_228);
x_230 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_230, 0, x_226);
lean_ctor_set(x_230, 1, x_229);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_231 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_addPPExplicitToExposeDiff_visit_spec__0___redArg(x_1, x_2, x_225, x_230, x_223, x_3, x_4, x_5, x_6, x_215);
lean_dec(x_225);
if (lean_obj_tag(x_231) == 0)
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_288; lean_object* x_306; uint8_t x_307; lean_object* x_315; lean_object* x_324; 
x_232 = lean_ctor_get(x_231, 0);
lean_inc(x_232);
x_233 = lean_ctor_get(x_232, 1);
lean_inc(x_233);
x_234 = lean_ctor_get(x_233, 1);
lean_inc(x_234);
if (lean_is_exclusive(x_233)) {
 lean_ctor_release(x_233, 0);
 lean_ctor_release(x_233, 1);
 x_235 = x_233;
} else {
 lean_dec_ref(x_233);
 x_235 = lean_box(0);
}
x_236 = lean_ctor_get(x_234, 1);
lean_inc(x_236);
if (lean_is_exclusive(x_234)) {
 lean_ctor_release(x_234, 0);
 lean_ctor_release(x_234, 1);
 x_237 = x_234;
} else {
 lean_dec_ref(x_234);
 x_237 = lean_box(0);
}
x_238 = lean_ctor_get(x_231, 1);
lean_inc(x_238);
if (lean_is_exclusive(x_231)) {
 lean_ctor_release(x_231, 0);
 lean_ctor_release(x_231, 1);
 x_239 = x_231;
} else {
 lean_dec_ref(x_231);
 x_239 = lean_box(0);
}
x_240 = lean_ctor_get(x_236, 0);
lean_inc(x_240);
x_241 = lean_ctor_get(x_236, 1);
lean_inc(x_241);
if (lean_is_exclusive(x_236)) {
 lean_ctor_release(x_236, 0);
 lean_ctor_release(x_236, 1);
 x_242 = x_236;
} else {
 lean_dec_ref(x_236);
 x_242 = lean_box(0);
}
lean_inc(x_140);
x_276 = lean_mk_array(x_140, x_217);
x_277 = lean_nat_sub(x_140, x_219);
lean_dec(x_140);
lean_inc(x_2);
x_278 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_2, x_276, x_277);
x_324 = lean_ctor_get(x_232, 0);
lean_inc(x_324);
lean_dec(x_232);
if (lean_obj_tag(x_324) == 0)
{
lean_free_object(x_150);
if (lean_obj_tag(x_148) == 4)
{
if (lean_obj_tag(x_149) == 4)
{
lean_object* x_325; lean_object* x_326; uint8_t x_327; 
x_325 = lean_ctor_get(x_148, 0);
lean_inc(x_325);
x_326 = lean_ctor_get(x_149, 0);
lean_inc(x_326);
x_327 = lean_name_eq(x_325, x_326);
lean_dec(x_326);
if (x_327 == 0)
{
lean_object* x_328; 
lean_dec(x_325);
x_328 = lean_box(0);
x_315 = x_328;
goto block_323;
}
else
{
lean_object* x_329; 
x_329 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_329, 0, x_325);
x_315 = x_329;
goto block_323;
}
}
else
{
lean_object* x_330; 
x_330 = lean_box(0);
x_315 = x_330;
goto block_323;
}
}
else
{
lean_object* x_331; 
x_331 = lean_box(0);
x_315 = x_331;
goto block_323;
}
}
else
{
lean_object* x_332; 
lean_dec(x_278);
lean_dec(x_242);
lean_dec(x_241);
lean_dec(x_240);
lean_dec(x_239);
lean_dec(x_237);
lean_dec(x_235);
lean_dec(x_224);
lean_dec(x_221);
lean_dec(x_216);
lean_dec(x_212);
lean_dec(x_149);
lean_dec(x_148);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_332 = lean_ctor_get(x_324, 0);
lean_inc(x_332);
lean_dec(x_324);
lean_ctor_set(x_150, 1, x_238);
lean_ctor_set(x_150, 0, x_332);
return x_150;
}
block_254:
{
lean_object* x_246; lean_object* x_247; 
x_246 = l_Lean_mkAppN(x_148, x_243);
lean_dec(x_243);
x_247 = l_Lean_mkAppN(x_149, x_244);
lean_dec(x_244);
if (lean_obj_tag(x_240) == 0)
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
x_248 = l_Lean_Expr_setPPExplicit(x_246, x_141);
x_249 = l_Lean_Expr_setPPExplicit(x_247, x_141);
if (lean_is_scalar(x_242)) {
 x_250 = lean_alloc_ctor(0, 2, 0);
} else {
 x_250 = x_242;
}
lean_ctor_set(x_250, 0, x_248);
lean_ctor_set(x_250, 1, x_249);
if (lean_is_scalar(x_239)) {
 x_251 = lean_alloc_ctor(0, 2, 0);
} else {
 x_251 = x_239;
}
lean_ctor_set(x_251, 0, x_250);
lean_ctor_set(x_251, 1, x_245);
return x_251;
}
else
{
lean_object* x_252; lean_object* x_253; 
lean_dec(x_240);
if (lean_is_scalar(x_242)) {
 x_252 = lean_alloc_ctor(0, 2, 0);
} else {
 x_252 = x_242;
}
lean_ctor_set(x_252, 0, x_246);
lean_ctor_set(x_252, 1, x_247);
if (lean_is_scalar(x_239)) {
 x_253 = lean_alloc_ctor(0, 2, 0);
} else {
 x_253 = x_239;
}
lean_ctor_set(x_253, 0, x_252);
lean_ctor_set(x_253, 1, x_245);
return x_253;
}
}
block_275:
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; 
x_263 = l_Lean_instInhabitedExpr;
x_264 = lean_array_get(x_263, x_257, x_262);
x_265 = lean_array_get(x_263, x_256, x_262);
x_266 = l_Lean_Meta_addPPExplicitToExposeDiff_visit(x_264, x_265, x_255, x_261, x_260, x_258, x_259);
if (lean_obj_tag(x_266) == 0)
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; 
lean_dec(x_2);
lean_dec(x_1);
x_267 = lean_ctor_get(x_266, 0);
lean_inc(x_267);
x_268 = lean_ctor_get(x_266, 1);
lean_inc(x_268);
lean_dec(x_266);
x_269 = lean_ctor_get(x_267, 0);
lean_inc(x_269);
x_270 = lean_ctor_get(x_267, 1);
lean_inc(x_270);
lean_dec(x_267);
x_271 = lean_array_set(x_257, x_262, x_269);
x_272 = lean_array_set(x_256, x_262, x_270);
lean_dec(x_262);
x_243 = x_271;
x_244 = x_272;
x_245 = x_268;
goto block_254;
}
else
{
lean_object* x_273; lean_object* x_274; 
lean_dec(x_262);
lean_dec(x_257);
lean_dec(x_256);
lean_dec(x_242);
lean_dec(x_240);
lean_dec(x_239);
lean_dec(x_149);
lean_dec(x_148);
x_273 = lean_ctor_get(x_266, 0);
lean_inc(x_273);
x_274 = lean_ctor_get(x_266, 1);
lean_inc(x_274);
lean_dec(x_266);
x_18 = x_273;
x_19 = x_274;
goto block_22;
}
}
block_287:
{
if (lean_obj_tag(x_240) == 0)
{
if (lean_obj_tag(x_241) == 0)
{
lean_dec(x_283);
lean_dec(x_282);
lean_dec(x_281);
lean_dec(x_280);
lean_dec(x_2);
lean_dec(x_1);
x_243 = x_279;
x_244 = x_278;
x_245 = x_284;
goto block_254;
}
else
{
lean_object* x_285; 
x_285 = lean_ctor_get(x_241, 0);
lean_inc(x_285);
lean_dec(x_241);
x_255 = x_280;
x_256 = x_278;
x_257 = x_279;
x_258 = x_283;
x_259 = x_284;
x_260 = x_282;
x_261 = x_281;
x_262 = x_285;
goto block_275;
}
}
else
{
lean_object* x_286; 
lean_dec(x_241);
x_286 = lean_ctor_get(x_240, 0);
lean_inc(x_286);
x_255 = x_280;
x_256 = x_278;
x_257 = x_279;
x_258 = x_283;
x_259 = x_284;
x_260 = x_282;
x_261 = x_281;
x_262 = x_286;
goto block_275;
}
}
block_305:
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; uint8_t x_292; 
x_289 = lean_mk_string_unchecked("sorryAx", 7, 7);
x_290 = l_Lean_Name_mkStr1(x_289);
x_291 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_291, 0, x_290);
x_292 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at___Lean_Meta_addPPExplicitToExposeDiff_visit_spec__1(x_288, x_291);
lean_dec(x_291);
lean_dec(x_288);
if (x_292 == 0)
{
lean_dec(x_237);
lean_dec(x_216);
x_279 = x_221;
x_280 = x_3;
x_281 = x_4;
x_282 = x_5;
x_283 = x_6;
x_284 = x_238;
goto block_287;
}
else
{
lean_object* x_293; 
x_293 = l_Lean_Meta_isLabeledSorry_x3f(x_1);
if (lean_obj_tag(x_293) == 0)
{
lean_dec(x_237);
lean_dec(x_216);
x_279 = x_221;
x_280 = x_3;
x_281 = x_4;
x_282 = x_5;
x_283 = x_6;
x_284 = x_238;
goto block_287;
}
else
{
lean_object* x_294; lean_object* x_295; 
x_294 = lean_ctor_get(x_293, 0);
lean_inc(x_294);
lean_dec(x_293);
x_295 = l_Lean_Meta_isLabeledSorry_x3f(x_2);
if (lean_obj_tag(x_295) == 0)
{
lean_dec(x_294);
lean_dec(x_237);
lean_dec(x_216);
x_279 = x_221;
x_280 = x_3;
x_281 = x_4;
x_282 = x_5;
x_283 = x_6;
x_284 = x_238;
goto block_287;
}
else
{
lean_object* x_296; uint8_t x_297; 
x_296 = lean_ctor_get(x_295, 0);
lean_inc(x_296);
lean_dec(x_295);
x_297 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at___Lean_Meta_addPPExplicitToExposeDiff_visit_spec__2(x_294, x_296);
lean_dec(x_296);
lean_dec(x_294);
if (x_297 == 0)
{
if (x_292 == 0)
{
lean_dec(x_237);
lean_dec(x_216);
x_279 = x_221;
x_280 = x_3;
x_281 = x_4;
x_282 = x_5;
x_283 = x_6;
x_284 = x_238;
goto block_287;
}
else
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; 
lean_dec(x_278);
lean_dec(x_242);
lean_dec(x_241);
lean_dec(x_240);
lean_dec(x_239);
lean_dec(x_221);
lean_dec(x_149);
lean_dec(x_148);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_298 = lean_mk_string_unchecked("pp", 2, 2);
x_299 = lean_mk_string_unchecked("sorrySource", 11, 11);
x_300 = l_Lean_Name_mkStr2(x_298, x_299);
lean_inc(x_300);
x_301 = l_Lean_Expr_setOption___at___Lean_Expr_setPPExplicit_spec__0(x_1, x_300, x_141);
x_302 = l_Lean_Expr_setOption___at___Lean_Expr_setPPExplicit_spec__0(x_2, x_300, x_141);
if (lean_is_scalar(x_237)) {
 x_303 = lean_alloc_ctor(0, 2, 0);
} else {
 x_303 = x_237;
}
lean_ctor_set(x_303, 0, x_301);
lean_ctor_set(x_303, 1, x_302);
if (lean_is_scalar(x_216)) {
 x_304 = lean_alloc_ctor(0, 2, 0);
} else {
 x_304 = x_216;
}
lean_ctor_set(x_304, 0, x_303);
lean_ctor_set(x_304, 1, x_238);
return x_304;
}
}
else
{
lean_dec(x_237);
lean_dec(x_216);
x_279 = x_221;
x_280 = x_3;
x_281 = x_4;
x_282 = x_5;
x_283 = x_6;
x_284 = x_238;
goto block_287;
}
}
}
}
}
block_314:
{
if (x_307 == 0)
{
lean_dec(x_235);
lean_dec(x_212);
x_288 = x_306;
goto block_305;
}
else
{
lean_object* x_308; uint8_t x_309; 
x_308 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_308, 0, x_223);
x_309 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at_____private_Lean_Meta_Basic_0__Lean_Meta_beqInfoCacheKey____x40_Lean_Meta_Basic___hyg_1324__spec__0(x_241, x_308);
lean_dec(x_308);
if (x_309 == 0)
{
lean_dec(x_235);
lean_dec(x_212);
x_288 = x_306;
goto block_305;
}
else
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; 
lean_dec(x_306);
lean_dec(x_278);
lean_dec(x_242);
lean_dec(x_241);
lean_dec(x_240);
lean_dec(x_239);
lean_dec(x_237);
lean_dec(x_221);
lean_dec(x_216);
lean_dec(x_149);
lean_dec(x_148);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_310 = l_Lean_Expr_setPPNumericTypes(x_1, x_141);
x_311 = l_Lean_Expr_setPPNumericTypes(x_2, x_141);
if (lean_is_scalar(x_235)) {
 x_312 = lean_alloc_ctor(0, 2, 0);
} else {
 x_312 = x_235;
}
lean_ctor_set(x_312, 0, x_310);
lean_ctor_set(x_312, 1, x_311);
if (lean_is_scalar(x_212)) {
 x_313 = lean_alloc_ctor(0, 2, 0);
} else {
 x_313 = x_212;
}
lean_ctor_set(x_313, 0, x_312);
lean_ctor_set(x_313, 1, x_238);
return x_313;
}
}
}
block_323:
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; uint8_t x_320; 
x_316 = lean_mk_string_unchecked("OfNat", 5, 5);
x_317 = lean_mk_string_unchecked("ofNat", 5, 5);
x_318 = l_Lean_Name_mkStr2(x_316, x_317);
x_319 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_319, 0, x_318);
x_320 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at___Lean_Meta_addPPExplicitToExposeDiff_visit_spec__1(x_315, x_319);
lean_dec(x_319);
if (x_320 == 0)
{
lean_dec(x_224);
x_306 = x_315;
x_307 = x_320;
goto block_314;
}
else
{
lean_object* x_321; uint8_t x_322; 
x_321 = lean_unsigned_to_nat(3u);
x_322 = lean_nat_dec_le(x_321, x_224);
lean_dec(x_224);
x_306 = x_315;
x_307 = x_322;
goto block_314;
}
}
}
else
{
lean_object* x_333; lean_object* x_334; 
lean_dec(x_224);
lean_dec(x_221);
lean_dec(x_217);
lean_dec(x_216);
lean_dec(x_212);
lean_free_object(x_150);
lean_dec(x_149);
lean_dec(x_148);
lean_dec(x_140);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_333 = lean_ctor_get(x_231, 0);
lean_inc(x_333);
x_334 = lean_ctor_get(x_231, 1);
lean_inc(x_334);
lean_dec(x_231);
x_18 = x_333;
x_19 = x_334;
goto block_22;
}
}
else
{
lean_object* x_335; lean_object* x_336; 
lean_dec(x_212);
lean_dec(x_210);
lean_free_object(x_150);
lean_dec(x_149);
lean_dec(x_148);
lean_dec(x_140);
lean_dec(x_139);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_335 = lean_ctor_get(x_213, 0);
lean_inc(x_335);
x_336 = lean_ctor_get(x_213, 1);
lean_inc(x_336);
lean_dec(x_213);
x_18 = x_335;
x_19 = x_336;
goto block_22;
}
}
else
{
lean_object* x_337; lean_object* x_338; 
lean_free_object(x_150);
lean_dec(x_149);
lean_dec(x_148);
lean_dec(x_140);
lean_dec(x_139);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_337 = lean_ctor_get(x_209, 0);
lean_inc(x_337);
x_338 = lean_ctor_get(x_209, 1);
lean_inc(x_338);
lean_dec(x_209);
x_18 = x_337;
x_19 = x_338;
goto block_22;
}
}
else
{
lean_object* x_339; lean_object* x_340; lean_object* x_341; 
x_339 = lean_ctor_get(x_150, 1);
lean_inc(x_339);
lean_dec(x_150);
x_340 = lean_box(0);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_148);
x_341 = lean_infer_type(x_148, x_3, x_4, x_5, x_6, x_339);
if (lean_obj_tag(x_341) == 0)
{
lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; 
x_342 = lean_ctor_get(x_341, 0);
lean_inc(x_342);
x_343 = lean_ctor_get(x_341, 1);
lean_inc(x_343);
if (lean_is_exclusive(x_341)) {
 lean_ctor_release(x_341, 0);
 lean_ctor_release(x_341, 1);
 x_344 = x_341;
} else {
 lean_dec_ref(x_341);
 x_344 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_149);
x_345 = lean_infer_type(x_149, x_3, x_4, x_5, x_6, x_343);
if (lean_obj_tag(x_345) == 0)
{
lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; 
x_346 = lean_ctor_get(x_345, 0);
lean_inc(x_346);
x_347 = lean_ctor_get(x_345, 1);
lean_inc(x_347);
if (lean_is_exclusive(x_345)) {
 lean_ctor_release(x_345, 0);
 lean_ctor_release(x_345, 1);
 x_348 = x_345;
} else {
 lean_dec_ref(x_345);
 x_348 = lean_box(0);
}
x_349 = l_Lean_Expr_sort___override(x_340);
lean_inc(x_349);
lean_inc(x_139);
x_350 = lean_mk_array(x_139, x_349);
x_351 = lean_unsigned_to_nat(1u);
x_352 = lean_nat_sub(x_139, x_351);
lean_dec(x_139);
lean_inc(x_1);
x_353 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_350, x_352);
x_354 = lean_box(0);
x_355 = lean_unsigned_to_nat(0u);
x_356 = lean_array_get_size(x_353);
lean_inc(x_356);
x_357 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_357, 0, x_355);
lean_ctor_set(x_357, 1, x_356);
lean_ctor_set(x_357, 2, x_351);
x_358 = lean_box(0);
x_359 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_359, 0, x_354);
lean_ctor_set(x_359, 1, x_354);
x_360 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_360, 0, x_346);
lean_ctor_set(x_360, 1, x_359);
x_361 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_361, 0, x_342);
lean_ctor_set(x_361, 1, x_360);
x_362 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_362, 0, x_358);
lean_ctor_set(x_362, 1, x_361);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_363 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_addPPExplicitToExposeDiff_visit_spec__0___redArg(x_1, x_2, x_357, x_362, x_355, x_3, x_4, x_5, x_6, x_347);
lean_dec(x_357);
if (lean_obj_tag(x_363) == 0)
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_420; lean_object* x_438; uint8_t x_439; lean_object* x_447; lean_object* x_456; 
x_364 = lean_ctor_get(x_363, 0);
lean_inc(x_364);
x_365 = lean_ctor_get(x_364, 1);
lean_inc(x_365);
x_366 = lean_ctor_get(x_365, 1);
lean_inc(x_366);
if (lean_is_exclusive(x_365)) {
 lean_ctor_release(x_365, 0);
 lean_ctor_release(x_365, 1);
 x_367 = x_365;
} else {
 lean_dec_ref(x_365);
 x_367 = lean_box(0);
}
x_368 = lean_ctor_get(x_366, 1);
lean_inc(x_368);
if (lean_is_exclusive(x_366)) {
 lean_ctor_release(x_366, 0);
 lean_ctor_release(x_366, 1);
 x_369 = x_366;
} else {
 lean_dec_ref(x_366);
 x_369 = lean_box(0);
}
x_370 = lean_ctor_get(x_363, 1);
lean_inc(x_370);
if (lean_is_exclusive(x_363)) {
 lean_ctor_release(x_363, 0);
 lean_ctor_release(x_363, 1);
 x_371 = x_363;
} else {
 lean_dec_ref(x_363);
 x_371 = lean_box(0);
}
x_372 = lean_ctor_get(x_368, 0);
lean_inc(x_372);
x_373 = lean_ctor_get(x_368, 1);
lean_inc(x_373);
if (lean_is_exclusive(x_368)) {
 lean_ctor_release(x_368, 0);
 lean_ctor_release(x_368, 1);
 x_374 = x_368;
} else {
 lean_dec_ref(x_368);
 x_374 = lean_box(0);
}
lean_inc(x_140);
x_408 = lean_mk_array(x_140, x_349);
x_409 = lean_nat_sub(x_140, x_351);
lean_dec(x_140);
lean_inc(x_2);
x_410 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_2, x_408, x_409);
x_456 = lean_ctor_get(x_364, 0);
lean_inc(x_456);
lean_dec(x_364);
if (lean_obj_tag(x_456) == 0)
{
if (lean_obj_tag(x_148) == 4)
{
if (lean_obj_tag(x_149) == 4)
{
lean_object* x_457; lean_object* x_458; uint8_t x_459; 
x_457 = lean_ctor_get(x_148, 0);
lean_inc(x_457);
x_458 = lean_ctor_get(x_149, 0);
lean_inc(x_458);
x_459 = lean_name_eq(x_457, x_458);
lean_dec(x_458);
if (x_459 == 0)
{
lean_object* x_460; 
lean_dec(x_457);
x_460 = lean_box(0);
x_447 = x_460;
goto block_455;
}
else
{
lean_object* x_461; 
x_461 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_461, 0, x_457);
x_447 = x_461;
goto block_455;
}
}
else
{
lean_object* x_462; 
x_462 = lean_box(0);
x_447 = x_462;
goto block_455;
}
}
else
{
lean_object* x_463; 
x_463 = lean_box(0);
x_447 = x_463;
goto block_455;
}
}
else
{
lean_object* x_464; lean_object* x_465; 
lean_dec(x_410);
lean_dec(x_374);
lean_dec(x_373);
lean_dec(x_372);
lean_dec(x_371);
lean_dec(x_369);
lean_dec(x_367);
lean_dec(x_356);
lean_dec(x_353);
lean_dec(x_348);
lean_dec(x_344);
lean_dec(x_149);
lean_dec(x_148);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_464 = lean_ctor_get(x_456, 0);
lean_inc(x_464);
lean_dec(x_456);
x_465 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_465, 0, x_464);
lean_ctor_set(x_465, 1, x_370);
return x_465;
}
block_386:
{
lean_object* x_378; lean_object* x_379; 
x_378 = l_Lean_mkAppN(x_148, x_375);
lean_dec(x_375);
x_379 = l_Lean_mkAppN(x_149, x_376);
lean_dec(x_376);
if (lean_obj_tag(x_372) == 0)
{
lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; 
x_380 = l_Lean_Expr_setPPExplicit(x_378, x_141);
x_381 = l_Lean_Expr_setPPExplicit(x_379, x_141);
if (lean_is_scalar(x_374)) {
 x_382 = lean_alloc_ctor(0, 2, 0);
} else {
 x_382 = x_374;
}
lean_ctor_set(x_382, 0, x_380);
lean_ctor_set(x_382, 1, x_381);
if (lean_is_scalar(x_371)) {
 x_383 = lean_alloc_ctor(0, 2, 0);
} else {
 x_383 = x_371;
}
lean_ctor_set(x_383, 0, x_382);
lean_ctor_set(x_383, 1, x_377);
return x_383;
}
else
{
lean_object* x_384; lean_object* x_385; 
lean_dec(x_372);
if (lean_is_scalar(x_374)) {
 x_384 = lean_alloc_ctor(0, 2, 0);
} else {
 x_384 = x_374;
}
lean_ctor_set(x_384, 0, x_378);
lean_ctor_set(x_384, 1, x_379);
if (lean_is_scalar(x_371)) {
 x_385 = lean_alloc_ctor(0, 2, 0);
} else {
 x_385 = x_371;
}
lean_ctor_set(x_385, 0, x_384);
lean_ctor_set(x_385, 1, x_377);
return x_385;
}
}
block_407:
{
lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; 
x_395 = l_Lean_instInhabitedExpr;
x_396 = lean_array_get(x_395, x_389, x_394);
x_397 = lean_array_get(x_395, x_388, x_394);
x_398 = l_Lean_Meta_addPPExplicitToExposeDiff_visit(x_396, x_397, x_387, x_393, x_392, x_390, x_391);
if (lean_obj_tag(x_398) == 0)
{
lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; 
lean_dec(x_2);
lean_dec(x_1);
x_399 = lean_ctor_get(x_398, 0);
lean_inc(x_399);
x_400 = lean_ctor_get(x_398, 1);
lean_inc(x_400);
lean_dec(x_398);
x_401 = lean_ctor_get(x_399, 0);
lean_inc(x_401);
x_402 = lean_ctor_get(x_399, 1);
lean_inc(x_402);
lean_dec(x_399);
x_403 = lean_array_set(x_389, x_394, x_401);
x_404 = lean_array_set(x_388, x_394, x_402);
lean_dec(x_394);
x_375 = x_403;
x_376 = x_404;
x_377 = x_400;
goto block_386;
}
else
{
lean_object* x_405; lean_object* x_406; 
lean_dec(x_394);
lean_dec(x_389);
lean_dec(x_388);
lean_dec(x_374);
lean_dec(x_372);
lean_dec(x_371);
lean_dec(x_149);
lean_dec(x_148);
x_405 = lean_ctor_get(x_398, 0);
lean_inc(x_405);
x_406 = lean_ctor_get(x_398, 1);
lean_inc(x_406);
lean_dec(x_398);
x_18 = x_405;
x_19 = x_406;
goto block_22;
}
}
block_419:
{
if (lean_obj_tag(x_372) == 0)
{
if (lean_obj_tag(x_373) == 0)
{
lean_dec(x_415);
lean_dec(x_414);
lean_dec(x_413);
lean_dec(x_412);
lean_dec(x_2);
lean_dec(x_1);
x_375 = x_411;
x_376 = x_410;
x_377 = x_416;
goto block_386;
}
else
{
lean_object* x_417; 
x_417 = lean_ctor_get(x_373, 0);
lean_inc(x_417);
lean_dec(x_373);
x_387 = x_412;
x_388 = x_410;
x_389 = x_411;
x_390 = x_415;
x_391 = x_416;
x_392 = x_414;
x_393 = x_413;
x_394 = x_417;
goto block_407;
}
}
else
{
lean_object* x_418; 
lean_dec(x_373);
x_418 = lean_ctor_get(x_372, 0);
lean_inc(x_418);
x_387 = x_412;
x_388 = x_410;
x_389 = x_411;
x_390 = x_415;
x_391 = x_416;
x_392 = x_414;
x_393 = x_413;
x_394 = x_418;
goto block_407;
}
}
block_437:
{
lean_object* x_421; lean_object* x_422; lean_object* x_423; uint8_t x_424; 
x_421 = lean_mk_string_unchecked("sorryAx", 7, 7);
x_422 = l_Lean_Name_mkStr1(x_421);
x_423 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_423, 0, x_422);
x_424 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at___Lean_Meta_addPPExplicitToExposeDiff_visit_spec__1(x_420, x_423);
lean_dec(x_423);
lean_dec(x_420);
if (x_424 == 0)
{
lean_dec(x_369);
lean_dec(x_348);
x_411 = x_353;
x_412 = x_3;
x_413 = x_4;
x_414 = x_5;
x_415 = x_6;
x_416 = x_370;
goto block_419;
}
else
{
lean_object* x_425; 
x_425 = l_Lean_Meta_isLabeledSorry_x3f(x_1);
if (lean_obj_tag(x_425) == 0)
{
lean_dec(x_369);
lean_dec(x_348);
x_411 = x_353;
x_412 = x_3;
x_413 = x_4;
x_414 = x_5;
x_415 = x_6;
x_416 = x_370;
goto block_419;
}
else
{
lean_object* x_426; lean_object* x_427; 
x_426 = lean_ctor_get(x_425, 0);
lean_inc(x_426);
lean_dec(x_425);
x_427 = l_Lean_Meta_isLabeledSorry_x3f(x_2);
if (lean_obj_tag(x_427) == 0)
{
lean_dec(x_426);
lean_dec(x_369);
lean_dec(x_348);
x_411 = x_353;
x_412 = x_3;
x_413 = x_4;
x_414 = x_5;
x_415 = x_6;
x_416 = x_370;
goto block_419;
}
else
{
lean_object* x_428; uint8_t x_429; 
x_428 = lean_ctor_get(x_427, 0);
lean_inc(x_428);
lean_dec(x_427);
x_429 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at___Lean_Meta_addPPExplicitToExposeDiff_visit_spec__2(x_426, x_428);
lean_dec(x_428);
lean_dec(x_426);
if (x_429 == 0)
{
if (x_424 == 0)
{
lean_dec(x_369);
lean_dec(x_348);
x_411 = x_353;
x_412 = x_3;
x_413 = x_4;
x_414 = x_5;
x_415 = x_6;
x_416 = x_370;
goto block_419;
}
else
{
lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; 
lean_dec(x_410);
lean_dec(x_374);
lean_dec(x_373);
lean_dec(x_372);
lean_dec(x_371);
lean_dec(x_353);
lean_dec(x_149);
lean_dec(x_148);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_430 = lean_mk_string_unchecked("pp", 2, 2);
x_431 = lean_mk_string_unchecked("sorrySource", 11, 11);
x_432 = l_Lean_Name_mkStr2(x_430, x_431);
lean_inc(x_432);
x_433 = l_Lean_Expr_setOption___at___Lean_Expr_setPPExplicit_spec__0(x_1, x_432, x_141);
x_434 = l_Lean_Expr_setOption___at___Lean_Expr_setPPExplicit_spec__0(x_2, x_432, x_141);
if (lean_is_scalar(x_369)) {
 x_435 = lean_alloc_ctor(0, 2, 0);
} else {
 x_435 = x_369;
}
lean_ctor_set(x_435, 0, x_433);
lean_ctor_set(x_435, 1, x_434);
if (lean_is_scalar(x_348)) {
 x_436 = lean_alloc_ctor(0, 2, 0);
} else {
 x_436 = x_348;
}
lean_ctor_set(x_436, 0, x_435);
lean_ctor_set(x_436, 1, x_370);
return x_436;
}
}
else
{
lean_dec(x_369);
lean_dec(x_348);
x_411 = x_353;
x_412 = x_3;
x_413 = x_4;
x_414 = x_5;
x_415 = x_6;
x_416 = x_370;
goto block_419;
}
}
}
}
}
block_446:
{
if (x_439 == 0)
{
lean_dec(x_367);
lean_dec(x_344);
x_420 = x_438;
goto block_437;
}
else
{
lean_object* x_440; uint8_t x_441; 
x_440 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_440, 0, x_355);
x_441 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at_____private_Lean_Meta_Basic_0__Lean_Meta_beqInfoCacheKey____x40_Lean_Meta_Basic___hyg_1324__spec__0(x_373, x_440);
lean_dec(x_440);
if (x_441 == 0)
{
lean_dec(x_367);
lean_dec(x_344);
x_420 = x_438;
goto block_437;
}
else
{
lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; 
lean_dec(x_438);
lean_dec(x_410);
lean_dec(x_374);
lean_dec(x_373);
lean_dec(x_372);
lean_dec(x_371);
lean_dec(x_369);
lean_dec(x_353);
lean_dec(x_348);
lean_dec(x_149);
lean_dec(x_148);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_442 = l_Lean_Expr_setPPNumericTypes(x_1, x_141);
x_443 = l_Lean_Expr_setPPNumericTypes(x_2, x_141);
if (lean_is_scalar(x_367)) {
 x_444 = lean_alloc_ctor(0, 2, 0);
} else {
 x_444 = x_367;
}
lean_ctor_set(x_444, 0, x_442);
lean_ctor_set(x_444, 1, x_443);
if (lean_is_scalar(x_344)) {
 x_445 = lean_alloc_ctor(0, 2, 0);
} else {
 x_445 = x_344;
}
lean_ctor_set(x_445, 0, x_444);
lean_ctor_set(x_445, 1, x_370);
return x_445;
}
}
}
block_455:
{
lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; uint8_t x_452; 
x_448 = lean_mk_string_unchecked("OfNat", 5, 5);
x_449 = lean_mk_string_unchecked("ofNat", 5, 5);
x_450 = l_Lean_Name_mkStr2(x_448, x_449);
x_451 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_451, 0, x_450);
x_452 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at___Lean_Meta_addPPExplicitToExposeDiff_visit_spec__1(x_447, x_451);
lean_dec(x_451);
if (x_452 == 0)
{
lean_dec(x_356);
x_438 = x_447;
x_439 = x_452;
goto block_446;
}
else
{
lean_object* x_453; uint8_t x_454; 
x_453 = lean_unsigned_to_nat(3u);
x_454 = lean_nat_dec_le(x_453, x_356);
lean_dec(x_356);
x_438 = x_447;
x_439 = x_454;
goto block_446;
}
}
}
else
{
lean_object* x_466; lean_object* x_467; 
lean_dec(x_356);
lean_dec(x_353);
lean_dec(x_349);
lean_dec(x_348);
lean_dec(x_344);
lean_dec(x_149);
lean_dec(x_148);
lean_dec(x_140);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_466 = lean_ctor_get(x_363, 0);
lean_inc(x_466);
x_467 = lean_ctor_get(x_363, 1);
lean_inc(x_467);
lean_dec(x_363);
x_18 = x_466;
x_19 = x_467;
goto block_22;
}
}
else
{
lean_object* x_468; lean_object* x_469; 
lean_dec(x_344);
lean_dec(x_342);
lean_dec(x_149);
lean_dec(x_148);
lean_dec(x_140);
lean_dec(x_139);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_468 = lean_ctor_get(x_345, 0);
lean_inc(x_468);
x_469 = lean_ctor_get(x_345, 1);
lean_inc(x_469);
lean_dec(x_345);
x_18 = x_468;
x_19 = x_469;
goto block_22;
}
}
else
{
lean_object* x_470; lean_object* x_471; 
lean_dec(x_149);
lean_dec(x_148);
lean_dec(x_140);
lean_dec(x_139);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_470 = lean_ctor_get(x_341, 0);
lean_inc(x_470);
x_471 = lean_ctor_get(x_341, 1);
lean_inc(x_471);
lean_dec(x_341);
x_18 = x_470;
x_19 = x_471;
goto block_22;
}
}
}
}
else
{
lean_object* x_472; lean_object* x_473; 
lean_dec(x_149);
lean_dec(x_148);
lean_dec(x_140);
lean_dec(x_139);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_472 = lean_ctor_get(x_150, 0);
lean_inc(x_472);
x_473 = lean_ctor_get(x_150, 1);
lean_inc(x_473);
lean_dec(x_150);
x_18 = x_472;
x_19 = x_473;
goto block_22;
}
}
else
{
lean_dec(x_140);
lean_dec(x_139);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
goto block_10;
}
}
else
{
lean_dec(x_140);
lean_dec(x_139);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
goto block_10;
}
}
}
case 6:
{
lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; uint8_t x_479; lean_object* x_480; 
x_474 = lean_ctor_get(x_1, 0);
lean_inc(x_474);
x_475 = lean_ctor_get(x_1, 1);
lean_inc(x_475);
x_476 = lean_ctor_get(x_2, 0);
lean_inc(x_476);
x_477 = lean_ctor_get(x_2, 1);
lean_inc(x_477);
x_478 = lean_ctor_get(x_2, 2);
lean_inc(x_478);
x_479 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_inc(x_2);
x_480 = l_Lean_Meta_addPPExplicitToExposeDiff_visit___lam__7(x_474, x_475, x_34, x_2, x_476, x_477, x_478, x_479, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_478);
lean_dec(x_477);
lean_dec(x_476);
x_23 = x_480;
goto block_33;
}
case 7:
{
lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; uint8_t x_486; lean_object* x_487; 
x_481 = lean_ctor_get(x_1, 0);
lean_inc(x_481);
x_482 = lean_ctor_get(x_1, 1);
lean_inc(x_482);
x_483 = lean_ctor_get(x_2, 0);
lean_inc(x_483);
x_484 = lean_ctor_get(x_2, 1);
lean_inc(x_484);
x_485 = lean_ctor_get(x_2, 2);
lean_inc(x_485);
x_486 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_inc(x_2);
x_487 = l_Lean_Meta_addPPExplicitToExposeDiff_visit___lam__7(x_481, x_482, x_34, x_2, x_483, x_484, x_485, x_486, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_485);
lean_dec(x_484);
lean_dec(x_483);
x_23 = x_487;
goto block_33;
}
case 10:
{
lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; 
lean_dec(x_34);
x_488 = lean_ctor_get(x_1, 0);
lean_inc(x_488);
x_489 = lean_ctor_get(x_1, 1);
lean_inc(x_489);
x_490 = lean_ctor_get(x_2, 0);
lean_inc(x_490);
x_491 = lean_ctor_get(x_2, 1);
lean_inc(x_491);
x_492 = l_Lean_Expr_app___override(x_488, x_489);
lean_inc(x_2);
lean_inc(x_1);
x_493 = l_Lean_Meta_addPPExplicitToExposeDiff_visit___lam__1(x_1, x_2, x_492, x_490, x_491, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_490);
lean_dec(x_492);
x_23 = x_493;
goto block_33;
}
default: 
{
lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; 
lean_dec(x_34);
x_494 = lean_ctor_get(x_1, 0);
lean_inc(x_494);
x_495 = lean_ctor_get(x_1, 1);
lean_inc(x_495);
x_496 = l_Lean_Expr_app___override(x_494, x_495);
lean_inc(x_2);
lean_inc(x_1);
x_497 = l_Lean_Meta_addPPExplicitToExposeDiff_visit___lam__0(x_1, x_2, x_496, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_496);
x_23 = x_497;
goto block_33;
}
}
}
case 6:
{
lean_dec(x_34);
switch (lean_obj_tag(x_2)) {
case 6:
{
lean_object* x_498; lean_object* x_499; lean_object* x_500; uint8_t x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; uint8_t x_505; lean_object* x_506; 
x_498 = lean_ctor_get(x_1, 0);
lean_inc(x_498);
x_499 = lean_ctor_get(x_1, 1);
lean_inc(x_499);
x_500 = lean_ctor_get(x_1, 2);
lean_inc(x_500);
x_501 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
x_502 = lean_ctor_get(x_2, 0);
lean_inc(x_502);
x_503 = lean_ctor_get(x_2, 1);
lean_inc(x_503);
x_504 = lean_ctor_get(x_2, 2);
lean_inc(x_504);
x_505 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_503);
lean_inc(x_499);
x_506 = l_Lean_Meta_isExprDefEq(x_499, x_503, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_506) == 0)
{
lean_object* x_507; uint8_t x_508; 
x_507 = lean_ctor_get(x_506, 0);
lean_inc(x_507);
x_508 = lean_unbox(x_507);
lean_dec(x_507);
if (x_508 == 0)
{
lean_object* x_509; lean_object* x_510; 
x_509 = lean_ctor_get(x_506, 1);
lean_inc(x_509);
lean_dec(x_506);
x_510 = l_Lean_Meta_addPPExplicitToExposeDiff_visit(x_499, x_503, x_3, x_4, x_5, x_6, x_509);
if (lean_obj_tag(x_510) == 0)
{
uint8_t x_511; 
lean_dec(x_2);
lean_dec(x_1);
x_511 = !lean_is_exclusive(x_510);
if (x_511 == 0)
{
lean_object* x_512; uint8_t x_513; 
x_512 = lean_ctor_get(x_510, 0);
x_513 = !lean_is_exclusive(x_512);
if (x_513 == 0)
{
lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; uint8_t x_519; lean_object* x_520; uint8_t x_521; lean_object* x_522; 
x_514 = lean_ctor_get(x_512, 0);
x_515 = lean_ctor_get(x_512, 1);
x_516 = lean_box(1);
x_517 = l_Lean_Expr_lam___override(x_498, x_514, x_500, x_501);
x_518 = l_Lean_Expr_lam___override(x_502, x_515, x_504, x_505);
x_519 = lean_unbox(x_516);
x_520 = l_Lean_Expr_setPPFunBinderTypes(x_517, x_519);
x_521 = lean_unbox(x_516);
x_522 = l_Lean_Expr_setPPFunBinderTypes(x_518, x_521);
lean_ctor_set(x_512, 1, x_522);
lean_ctor_set(x_512, 0, x_520);
return x_510;
}
else
{
lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; uint8_t x_528; lean_object* x_529; uint8_t x_530; lean_object* x_531; lean_object* x_532; 
x_523 = lean_ctor_get(x_512, 0);
x_524 = lean_ctor_get(x_512, 1);
lean_inc(x_524);
lean_inc(x_523);
lean_dec(x_512);
x_525 = lean_box(1);
x_526 = l_Lean_Expr_lam___override(x_498, x_523, x_500, x_501);
x_527 = l_Lean_Expr_lam___override(x_502, x_524, x_504, x_505);
x_528 = lean_unbox(x_525);
x_529 = l_Lean_Expr_setPPFunBinderTypes(x_526, x_528);
x_530 = lean_unbox(x_525);
x_531 = l_Lean_Expr_setPPFunBinderTypes(x_527, x_530);
x_532 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_532, 0, x_529);
lean_ctor_set(x_532, 1, x_531);
lean_ctor_set(x_510, 0, x_532);
return x_510;
}
}
else
{
lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; uint8_t x_541; lean_object* x_542; uint8_t x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; 
x_533 = lean_ctor_get(x_510, 0);
x_534 = lean_ctor_get(x_510, 1);
lean_inc(x_534);
lean_inc(x_533);
lean_dec(x_510);
x_535 = lean_ctor_get(x_533, 0);
lean_inc(x_535);
x_536 = lean_ctor_get(x_533, 1);
lean_inc(x_536);
if (lean_is_exclusive(x_533)) {
 lean_ctor_release(x_533, 0);
 lean_ctor_release(x_533, 1);
 x_537 = x_533;
} else {
 lean_dec_ref(x_533);
 x_537 = lean_box(0);
}
x_538 = lean_box(1);
x_539 = l_Lean_Expr_lam___override(x_498, x_535, x_500, x_501);
x_540 = l_Lean_Expr_lam___override(x_502, x_536, x_504, x_505);
x_541 = lean_unbox(x_538);
x_542 = l_Lean_Expr_setPPFunBinderTypes(x_539, x_541);
x_543 = lean_unbox(x_538);
x_544 = l_Lean_Expr_setPPFunBinderTypes(x_540, x_543);
if (lean_is_scalar(x_537)) {
 x_545 = lean_alloc_ctor(0, 2, 0);
} else {
 x_545 = x_537;
}
lean_ctor_set(x_545, 0, x_542);
lean_ctor_set(x_545, 1, x_544);
x_546 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_546, 0, x_545);
lean_ctor_set(x_546, 1, x_534);
return x_546;
}
}
else
{
lean_object* x_547; lean_object* x_548; 
lean_dec(x_504);
lean_dec(x_502);
lean_dec(x_500);
lean_dec(x_498);
x_547 = lean_ctor_get(x_510, 0);
lean_inc(x_547);
x_548 = lean_ctor_get(x_510, 1);
lean_inc(x_548);
lean_dec(x_510);
x_18 = x_547;
x_19 = x_548;
goto block_22;
}
}
else
{
lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; 
x_549 = lean_ctor_get(x_506, 1);
lean_inc(x_549);
lean_dec(x_506);
x_550 = lean_box(x_501);
x_551 = lean_box(x_505);
lean_inc(x_499);
lean_inc(x_498);
x_552 = lean_alloc_closure((void*)(l_Lean_Meta_addPPExplicitToExposeDiff_visit___lam__8___boxed), 14, 8);
lean_closure_set(x_552, 0, x_500);
lean_closure_set(x_552, 1, x_504);
lean_closure_set(x_552, 2, x_498);
lean_closure_set(x_552, 3, x_499);
lean_closure_set(x_552, 4, x_550);
lean_closure_set(x_552, 5, x_502);
lean_closure_set(x_552, 6, x_503);
lean_closure_set(x_552, 7, x_551);
x_553 = l_Lean_Meta_withLocalDeclD___at___Lean_Meta_addPPExplicitToExposeDiff_visit_spec__3___redArg(x_498, x_499, x_552, x_3, x_4, x_5, x_6, x_549);
if (lean_obj_tag(x_553) == 0)
{
uint8_t x_554; 
lean_dec(x_2);
lean_dec(x_1);
x_554 = !lean_is_exclusive(x_553);
if (x_554 == 0)
{
return x_553;
}
else
{
lean_object* x_555; lean_object* x_556; lean_object* x_557; 
x_555 = lean_ctor_get(x_553, 0);
x_556 = lean_ctor_get(x_553, 1);
lean_inc(x_556);
lean_inc(x_555);
lean_dec(x_553);
x_557 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_557, 0, x_555);
lean_ctor_set(x_557, 1, x_556);
return x_557;
}
}
else
{
lean_object* x_558; lean_object* x_559; 
x_558 = lean_ctor_get(x_553, 0);
lean_inc(x_558);
x_559 = lean_ctor_get(x_553, 1);
lean_inc(x_559);
lean_dec(x_553);
x_18 = x_558;
x_19 = x_559;
goto block_22;
}
}
}
else
{
lean_object* x_560; lean_object* x_561; 
lean_dec(x_504);
lean_dec(x_503);
lean_dec(x_502);
lean_dec(x_500);
lean_dec(x_499);
lean_dec(x_498);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_560 = lean_ctor_get(x_506, 0);
lean_inc(x_560);
x_561 = lean_ctor_get(x_506, 1);
lean_inc(x_561);
lean_dec(x_506);
x_18 = x_560;
x_19 = x_561;
goto block_22;
}
}
case 10:
{
lean_object* x_562; lean_object* x_563; lean_object* x_564; uint8_t x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; 
x_562 = lean_ctor_get(x_1, 0);
lean_inc(x_562);
x_563 = lean_ctor_get(x_1, 1);
lean_inc(x_563);
x_564 = lean_ctor_get(x_1, 2);
lean_inc(x_564);
x_565 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
x_566 = lean_ctor_get(x_2, 0);
lean_inc(x_566);
x_567 = lean_ctor_get(x_2, 1);
lean_inc(x_567);
x_568 = l_Lean_Expr_lam___override(x_562, x_563, x_564, x_565);
lean_inc(x_2);
lean_inc(x_1);
x_569 = l_Lean_Meta_addPPExplicitToExposeDiff_visit___lam__1(x_1, x_2, x_568, x_566, x_567, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_566);
lean_dec(x_568);
x_23 = x_569;
goto block_33;
}
default: 
{
lean_object* x_570; lean_object* x_571; lean_object* x_572; uint8_t x_573; lean_object* x_574; lean_object* x_575; 
x_570 = lean_ctor_get(x_1, 0);
lean_inc(x_570);
x_571 = lean_ctor_get(x_1, 1);
lean_inc(x_571);
x_572 = lean_ctor_get(x_1, 2);
lean_inc(x_572);
x_573 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
x_574 = l_Lean_Expr_lam___override(x_570, x_571, x_572, x_573);
lean_inc(x_2);
lean_inc(x_1);
x_575 = l_Lean_Meta_addPPExplicitToExposeDiff_visit___lam__0(x_1, x_2, x_574, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_574);
x_23 = x_575;
goto block_33;
}
}
}
case 7:
{
lean_dec(x_34);
switch (lean_obj_tag(x_2)) {
case 7:
{
lean_object* x_576; lean_object* x_577; lean_object* x_578; uint8_t x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; uint8_t x_583; lean_object* x_584; 
x_576 = lean_ctor_get(x_1, 0);
lean_inc(x_576);
x_577 = lean_ctor_get(x_1, 1);
lean_inc(x_577);
x_578 = lean_ctor_get(x_1, 2);
lean_inc(x_578);
x_579 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
x_580 = lean_ctor_get(x_2, 0);
lean_inc(x_580);
x_581 = lean_ctor_get(x_2, 1);
lean_inc(x_581);
x_582 = lean_ctor_get(x_2, 2);
lean_inc(x_582);
x_583 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_581);
lean_inc(x_577);
x_584 = l_Lean_Meta_isExprDefEq(x_577, x_581, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_584) == 0)
{
lean_object* x_585; uint8_t x_586; 
x_585 = lean_ctor_get(x_584, 0);
lean_inc(x_585);
x_586 = lean_unbox(x_585);
lean_dec(x_585);
if (x_586 == 0)
{
lean_object* x_587; lean_object* x_588; 
x_587 = lean_ctor_get(x_584, 1);
lean_inc(x_587);
lean_dec(x_584);
x_588 = l_Lean_Meta_addPPExplicitToExposeDiff_visit(x_577, x_581, x_3, x_4, x_5, x_6, x_587);
if (lean_obj_tag(x_588) == 0)
{
uint8_t x_589; 
lean_dec(x_2);
lean_dec(x_1);
x_589 = !lean_is_exclusive(x_588);
if (x_589 == 0)
{
lean_object* x_590; uint8_t x_591; 
x_590 = lean_ctor_get(x_588, 0);
x_591 = !lean_is_exclusive(x_590);
if (x_591 == 0)
{
lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; uint8_t x_597; lean_object* x_598; uint8_t x_599; lean_object* x_600; 
x_592 = lean_ctor_get(x_590, 0);
x_593 = lean_ctor_get(x_590, 1);
x_594 = lean_box(1);
x_595 = l_Lean_Expr_forallE___override(x_576, x_592, x_578, x_579);
x_596 = l_Lean_Expr_forallE___override(x_580, x_593, x_582, x_583);
x_597 = lean_unbox(x_594);
x_598 = l_Lean_Expr_setPPPiBinderTypes(x_595, x_597);
x_599 = lean_unbox(x_594);
x_600 = l_Lean_Expr_setPPPiBinderTypes(x_596, x_599);
lean_ctor_set(x_590, 1, x_600);
lean_ctor_set(x_590, 0, x_598);
return x_588;
}
else
{
lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; uint8_t x_606; lean_object* x_607; uint8_t x_608; lean_object* x_609; lean_object* x_610; 
x_601 = lean_ctor_get(x_590, 0);
x_602 = lean_ctor_get(x_590, 1);
lean_inc(x_602);
lean_inc(x_601);
lean_dec(x_590);
x_603 = lean_box(1);
x_604 = l_Lean_Expr_forallE___override(x_576, x_601, x_578, x_579);
x_605 = l_Lean_Expr_forallE___override(x_580, x_602, x_582, x_583);
x_606 = lean_unbox(x_603);
x_607 = l_Lean_Expr_setPPPiBinderTypes(x_604, x_606);
x_608 = lean_unbox(x_603);
x_609 = l_Lean_Expr_setPPPiBinderTypes(x_605, x_608);
x_610 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_610, 0, x_607);
lean_ctor_set(x_610, 1, x_609);
lean_ctor_set(x_588, 0, x_610);
return x_588;
}
}
else
{
lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; uint8_t x_619; lean_object* x_620; uint8_t x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; 
x_611 = lean_ctor_get(x_588, 0);
x_612 = lean_ctor_get(x_588, 1);
lean_inc(x_612);
lean_inc(x_611);
lean_dec(x_588);
x_613 = lean_ctor_get(x_611, 0);
lean_inc(x_613);
x_614 = lean_ctor_get(x_611, 1);
lean_inc(x_614);
if (lean_is_exclusive(x_611)) {
 lean_ctor_release(x_611, 0);
 lean_ctor_release(x_611, 1);
 x_615 = x_611;
} else {
 lean_dec_ref(x_611);
 x_615 = lean_box(0);
}
x_616 = lean_box(1);
x_617 = l_Lean_Expr_forallE___override(x_576, x_613, x_578, x_579);
x_618 = l_Lean_Expr_forallE___override(x_580, x_614, x_582, x_583);
x_619 = lean_unbox(x_616);
x_620 = l_Lean_Expr_setPPPiBinderTypes(x_617, x_619);
x_621 = lean_unbox(x_616);
x_622 = l_Lean_Expr_setPPPiBinderTypes(x_618, x_621);
if (lean_is_scalar(x_615)) {
 x_623 = lean_alloc_ctor(0, 2, 0);
} else {
 x_623 = x_615;
}
lean_ctor_set(x_623, 0, x_620);
lean_ctor_set(x_623, 1, x_622);
x_624 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_624, 0, x_623);
lean_ctor_set(x_624, 1, x_612);
return x_624;
}
}
else
{
lean_object* x_625; lean_object* x_626; 
lean_dec(x_582);
lean_dec(x_580);
lean_dec(x_578);
lean_dec(x_576);
x_625 = lean_ctor_get(x_588, 0);
lean_inc(x_625);
x_626 = lean_ctor_get(x_588, 1);
lean_inc(x_626);
lean_dec(x_588);
x_18 = x_625;
x_19 = x_626;
goto block_22;
}
}
else
{
lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; 
x_627 = lean_ctor_get(x_584, 1);
lean_inc(x_627);
lean_dec(x_584);
x_628 = lean_box(x_579);
x_629 = lean_box(x_583);
lean_inc(x_577);
lean_inc(x_576);
x_630 = lean_alloc_closure((void*)(l_Lean_Meta_addPPExplicitToExposeDiff_visit___lam__9___boxed), 14, 8);
lean_closure_set(x_630, 0, x_578);
lean_closure_set(x_630, 1, x_582);
lean_closure_set(x_630, 2, x_576);
lean_closure_set(x_630, 3, x_577);
lean_closure_set(x_630, 4, x_628);
lean_closure_set(x_630, 5, x_580);
lean_closure_set(x_630, 6, x_581);
lean_closure_set(x_630, 7, x_629);
x_631 = l_Lean_Meta_withLocalDeclD___at___Lean_Meta_addPPExplicitToExposeDiff_visit_spec__3___redArg(x_576, x_577, x_630, x_3, x_4, x_5, x_6, x_627);
if (lean_obj_tag(x_631) == 0)
{
uint8_t x_632; 
lean_dec(x_2);
lean_dec(x_1);
x_632 = !lean_is_exclusive(x_631);
if (x_632 == 0)
{
return x_631;
}
else
{
lean_object* x_633; lean_object* x_634; lean_object* x_635; 
x_633 = lean_ctor_get(x_631, 0);
x_634 = lean_ctor_get(x_631, 1);
lean_inc(x_634);
lean_inc(x_633);
lean_dec(x_631);
x_635 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_635, 0, x_633);
lean_ctor_set(x_635, 1, x_634);
return x_635;
}
}
else
{
lean_object* x_636; lean_object* x_637; 
x_636 = lean_ctor_get(x_631, 0);
lean_inc(x_636);
x_637 = lean_ctor_get(x_631, 1);
lean_inc(x_637);
lean_dec(x_631);
x_18 = x_636;
x_19 = x_637;
goto block_22;
}
}
}
else
{
lean_object* x_638; lean_object* x_639; 
lean_dec(x_582);
lean_dec(x_581);
lean_dec(x_580);
lean_dec(x_578);
lean_dec(x_577);
lean_dec(x_576);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_638 = lean_ctor_get(x_584, 0);
lean_inc(x_638);
x_639 = lean_ctor_get(x_584, 1);
lean_inc(x_639);
lean_dec(x_584);
x_18 = x_638;
x_19 = x_639;
goto block_22;
}
}
case 10:
{
lean_object* x_640; lean_object* x_641; lean_object* x_642; uint8_t x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; 
x_640 = lean_ctor_get(x_1, 0);
lean_inc(x_640);
x_641 = lean_ctor_get(x_1, 1);
lean_inc(x_641);
x_642 = lean_ctor_get(x_1, 2);
lean_inc(x_642);
x_643 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
x_644 = lean_ctor_get(x_2, 0);
lean_inc(x_644);
x_645 = lean_ctor_get(x_2, 1);
lean_inc(x_645);
x_646 = l_Lean_Expr_forallE___override(x_640, x_641, x_642, x_643);
lean_inc(x_2);
lean_inc(x_1);
x_647 = l_Lean_Meta_addPPExplicitToExposeDiff_visit___lam__1(x_1, x_2, x_646, x_644, x_645, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_644);
lean_dec(x_646);
x_23 = x_647;
goto block_33;
}
default: 
{
lean_object* x_648; lean_object* x_649; lean_object* x_650; uint8_t x_651; lean_object* x_652; lean_object* x_653; 
x_648 = lean_ctor_get(x_1, 0);
lean_inc(x_648);
x_649 = lean_ctor_get(x_1, 1);
lean_inc(x_649);
x_650 = lean_ctor_get(x_1, 2);
lean_inc(x_650);
x_651 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
x_652 = l_Lean_Expr_forallE___override(x_648, x_649, x_650, x_651);
lean_inc(x_2);
lean_inc(x_1);
x_653 = l_Lean_Meta_addPPExplicitToExposeDiff_visit___lam__0(x_1, x_2, x_652, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_652);
x_23 = x_653;
goto block_33;
}
}
}
case 8:
{
switch (lean_obj_tag(x_2)) {
case 6:
{
lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; uint8_t x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; uint8_t x_662; lean_object* x_663; 
x_654 = lean_ctor_get(x_1, 0);
lean_inc(x_654);
x_655 = lean_ctor_get(x_1, 1);
lean_inc(x_655);
x_656 = lean_ctor_get(x_1, 2);
lean_inc(x_656);
x_657 = lean_ctor_get(x_1, 3);
lean_inc(x_657);
x_658 = lean_ctor_get_uint8(x_1, sizeof(void*)*4 + 8);
x_659 = lean_ctor_get(x_2, 0);
lean_inc(x_659);
x_660 = lean_ctor_get(x_2, 1);
lean_inc(x_660);
x_661 = lean_ctor_get(x_2, 2);
lean_inc(x_661);
x_662 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_inc(x_2);
x_663 = l_Lean_Meta_addPPExplicitToExposeDiff_visit___lam__10(x_654, x_655, x_656, x_657, x_658, x_34, x_2, x_659, x_660, x_661, x_662, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_661);
lean_dec(x_660);
lean_dec(x_659);
x_23 = x_663;
goto block_33;
}
case 7:
{
lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; uint8_t x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; uint8_t x_672; lean_object* x_673; 
x_664 = lean_ctor_get(x_1, 0);
lean_inc(x_664);
x_665 = lean_ctor_get(x_1, 1);
lean_inc(x_665);
x_666 = lean_ctor_get(x_1, 2);
lean_inc(x_666);
x_667 = lean_ctor_get(x_1, 3);
lean_inc(x_667);
x_668 = lean_ctor_get_uint8(x_1, sizeof(void*)*4 + 8);
x_669 = lean_ctor_get(x_2, 0);
lean_inc(x_669);
x_670 = lean_ctor_get(x_2, 1);
lean_inc(x_670);
x_671 = lean_ctor_get(x_2, 2);
lean_inc(x_671);
x_672 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_inc(x_2);
x_673 = l_Lean_Meta_addPPExplicitToExposeDiff_visit___lam__10(x_664, x_665, x_666, x_667, x_668, x_34, x_2, x_669, x_670, x_671, x_672, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_671);
lean_dec(x_670);
lean_dec(x_669);
x_23 = x_673;
goto block_33;
}
case 10:
{
lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; uint8_t x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; 
lean_dec(x_34);
x_674 = lean_ctor_get(x_1, 0);
lean_inc(x_674);
x_675 = lean_ctor_get(x_1, 1);
lean_inc(x_675);
x_676 = lean_ctor_get(x_1, 2);
lean_inc(x_676);
x_677 = lean_ctor_get(x_1, 3);
lean_inc(x_677);
x_678 = lean_ctor_get_uint8(x_1, sizeof(void*)*4 + 8);
x_679 = lean_ctor_get(x_2, 0);
lean_inc(x_679);
x_680 = lean_ctor_get(x_2, 1);
lean_inc(x_680);
x_681 = l_Lean_Expr_letE___override(x_674, x_675, x_676, x_677, x_678);
lean_inc(x_2);
lean_inc(x_1);
x_682 = l_Lean_Meta_addPPExplicitToExposeDiff_visit___lam__1(x_1, x_2, x_681, x_679, x_680, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_679);
lean_dec(x_681);
x_23 = x_682;
goto block_33;
}
default: 
{
lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; uint8_t x_687; lean_object* x_688; lean_object* x_689; 
lean_dec(x_34);
x_683 = lean_ctor_get(x_1, 0);
lean_inc(x_683);
x_684 = lean_ctor_get(x_1, 1);
lean_inc(x_684);
x_685 = lean_ctor_get(x_1, 2);
lean_inc(x_685);
x_686 = lean_ctor_get(x_1, 3);
lean_inc(x_686);
x_687 = lean_ctor_get_uint8(x_1, sizeof(void*)*4 + 8);
x_688 = l_Lean_Expr_letE___override(x_683, x_684, x_685, x_686, x_687);
lean_inc(x_2);
lean_inc(x_1);
x_689 = l_Lean_Meta_addPPExplicitToExposeDiff_visit___lam__0(x_1, x_2, x_688, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_688);
x_23 = x_689;
goto block_33;
}
}
}
case 9:
{
switch (lean_obj_tag(x_2)) {
case 6:
{
lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; uint8_t x_694; lean_object* x_695; 
x_690 = lean_ctor_get(x_1, 0);
lean_inc(x_690);
x_691 = lean_ctor_get(x_2, 0);
lean_inc(x_691);
x_692 = lean_ctor_get(x_2, 1);
lean_inc(x_692);
x_693 = lean_ctor_get(x_2, 2);
lean_inc(x_693);
x_694 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_inc(x_2);
x_695 = l_Lean_Meta_addPPExplicitToExposeDiff_visit___lam__11(x_690, x_34, x_2, x_691, x_692, x_693, x_694, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_693);
lean_dec(x_692);
lean_dec(x_691);
x_23 = x_695;
goto block_33;
}
case 7:
{
lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; uint8_t x_700; lean_object* x_701; 
x_696 = lean_ctor_get(x_1, 0);
lean_inc(x_696);
x_697 = lean_ctor_get(x_2, 0);
lean_inc(x_697);
x_698 = lean_ctor_get(x_2, 1);
lean_inc(x_698);
x_699 = lean_ctor_get(x_2, 2);
lean_inc(x_699);
x_700 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_inc(x_2);
x_701 = l_Lean_Meta_addPPExplicitToExposeDiff_visit___lam__11(x_696, x_34, x_2, x_697, x_698, x_699, x_700, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_699);
lean_dec(x_698);
lean_dec(x_697);
x_23 = x_701;
goto block_33;
}
case 10:
{
lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; 
lean_dec(x_34);
x_702 = lean_ctor_get(x_1, 0);
lean_inc(x_702);
x_703 = lean_ctor_get(x_2, 0);
lean_inc(x_703);
x_704 = lean_ctor_get(x_2, 1);
lean_inc(x_704);
x_705 = l_Lean_Expr_lit___override(x_702);
lean_inc(x_2);
lean_inc(x_1);
x_706 = l_Lean_Meta_addPPExplicitToExposeDiff_visit___lam__1(x_1, x_2, x_705, x_703, x_704, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_703);
lean_dec(x_705);
x_23 = x_706;
goto block_33;
}
default: 
{
lean_object* x_707; lean_object* x_708; lean_object* x_709; 
lean_dec(x_34);
x_707 = lean_ctor_get(x_1, 0);
lean_inc(x_707);
x_708 = l_Lean_Expr_lit___override(x_707);
lean_inc(x_2);
lean_inc(x_1);
x_709 = l_Lean_Meta_addPPExplicitToExposeDiff_visit___lam__0(x_1, x_2, x_708, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_708);
x_23 = x_709;
goto block_33;
}
}
}
case 10:
{
lean_object* x_710; lean_object* x_711; lean_object* x_712; 
lean_dec(x_34);
x_710 = lean_ctor_get(x_1, 0);
lean_inc(x_710);
x_711 = lean_ctor_get(x_1, 1);
lean_inc(x_711);
lean_inc(x_2);
lean_inc(x_711);
x_712 = l_Lean_Meta_addPPExplicitToExposeDiff_visit(x_711, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_712) == 0)
{
lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; size_t x_723; size_t x_724; uint8_t x_725; 
lean_dec(x_2);
x_713 = lean_ctor_get(x_712, 0);
lean_inc(x_713);
x_714 = lean_ctor_get(x_712, 1);
lean_inc(x_714);
if (lean_is_exclusive(x_712)) {
 lean_ctor_release(x_712, 0);
 lean_ctor_release(x_712, 1);
 x_715 = x_712;
} else {
 lean_dec_ref(x_712);
 x_715 = lean_box(0);
}
x_716 = lean_ctor_get(x_713, 0);
lean_inc(x_716);
x_717 = lean_ctor_get(x_713, 1);
lean_inc(x_717);
if (lean_is_exclusive(x_713)) {
 lean_ctor_release(x_713, 0);
 lean_ctor_release(x_713, 1);
 x_718 = x_713;
} else {
 lean_dec_ref(x_713);
 x_718 = lean_box(0);
}
x_723 = lean_ptr_addr(x_711);
lean_dec(x_711);
x_724 = lean_ptr_addr(x_716);
x_725 = lean_usize_dec_eq(x_723, x_724);
if (x_725 == 0)
{
lean_object* x_726; 
lean_dec(x_1);
x_726 = l_Lean_Expr_mdata___override(x_710, x_716);
x_719 = x_726;
goto block_722;
}
else
{
lean_dec(x_716);
lean_dec(x_710);
x_719 = x_1;
goto block_722;
}
block_722:
{
lean_object* x_720; lean_object* x_721; 
if (lean_is_scalar(x_718)) {
 x_720 = lean_alloc_ctor(0, 2, 0);
} else {
 x_720 = x_718;
}
lean_ctor_set(x_720, 0, x_719);
lean_ctor_set(x_720, 1, x_717);
if (lean_is_scalar(x_715)) {
 x_721 = lean_alloc_ctor(0, 2, 0);
} else {
 x_721 = x_715;
}
lean_ctor_set(x_721, 0, x_720);
lean_ctor_set(x_721, 1, x_714);
return x_721;
}
}
else
{
lean_object* x_727; lean_object* x_728; 
lean_dec(x_711);
lean_dec(x_710);
x_727 = lean_ctor_get(x_712, 0);
lean_inc(x_727);
x_728 = lean_ctor_get(x_712, 1);
lean_inc(x_728);
lean_dec(x_712);
x_18 = x_727;
x_19 = x_728;
goto block_22;
}
}
default: 
{
switch (lean_obj_tag(x_2)) {
case 6:
{
lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; uint8_t x_735; lean_object* x_736; 
x_729 = lean_ctor_get(x_1, 0);
lean_inc(x_729);
x_730 = lean_ctor_get(x_1, 1);
lean_inc(x_730);
x_731 = lean_ctor_get(x_1, 2);
lean_inc(x_731);
x_732 = lean_ctor_get(x_2, 0);
lean_inc(x_732);
x_733 = lean_ctor_get(x_2, 1);
lean_inc(x_733);
x_734 = lean_ctor_get(x_2, 2);
lean_inc(x_734);
x_735 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_inc(x_2);
x_736 = l_Lean_Meta_addPPExplicitToExposeDiff_visit___lam__12(x_729, x_730, x_731, x_34, x_2, x_732, x_733, x_734, x_735, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_734);
lean_dec(x_733);
lean_dec(x_732);
x_23 = x_736;
goto block_33;
}
case 7:
{
lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; uint8_t x_743; lean_object* x_744; 
x_737 = lean_ctor_get(x_1, 0);
lean_inc(x_737);
x_738 = lean_ctor_get(x_1, 1);
lean_inc(x_738);
x_739 = lean_ctor_get(x_1, 2);
lean_inc(x_739);
x_740 = lean_ctor_get(x_2, 0);
lean_inc(x_740);
x_741 = lean_ctor_get(x_2, 1);
lean_inc(x_741);
x_742 = lean_ctor_get(x_2, 2);
lean_inc(x_742);
x_743 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_inc(x_2);
x_744 = l_Lean_Meta_addPPExplicitToExposeDiff_visit___lam__12(x_737, x_738, x_739, x_34, x_2, x_740, x_741, x_742, x_743, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_742);
lean_dec(x_741);
lean_dec(x_740);
x_23 = x_744;
goto block_33;
}
case 10:
{
lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; lean_object* x_751; 
lean_dec(x_34);
x_745 = lean_ctor_get(x_1, 0);
lean_inc(x_745);
x_746 = lean_ctor_get(x_1, 1);
lean_inc(x_746);
x_747 = lean_ctor_get(x_1, 2);
lean_inc(x_747);
x_748 = lean_ctor_get(x_2, 0);
lean_inc(x_748);
x_749 = lean_ctor_get(x_2, 1);
lean_inc(x_749);
x_750 = l_Lean_Expr_proj___override(x_745, x_746, x_747);
lean_inc(x_2);
lean_inc(x_1);
x_751 = l_Lean_Meta_addPPExplicitToExposeDiff_visit___lam__1(x_1, x_2, x_750, x_748, x_749, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_748);
lean_dec(x_750);
x_23 = x_751;
goto block_33;
}
default: 
{
lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_756; 
lean_dec(x_34);
x_752 = lean_ctor_get(x_1, 0);
lean_inc(x_752);
x_753 = lean_ctor_get(x_1, 1);
lean_inc(x_753);
x_754 = lean_ctor_get(x_1, 2);
lean_inc(x_754);
x_755 = l_Lean_Expr_proj___override(x_752, x_753, x_754);
lean_inc(x_2);
lean_inc(x_1);
x_756 = l_Lean_Meta_addPPExplicitToExposeDiff_visit___lam__0(x_1, x_2, x_755, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_755);
x_23 = x_756;
goto block_33;
}
}
}
}
block_10:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
block_17:
{
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_2);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_2);
lean_dec(x_1);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set(x_16, 1, x_11);
return x_16;
}
}
block_22:
{
uint8_t x_20; 
x_20 = l_Lean_Exception_isInterrupt(x_18);
if (x_20 == 0)
{
uint8_t x_21; 
x_21 = l_Lean_Exception_isRuntime(x_18);
x_11 = x_19;
x_12 = x_18;
x_13 = x_21;
goto block_17;
}
else
{
x_11 = x_19;
x_12 = x_18;
x_13 = x_20;
goto block_17;
}
}
block_33:
{
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
lean_dec(x_2);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec(x_25);
lean_ctor_set(x_23, 0, x_26);
return x_23;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_23, 0);
x_28 = lean_ctor_get(x_23, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_23);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_23, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_23, 1);
lean_inc(x_32);
lean_dec(x_23);
x_18 = x_31;
x_19 = x_32;
goto block_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_addPPExplicitToExposeDiff_visit_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_addPPExplicitToExposeDiff_visit_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_addPPExplicitToExposeDiff_visit_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_addPPExplicitToExposeDiff_visit_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_8);
lean_dec(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at___Lean_Meta_addPPExplicitToExposeDiff_visit_spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at___Lean_Meta_addPPExplicitToExposeDiff_visit_spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at___Lean_Meta_addPPExplicitToExposeDiff_visit_spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at___Lean_Meta_addPPExplicitToExposeDiff_visit_spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___Lean_Meta_withLocalDeclD___at___Lean_Meta_addPPExplicitToExposeDiff_visit_spec__3_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_2);
lean_dec(x_2);
x_12 = lean_unbox(x_5);
lean_dec(x_5);
x_13 = l_Lean_Meta_withLocalDecl___at___Lean_Meta_withLocalDeclD___at___Lean_Meta_addPPExplicitToExposeDiff_visit_spec__3_spec__3___redArg(x_1, x_11, x_3, x_4, x_12, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___Lean_Meta_withLocalDeclD___at___Lean_Meta_addPPExplicitToExposeDiff_visit_spec__3_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_unbox(x_3);
lean_dec(x_3);
x_13 = lean_unbox(x_6);
lean_dec(x_6);
x_14 = l_Lean_Meta_withLocalDecl___at___Lean_Meta_withLocalDeclD___at___Lean_Meta_addPPExplicitToExposeDiff_visit_spec__3_spec__3(x_1, x_2, x_12, x_4, x_5, x_13, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addPPExplicitToExposeDiff_visit___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_addPPExplicitToExposeDiff_visit___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addPPExplicitToExposeDiff_visit___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_addPPExplicitToExposeDiff_visit___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addPPExplicitToExposeDiff_visit___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_7);
lean_dec(x_7);
x_14 = l_Lean_Meta_addPPExplicitToExposeDiff_visit___lam__2(x_1, x_2, x_3, x_4, x_5, x_6, x_13, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addPPExplicitToExposeDiff_visit___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_7);
lean_dec(x_7);
x_14 = l_Lean_Meta_addPPExplicitToExposeDiff_visit___lam__3(x_1, x_2, x_3, x_4, x_5, x_6, x_13, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addPPExplicitToExposeDiff_visit___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_7);
lean_dec(x_7);
x_14 = l_Lean_Meta_addPPExplicitToExposeDiff_visit___lam__4(x_1, x_2, x_3, x_4, x_5, x_6, x_13, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addPPExplicitToExposeDiff_visit___lam__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_7);
lean_dec(x_7);
x_14 = l_Lean_Meta_addPPExplicitToExposeDiff_visit___lam__5(x_1, x_2, x_3, x_4, x_5, x_6, x_13, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addPPExplicitToExposeDiff_visit___lam__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_8);
lean_dec(x_8);
x_15 = l_Lean_Meta_addPPExplicitToExposeDiff_visit___lam__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_14, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addPPExplicitToExposeDiff_visit___lam__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_8);
lean_dec(x_8);
x_15 = l_Lean_Meta_addPPExplicitToExposeDiff_visit___lam__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_14, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addPPExplicitToExposeDiff_visit___lam__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; uint8_t x_16; lean_object* x_17; 
x_15 = lean_unbox(x_5);
lean_dec(x_5);
x_16 = lean_unbox(x_8);
lean_dec(x_8);
x_17 = l_Lean_Meta_addPPExplicitToExposeDiff_visit___lam__8(x_1, x_2, x_3, x_4, x_15, x_6, x_7, x_16, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_2);
lean_dec(x_1);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addPPExplicitToExposeDiff_visit___lam__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; uint8_t x_16; lean_object* x_17; 
x_15 = lean_unbox(x_5);
lean_dec(x_5);
x_16 = lean_unbox(x_8);
lean_dec(x_8);
x_17 = l_Lean_Meta_addPPExplicitToExposeDiff_visit___lam__9(x_1, x_2, x_3, x_4, x_15, x_6, x_7, x_16, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_2);
lean_dec(x_1);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addPPExplicitToExposeDiff_visit___lam__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_17 = lean_unbox(x_5);
lean_dec(x_5);
x_18 = lean_unbox(x_11);
lean_dec(x_11);
x_19 = l_Lean_Meta_addPPExplicitToExposeDiff_visit___lam__10(x_1, x_2, x_3, x_4, x_17, x_6, x_7, x_8, x_9, x_10, x_18, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addPPExplicitToExposeDiff_visit___lam__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_7);
lean_dec(x_7);
x_14 = l_Lean_Meta_addPPExplicitToExposeDiff_visit___lam__11(x_1, x_2, x_3, x_4, x_5, x_6, x_13, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addPPExplicitToExposeDiff_visit___lam__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_9);
lean_dec(x_9);
x_16 = l_Lean_Meta_addPPExplicitToExposeDiff_visit___lam__12(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_15, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___Lean_Meta_addPPExplicitToExposeDiff_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = l_Lean_Meta_saveState___redArg(x_3, x_4, x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_5);
lean_inc(x_3);
x_10 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Meta_SavedState_restore___redArg(x_8, x_3, x_5, x_12);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_8);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
lean_ctor_set(x_13, 0, x_11);
return x_13;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_11);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_10, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
lean_dec(x_10);
x_20 = l_Lean_Meta_SavedState_restore___redArg(x_8, x_3, x_5, x_19);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_8);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
lean_ctor_set_tag(x_20, 1);
lean_ctor_set(x_20, 0, x_18);
return x_20;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_18);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___Lean_Meta_addPPExplicitToExposeDiff_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_withoutModifyingState___at___Lean_Meta_addPPExplicitToExposeDiff_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addPPExplicitToExposeDiff___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(x_1, x_4, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(x_2, x_4, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Meta_addPPExplicitToExposeDiff_visit(x_9, x_12, x_3, x_4, x_5, x_6, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addPPExplicitToExposeDiff(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_20; 
lean_inc(x_2);
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_addPPExplicitToExposeDiff___lam__0), 7, 2);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_2);
x_14 = lean_ctor_get(x_5, 2);
lean_inc(x_14);
x_15 = lean_mk_string_unchecked("pp", 2, 2);
x_16 = lean_mk_string_unchecked("all", 3, 3);
lean_inc(x_15);
x_17 = l_Lean_Name_mkStr2(x_15, x_16);
x_18 = lean_box(0);
x_19 = lean_unbox(x_18);
x_20 = l_Lean_KVMap_getBool(x_14, x_17, x_19);
lean_dec(x_17);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_mk_string_unchecked("explicit", 8, 8);
x_22 = l_Lean_Name_mkStr2(x_15, x_21);
x_23 = l_Lean_KVMap_getBool(x_14, x_22, x_20);
lean_dec(x_22);
lean_dec(x_14);
x_9 = x_23;
goto block_13;
}
else
{
lean_dec(x_15);
lean_dec(x_14);
x_9 = x_20;
goto block_13;
}
block_13:
{
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_2);
lean_dec(x_1);
x_10 = l_Lean_withoutModifyingState___at___Lean_Meta_addPPExplicitToExposeDiff_spec__0___redArg(x_8, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_2);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_7);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Meta_throwLetTypeMismatchMessage_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_alloc_closure((void*)(l_Lean_Meta_instInhabitedMetaM___lam__0___boxed), 5, 0);
x_8 = lean_panic_fn(x_7, x_1);
x_9 = lean_apply_5(x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Meta_throwLetTypeMismatchMessage_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_panic___at___Lean_Meta_throwLetTypeMismatchMessage_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwLetTypeMismatchMessage___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_2, 2);
lean_inc(x_20);
x_21 = lean_local_ctx_find(x_20, x_1);
if (lean_obj_tag(x_21) == 0)
{
x_7 = x_2;
x_8 = x_3;
x_9 = x_4;
x_10 = x_5;
x_11 = x_6;
goto block_19;
}
else
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec(x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_dec(x_22);
x_7 = x_2;
x_8 = x_3;
x_9 = x_4;
x_10 = x_5;
x_11 = x_6;
goto block_19;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_22, 3);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 4);
lean_inc(x_24);
lean_dec(x_22);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_24);
x_25 = lean_infer_type(x_24, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_28 = l_Lean_Meta_addPPExplicitToExposeDiff(x_26, x_23, x_2, x_3, x_4, x_5, x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = !lean_is_exclusive(x_29);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_32 = lean_ctor_get(x_29, 0);
x_33 = lean_ctor_get(x_29, 1);
x_34 = lean_mk_string_unchecked("invalid let declaration, term", 29, 29);
x_35 = l_Lean_stringToMessageData(x_34);
lean_dec(x_34);
x_36 = l_Lean_indentExpr(x_24);
lean_ctor_set_tag(x_29, 7);
lean_ctor_set(x_29, 1, x_36);
lean_ctor_set(x_29, 0, x_35);
x_37 = lean_mk_string_unchecked("\nhas type", 9, 9);
x_38 = l_Lean_stringToMessageData(x_37);
lean_dec(x_37);
x_39 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_39, 0, x_29);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Lean_indentExpr(x_32);
x_41 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_mk_string_unchecked("\nbut is expected to have type", 29, 29);
x_43 = l_Lean_stringToMessageData(x_42);
lean_dec(x_42);
x_44 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_43);
x_45 = l_Lean_indentExpr(x_33);
x_46 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_mk_string_unchecked("", 0, 0);
x_48 = l_Lean_stringToMessageData(x_47);
lean_dec(x_47);
x_49 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_48);
x_50 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_49, x_2, x_3, x_4, x_5, x_30);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_51 = lean_ctor_get(x_29, 0);
x_52 = lean_ctor_get(x_29, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_29);
x_53 = lean_mk_string_unchecked("invalid let declaration, term", 29, 29);
x_54 = l_Lean_stringToMessageData(x_53);
lean_dec(x_53);
x_55 = l_Lean_indentExpr(x_24);
x_56 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
x_57 = lean_mk_string_unchecked("\nhas type", 9, 9);
x_58 = l_Lean_stringToMessageData(x_57);
lean_dec(x_57);
x_59 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_59, 0, x_56);
lean_ctor_set(x_59, 1, x_58);
x_60 = l_Lean_indentExpr(x_51);
x_61 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_mk_string_unchecked("\nbut is expected to have type", 29, 29);
x_63 = l_Lean_stringToMessageData(x_62);
lean_dec(x_62);
x_64 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set(x_64, 1, x_63);
x_65 = l_Lean_indentExpr(x_52);
x_66 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
x_67 = lean_mk_string_unchecked("", 0, 0);
x_68 = l_Lean_stringToMessageData(x_67);
lean_dec(x_67);
x_69 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_69, 0, x_66);
lean_ctor_set(x_69, 1, x_68);
x_70 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_69, x_2, x_3, x_4, x_5, x_30);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_70;
}
}
else
{
uint8_t x_71; 
lean_dec(x_24);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_71 = !lean_is_exclusive(x_28);
if (x_71 == 0)
{
return x_28;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_28, 0);
x_73 = lean_ctor_get(x_28, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_28);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
else
{
uint8_t x_75; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_75 = !lean_is_exclusive(x_25);
if (x_75 == 0)
{
return x_25;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_25, 0);
x_77 = lean_ctor_get(x_25, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_25);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
}
block_19:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_mk_string_unchecked("Lean.Meta.Check", 15, 15);
x_13 = lean_mk_string_unchecked("Lean.Meta.throwLetTypeMismatchMessage", 37, 37);
x_14 = lean_unsigned_to_nat(179u);
x_15 = lean_unsigned_to_nat(9u);
x_16 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_17 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_12, x_13, x_14, x_15, x_16);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_12);
x_18 = l_panic___at___Lean_Meta_throwLetTypeMismatchMessage_spec__0___redArg(x_17, x_7, x_8, x_9, x_10, x_11);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwLetTypeMismatchMessage(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_throwLetTypeMismatchMessage___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHasTypeButIsExpectedMsg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_66; lean_object* x_67; lean_object* x_71; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_71 = lean_infer_type(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_71) == 0)
{
uint8_t x_72; 
x_72 = !lean_is_exclusive(x_71);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_71, 0);
x_74 = lean_ctor_get(x_71, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_75 = lean_infer_type(x_2, x_3, x_4, x_5, x_6, x_74);
if (lean_obj_tag(x_75) == 0)
{
uint8_t x_76; 
x_76 = !lean_is_exclusive(x_75);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_75, 0);
x_78 = lean_ctor_get(x_75, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_79 = l_Lean_Meta_addPPExplicitToExposeDiff(x_1, x_2, x_3, x_4, x_5, x_6, x_78);
if (lean_obj_tag(x_79) == 0)
{
uint8_t x_80; 
x_80 = !lean_is_exclusive(x_79);
if (x_80 == 0)
{
lean_object* x_81; uint8_t x_82; 
x_81 = lean_ctor_get(x_79, 0);
x_82 = !lean_is_exclusive(x_81);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_83 = lean_ctor_get(x_79, 1);
x_84 = lean_ctor_get(x_81, 0);
x_85 = lean_ctor_get(x_81, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_86 = l_Lean_Meta_addPPExplicitToExposeDiff(x_73, x_77, x_3, x_4, x_5, x_6, x_83);
if (lean_obj_tag(x_86) == 0)
{
uint8_t x_87; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_87 = !lean_is_exclusive(x_86);
if (x_87 == 0)
{
lean_object* x_88; uint8_t x_89; 
x_88 = lean_ctor_get(x_86, 0);
x_89 = !lean_is_exclusive(x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_90 = lean_ctor_get(x_88, 0);
x_91 = lean_ctor_get(x_88, 1);
x_92 = lean_mk_string_unchecked("has type", 8, 8);
x_93 = l_Lean_stringToMessageData(x_92);
lean_dec(x_92);
x_94 = lean_mk_string_unchecked("", 0, 0);
x_95 = l_Lean_stringToMessageData(x_94);
lean_dec(x_94);
x_96 = l_Lean_MessageData_ofExpr(x_84);
lean_inc(x_95);
lean_ctor_set_tag(x_88, 7);
lean_ctor_set(x_88, 1, x_96);
lean_ctor_set(x_88, 0, x_95);
x_97 = lean_mk_string_unchecked(" : ", 3, 3);
x_98 = l_Lean_stringToMessageData(x_97);
lean_dec(x_97);
lean_inc(x_98);
lean_ctor_set_tag(x_81, 7);
lean_ctor_set(x_81, 1, x_98);
lean_ctor_set(x_81, 0, x_88);
x_99 = l_Lean_MessageData_ofExpr(x_90);
lean_ctor_set_tag(x_79, 7);
lean_ctor_set(x_79, 1, x_99);
lean_inc(x_95);
lean_ctor_set_tag(x_75, 7);
lean_ctor_set(x_75, 1, x_95);
lean_ctor_set(x_75, 0, x_79);
x_100 = l_Lean_indentD(x_75);
lean_ctor_set_tag(x_71, 7);
lean_ctor_set(x_71, 1, x_100);
lean_ctor_set(x_71, 0, x_93);
x_101 = lean_mk_string_unchecked("\nbut is expected to have type", 29, 29);
x_102 = l_Lean_stringToMessageData(x_101);
lean_dec(x_101);
x_103 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_103, 0, x_71);
lean_ctor_set(x_103, 1, x_102);
x_104 = l_Lean_MessageData_ofExpr(x_85);
lean_inc(x_95);
x_105 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_105, 0, x_95);
lean_ctor_set(x_105, 1, x_104);
x_106 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_98);
x_107 = l_Lean_MessageData_ofExpr(x_91);
x_108 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
lean_inc(x_95);
x_109 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_95);
x_110 = l_Lean_indentD(x_109);
x_111 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_111, 0, x_103);
lean_ctor_set(x_111, 1, x_110);
x_112 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_95);
lean_ctor_set(x_86, 0, x_112);
return x_86;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_113 = lean_ctor_get(x_88, 0);
x_114 = lean_ctor_get(x_88, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_88);
x_115 = lean_mk_string_unchecked("has type", 8, 8);
x_116 = l_Lean_stringToMessageData(x_115);
lean_dec(x_115);
x_117 = lean_mk_string_unchecked("", 0, 0);
x_118 = l_Lean_stringToMessageData(x_117);
lean_dec(x_117);
x_119 = l_Lean_MessageData_ofExpr(x_84);
lean_inc(x_118);
x_120 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
x_121 = lean_mk_string_unchecked(" : ", 3, 3);
x_122 = l_Lean_stringToMessageData(x_121);
lean_dec(x_121);
lean_inc(x_122);
lean_ctor_set_tag(x_81, 7);
lean_ctor_set(x_81, 1, x_122);
lean_ctor_set(x_81, 0, x_120);
x_123 = l_Lean_MessageData_ofExpr(x_113);
lean_ctor_set_tag(x_79, 7);
lean_ctor_set(x_79, 1, x_123);
lean_inc(x_118);
lean_ctor_set_tag(x_75, 7);
lean_ctor_set(x_75, 1, x_118);
lean_ctor_set(x_75, 0, x_79);
x_124 = l_Lean_indentD(x_75);
lean_ctor_set_tag(x_71, 7);
lean_ctor_set(x_71, 1, x_124);
lean_ctor_set(x_71, 0, x_116);
x_125 = lean_mk_string_unchecked("\nbut is expected to have type", 29, 29);
x_126 = l_Lean_stringToMessageData(x_125);
lean_dec(x_125);
x_127 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_127, 0, x_71);
lean_ctor_set(x_127, 1, x_126);
x_128 = l_Lean_MessageData_ofExpr(x_85);
lean_inc(x_118);
x_129 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_129, 0, x_118);
lean_ctor_set(x_129, 1, x_128);
x_130 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_122);
x_131 = l_Lean_MessageData_ofExpr(x_114);
x_132 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
lean_inc(x_118);
x_133 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_118);
x_134 = l_Lean_indentD(x_133);
x_135 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_135, 0, x_127);
lean_ctor_set(x_135, 1, x_134);
x_136 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_118);
lean_ctor_set(x_86, 0, x_136);
return x_86;
}
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_137 = lean_ctor_get(x_86, 0);
x_138 = lean_ctor_get(x_86, 1);
lean_inc(x_138);
lean_inc(x_137);
lean_dec(x_86);
x_139 = lean_ctor_get(x_137, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_137, 1);
lean_inc(x_140);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 lean_ctor_release(x_137, 1);
 x_141 = x_137;
} else {
 lean_dec_ref(x_137);
 x_141 = lean_box(0);
}
x_142 = lean_mk_string_unchecked("has type", 8, 8);
x_143 = l_Lean_stringToMessageData(x_142);
lean_dec(x_142);
x_144 = lean_mk_string_unchecked("", 0, 0);
x_145 = l_Lean_stringToMessageData(x_144);
lean_dec(x_144);
x_146 = l_Lean_MessageData_ofExpr(x_84);
lean_inc(x_145);
if (lean_is_scalar(x_141)) {
 x_147 = lean_alloc_ctor(7, 2, 0);
} else {
 x_147 = x_141;
 lean_ctor_set_tag(x_147, 7);
}
lean_ctor_set(x_147, 0, x_145);
lean_ctor_set(x_147, 1, x_146);
x_148 = lean_mk_string_unchecked(" : ", 3, 3);
x_149 = l_Lean_stringToMessageData(x_148);
lean_dec(x_148);
lean_inc(x_149);
lean_ctor_set_tag(x_81, 7);
lean_ctor_set(x_81, 1, x_149);
lean_ctor_set(x_81, 0, x_147);
x_150 = l_Lean_MessageData_ofExpr(x_139);
lean_ctor_set_tag(x_79, 7);
lean_ctor_set(x_79, 1, x_150);
lean_inc(x_145);
lean_ctor_set_tag(x_75, 7);
lean_ctor_set(x_75, 1, x_145);
lean_ctor_set(x_75, 0, x_79);
x_151 = l_Lean_indentD(x_75);
lean_ctor_set_tag(x_71, 7);
lean_ctor_set(x_71, 1, x_151);
lean_ctor_set(x_71, 0, x_143);
x_152 = lean_mk_string_unchecked("\nbut is expected to have type", 29, 29);
x_153 = l_Lean_stringToMessageData(x_152);
lean_dec(x_152);
x_154 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_154, 0, x_71);
lean_ctor_set(x_154, 1, x_153);
x_155 = l_Lean_MessageData_ofExpr(x_85);
lean_inc(x_145);
x_156 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_156, 0, x_145);
lean_ctor_set(x_156, 1, x_155);
x_157 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_149);
x_158 = l_Lean_MessageData_ofExpr(x_140);
x_159 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_159, 0, x_157);
lean_ctor_set(x_159, 1, x_158);
lean_inc(x_145);
x_160 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_145);
x_161 = l_Lean_indentD(x_160);
x_162 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_162, 0, x_154);
lean_ctor_set(x_162, 1, x_161);
x_163 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_145);
x_164 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_164, 1, x_138);
return x_164;
}
}
else
{
lean_object* x_165; lean_object* x_166; 
lean_free_object(x_81);
lean_dec(x_85);
lean_dec(x_84);
lean_free_object(x_79);
lean_free_object(x_75);
lean_free_object(x_71);
x_165 = lean_ctor_get(x_86, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_86, 1);
lean_inc(x_166);
lean_dec(x_86);
x_66 = x_165;
x_67 = x_166;
goto block_70;
}
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_167 = lean_ctor_get(x_79, 1);
x_168 = lean_ctor_get(x_81, 0);
x_169 = lean_ctor_get(x_81, 1);
lean_inc(x_169);
lean_inc(x_168);
lean_dec(x_81);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_170 = l_Lean_Meta_addPPExplicitToExposeDiff(x_73, x_77, x_3, x_4, x_5, x_6, x_167);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_170, 1);
lean_inc(x_172);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 lean_ctor_release(x_170, 1);
 x_173 = x_170;
} else {
 lean_dec_ref(x_170);
 x_173 = lean_box(0);
}
x_174 = lean_ctor_get(x_171, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_171, 1);
lean_inc(x_175);
if (lean_is_exclusive(x_171)) {
 lean_ctor_release(x_171, 0);
 lean_ctor_release(x_171, 1);
 x_176 = x_171;
} else {
 lean_dec_ref(x_171);
 x_176 = lean_box(0);
}
x_177 = lean_mk_string_unchecked("has type", 8, 8);
x_178 = l_Lean_stringToMessageData(x_177);
lean_dec(x_177);
x_179 = lean_mk_string_unchecked("", 0, 0);
x_180 = l_Lean_stringToMessageData(x_179);
lean_dec(x_179);
x_181 = l_Lean_MessageData_ofExpr(x_168);
lean_inc(x_180);
if (lean_is_scalar(x_176)) {
 x_182 = lean_alloc_ctor(7, 2, 0);
} else {
 x_182 = x_176;
 lean_ctor_set_tag(x_182, 7);
}
lean_ctor_set(x_182, 0, x_180);
lean_ctor_set(x_182, 1, x_181);
x_183 = lean_mk_string_unchecked(" : ", 3, 3);
x_184 = l_Lean_stringToMessageData(x_183);
lean_dec(x_183);
lean_inc(x_184);
x_185 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_185, 0, x_182);
lean_ctor_set(x_185, 1, x_184);
x_186 = l_Lean_MessageData_ofExpr(x_174);
lean_ctor_set_tag(x_79, 7);
lean_ctor_set(x_79, 1, x_186);
lean_ctor_set(x_79, 0, x_185);
lean_inc(x_180);
lean_ctor_set_tag(x_75, 7);
lean_ctor_set(x_75, 1, x_180);
lean_ctor_set(x_75, 0, x_79);
x_187 = l_Lean_indentD(x_75);
lean_ctor_set_tag(x_71, 7);
lean_ctor_set(x_71, 1, x_187);
lean_ctor_set(x_71, 0, x_178);
x_188 = lean_mk_string_unchecked("\nbut is expected to have type", 29, 29);
x_189 = l_Lean_stringToMessageData(x_188);
lean_dec(x_188);
x_190 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_190, 0, x_71);
lean_ctor_set(x_190, 1, x_189);
x_191 = l_Lean_MessageData_ofExpr(x_169);
lean_inc(x_180);
x_192 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_192, 0, x_180);
lean_ctor_set(x_192, 1, x_191);
x_193 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set(x_193, 1, x_184);
x_194 = l_Lean_MessageData_ofExpr(x_175);
x_195 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_195, 0, x_193);
lean_ctor_set(x_195, 1, x_194);
lean_inc(x_180);
x_196 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set(x_196, 1, x_180);
x_197 = l_Lean_indentD(x_196);
x_198 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_198, 0, x_190);
lean_ctor_set(x_198, 1, x_197);
x_199 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_199, 0, x_198);
lean_ctor_set(x_199, 1, x_180);
if (lean_is_scalar(x_173)) {
 x_200 = lean_alloc_ctor(0, 2, 0);
} else {
 x_200 = x_173;
}
lean_ctor_set(x_200, 0, x_199);
lean_ctor_set(x_200, 1, x_172);
return x_200;
}
else
{
lean_object* x_201; lean_object* x_202; 
lean_dec(x_169);
lean_dec(x_168);
lean_free_object(x_79);
lean_free_object(x_75);
lean_free_object(x_71);
x_201 = lean_ctor_get(x_170, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_170, 1);
lean_inc(x_202);
lean_dec(x_170);
x_66 = x_201;
x_67 = x_202;
goto block_70;
}
}
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_203 = lean_ctor_get(x_79, 0);
x_204 = lean_ctor_get(x_79, 1);
lean_inc(x_204);
lean_inc(x_203);
lean_dec(x_79);
x_205 = lean_ctor_get(x_203, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_203, 1);
lean_inc(x_206);
if (lean_is_exclusive(x_203)) {
 lean_ctor_release(x_203, 0);
 lean_ctor_release(x_203, 1);
 x_207 = x_203;
} else {
 lean_dec_ref(x_203);
 x_207 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_208 = l_Lean_Meta_addPPExplicitToExposeDiff(x_73, x_77, x_3, x_4, x_5, x_6, x_204);
if (lean_obj_tag(x_208) == 0)
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_209 = lean_ctor_get(x_208, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_208, 1);
lean_inc(x_210);
if (lean_is_exclusive(x_208)) {
 lean_ctor_release(x_208, 0);
 lean_ctor_release(x_208, 1);
 x_211 = x_208;
} else {
 lean_dec_ref(x_208);
 x_211 = lean_box(0);
}
x_212 = lean_ctor_get(x_209, 0);
lean_inc(x_212);
x_213 = lean_ctor_get(x_209, 1);
lean_inc(x_213);
if (lean_is_exclusive(x_209)) {
 lean_ctor_release(x_209, 0);
 lean_ctor_release(x_209, 1);
 x_214 = x_209;
} else {
 lean_dec_ref(x_209);
 x_214 = lean_box(0);
}
x_215 = lean_mk_string_unchecked("has type", 8, 8);
x_216 = l_Lean_stringToMessageData(x_215);
lean_dec(x_215);
x_217 = lean_mk_string_unchecked("", 0, 0);
x_218 = l_Lean_stringToMessageData(x_217);
lean_dec(x_217);
x_219 = l_Lean_MessageData_ofExpr(x_205);
lean_inc(x_218);
if (lean_is_scalar(x_214)) {
 x_220 = lean_alloc_ctor(7, 2, 0);
} else {
 x_220 = x_214;
 lean_ctor_set_tag(x_220, 7);
}
lean_ctor_set(x_220, 0, x_218);
lean_ctor_set(x_220, 1, x_219);
x_221 = lean_mk_string_unchecked(" : ", 3, 3);
x_222 = l_Lean_stringToMessageData(x_221);
lean_dec(x_221);
lean_inc(x_222);
if (lean_is_scalar(x_207)) {
 x_223 = lean_alloc_ctor(7, 2, 0);
} else {
 x_223 = x_207;
 lean_ctor_set_tag(x_223, 7);
}
lean_ctor_set(x_223, 0, x_220);
lean_ctor_set(x_223, 1, x_222);
x_224 = l_Lean_MessageData_ofExpr(x_212);
x_225 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_225, 0, x_223);
lean_ctor_set(x_225, 1, x_224);
lean_inc(x_218);
lean_ctor_set_tag(x_75, 7);
lean_ctor_set(x_75, 1, x_218);
lean_ctor_set(x_75, 0, x_225);
x_226 = l_Lean_indentD(x_75);
lean_ctor_set_tag(x_71, 7);
lean_ctor_set(x_71, 1, x_226);
lean_ctor_set(x_71, 0, x_216);
x_227 = lean_mk_string_unchecked("\nbut is expected to have type", 29, 29);
x_228 = l_Lean_stringToMessageData(x_227);
lean_dec(x_227);
x_229 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_229, 0, x_71);
lean_ctor_set(x_229, 1, x_228);
x_230 = l_Lean_MessageData_ofExpr(x_206);
lean_inc(x_218);
x_231 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_231, 0, x_218);
lean_ctor_set(x_231, 1, x_230);
x_232 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_232, 0, x_231);
lean_ctor_set(x_232, 1, x_222);
x_233 = l_Lean_MessageData_ofExpr(x_213);
x_234 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_234, 0, x_232);
lean_ctor_set(x_234, 1, x_233);
lean_inc(x_218);
x_235 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_235, 0, x_234);
lean_ctor_set(x_235, 1, x_218);
x_236 = l_Lean_indentD(x_235);
x_237 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_237, 0, x_229);
lean_ctor_set(x_237, 1, x_236);
x_238 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_238, 0, x_237);
lean_ctor_set(x_238, 1, x_218);
if (lean_is_scalar(x_211)) {
 x_239 = lean_alloc_ctor(0, 2, 0);
} else {
 x_239 = x_211;
}
lean_ctor_set(x_239, 0, x_238);
lean_ctor_set(x_239, 1, x_210);
return x_239;
}
else
{
lean_object* x_240; lean_object* x_241; 
lean_dec(x_207);
lean_dec(x_206);
lean_dec(x_205);
lean_free_object(x_75);
lean_free_object(x_71);
x_240 = lean_ctor_get(x_208, 0);
lean_inc(x_240);
x_241 = lean_ctor_get(x_208, 1);
lean_inc(x_241);
lean_dec(x_208);
x_66 = x_240;
x_67 = x_241;
goto block_70;
}
}
}
else
{
lean_object* x_242; lean_object* x_243; 
lean_free_object(x_75);
lean_dec(x_77);
lean_free_object(x_71);
lean_dec(x_73);
x_242 = lean_ctor_get(x_79, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_79, 1);
lean_inc(x_243);
lean_dec(x_79);
x_66 = x_242;
x_67 = x_243;
goto block_70;
}
}
else
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; 
x_244 = lean_ctor_get(x_75, 0);
x_245 = lean_ctor_get(x_75, 1);
lean_inc(x_245);
lean_inc(x_244);
lean_dec(x_75);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_246 = l_Lean_Meta_addPPExplicitToExposeDiff(x_1, x_2, x_3, x_4, x_5, x_6, x_245);
if (lean_obj_tag(x_246) == 0)
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; 
x_247 = lean_ctor_get(x_246, 0);
lean_inc(x_247);
x_248 = lean_ctor_get(x_246, 1);
lean_inc(x_248);
if (lean_is_exclusive(x_246)) {
 lean_ctor_release(x_246, 0);
 lean_ctor_release(x_246, 1);
 x_249 = x_246;
} else {
 lean_dec_ref(x_246);
 x_249 = lean_box(0);
}
x_250 = lean_ctor_get(x_247, 0);
lean_inc(x_250);
x_251 = lean_ctor_get(x_247, 1);
lean_inc(x_251);
if (lean_is_exclusive(x_247)) {
 lean_ctor_release(x_247, 0);
 lean_ctor_release(x_247, 1);
 x_252 = x_247;
} else {
 lean_dec_ref(x_247);
 x_252 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_253 = l_Lean_Meta_addPPExplicitToExposeDiff(x_73, x_244, x_3, x_4, x_5, x_6, x_248);
if (lean_obj_tag(x_253) == 0)
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_254 = lean_ctor_get(x_253, 0);
lean_inc(x_254);
x_255 = lean_ctor_get(x_253, 1);
lean_inc(x_255);
if (lean_is_exclusive(x_253)) {
 lean_ctor_release(x_253, 0);
 lean_ctor_release(x_253, 1);
 x_256 = x_253;
} else {
 lean_dec_ref(x_253);
 x_256 = lean_box(0);
}
x_257 = lean_ctor_get(x_254, 0);
lean_inc(x_257);
x_258 = lean_ctor_get(x_254, 1);
lean_inc(x_258);
if (lean_is_exclusive(x_254)) {
 lean_ctor_release(x_254, 0);
 lean_ctor_release(x_254, 1);
 x_259 = x_254;
} else {
 lean_dec_ref(x_254);
 x_259 = lean_box(0);
}
x_260 = lean_mk_string_unchecked("has type", 8, 8);
x_261 = l_Lean_stringToMessageData(x_260);
lean_dec(x_260);
x_262 = lean_mk_string_unchecked("", 0, 0);
x_263 = l_Lean_stringToMessageData(x_262);
lean_dec(x_262);
x_264 = l_Lean_MessageData_ofExpr(x_250);
lean_inc(x_263);
if (lean_is_scalar(x_259)) {
 x_265 = lean_alloc_ctor(7, 2, 0);
} else {
 x_265 = x_259;
 lean_ctor_set_tag(x_265, 7);
}
lean_ctor_set(x_265, 0, x_263);
lean_ctor_set(x_265, 1, x_264);
x_266 = lean_mk_string_unchecked(" : ", 3, 3);
x_267 = l_Lean_stringToMessageData(x_266);
lean_dec(x_266);
lean_inc(x_267);
if (lean_is_scalar(x_252)) {
 x_268 = lean_alloc_ctor(7, 2, 0);
} else {
 x_268 = x_252;
 lean_ctor_set_tag(x_268, 7);
}
lean_ctor_set(x_268, 0, x_265);
lean_ctor_set(x_268, 1, x_267);
x_269 = l_Lean_MessageData_ofExpr(x_257);
if (lean_is_scalar(x_249)) {
 x_270 = lean_alloc_ctor(7, 2, 0);
} else {
 x_270 = x_249;
 lean_ctor_set_tag(x_270, 7);
}
lean_ctor_set(x_270, 0, x_268);
lean_ctor_set(x_270, 1, x_269);
lean_inc(x_263);
x_271 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_271, 0, x_270);
lean_ctor_set(x_271, 1, x_263);
x_272 = l_Lean_indentD(x_271);
lean_ctor_set_tag(x_71, 7);
lean_ctor_set(x_71, 1, x_272);
lean_ctor_set(x_71, 0, x_261);
x_273 = lean_mk_string_unchecked("\nbut is expected to have type", 29, 29);
x_274 = l_Lean_stringToMessageData(x_273);
lean_dec(x_273);
x_275 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_275, 0, x_71);
lean_ctor_set(x_275, 1, x_274);
x_276 = l_Lean_MessageData_ofExpr(x_251);
lean_inc(x_263);
x_277 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_277, 0, x_263);
lean_ctor_set(x_277, 1, x_276);
x_278 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_278, 0, x_277);
lean_ctor_set(x_278, 1, x_267);
x_279 = l_Lean_MessageData_ofExpr(x_258);
x_280 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_280, 0, x_278);
lean_ctor_set(x_280, 1, x_279);
lean_inc(x_263);
x_281 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_281, 0, x_280);
lean_ctor_set(x_281, 1, x_263);
x_282 = l_Lean_indentD(x_281);
x_283 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_283, 0, x_275);
lean_ctor_set(x_283, 1, x_282);
x_284 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_284, 0, x_283);
lean_ctor_set(x_284, 1, x_263);
if (lean_is_scalar(x_256)) {
 x_285 = lean_alloc_ctor(0, 2, 0);
} else {
 x_285 = x_256;
}
lean_ctor_set(x_285, 0, x_284);
lean_ctor_set(x_285, 1, x_255);
return x_285;
}
else
{
lean_object* x_286; lean_object* x_287; 
lean_dec(x_252);
lean_dec(x_251);
lean_dec(x_250);
lean_dec(x_249);
lean_free_object(x_71);
x_286 = lean_ctor_get(x_253, 0);
lean_inc(x_286);
x_287 = lean_ctor_get(x_253, 1);
lean_inc(x_287);
lean_dec(x_253);
x_66 = x_286;
x_67 = x_287;
goto block_70;
}
}
else
{
lean_object* x_288; lean_object* x_289; 
lean_dec(x_244);
lean_free_object(x_71);
lean_dec(x_73);
x_288 = lean_ctor_get(x_246, 0);
lean_inc(x_288);
x_289 = lean_ctor_get(x_246, 1);
lean_inc(x_289);
lean_dec(x_246);
x_66 = x_288;
x_67 = x_289;
goto block_70;
}
}
}
else
{
lean_object* x_290; lean_object* x_291; 
lean_free_object(x_71);
lean_dec(x_73);
x_290 = lean_ctor_get(x_75, 0);
lean_inc(x_290);
x_291 = lean_ctor_get(x_75, 1);
lean_inc(x_291);
lean_dec(x_75);
x_66 = x_290;
x_67 = x_291;
goto block_70;
}
}
else
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; 
x_292 = lean_ctor_get(x_71, 0);
x_293 = lean_ctor_get(x_71, 1);
lean_inc(x_293);
lean_inc(x_292);
lean_dec(x_71);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_294 = lean_infer_type(x_2, x_3, x_4, x_5, x_6, x_293);
if (lean_obj_tag(x_294) == 0)
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; 
x_295 = lean_ctor_get(x_294, 0);
lean_inc(x_295);
x_296 = lean_ctor_get(x_294, 1);
lean_inc(x_296);
if (lean_is_exclusive(x_294)) {
 lean_ctor_release(x_294, 0);
 lean_ctor_release(x_294, 1);
 x_297 = x_294;
} else {
 lean_dec_ref(x_294);
 x_297 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_298 = l_Lean_Meta_addPPExplicitToExposeDiff(x_1, x_2, x_3, x_4, x_5, x_6, x_296);
if (lean_obj_tag(x_298) == 0)
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; 
x_299 = lean_ctor_get(x_298, 0);
lean_inc(x_299);
x_300 = lean_ctor_get(x_298, 1);
lean_inc(x_300);
if (lean_is_exclusive(x_298)) {
 lean_ctor_release(x_298, 0);
 lean_ctor_release(x_298, 1);
 x_301 = x_298;
} else {
 lean_dec_ref(x_298);
 x_301 = lean_box(0);
}
x_302 = lean_ctor_get(x_299, 0);
lean_inc(x_302);
x_303 = lean_ctor_get(x_299, 1);
lean_inc(x_303);
if (lean_is_exclusive(x_299)) {
 lean_ctor_release(x_299, 0);
 lean_ctor_release(x_299, 1);
 x_304 = x_299;
} else {
 lean_dec_ref(x_299);
 x_304 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_305 = l_Lean_Meta_addPPExplicitToExposeDiff(x_292, x_295, x_3, x_4, x_5, x_6, x_300);
if (lean_obj_tag(x_305) == 0)
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_306 = lean_ctor_get(x_305, 0);
lean_inc(x_306);
x_307 = lean_ctor_get(x_305, 1);
lean_inc(x_307);
if (lean_is_exclusive(x_305)) {
 lean_ctor_release(x_305, 0);
 lean_ctor_release(x_305, 1);
 x_308 = x_305;
} else {
 lean_dec_ref(x_305);
 x_308 = lean_box(0);
}
x_309 = lean_ctor_get(x_306, 0);
lean_inc(x_309);
x_310 = lean_ctor_get(x_306, 1);
lean_inc(x_310);
if (lean_is_exclusive(x_306)) {
 lean_ctor_release(x_306, 0);
 lean_ctor_release(x_306, 1);
 x_311 = x_306;
} else {
 lean_dec_ref(x_306);
 x_311 = lean_box(0);
}
x_312 = lean_mk_string_unchecked("has type", 8, 8);
x_313 = l_Lean_stringToMessageData(x_312);
lean_dec(x_312);
x_314 = lean_mk_string_unchecked("", 0, 0);
x_315 = l_Lean_stringToMessageData(x_314);
lean_dec(x_314);
x_316 = l_Lean_MessageData_ofExpr(x_302);
lean_inc(x_315);
if (lean_is_scalar(x_311)) {
 x_317 = lean_alloc_ctor(7, 2, 0);
} else {
 x_317 = x_311;
 lean_ctor_set_tag(x_317, 7);
}
lean_ctor_set(x_317, 0, x_315);
lean_ctor_set(x_317, 1, x_316);
x_318 = lean_mk_string_unchecked(" : ", 3, 3);
x_319 = l_Lean_stringToMessageData(x_318);
lean_dec(x_318);
lean_inc(x_319);
if (lean_is_scalar(x_304)) {
 x_320 = lean_alloc_ctor(7, 2, 0);
} else {
 x_320 = x_304;
 lean_ctor_set_tag(x_320, 7);
}
lean_ctor_set(x_320, 0, x_317);
lean_ctor_set(x_320, 1, x_319);
x_321 = l_Lean_MessageData_ofExpr(x_309);
if (lean_is_scalar(x_301)) {
 x_322 = lean_alloc_ctor(7, 2, 0);
} else {
 x_322 = x_301;
 lean_ctor_set_tag(x_322, 7);
}
lean_ctor_set(x_322, 0, x_320);
lean_ctor_set(x_322, 1, x_321);
lean_inc(x_315);
if (lean_is_scalar(x_297)) {
 x_323 = lean_alloc_ctor(7, 2, 0);
} else {
 x_323 = x_297;
 lean_ctor_set_tag(x_323, 7);
}
lean_ctor_set(x_323, 0, x_322);
lean_ctor_set(x_323, 1, x_315);
x_324 = l_Lean_indentD(x_323);
x_325 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_325, 0, x_313);
lean_ctor_set(x_325, 1, x_324);
x_326 = lean_mk_string_unchecked("\nbut is expected to have type", 29, 29);
x_327 = l_Lean_stringToMessageData(x_326);
lean_dec(x_326);
x_328 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_328, 0, x_325);
lean_ctor_set(x_328, 1, x_327);
x_329 = l_Lean_MessageData_ofExpr(x_303);
lean_inc(x_315);
x_330 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_330, 0, x_315);
lean_ctor_set(x_330, 1, x_329);
x_331 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_331, 0, x_330);
lean_ctor_set(x_331, 1, x_319);
x_332 = l_Lean_MessageData_ofExpr(x_310);
x_333 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_333, 0, x_331);
lean_ctor_set(x_333, 1, x_332);
lean_inc(x_315);
x_334 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_334, 0, x_333);
lean_ctor_set(x_334, 1, x_315);
x_335 = l_Lean_indentD(x_334);
x_336 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_336, 0, x_328);
lean_ctor_set(x_336, 1, x_335);
x_337 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_337, 0, x_336);
lean_ctor_set(x_337, 1, x_315);
if (lean_is_scalar(x_308)) {
 x_338 = lean_alloc_ctor(0, 2, 0);
} else {
 x_338 = x_308;
}
lean_ctor_set(x_338, 0, x_337);
lean_ctor_set(x_338, 1, x_307);
return x_338;
}
else
{
lean_object* x_339; lean_object* x_340; 
lean_dec(x_304);
lean_dec(x_303);
lean_dec(x_302);
lean_dec(x_301);
lean_dec(x_297);
x_339 = lean_ctor_get(x_305, 0);
lean_inc(x_339);
x_340 = lean_ctor_get(x_305, 1);
lean_inc(x_340);
lean_dec(x_305);
x_66 = x_339;
x_67 = x_340;
goto block_70;
}
}
else
{
lean_object* x_341; lean_object* x_342; 
lean_dec(x_297);
lean_dec(x_295);
lean_dec(x_292);
x_341 = lean_ctor_get(x_298, 0);
lean_inc(x_341);
x_342 = lean_ctor_get(x_298, 1);
lean_inc(x_342);
lean_dec(x_298);
x_66 = x_341;
x_67 = x_342;
goto block_70;
}
}
else
{
lean_object* x_343; lean_object* x_344; 
lean_dec(x_292);
x_343 = lean_ctor_get(x_294, 0);
lean_inc(x_343);
x_344 = lean_ctor_get(x_294, 1);
lean_inc(x_344);
lean_dec(x_294);
x_66 = x_343;
x_67 = x_344;
goto block_70;
}
}
}
else
{
lean_object* x_345; lean_object* x_346; 
x_345 = lean_ctor_get(x_71, 0);
lean_inc(x_345);
x_346 = lean_ctor_get(x_71, 1);
lean_inc(x_346);
lean_dec(x_71);
x_66 = x_345;
x_67 = x_346;
goto block_70;
}
block_65:
{
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
x_11 = l_Lean_Meta_addPPExplicitToExposeDiff(x_1, x_2, x_3, x_4, x_5, x_6, x_9);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = lean_mk_string_unchecked("has type", 8, 8);
x_18 = l_Lean_stringToMessageData(x_17);
lean_dec(x_17);
x_19 = l_Lean_indentExpr(x_15);
lean_ctor_set_tag(x_13, 7);
lean_ctor_set(x_13, 1, x_19);
lean_ctor_set(x_13, 0, x_18);
x_20 = lean_mk_string_unchecked("\nbut is expected to have type", 29, 29);
x_21 = l_Lean_stringToMessageData(x_20);
lean_dec(x_20);
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_13);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_indentExpr(x_16);
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_mk_string_unchecked("", 0, 0);
x_26 = l_Lean_stringToMessageData(x_25);
lean_dec(x_25);
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_26);
lean_ctor_set(x_11, 0, x_27);
return x_11;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_28 = lean_ctor_get(x_13, 0);
x_29 = lean_ctor_get(x_13, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_13);
x_30 = lean_mk_string_unchecked("has type", 8, 8);
x_31 = l_Lean_stringToMessageData(x_30);
lean_dec(x_30);
x_32 = l_Lean_indentExpr(x_28);
x_33 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_mk_string_unchecked("\nbut is expected to have type", 29, 29);
x_35 = l_Lean_stringToMessageData(x_34);
lean_dec(x_34);
x_36 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_Lean_indentExpr(x_29);
x_38 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_mk_string_unchecked("", 0, 0);
x_40 = l_Lean_stringToMessageData(x_39);
lean_dec(x_39);
x_41 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set(x_41, 1, x_40);
lean_ctor_set(x_11, 0, x_41);
return x_11;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_42 = lean_ctor_get(x_11, 0);
x_43 = lean_ctor_get(x_11, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_11);
x_44 = lean_ctor_get(x_42, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_46 = x_42;
} else {
 lean_dec_ref(x_42);
 x_46 = lean_box(0);
}
x_47 = lean_mk_string_unchecked("has type", 8, 8);
x_48 = l_Lean_stringToMessageData(x_47);
lean_dec(x_47);
x_49 = l_Lean_indentExpr(x_44);
if (lean_is_scalar(x_46)) {
 x_50 = lean_alloc_ctor(7, 2, 0);
} else {
 x_50 = x_46;
 lean_ctor_set_tag(x_50, 7);
}
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_mk_string_unchecked("\nbut is expected to have type", 29, 29);
x_52 = l_Lean_stringToMessageData(x_51);
lean_dec(x_51);
x_53 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_52);
x_54 = l_Lean_indentExpr(x_45);
x_55 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_mk_string_unchecked("", 0, 0);
x_57 = l_Lean_stringToMessageData(x_56);
lean_dec(x_56);
x_58 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_57);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_43);
return x_59;
}
}
else
{
uint8_t x_60; 
x_60 = !lean_is_exclusive(x_11);
if (x_60 == 0)
{
return x_11;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_11, 0);
x_62 = lean_ctor_get(x_11, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_11);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
else
{
lean_object* x_64; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_8);
lean_ctor_set(x_64, 1, x_9);
return x_64;
}
}
block_70:
{
uint8_t x_68; 
x_68 = l_Lean_Exception_isInterrupt(x_66);
if (x_68 == 0)
{
uint8_t x_69; 
x_69 = l_Lean_Exception_isRuntime(x_66);
x_8 = x_66;
x_9 = x_67;
x_10 = x_69;
goto block_65;
}
else
{
x_8 = x_66;
x_9 = x_67;
x_10 = x_68;
goto block_65;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwAppTypeMismatch___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_8 = l___private_Lean_Meta_Check_0__Lean_Meta_getFunctionDomain(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_52; uint8_t x_53; uint8_t x_54; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_13 = x_9;
} else {
 lean_dec_ref(x_9);
 x_13 = lean_box(0);
}
lean_inc(x_2);
x_52 = l_Lean_Expr_app___override(x_1, x_2);
x_53 = lean_unbox(x_12);
lean_dec(x_12);
x_54 = l_Lean_BinderInfo_isExplicit(x_53);
if (x_54 == 0)
{
lean_object* x_55; 
x_55 = l_Lean_Expr_setAppPPExplicit(x_52);
x_14 = x_55;
x_15 = x_3;
x_16 = x_4;
x_17 = x_5;
x_18 = x_6;
x_19 = x_10;
goto block_51;
}
else
{
x_14 = x_52;
x_15 = x_3;
x_16 = x_4;
x_17 = x_5;
x_18 = x_6;
x_19 = x_10;
goto block_51;
}
block_51:
{
lean_object* x_20; 
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_2);
x_20 = lean_infer_type(x_2, x_15, x_16, x_17, x_18, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_23 = l_Lean_Meta_mkHasTypeButIsExpectedMsg(x_21, x_11, x_15, x_16, x_17, x_18, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_mk_string_unchecked("application type mismatch", 25, 25);
x_27 = l_Lean_stringToMessageData(x_26);
lean_dec(x_26);
x_28 = l_Lean_indentExpr(x_14);
if (lean_is_scalar(x_13)) {
 x_29 = lean_alloc_ctor(7, 2, 0);
} else {
 x_29 = x_13;
 lean_ctor_set_tag(x_29, 7);
}
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_mk_string_unchecked("\nargument", 9, 9);
x_31 = l_Lean_stringToMessageData(x_30);
lean_dec(x_30);
x_32 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Lean_indentExpr(x_2);
x_34 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_mk_string_unchecked("\n", 1, 1);
x_36 = l_Lean_stringToMessageData(x_35);
lean_dec(x_35);
x_37 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_24);
x_39 = lean_mk_string_unchecked("", 0, 0);
x_40 = l_Lean_stringToMessageData(x_39);
lean_dec(x_39);
x_41 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_41, x_15, x_16, x_17, x_18, x_25);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
return x_42;
}
else
{
uint8_t x_43; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_2);
x_43 = !lean_is_exclusive(x_23);
if (x_43 == 0)
{
return x_23;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_23, 0);
x_45 = lean_ctor_get(x_23, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_23);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_2);
x_47 = !lean_is_exclusive(x_20);
if (x_47 == 0)
{
return x_20;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_20, 0);
x_49 = lean_ctor_get(x_20, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_20);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
}
else
{
uint8_t x_56; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_56 = !lean_is_exclusive(x_8);
if (x_56 == 0)
{
return x_8;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_8, 0);
x_58 = lean_ctor_get(x_8, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_8);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwAppTypeMismatch(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_throwAppTypeMismatch___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkApp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_11 = lean_whnf(x_9, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 7)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_15 = lean_infer_type(x_2, x_3, x_4, x_5, x_6, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_18 = l_Lean_Meta_isExprDefEq(x_14, x_16, x_3, x_4, x_5, x_6, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_unbox(x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = l_Lean_Meta_throwAppTypeMismatch___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_21);
return x_22;
}
else
{
uint8_t x_23; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_18);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_18, 0);
lean_dec(x_24);
x_25 = lean_box(0);
lean_ctor_set(x_18, 0, x_25);
return x_18;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_18, 1);
lean_inc(x_26);
lean_dec(x_18);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
}
else
{
uint8_t x_29; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_18);
if (x_29 == 0)
{
return x_18;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_18, 0);
x_31 = lean_ctor_get(x_18, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_18);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_15);
if (x_33 == 0)
{
return x_15;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_15, 0);
x_35 = lean_ctor_get(x_15, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_15);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_12);
x_37 = lean_ctor_get(x_11, 1);
lean_inc(x_37);
lean_dec(x_11);
x_38 = l_Lean_Expr_app___override(x_1, x_2);
x_39 = l_Lean_Meta_throwFunctionExpected___redArg(x_38, x_3, x_4, x_5, x_6, x_37);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_39;
}
}
else
{
uint8_t x_40; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_11);
if (x_40 == 0)
{
return x_11;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_11, 0);
x_42 = lean_ctor_get(x_11, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_11);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_44 = !lean_is_exclusive(x_8);
if (x_44 == 0)
{
return x_8;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_8, 0);
x_46 = lean_ctor_get(x_8, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_8);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkProj(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_9 = lean_infer_type(x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_12 = lean_whnf(x_10, x_4, x_5, x_6, x_7, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Expr_proj___override(x_1, x_2, x_3);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_15);
x_16 = lean_infer_type(x_15, x_4, x_5, x_6, x_7, x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_13);
x_19 = l_Lean_Meta_isProp(x_13, x_4, x_5, x_6, x_7, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_22 = l_Lean_Meta_isProp(x_17, x_4, x_5, x_6, x_7, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_29; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_25 = x_22;
} else {
 lean_dec_ref(x_22);
 x_25 = lean_box(0);
}
x_29 = lean_unbox(x_20);
lean_dec(x_20);
if (x_29 == 0)
{
lean_dec(x_23);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
goto block_28;
}
else
{
uint8_t x_30; 
x_30 = lean_unbox(x_23);
lean_dec(x_23);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_25);
x_31 = lean_mk_string_unchecked("invalid projection", 18, 18);
x_32 = l_Lean_stringToMessageData(x_31);
lean_dec(x_31);
x_33 = l_Lean_indentExpr(x_15);
x_34 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_mk_string_unchecked("\nfrom type", 10, 10);
x_36 = l_Lean_stringToMessageData(x_35);
lean_dec(x_35);
x_37 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_Lean_indentExpr(x_13);
x_39 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_mk_string_unchecked("", 0, 0);
x_41 = l_Lean_stringToMessageData(x_40);
lean_dec(x_40);
x_42 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_41);
x_43 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_42, x_4, x_5, x_6, x_7, x_24);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_43;
}
else
{
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
goto block_28;
}
}
block_28:
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_box(0);
if (lean_is_scalar(x_25)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_25;
}
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_24);
return x_27;
}
}
else
{
uint8_t x_44; 
lean_dec(x_20);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_44 = !lean_is_exclusive(x_22);
if (x_44 == 0)
{
return x_22;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_22, 0);
x_46 = lean_ctor_get(x_22, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_22);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
uint8_t x_48; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_48 = !lean_is_exclusive(x_19);
if (x_48 == 0)
{
return x_19;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_19, 0);
x_50 = lean_ctor_get(x_19, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_19);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
uint8_t x_52; 
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_52 = !lean_is_exclusive(x_16);
if (x_52 == 0)
{
return x_16;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_16, 0);
x_54 = lean_ctor_get(x_16, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_16);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
uint8_t x_56; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_56 = !lean_is_exclusive(x_12);
if (x_56 == 0)
{
return x_12;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_12, 0);
x_58 = lean_ctor_get(x_12, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_12);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
uint8_t x_60; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_60 = !lean_is_exclusive(x_9);
if (x_60 == 0)
{
return x_9;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_9, 0);
x_62 = lean_ctor_get(x_9, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_9);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_check(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_17; uint8_t x_18; 
x_17 = lean_st_ref_get(x_2, x_7);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint64_t x_23; lean_object* x_24; uint64_t x_25; uint64_t x_26; uint64_t x_27; lean_object* x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; size_t x_32; size_t x_33; lean_object* x_34; size_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_90; size_t x_94; size_t x_95; lean_object* x_96; lean_object* x_97; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_array_get_size(x_21);
x_23 = l_Lean_Expr_hash(x_1);
x_24 = lean_unsigned_to_nat(32u);
x_25 = lean_uint64_of_nat(x_24);
x_26 = lean_uint64_shift_right(x_23, x_25);
x_27 = lean_uint64_xor(x_23, x_26);
x_28 = lean_unsigned_to_nat(16u);
x_29 = lean_uint64_of_nat(x_28);
x_30 = lean_uint64_shift_right(x_27, x_29);
x_31 = lean_uint64_xor(x_27, x_30);
x_32 = lean_uint64_to_usize(x_31);
x_33 = lean_usize_of_nat(x_22);
lean_dec(x_22);
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_usize_of_nat(x_34);
x_94 = lean_usize_sub(x_33, x_35);
x_95 = lean_usize_land(x_32, x_94);
x_96 = lean_array_uget(x_21, x_95);
lean_dec(x_21);
x_97 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__0(lean_box(0), x_1, x_96);
lean_dec(x_96);
if (lean_obj_tag(x_97) == 0)
{
lean_free_object(x_17);
switch (lean_obj_tag(x_1)) {
case 4:
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_1, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_1, 1);
lean_inc(x_99);
x_100 = l___private_Lean_Meta_Check_0__Lean_Meta_checkConstant(x_98, x_99, x_3, x_4, x_5, x_6, x_20);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_90 = x_100;
goto block_93;
}
case 5:
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_1, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_1, 1);
lean_inc(x_102);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_101);
x_103 = l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_check(x_101, x_2, x_3, x_4, x_5, x_6, x_20);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; 
x_104 = lean_ctor_get(x_103, 1);
lean_inc(x_104);
lean_dec(x_103);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_102);
x_105 = l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_check(x_102, x_2, x_3, x_4, x_5, x_6, x_104);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; 
x_106 = lean_ctor_get(x_105, 1);
lean_inc(x_106);
lean_dec(x_105);
x_107 = l_Lean_Meta_checkApp(x_101, x_102, x_3, x_4, x_5, x_6, x_106);
x_90 = x_107;
goto block_93;
}
else
{
lean_dec(x_102);
lean_dec(x_101);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_90 = x_105;
goto block_93;
}
}
else
{
lean_dec(x_102);
lean_dec(x_101);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_90 = x_103;
goto block_93;
}
}
case 6:
{
lean_object* x_108; 
lean_inc(x_2);
lean_inc(x_1);
x_108 = l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkLambdaLet(x_1, x_2, x_3, x_4, x_5, x_6, x_20);
x_90 = x_108;
goto block_93;
}
case 7:
{
lean_object* x_109; 
lean_inc(x_2);
lean_inc(x_1);
x_109 = l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkForall(x_1, x_2, x_3, x_4, x_5, x_6, x_20);
x_90 = x_109;
goto block_93;
}
case 8:
{
lean_object* x_110; 
lean_inc(x_2);
lean_inc(x_1);
x_110 = l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkLambdaLet(x_1, x_2, x_3, x_4, x_5, x_6, x_20);
x_90 = x_110;
goto block_93;
}
case 10:
{
lean_object* x_111; lean_object* x_112; 
x_111 = lean_ctor_get(x_1, 1);
lean_inc(x_111);
lean_inc(x_2);
x_112 = l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_check(x_111, x_2, x_3, x_4, x_5, x_6, x_20);
x_90 = x_112;
goto block_93;
}
case 11:
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_113 = lean_ctor_get(x_1, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_1, 1);
lean_inc(x_114);
x_115 = lean_ctor_get(x_1, 2);
lean_inc(x_115);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_115);
x_116 = l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_check(x_115, x_2, x_3, x_4, x_5, x_6, x_20);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; 
x_117 = lean_ctor_get(x_116, 1);
lean_inc(x_117);
lean_dec(x_116);
x_118 = l_Lean_Meta_checkProj(x_113, x_114, x_115, x_3, x_4, x_5, x_6, x_117);
x_90 = x_118;
goto block_93;
}
else
{
lean_dec(x_115);
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_90 = x_116;
goto block_93;
}
}
default: 
{
lean_object* x_119; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_119 = lean_box(0);
x_36 = x_119;
x_37 = x_20;
goto block_89;
}
}
}
else
{
lean_object* x_120; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_120 = lean_ctor_get(x_97, 0);
lean_inc(x_120);
lean_dec(x_97);
lean_ctor_set(x_17, 0, x_120);
return x_17;
}
block_89:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_38 = lean_st_ref_take(x_2, x_37);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = !lean_is_exclusive(x_39);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; size_t x_45; size_t x_46; size_t x_47; lean_object* x_48; uint8_t x_49; 
x_42 = lean_ctor_get(x_39, 0);
x_43 = lean_ctor_get(x_39, 1);
x_44 = lean_array_get_size(x_43);
x_45 = lean_usize_of_nat(x_44);
lean_dec(x_44);
x_46 = lean_usize_sub(x_45, x_35);
x_47 = lean_usize_land(x_32, x_46);
x_48 = lean_array_uget(x_43, x_47);
x_49 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__1(lean_box(0), x_1, x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_50 = lean_nat_add(x_42, x_34);
lean_dec(x_42);
lean_inc(x_36);
x_51 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_51, 0, x_1);
lean_ctor_set(x_51, 1, x_36);
lean_ctor_set(x_51, 2, x_48);
x_52 = lean_array_uset(x_43, x_47, x_51);
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
lean_object* x_59; 
x_59 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__2(lean_box(0), x_52);
lean_ctor_set(x_39, 1, x_59);
lean_ctor_set(x_39, 0, x_50);
x_8 = x_40;
x_9 = x_36;
x_10 = x_39;
goto block_16;
}
else
{
lean_ctor_set(x_39, 1, x_52);
lean_ctor_set(x_39, 0, x_50);
x_8 = x_40;
x_9 = x_36;
x_10 = x_39;
goto block_16;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_60 = lean_box(0);
x_61 = lean_array_uset(x_43, x_47, x_60);
lean_inc(x_36);
x_62 = l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__5(lean_box(0), x_1, x_36, x_48);
x_63 = lean_array_uset(x_61, x_47, x_62);
lean_ctor_set(x_39, 1, x_63);
x_8 = x_40;
x_9 = x_36;
x_10 = x_39;
goto block_16;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; size_t x_67; size_t x_68; size_t x_69; lean_object* x_70; uint8_t x_71; 
x_64 = lean_ctor_get(x_39, 0);
x_65 = lean_ctor_get(x_39, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_39);
x_66 = lean_array_get_size(x_65);
x_67 = lean_usize_of_nat(x_66);
lean_dec(x_66);
x_68 = lean_usize_sub(x_67, x_35);
x_69 = lean_usize_land(x_32, x_68);
x_70 = lean_array_uget(x_65, x_69);
x_71 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__1(lean_box(0), x_1, x_70);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_72 = lean_nat_add(x_64, x_34);
lean_dec(x_64);
lean_inc(x_36);
x_73 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_73, 0, x_1);
lean_ctor_set(x_73, 1, x_36);
lean_ctor_set(x_73, 2, x_70);
x_74 = lean_array_uset(x_65, x_69, x_73);
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
lean_object* x_81; lean_object* x_82; 
x_81 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__2(lean_box(0), x_74);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_72);
lean_ctor_set(x_82, 1, x_81);
x_8 = x_40;
x_9 = x_36;
x_10 = x_82;
goto block_16;
}
else
{
lean_object* x_83; 
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_72);
lean_ctor_set(x_83, 1, x_74);
x_8 = x_40;
x_9 = x_36;
x_10 = x_83;
goto block_16;
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_84 = lean_box(0);
x_85 = lean_array_uset(x_65, x_69, x_84);
lean_inc(x_36);
x_86 = l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__5(lean_box(0), x_1, x_36, x_70);
x_87 = lean_array_uset(x_85, x_69, x_86);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_64);
lean_ctor_set(x_88, 1, x_87);
x_8 = x_40;
x_9 = x_36;
x_10 = x_88;
goto block_16;
}
}
}
block_93:
{
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
x_36 = x_91;
x_37 = x_92;
goto block_89;
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_90;
}
}
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; uint64_t x_125; lean_object* x_126; uint64_t x_127; uint64_t x_128; uint64_t x_129; lean_object* x_130; uint64_t x_131; uint64_t x_132; uint64_t x_133; size_t x_134; size_t x_135; lean_object* x_136; size_t x_137; lean_object* x_138; lean_object* x_139; lean_object* x_170; size_t x_174; size_t x_175; lean_object* x_176; lean_object* x_177; 
x_121 = lean_ctor_get(x_17, 0);
x_122 = lean_ctor_get(x_17, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_17);
x_123 = lean_ctor_get(x_121, 1);
lean_inc(x_123);
lean_dec(x_121);
x_124 = lean_array_get_size(x_123);
x_125 = l_Lean_Expr_hash(x_1);
x_126 = lean_unsigned_to_nat(32u);
x_127 = lean_uint64_of_nat(x_126);
x_128 = lean_uint64_shift_right(x_125, x_127);
x_129 = lean_uint64_xor(x_125, x_128);
x_130 = lean_unsigned_to_nat(16u);
x_131 = lean_uint64_of_nat(x_130);
x_132 = lean_uint64_shift_right(x_129, x_131);
x_133 = lean_uint64_xor(x_129, x_132);
x_134 = lean_uint64_to_usize(x_133);
x_135 = lean_usize_of_nat(x_124);
lean_dec(x_124);
x_136 = lean_unsigned_to_nat(1u);
x_137 = lean_usize_of_nat(x_136);
x_174 = lean_usize_sub(x_135, x_137);
x_175 = lean_usize_land(x_134, x_174);
x_176 = lean_array_uget(x_123, x_175);
lean_dec(x_123);
x_177 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__0(lean_box(0), x_1, x_176);
lean_dec(x_176);
if (lean_obj_tag(x_177) == 0)
{
switch (lean_obj_tag(x_1)) {
case 4:
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_178 = lean_ctor_get(x_1, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_1, 1);
lean_inc(x_179);
x_180 = l___private_Lean_Meta_Check_0__Lean_Meta_checkConstant(x_178, x_179, x_3, x_4, x_5, x_6, x_122);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_170 = x_180;
goto block_173;
}
case 5:
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_181 = lean_ctor_get(x_1, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_1, 1);
lean_inc(x_182);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_181);
x_183 = l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_check(x_181, x_2, x_3, x_4, x_5, x_6, x_122);
if (lean_obj_tag(x_183) == 0)
{
lean_object* x_184; lean_object* x_185; 
x_184 = lean_ctor_get(x_183, 1);
lean_inc(x_184);
lean_dec(x_183);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_182);
x_185 = l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_check(x_182, x_2, x_3, x_4, x_5, x_6, x_184);
if (lean_obj_tag(x_185) == 0)
{
lean_object* x_186; lean_object* x_187; 
x_186 = lean_ctor_get(x_185, 1);
lean_inc(x_186);
lean_dec(x_185);
x_187 = l_Lean_Meta_checkApp(x_181, x_182, x_3, x_4, x_5, x_6, x_186);
x_170 = x_187;
goto block_173;
}
else
{
lean_dec(x_182);
lean_dec(x_181);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_170 = x_185;
goto block_173;
}
}
else
{
lean_dec(x_182);
lean_dec(x_181);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_170 = x_183;
goto block_173;
}
}
case 6:
{
lean_object* x_188; 
lean_inc(x_2);
lean_inc(x_1);
x_188 = l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkLambdaLet(x_1, x_2, x_3, x_4, x_5, x_6, x_122);
x_170 = x_188;
goto block_173;
}
case 7:
{
lean_object* x_189; 
lean_inc(x_2);
lean_inc(x_1);
x_189 = l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkForall(x_1, x_2, x_3, x_4, x_5, x_6, x_122);
x_170 = x_189;
goto block_173;
}
case 8:
{
lean_object* x_190; 
lean_inc(x_2);
lean_inc(x_1);
x_190 = l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkLambdaLet(x_1, x_2, x_3, x_4, x_5, x_6, x_122);
x_170 = x_190;
goto block_173;
}
case 10:
{
lean_object* x_191; lean_object* x_192; 
x_191 = lean_ctor_get(x_1, 1);
lean_inc(x_191);
lean_inc(x_2);
x_192 = l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_check(x_191, x_2, x_3, x_4, x_5, x_6, x_122);
x_170 = x_192;
goto block_173;
}
case 11:
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_193 = lean_ctor_get(x_1, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_1, 1);
lean_inc(x_194);
x_195 = lean_ctor_get(x_1, 2);
lean_inc(x_195);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_195);
x_196 = l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_check(x_195, x_2, x_3, x_4, x_5, x_6, x_122);
if (lean_obj_tag(x_196) == 0)
{
lean_object* x_197; lean_object* x_198; 
x_197 = lean_ctor_get(x_196, 1);
lean_inc(x_197);
lean_dec(x_196);
x_198 = l_Lean_Meta_checkProj(x_193, x_194, x_195, x_3, x_4, x_5, x_6, x_197);
x_170 = x_198;
goto block_173;
}
else
{
lean_dec(x_195);
lean_dec(x_194);
lean_dec(x_193);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_170 = x_196;
goto block_173;
}
}
default: 
{
lean_object* x_199; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_199 = lean_box(0);
x_138 = x_199;
x_139 = x_122;
goto block_169;
}
}
}
else
{
lean_object* x_200; lean_object* x_201; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_200 = lean_ctor_get(x_177, 0);
lean_inc(x_200);
lean_dec(x_177);
x_201 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_201, 0, x_200);
lean_ctor_set(x_201, 1, x_122);
return x_201;
}
block_169:
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; size_t x_147; size_t x_148; size_t x_149; lean_object* x_150; uint8_t x_151; 
x_140 = lean_st_ref_take(x_2, x_139);
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_140, 1);
lean_inc(x_142);
lean_dec(x_140);
x_143 = lean_ctor_get(x_141, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_141, 1);
lean_inc(x_144);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_145 = x_141;
} else {
 lean_dec_ref(x_141);
 x_145 = lean_box(0);
}
x_146 = lean_array_get_size(x_144);
x_147 = lean_usize_of_nat(x_146);
lean_dec(x_146);
x_148 = lean_usize_sub(x_147, x_137);
x_149 = lean_usize_land(x_134, x_148);
x_150 = lean_array_uget(x_144, x_149);
x_151 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__1(lean_box(0), x_1, x_150);
if (x_151 == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; uint8_t x_160; 
x_152 = lean_nat_add(x_143, x_136);
lean_dec(x_143);
lean_inc(x_138);
x_153 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_153, 0, x_1);
lean_ctor_set(x_153, 1, x_138);
lean_ctor_set(x_153, 2, x_150);
x_154 = lean_array_uset(x_144, x_149, x_153);
x_155 = lean_unsigned_to_nat(2u);
x_156 = lean_nat_shiftl(x_152, x_155);
x_157 = lean_unsigned_to_nat(3u);
x_158 = lean_nat_div(x_156, x_157);
lean_dec(x_156);
x_159 = lean_array_get_size(x_154);
x_160 = lean_nat_dec_le(x_158, x_159);
lean_dec(x_159);
lean_dec(x_158);
if (x_160 == 0)
{
lean_object* x_161; lean_object* x_162; 
x_161 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__2(lean_box(0), x_154);
if (lean_is_scalar(x_145)) {
 x_162 = lean_alloc_ctor(0, 2, 0);
} else {
 x_162 = x_145;
}
lean_ctor_set(x_162, 0, x_152);
lean_ctor_set(x_162, 1, x_161);
x_8 = x_142;
x_9 = x_138;
x_10 = x_162;
goto block_16;
}
else
{
lean_object* x_163; 
if (lean_is_scalar(x_145)) {
 x_163 = lean_alloc_ctor(0, 2, 0);
} else {
 x_163 = x_145;
}
lean_ctor_set(x_163, 0, x_152);
lean_ctor_set(x_163, 1, x_154);
x_8 = x_142;
x_9 = x_138;
x_10 = x_163;
goto block_16;
}
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_164 = lean_box(0);
x_165 = lean_array_uset(x_144, x_149, x_164);
lean_inc(x_138);
x_166 = l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__5(lean_box(0), x_1, x_138, x_150);
x_167 = lean_array_uset(x_165, x_149, x_166);
if (lean_is_scalar(x_145)) {
 x_168 = lean_alloc_ctor(0, 2, 0);
} else {
 x_168 = x_145;
}
lean_ctor_set(x_168, 0, x_143);
lean_ctor_set(x_168, 1, x_167);
x_8 = x_142;
x_9 = x_138;
x_10 = x_168;
goto block_16;
}
}
block_173:
{
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; lean_object* x_172; 
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_170, 1);
lean_inc(x_172);
lean_dec(x_170);
x_138 = x_171;
x_139 = x_172;
goto block_169;
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_170;
}
}
}
block_16:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_st_ref_set(x_2, x_10, x_8);
lean_dec(x_2);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
lean_ctor_set(x_11, 0, x_9);
return x_11;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_9);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkLambdaLet_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_19; 
x_19 = lean_usize_dec_eq(x_2, x_3);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_4);
x_20 = lean_array_uget(x_1, x_2);
lean_inc(x_6);
x_21 = l_Lean_Meta_getFVarLocalDecl___redArg(x_20, x_6, x_8, x_9, x_10);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_20);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_ctor_get(x_22, 3);
lean_inc(x_24);
lean_dec(x_22);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_24);
x_25 = l___private_Lean_Meta_Check_0__Lean_Meta_ensureType(x_24, x_6, x_7, x_8, x_9, x_23);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_27 = l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_check(x_24, x_5, x_6, x_7, x_8, x_9, x_26);
x_11 = x_27;
goto block_18;
}
else
{
lean_dec(x_24);
x_11 = x_25;
goto block_18;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_21, 1);
lean_inc(x_28);
lean_dec(x_21);
x_29 = lean_ctor_get(x_22, 3);
lean_inc(x_29);
x_30 = lean_ctor_get(x_22, 4);
lean_inc(x_30);
lean_dec(x_22);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_29);
x_31 = l___private_Lean_Meta_Check_0__Lean_Meta_ensureType(x_29, x_6, x_7, x_8, x_9, x_28);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_29);
x_33 = l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_check(x_29, x_5, x_6, x_7, x_8, x_9, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_30);
x_35 = lean_infer_type(x_30, x_6, x_7, x_8, x_9, x_34);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_38 = l_Lean_Meta_isExprDefEq(x_29, x_36, x_6, x_7, x_8, x_9, x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_unbox(x_39);
lean_dec(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_dec(x_38);
x_42 = l_Lean_Expr_fvarId_x21(x_20);
lean_dec(x_20);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_43 = l_Lean_Meta_throwLetTypeMismatchMessage___redArg(x_42, x_6, x_7, x_8, x_9, x_41);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec(x_43);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_45 = l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_check(x_30, x_5, x_6, x_7, x_8, x_9, x_44);
x_11 = x_45;
goto block_18;
}
else
{
lean_dec(x_30);
x_11 = x_43;
goto block_18;
}
}
else
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_20);
x_46 = lean_ctor_get(x_38, 1);
lean_inc(x_46);
lean_dec(x_38);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_47 = l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_check(x_30, x_5, x_6, x_7, x_8, x_9, x_46);
x_11 = x_47;
goto block_18;
}
}
else
{
uint8_t x_48; 
lean_dec(x_30);
lean_dec(x_20);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_48 = !lean_is_exclusive(x_38);
if (x_48 == 0)
{
return x_38;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_38, 0);
x_50 = lean_ctor_get(x_38, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_38);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
uint8_t x_52; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_20);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_52 = !lean_is_exclusive(x_35);
if (x_52 == 0)
{
return x_35;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_35, 0);
x_54 = lean_ctor_get(x_35, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_35);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_20);
x_11 = x_33;
goto block_18;
}
}
else
{
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_20);
x_11 = x_31;
goto block_18;
}
}
}
else
{
uint8_t x_56; 
lean_dec(x_20);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_56 = !lean_is_exclusive(x_21);
if (x_56 == 0)
{
return x_21;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_21, 0);
x_58 = lean_ctor_get(x_21, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_21);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
lean_object* x_60; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_4);
lean_ctor_set(x_60, 1, x_10);
return x_60;
}
block_18:
{
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_usize_of_nat(x_14);
x_16 = lean_usize_add(x_2, x_15);
x_2 = x_16;
x_4 = x_12;
x_10 = x_13;
goto _start;
}
else
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at_____private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkLambdaLet_spec__1___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = lean_apply_8(x_1, x_3, x_4, x_2, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at_____private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkLambdaLet_spec__1___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_lambdaLetTelescope___at_____private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkLambdaLet_spec__1___redArg___lam__0), 9, 2);
lean_closure_set(x_10, 0, x_2);
lean_closure_set(x_10, 1, x_4);
x_11 = lean_box(1);
x_12 = lean_box(0);
x_13 = lean_unbox(x_11);
x_14 = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp___redArg(x_1, x_13, x_12, x_10, x_3, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_14) == 0)
{
return x_14;
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
return x_14;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_14);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at_____private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkLambdaLet_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_lambdaLetTelescope___at_____private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkLambdaLet_spec__1___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkLambdaLet___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_array_get_size(x_1);
x_11 = lean_nat_dec_lt(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_10);
x_12 = l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_check(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_12;
}
else
{
uint8_t x_13; 
x_13 = lean_nat_dec_le(x_10, x_10);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_10);
x_14 = l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_check(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_14;
}
else
{
lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_15 = lean_box(0);
x_16 = lean_usize_of_nat(x_9);
x_17 = lean_usize_of_nat(x_10);
lean_dec(x_10);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_18 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkLambdaLet_spec__0(x_1, x_16, x_17, x_15, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_check(x_2, x_3, x_4, x_5, x_6, x_7, x_19);
return x_20;
}
else
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_18;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkLambdaLet(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_8 = lean_alloc_closure((void*)(l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkLambdaLet___lam__0___boxed), 8, 0);
x_9 = lean_box(0);
x_10 = lean_unbox(x_9);
x_11 = l_Lean_Meta_lambdaLetTelescope___at_____private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkLambdaLet_spec__1___redArg(x_1, x_8, x_10, x_2, x_3, x_4, x_5, x_6, x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkForall_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_19; 
x_19 = lean_usize_dec_eq(x_2, x_3);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_4);
x_20 = lean_array_uget(x_1, x_2);
lean_inc(x_6);
x_21 = l_Lean_Meta_getFVarLocalDecl___redArg(x_20, x_6, x_8, x_9, x_10);
lean_dec(x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_29; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_29 = lean_ctor_get(x_22, 3);
lean_inc(x_29);
lean_dec(x_22);
x_24 = x_29;
goto block_28;
block_28:
{
lean_object* x_25; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_24);
x_25 = l___private_Lean_Meta_Check_0__Lean_Meta_ensureType(x_24, x_6, x_7, x_8, x_9, x_23);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_27 = l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_check(x_24, x_5, x_6, x_7, x_8, x_9, x_26);
x_11 = x_27;
goto block_18;
}
else
{
lean_dec(x_24);
x_11 = x_25;
goto block_18;
}
}
}
else
{
uint8_t x_30; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_30 = !lean_is_exclusive(x_21);
if (x_30 == 0)
{
return x_21;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_21, 0);
x_32 = lean_ctor_get(x_21, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_21);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
lean_object* x_34; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_4);
lean_ctor_set(x_34, 1, x_10);
return x_34;
}
block_18:
{
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_usize_of_nat(x_14);
x_16 = lean_usize_add(x_2, x_15);
x_2 = x_16;
x_4 = x_12;
x_10 = x_13;
goto _start;
}
else
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at_____private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkForall_spec__1___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_lambdaLetTelescope___at_____private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkLambdaLet_spec__1___redArg___lam__0), 9, 2);
lean_closure_set(x_10, 0, x_2);
lean_closure_set(x_10, 1, x_4);
x_11 = lean_box(0);
x_12 = lean_box(0);
x_13 = lean_unbox(x_11);
x_14 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux___redArg(x_13, x_12, x_1, x_10, x_3, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_14) == 0)
{
return x_14;
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
return x_14;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_14);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at_____private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkForall_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_forallTelescope___at_____private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkForall_spec__1___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkForall___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_array_get_size(x_1);
x_16 = lean_nat_dec_lt(x_14, x_15);
if (x_16 == 0)
{
lean_dec(x_15);
x_9 = x_8;
goto block_13;
}
else
{
uint8_t x_17; 
x_17 = lean_nat_dec_le(x_15, x_15);
if (x_17 == 0)
{
lean_dec(x_15);
x_9 = x_8;
goto block_13;
}
else
{
lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; 
x_18 = lean_box(0);
x_19 = lean_usize_of_nat(x_14);
x_20 = lean_usize_of_nat(x_15);
lean_dec(x_15);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_21 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkForall_spec__0(x_1, x_19, x_20, x_18, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_9 = x_22;
goto block_13;
}
else
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_21;
}
}
}
block_13:
{
lean_object* x_10; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_10 = l___private_Lean_Meta_Check_0__Lean_Meta_ensureType(x_2, x_4, x_5, x_6, x_7, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_check(x_2, x_3, x_4, x_5, x_6, x_7, x_11);
return x_12;
}
else
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkForall(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_8 = lean_alloc_closure((void*)(l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkForall___lam__0___boxed), 8, 0);
x_9 = lean_box(0);
x_10 = lean_unbox(x_9);
x_11 = l_Lean_Meta_forallTelescope___at_____private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkForall_spec__1___redArg(x_1, x_8, x_10, x_2, x_3, x_4, x_5, x_6, x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkLambdaLet_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkLambdaLet_spec__0(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at_____private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkLambdaLet_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = l_Lean_Meta_lambdaLetTelescope___at_____private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkLambdaLet_spec__1___redArg(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at_____private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkLambdaLet_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_4);
lean_dec(x_4);
x_12 = l_Lean_Meta_lambdaLetTelescope___at_____private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkLambdaLet_spec__1(x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkLambdaLet___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkLambdaLet___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkForall_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkForall_spec__0(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at_____private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkForall_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = l_Lean_Meta_forallTelescope___at_____private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkForall_spec__1___redArg(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at_____private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkForall_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_4);
lean_dec(x_4);
x_12 = l_Lean_Meta_forallTelescope___at_____private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkForall_spec__1(x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkForall___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkForall___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_7 = lean_unsigned_to_nat(8u);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_unsigned_to_nat(2u);
x_10 = lean_nat_shiftl(x_7, x_9);
x_11 = lean_unsigned_to_nat(3u);
x_12 = lean_nat_div(x_10, x_11);
lean_dec(x_10);
x_13 = l_Nat_nextPowerOfTwo(x_12);
lean_dec(x_12);
x_14 = lean_box(0);
x_15 = lean_mk_array(x_13, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_8);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_st_mk_ref(x_16, x_6);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_18);
x_20 = l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_check(x_1, x_18, x_2, x_3, x_4, x_5, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_st_ref_get(x_18, x_22);
lean_dec(x_18);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
lean_ctor_set(x_23, 0, x_21);
return x_23;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_21);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
else
{
lean_dec(x_18);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_check___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_mk_string_unchecked("", 0, 0);
x_9 = l_Lean_stringToMessageData(x_8);
lean_dec(x_8);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_21; 
x_21 = lean_mk_string_unchecked("❌️", 6, 2);
x_10 = x_21;
goto block_20;
}
else
{
lean_object* x_22; 
x_22 = lean_mk_string_unchecked("✅️", 6, 2);
x_10 = x_22;
goto block_20;
}
block_20:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_11 = l_Lean_stringToMessageData(x_10);
lean_inc(x_9);
x_12 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_mk_string_unchecked(" ", 1, 1);
x_14 = l_Lean_stringToMessageData(x_13);
lean_dec(x_13);
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_MessageData_ofExpr(x_1);
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_9);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_7);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_check___lam__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; lean_object* x_27; uint64_t x_28; lean_object* x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; 
x_9 = lean_ctor_get(x_4, 0);
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
lean_ctor_set_uint8(x_27, 9, x_1);
lean_ctor_set_uint8(x_27, 10, x_19);
lean_ctor_set_uint8(x_27, 11, x_20);
lean_ctor_set_uint8(x_27, 12, x_21);
lean_ctor_set_uint8(x_27, 13, x_22);
lean_ctor_set_uint8(x_27, 14, x_23);
lean_ctor_set_uint8(x_27, 15, x_24);
lean_ctor_set_uint8(x_27, 16, x_25);
lean_ctor_set_uint8(x_27, 17, x_26);
x_28 = lean_ctor_get_uint64(x_4, sizeof(void*)*7);
x_29 = lean_unsigned_to_nat(2u);
x_30 = lean_uint64_of_nat(x_29);
x_31 = lean_uint64_shift_right(x_28, x_30);
x_32 = lean_uint64_shift_left(x_31, x_30);
x_33 = l_Lean_Meta_TransparencyMode_toUInt64(x_1);
x_34 = lean_uint64_lor(x_32, x_33);
x_35 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 8);
x_36 = lean_ctor_get(x_4, 1);
x_37 = lean_ctor_get(x_4, 2);
x_38 = lean_ctor_get(x_4, 3);
x_39 = lean_ctor_get(x_4, 4);
x_40 = lean_ctor_get(x_4, 5);
x_41 = lean_ctor_get(x_4, 6);
x_42 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 9);
x_43 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 10);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
x_44 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_44, 0, x_27);
lean_ctor_set(x_44, 1, x_36);
lean_ctor_set(x_44, 2, x_37);
lean_ctor_set(x_44, 3, x_38);
lean_ctor_set(x_44, 4, x_39);
lean_ctor_set(x_44, 5, x_40);
lean_ctor_set(x_44, 6, x_41);
lean_ctor_set_uint64(x_44, sizeof(void*)*7, x_34);
lean_ctor_set_uint8(x_44, sizeof(void*)*7 + 8, x_35);
lean_ctor_set_uint8(x_44, sizeof(void*)*7 + 9, x_42);
lean_ctor_set_uint8(x_44, sizeof(void*)*7 + 10, x_43);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_45 = l___private_Lean_Meta_Check_0__Lean_Meta_checkAux(x_2, x_44, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_45) == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; uint8_t x_64; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
x_64 = l_Lean_Exception_isInterrupt(x_46);
if (x_64 == 0)
{
uint8_t x_65; 
x_65 = l_Lean_Exception_isRuntime(x_46);
x_48 = x_65;
goto block_63;
}
else
{
x_48 = x_64;
goto block_63;
}
block_63:
{
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; 
lean_dec(x_45);
lean_inc(x_3);
x_49 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0(x_3, x_4, x_5, x_6, x_7, x_47);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_unbox(x_50);
lean_dec(x_50);
if (x_51 == 0)
{
uint8_t x_52; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_52 = !lean_is_exclusive(x_49);
if (x_52 == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_49, 0);
lean_dec(x_53);
lean_ctor_set_tag(x_49, 1);
lean_ctor_set(x_49, 0, x_46);
return x_49;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_49, 1);
lean_inc(x_54);
lean_dec(x_49);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_46);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_56 = lean_ctor_get(x_49, 1);
lean_inc(x_56);
lean_dec(x_49);
lean_inc(x_46);
x_57 = l_Lean_Exception_toMessageData(x_46);
x_58 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_3, x_57, x_4, x_5, x_6, x_7, x_56);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_59 = !lean_is_exclusive(x_58);
if (x_59 == 0)
{
lean_object* x_60; 
x_60 = lean_ctor_get(x_58, 0);
lean_dec(x_60);
lean_ctor_set_tag(x_58, 1);
lean_ctor_set(x_58, 0, x_46);
return x_58;
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_58, 1);
lean_inc(x_61);
lean_dec(x_58);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_46);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
else
{
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_45;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_check(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
lean_inc(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_Meta_check___lam__0___boxed), 7, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = lean_mk_string_unchecked("Meta", 4, 4);
x_9 = lean_mk_string_unchecked("check", 5, 5);
x_10 = l_Lean_Name_mkStr2(x_8, x_9);
x_11 = lean_box(0);
lean_inc(x_10);
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_check___lam__1___boxed), 8, 3);
lean_closure_set(x_12, 0, x_11);
lean_closure_set(x_12, 1, x_1);
lean_closure_set(x_12, 2, x_10);
x_13 = lean_box(1);
x_14 = lean_mk_string_unchecked("", 0, 0);
x_15 = lean_unbox(x_13);
x_16 = l_Lean_withTraceNode___at___Lean_Meta_processPostponed_spec__0(lean_box(0), x_10, x_7, x_12, x_15, x_14, x_2, x_3, x_4, x_5, x_6);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_check___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_check___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_check___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
lean_dec(x_1);
x_10 = l_Lean_Meta_check___lam__1(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeCorrect(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_check(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
lean_dec(x_9);
x_10 = lean_box(1);
lean_ctor_set(x_7, 0, x_10);
return x_7;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_7, 1);
lean_inc(x_11);
lean_dec(x_7);
x_12 = lean_box(1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_22; 
x_14 = lean_ctor_get(x_7, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_7, 1);
lean_inc(x_15);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_16 = x_7;
} else {
 lean_dec_ref(x_7);
 x_16 = lean_box(0);
}
x_22 = l_Lean_Exception_isInterrupt(x_14);
if (x_22 == 0)
{
uint8_t x_23; 
x_23 = l_Lean_Exception_isRuntime(x_14);
x_17 = x_23;
goto block_21;
}
else
{
x_17 = x_22;
goto block_21;
}
block_21:
{
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_14);
x_18 = lean_box(x_17);
if (lean_is_scalar(x_16)) {
 x_19 = lean_alloc_ctor(0, 2, 0);
} else {
 x_19 = x_16;
 lean_ctor_set_tag(x_19, 0);
}
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_15);
return x_19;
}
else
{
lean_object* x_20; 
if (lean_is_scalar(x_16)) {
 x_20 = lean_alloc_ctor(1, 2, 0);
} else {
 x_20 = x_16;
}
lean_ctor_set(x_20, 0, x_14);
lean_ctor_set(x_20, 1, x_15);
return x_20;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Check___hyg_4727_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_2 = lean_mk_string_unchecked("Meta", 4, 4);
x_3 = lean_mk_string_unchecked("check", 5, 5);
lean_inc(x_2);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(0);
x_6 = lean_box(0);
x_7 = lean_mk_string_unchecked("Lean", 4, 4);
lean_inc(x_7);
x_8 = l_Lean_Name_str___override(x_6, x_7);
lean_inc(x_2);
x_9 = l_Lean_Name_str___override(x_8, x_2);
x_10 = lean_mk_string_unchecked("initFn", 6, 6);
x_11 = l_Lean_Name_str___override(x_9, x_10);
x_12 = lean_mk_string_unchecked("_@", 2, 2);
x_13 = l_Lean_Name_str___override(x_11, x_12);
x_14 = l_Lean_Name_str___override(x_13, x_7);
x_15 = l_Lean_Name_str___override(x_14, x_2);
x_16 = lean_mk_string_unchecked("Check", 5, 5);
x_17 = l_Lean_Name_str___override(x_15, x_16);
x_18 = lean_mk_string_unchecked("_hyg", 4, 4);
x_19 = l_Lean_Name_str___override(x_17, x_18);
x_20 = lean_unsigned_to_nat(4727u);
x_21 = l_Lean_Name_num___override(x_19, x_20);
x_22 = lean_unbox(x_5);
x_23 = l_Lean_registerTraceClass(x_4, x_22, x_21, x_1);
return x_23;
}
}
lean_object* initialize_Lean_Meta_InferType(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Sorry(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Check(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_InferType(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sorry(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
if (builtin) {res = l_Lean_Meta_initFn____x40_Lean_Meta_Check___hyg_4727_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
