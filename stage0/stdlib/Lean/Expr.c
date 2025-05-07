// Lean compiler output
// Module: Lean.Expr
// Imports: Init.Data.Hashable Init.Data.Int Lean.Data.KVMap Lean.Data.SMap Lean.Level Std.Data.HashSet.Basic
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
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_bindingName_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_fvarId_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Expr_setAppPPExplicit_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux___boxed(lean_object*, lean_object*);
lean_object* l_panic___at___Lean_Level_normalize_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_letValue_x21___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__0(lean_object*, lean_object*, lean_object*);
uint8_t l_ptrEqList___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_reprPrec(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isArrow___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getAppNumArgs_x27(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_rawNatLit_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instForInFVarIdSetFVarId(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_sizeWithoutSharing___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instBEqFVarId;
LEAN_EXPORT lean_object* l_Lean_mkLet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_List_foldl___at___Lean_Expr_const___override_spec__0(uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isHeadBetaTargetFn___boxed(lean_object*, lean_object*);
uint8_t lean_uint32_to_uint8(uint32_t);
LEAN_EXPORT lean_object* l_Lean_Expr_looseBVarRange(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedMVarIdMap(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkNatLit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_BinderInfo_isInstImplicit___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instFVarIdSetEmptyCollection___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_hashEx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instFVarIdSetInhabited;
LEAN_EXPORT lean_object* l_Lean_Expr_appFn___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkLHSGoalRaw(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instCoeExprExprStructEq;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_113_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_expr_mk_let(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isConst___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Expr_setAppPPExplicitForExposingMVars_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_ExprStructEq_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isProj___boxed(lean_object*);
LEAN_EXPORT lean_object* lean_expr_mk_app(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_reprMVarId____x40_Lean_Expr___hyg_2016_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___Lean_Expr_const___override_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_424_(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Nat_mkInstLT;
lean_object* l_Lean_instEmptyCollectionRBTree(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkSimpleThunk(lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
LEAN_EXPORT lean_object* l_Lean_Expr_liftLooseBVars___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg___lam__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVarId___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_setOption(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBodyMaxDepth(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_traverseApp___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_sizeWithoutSharing___lam__0(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_ExprStructEq_instToString___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Int_mkInstPow;
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_eqv___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isStringLit___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkApp9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkApp7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprData__1;
LEAN_EXPORT lean_object* l_Lean_Expr_isBVar___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_letType_x21___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_forallInfo(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_projExpr_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at___Lean_FVarIdSet_insert_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarIdSet_insert(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkSimpleThunkType(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ExprStructEq_beq___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkApp8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1017_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint8_t lean_uint16_dec_lt(uint16_t, uint16_t);
LEAN_EXPORT lean_object* l_Lean_mkIntLE(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshLMVarId___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkIff(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_lt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406____boxed(lean_object*, lean_object*);
uint8_t l_Lean_Level_hasParam(lean_object*);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Nat_mkInstAdd;
LEAN_EXPORT lean_object* l_Lean_Expr_hasAnyFVar___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getAutoParamTactic_x3f(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isLet(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getAppFn___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg___lam__11(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isRawNatLit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_inaccessible_x3f___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isOptParam(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg___lam__12(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_quote(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getArg_x21_x27___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Expr_setAppPPExplicitForExposingMVars_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isApp(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_binderInfo___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_binderInfoEx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkIntSub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_lit___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_BinderInfo_noConfusion___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_forallDomain(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ExprStructEq_hash___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instLTLiteral;
lean_object* l_Array_reverse(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Nat_mkInstHPow;
LEAN_EXPORT lean_object* l_Lean_Expr_sort___override(lean_object*);
uint32_t lean_uint8_to_uint32(uint8_t);
LEAN_EXPORT lean_object* l_Lean_mkSort(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_forallBody___redArg(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkIntLit___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instBEqMVarId;
LEAN_EXPORT uint8_t l_Lean_Expr_isStringLit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getAppPrefix___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_lowerLooseBVars___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_patternRefAnnotationKey;
LEAN_EXPORT lean_object* l_Lean_instInhabitedExprStructEq;
LEAN_EXPORT lean_object* l_Lean_Expr_constLevels_x21___boxed(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3026_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Literal_type___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDecIsTrue(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprData__1___lam__0(uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at_____private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3026__spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_data___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_intSubFn;
LEAN_EXPORT uint8_t l_Lean_Expr_isCharLit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprFVarId___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVars___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lean_expr_has_fvar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkProj(lean_object*, lean_object*, lean_object*);
uint64_t lean_expr_data(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_FVarIdSet_insert_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_hasFVarEx___boxed(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lean_ExprStructEq_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Nat_mkInstHDiv;
LEAN_EXPORT lean_object* l_Lean_mkIntDiv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Expr_mkData_spec__0___boxed__const__1;
LEAN_EXPORT lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_bvar___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getAppNumArgs___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_letE___override___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_instBEq;
LEAN_EXPORT lean_object* l_Lean_Expr_setAppPPExplicit(lean_object*);
LEAN_EXPORT uint8_t l_Lean_instFVarIdSetEmptyCollection___lam__0(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_panic___at___Lean_Expr_bindingInfo_x21_spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_424____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_fvarId_x3f___boxed(lean_object*);
uint8_t lean_expr_has_loose_bvar(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_forallDomain___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_intLEPred;
LEAN_EXPORT uint64_t l_Lean_Expr_Data_hash(uint64_t);
LEAN_EXPORT lean_object* l_Lean_mkBVar(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isLetFun(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg___lam__10___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshMVarId___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Int_mkInstHDiv;
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isAppOfArity___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isType0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_projIdx_x21___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_hasLevelMVarEx___boxed(lean_object*);
lean_object* l_Lean_RBNode_setBlack___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_Data_hasExprMVar(uint64_t);
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBodyMaxDepth___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_mkAppData___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getBoundedAppFn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprExpr;
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_beqMVarId____x40_Lean_Expr___hyg_1926_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getBoundedAppFn___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_BinderInfo_noConfusion___redArg___lam__0(lean_object*);
lean_object* l_Std_Format_joinSep(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instBEqData__1___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_BinderInfo_noConfusion___redArg(uint8_t, uint8_t);
LEAN_EXPORT uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkApp10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_traverseApp___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_intEqPred;
LEAN_EXPORT lean_object* l_Lean_mkIntMod(lean_object*, lean_object*);
uint64_t lean_string_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_stripArgsN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_setPPUniverses(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Expr_isMVar___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isLambda___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_Data_hash___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkIntMul(lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBody___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
LEAN_EXPORT uint32_t l_Lean_Expr_approxDepth(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_mvar___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_appArg___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Literal_type(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getAppArgsN_loop(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_annotation_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_setPPExplicit___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isForall___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_appFn_x21_x27(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MData_empty;
LEAN_EXPORT lean_object* l_Lean_Expr_appArg___redArg___boxed(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_expr_mk_forall(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Expr_getAppNumArgs_x27_go___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isLHSGoal_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Nat_mkInstDiv;
LEAN_EXPORT lean_object* l_Lean_mkMData(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_isPatternWithRef(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isMData___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Int_mkInstNatCast;
LEAN_EXPORT lean_object* l_Lean_Expr_getAppFn_x27___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_quickLt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_expr_mk_bvar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_abstractRange___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getAppRevArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionFVarIdMap(lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
LEAN_EXPORT lean_object* lean_expr_mk_lit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_appArg_x21(lean_object*);
uint64_t lean_uint64_land(uint64_t, uint64_t);
LEAN_EXPORT lean_object* lean_expr_mk_proj(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_BinderInfo_toCtorIdx(uint8_t);
LEAN_EXPORT uint8_t l_Lean_Expr_isAtomic(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isType(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Nat_mkInstMul;
lean_object* l_Lean_mkFreshId(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isBVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_stripArgsN___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_BinderInfo_isStrictImplicit(uint8_t);
LEAN_EXPORT lean_object* l_Lean_mkFreshLMVarId(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isHeadBetaTargetFn(uint8_t, lean_object*);
LEAN_EXPORT lean_object* lean_expr_mk_const(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVarId(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_hasParam___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_betaRev_go(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_containsFVar(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_hasMVar(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isSemiOutParam(lean_object*);
LEAN_EXPORT lean_object* l_Lean_isLHSGoal_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getAutoParamTactic_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_intMulFn;
LEAN_EXPORT lean_object* l_Lean_Expr_Data_hasFVar___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_patternAnnotation_x3f___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isLambda(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkNatAdd(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Int_mkInstPowNat;
LEAN_EXPORT lean_object* l_Lean_Int_mkInstLE;
size_t lean_ptr_addr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_sizeWithoutSharing(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_updateForallE_x21(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedMVarId;
LEAN_EXPORT uint64_t l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(lean_object*);
lean_object* lean_expr_instantiate_rev_range(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkIntDvd(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Int_mkInstDiv;
LEAN_EXPORT lean_object* l_Lean_mkApp2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAppRev(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_dbgToString___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getNumHeadForalls___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isType___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Nat_mkInstMod;
LEAN_EXPORT uint8_t l_Lean_Expr_isAppOfArity_x27(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAppRange(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_abstract(lean_object*, lean_object*);
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getNumHeadForalls(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkPropEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_forallBody___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkStrLit(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_mkAppRangeAux(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lean_Expr_mkDataForBinder(uint64_t, lean_object*, uint32_t, uint8_t, uint8_t, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_instReprBinderInfo;
LEAN_EXPORT lean_object* l_Lean_instBEqBinderInfo;
LEAN_EXPORT lean_object* l_Lean_BinderInfo_noConfusion___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkIntEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getAppArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarIdMap_insert___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isSort(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_litValue_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_setOption___at___Lean_Expr_setPPExplicit_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Nat_mkInstPow;
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_updateFVar_x21___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_abstract___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at___Lean_MVarIdSet_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_MVarIdSet_insert_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkInaccessible(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isProp___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at_____private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3026__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkLambda___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lean_expr_has_mvar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_appFn___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_eta___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_betaRev_go___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedFVarIdMap(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isOptParam___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_BinderInfo_toCtorIdx___boxed(lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_mkAppN_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withApp___redArg(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint32_t lean_uint32_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isHeadBetaTarget___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_bindingBody_x21___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getBoundedAppArgsAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_beqFVarId____x40_Lean_Expr___hyg_1672_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_litValue_x21___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getAppNumArgs_x27_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg___lam__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_projExpr_x21___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_inaccessible_x3f(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Literal_lt(lean_object*, lean_object*);
uint64_t lean_uint8_to_uint64(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Expr_getOptParamDefault_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_natAddFn;
LEAN_EXPORT lean_object* l_Lean_Int_mkInstSub;
LEAN_EXPORT lean_object* l_Lean_FVarIdMap_insert(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppRev___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_patternWithRef_x3f___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_hasAnyFVar_visit___at___Lean_Expr_containsFVar_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprData__1___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_equal___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_setPPExplicit(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Expr_isAutoParam___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAppN___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_letType_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_setPPNumericTypes___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_mkDataForBinder___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_sizeWithoutSharing___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_instToString;
LEAN_EXPORT uint8_t lean_expr_has_level_mvar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_projIdx_x21(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Expr_appFn_x21_spec__0(lean_object*);
extern uint64_t l_instInhabitedUInt64;
lean_object* lean_expr_instantiate(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isMVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_appArg_x21___boxed(lean_object*);
lean_object* lean_uint64_to_nat(uint64_t);
LEAN_EXPORT lean_object* l_Lean_Expr_getArg_x21(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isLit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_appArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_Data_approxDepth___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT uint8_t l_Lean_instInhabitedBinderInfo;
LEAN_EXPORT lean_object* l_Lean_Expr_appArg_x21_x27___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_beqFVarId____x40_Lean_Expr___hyg_1672____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Expr_getAppArgsN_loop_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_quickComp___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isSort___boxed(lean_object*);
LEAN_EXPORT uint64_t l_Lean_Expr_mkDataForLet(uint64_t, lean_object*, uint32_t, uint8_t, uint8_t, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Expr_inferImplicit(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_hashMVarId____x40_Lean_Expr___hyg_1984____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_BinderInfo_isExplicit___boxed(lean_object*);
lean_object* l_Array_extract(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lean_expr_has_level_param(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Nat_mkInstSub;
LEAN_EXPORT lean_object* l_Lean_Expr_consumeMData___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAndN(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_forallInfo___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Nat_mkInstHSub;
LEAN_EXPORT lean_object* l_Lean_BinderInfo_noConfusion___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVar(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateRev___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_BinderInfo_isStrictImplicit___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Literal_lt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isCharLit___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_hasAnyFVar_visit___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_reprMVarId___redArg____x40_Lean_Expr___hyg_2016_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instCoeExprExprStructEq___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_appFnCleanup(lean_object*, lean_object*);
uint64_t lean_uint64_add(uint64_t, uint64_t);
LEAN_EXPORT uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isHeadBetaTarget(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lean_is_out_param(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_forallBody___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateRange___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint16_t lean_uint8_to_uint16(uint8_t);
LEAN_EXPORT lean_object* l_panic___at___Lean_Expr_mvarId_x21_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_casesOn___override(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isPatternWithRef___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkConst(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkNatSub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_forallInfo___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_intNatCastFn;
LEAN_EXPORT lean_object* l_Lean_Expr_inferImplicit___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_setOption___at___Lean_Expr_setPPExplicit_spec__0(lean_object*, lean_object*, uint8_t);
uint8_t lean_expr_quick_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_intDivFn;
LEAN_EXPORT lean_object* l_Lean_Expr_isAppOfArity_x27___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshMVarId(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkNatLE(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_expr_mk_fvar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_constName_x21(lean_object*);
uint8_t l_Lean_Level_hasMVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_forallName___redArg___boxed(lean_object*);
LEAN_EXPORT uint64_t l_Lean_Literal_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedExpr;
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg___lam__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_mkData___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at_____private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3026__spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_mkAppRev_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Expr_mkData_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_etaExpanded_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_constName_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_hasMVarEx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_traverseApp(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lean_Expr_hash(lean_object*);
LEAN_EXPORT uint8_t l_Lean_BinderInfo_isInstImplicit(uint8_t);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Expr_setAppPPExplicit_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAnnotation(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_bindingDomain_x21___boxed(lean_object*);
uint8_t lean_uint64_to_uint8(uint64_t);
LEAN_EXPORT lean_object* l_Lean_Expr_setOption___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isFalse___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_updateFVar_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_casesOn___override___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkLit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_bvarIdx_x21___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_appFn_x21___boxed(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint16_t lean_uint16_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Int_mkInstMul;
LEAN_EXPORT lean_object* l_Lean_Expr_traverseApp___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_expr_consume_type_annotations(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_intModFn;
LEAN_EXPORT lean_object* l_Lean_mkPatternWithRef(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_mkAppN_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_natMulFn;
LEAN_EXPORT lean_object* l_Lean_Expr_hasLooseBVars___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isArrow(lean_object*);
uint32_t lean_uint64_to_uint32(uint64_t);
uint8_t lean_expr_equal(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instHashableFVarId;
lean_object* l_Lean_RBTree_instForIn(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBMap_instForInProd(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprMVarId;
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isOutParam___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isAppOf___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ctorName___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_letName_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAppRev___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint32_to_uint64(uint32_t);
LEAN_EXPORT lean_object* l_Lean_instFVarIdHashSetInhabited;
LEAN_EXPORT lean_object* l_Lean_mkNot(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_bindingName_x21___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__4(lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_lift_loose_bvars(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_letName_x21___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_natLEPred;
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_withAppRevAux(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_uint16_to_uint8(uint16_t);
lean_object* lean_expr_lower_loose_bvars(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_constName_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppRev(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Nat_mkInstLE;
LEAN_EXPORT lean_object* l_panic___at___Lean_Expr_bindingInfo_x21_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedLiteral;
LEAN_EXPORT uint8_t l_Lean_Expr_Data_hasLevelParam(uint64_t);
LEAN_EXPORT uint8_t l_Lean_Expr_Data_hasLevelMVar(uint64_t);
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionMVarIdMap(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_hasExprMVar___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_forallName___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_appFn_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAppRange___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_Data_hasExprMVar___boxed(lean_object*);
LEAN_EXPORT uint64_t l___private_Lean_Expr_0__Lean_hashMVarId____x40_Lean_Expr___hyg_1984_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instHashableBinderInfo;
lean_object* l_Lean_Level_hasMVar___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Int_mkInstHMul;
LEAN_EXPORT lean_object* l_Lean_instCoeExprExprStructEq___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Expr_litValue_x21_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkIntLit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withApp(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_BinderInfo_isImplicit(uint8_t);
LEAN_EXPORT lean_object* l_Lean_mkIntAdd(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getOptParamDefault_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_updateForallBinderInfos(lean_object*, lean_object*);
lean_object* l_Array_instInhabited(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_forallDomain___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_hasExprMVarEx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Nat_mkInstHAdd;
LEAN_EXPORT lean_object* l_Lean_mkIntNatCast(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_hasAnyFVar(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instHashableMVarId;
LEAN_EXPORT lean_object* l_Lean_Expr_ctorName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedFVarId;
LEAN_EXPORT uint8_t l_Lean_Expr_hasLooseBVarInExplicitDomain(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_mkAppRevRangeAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lean_Expr_mkData(uint64_t, lean_object*, uint32_t, uint8_t, uint8_t, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_instBEqLiteral;
LEAN_EXPORT lean_object* l_Lean_Expr_eta___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_natSubFn;
LEAN_EXPORT uint8_t l_Lean_Expr_Data_hasFVar(uint64_t);
LEAN_EXPORT lean_object* l_Lean_Expr_updateLambdaE_x21(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_fvarId_x21___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getBoundedAppArgs(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdMapProdMVarId(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_binderInfo(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_hasAnyFVar_visit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArg_x21___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_instDecidableLtLiteral(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkOr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_eta(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_reprMVarId____x40_Lean_Expr___hyg_2016____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMVarIdSetInhabited;
LEAN_EXPORT lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBinderNames___boxed(lean_object*);
uint8_t lean_expr_lt(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isAutoParam(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instFVarIdHashSetEmptyCollection;
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ExprStructEq_instToString;
LEAN_EXPORT uint8_t l_Lean_Expr_isFVarOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_lit_type(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_containsFVar___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkForallEx___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isLetFun___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_113____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkForall(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_letBody_x21___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isFalse(lean_object*);
LEAN_EXPORT lean_object* l_Lean_FVarIdSet_insert(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_hasAnyFVar_visit___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at___Lean_MVarIdSet_insert_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ExprStructEq_instHashable;
lean_object* lean_nat_abs(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_etaExpandedBody___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_forallName(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_Data_hasLevelParam___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_bindingDomain_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_letValue_x21(lean_object*);
LEAN_EXPORT uint64_t l_Lean_BinderInfo_hash(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Nat_mkInstHMul;
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_mkAppRevRangeAux(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVars(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isTrue___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_instantiate___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Literal_hash___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isFVar___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getAppNumArgs_x27___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_instBEqData__1___lam__0(uint64_t, uint64_t);
lean_object* l_Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdSetMVarId(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBody(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
uint16_t lean_uint16_add(uint16_t, uint16_t);
LEAN_EXPORT lean_object* l_Lean_Expr_getAppPrefix(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_setPPPiBinderTypes___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Int_mkType;
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isProj(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkRawNatLit(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_Data_approxDepth(uint64_t);
LEAN_EXPORT lean_object* l_List_repr___at_____private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3026__spec__0___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_FVarIdMap_insert___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lean_Expr_mkAppData(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_FVarIdSet_insert_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_etaExpandedAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_hasLevelParam___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_beqLiteral____x40_Lean_Expr___hyg_34____boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_expr_mk_mvar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDecIsFalse(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_appFn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getArgD(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMVarIdSetEmptyCollection;
LEAN_EXPORT lean_object* l_Lean_Expr_appArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Int_mkInstLT;
LEAN_EXPORT lean_object* l_Lean_Expr_getForallArity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArgD(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_mkAppRangeAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_BinderInfo_isExplicit(uint8_t);
LEAN_EXPORT lean_object* l_Lean_mkAnd(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3026____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_lam___override___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_uint16_dec_le(uint16_t, uint16_t);
LEAN_EXPORT lean_object* l_Lean_patternWithRef_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBinderNames(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateRevRange___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_expr_mk_lambda(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_instReprFVarId___lam__0(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_Data_hasLevelMVar___boxed(lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_hasLooseBVarInExplicitDomain___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_mdataExpr_x21___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getAppFn_x27(lean_object*);
uint64_t l_Lean_Name_hash___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_constName_x21___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkNatSucc(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isAtomic___boxed(lean_object*);
uint8_t l_Lean_KVMap_getBool(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkForall___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Nat_mkInstNatPow;
LEAN_EXPORT lean_object* l_Lean_ExprStructEq_instBEq;
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_hasAnyFVar_visit___at___Lean_Expr_containsFVar_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_annotation_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_instHashable;
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg___lam__10(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_natEqPred;
LEAN_EXPORT lean_object* l_Lean_Expr_approxDepth___boxed(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_betaRev___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_mkDataForLet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lean_expr_binder_info(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Int_mkInstHPow;
uint8_t l_Lean_RBNode_isRed___redArg(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVar___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_setPPUniverses___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getAppFn(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_bindingInfo_x21___boxed(lean_object*);
extern lean_object* l_Lean_levelOne;
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_intAddFn;
LEAN_EXPORT uint8_t l_Lean_Expr_isProp(lean_object*);
LEAN_EXPORT lean_object* l_Lean_reflBoolTrue;
lean_object* l_Lean_KVMap_insert(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_instDecidableLtLiteral___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isApp___boxed(lean_object*);
LEAN_EXPORT lean_object* lean_expr_mk_mdata(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Nat_mkType;
LEAN_EXPORT lean_object* l_Lean_instReprFVarId;
LEAN_EXPORT lean_object* l_Lean_Expr_isType0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_setAppPPExplicitForExposingMVars(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isBinding___boxed(lean_object*);
uint8_t lean_uint8_of_nat(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_beqLiteral____x40_Lean_Expr___hyg_34_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_int_x3f(lean_object*);
uint64_t l_Lean_Level_hash(lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getAppArgsN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Int_mkInstHAdd;
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Expr_getAppFnArgs_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_etaExpandedBody___lam__0___boxed(lean_object*, lean_object*);
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Expr_letFunAppArgs_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkNatMul(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT lean_object* l_panic___at___Lean_Expr_constLevels_x21_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_setPPNumericTypes(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Nat_mkInstHMod;
LEAN_EXPORT lean_object* l_Lean_mkEM(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isSemiOutParam___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isTrue(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_quickComp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_hasMVar___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkApp(lean_object*, lean_object*);
lean_object* l_Std_HashSet_instEmptyCollection(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_quickCmp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isRawNatLit___boxed(lean_object*);
lean_object* lean_uint8_to_nat(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Expr_forallName___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkLambdaEx___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_patternAnnotation_x3f(lean_object*);
LEAN_EXPORT uint64_t l_panic___at___Lean_Expr_mkData_spec__0(lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Expr_appFn_x21_x27___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_BinderInfo_isImplicit___boxed(lean_object*);
uint8_t lean_uint32_dec_lt(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Expr_appArg_x21_x27(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_constName(lean_object*);
uint64_t lean_bool_to_uint64(uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_Data_looseBVarRange___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_updateFn___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_forallE___override___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_forallBody(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lean_Expr_Data_looseBVarRange(uint64_t);
LEAN_EXPORT uint8_t l_Lean_Expr_hasFVar(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_hasLevelParam(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_mkAppData___boxed__const__1;
LEAN_EXPORT lean_object* l_Lean_Expr_forallDomain___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_hasAnyFVar_visit___at___Lean_Expr_containsFVar_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkMVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_mkAppRevRange___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_betaRev(lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Expr_getArgD___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KVMap_findCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Int_mkInstAdd;
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_fvar___override(lean_object*);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_hash___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_looseBVarRange___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Int_mkInstHSub;
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_setPPFunBinderTypes(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_instReprLiteral;
LEAN_EXPORT lean_object* l_Lean_Expr_getArg_x21_x27(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_hasAnyFVar_visit___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_bindingBody_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_appFn___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg___lam__3(lean_object*, lean_object*, lean_object*);
uint32_t lean_uint32_add(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Expr_setPPFunBinderTypes___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_instantiate1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_KVMap_empty;
LEAN_EXPORT lean_object* l_Lean_Expr_hasLooseBVar___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at___Lean_FVarIdSet_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_hasLevelParamEx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_sortLevel_x21___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getAppFnArgs(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
uint64_t lean_uint8_to_uint64(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Expr_updateFn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_BinderInfo_toUInt64___boxed(lean_object*);
lean_object* l_panic___at_____private_Init_Prelude_0__Lean_assembleParts_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_hasFVar___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_intNegFn;
LEAN_EXPORT lean_object* l_Lean_Expr_headBeta(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isLit___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_sortLevel_x21(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_mkAppRev_spec__0(lean_object*, size_t, size_t, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarIdMap_insert(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isMData(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isBinding(lean_object*);
LEAN_EXPORT lean_object* lean_expr_mk_sort(lean_object*);
lean_object* lean_int_neg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Int_mkInstNeg;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_BinderInfo_noConfusion(lean_object*, uint8_t, uint8_t, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Expr_mkAppRevRange(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___at___String_toNat_x21_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_betaRev_go___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArgD___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_bvarIdx_x21(lean_object*);
lean_object* lean_expr_dbg_to_string(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_letFun_x3f(lean_object*);
uint8_t l_List_any___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_etaExpandedBody(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Expr_fvarId_x21_spec__0(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isConst(lean_object*);
lean_object* l_StateT_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getNumHeadLambdas___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Expr_forallInfo___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_beta(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_hasAnyFVar_visit___at___Lean_Expr_containsFVar_spec__0___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instFVarIdSetEmptyCollection;
LEAN_EXPORT lean_object* l_Lean_Expr_mdataExpr_x21(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_beqMVarId____x40_Lean_Expr___hyg_1926____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Int_mkInstHMod;
LEAN_EXPORT lean_object* l_Lean_Expr_setPPPiBinderTypes(lean_object*, uint8_t);
LEAN_EXPORT uint8_t l_Lean_Expr_isFVar(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_bindingInfo_x21(lean_object*);
lean_object* l_List_lengthTR(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isForall(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isLet___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instHashableLiteral;
LEAN_EXPORT lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isConstOf___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lean_expr_has_expr_mvar(lean_object*);
LEAN_EXPORT uint32_t lean_expr_loose_bvar_range(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_traverseApp___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_looseBVarRangeEx___boxed(lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_ExprStructEq_instToString___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkNatEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_consumeMData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getArg_x21___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_nat_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_hasLevelMVar___boxed(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isFVarOf___boxed(lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_mvarId_x21___boxed(lean_object*);
lean_object* lean_expr_instantiate_range(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkIntNeg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instBEqData__1;
lean_object* l_instInhabitedList(lean_object*);
lean_object* lean_expr_abstract_range(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Int_mkInstMod;
LEAN_EXPORT uint64_t lean_expr_hash(lean_object*);
LEAN_EXPORT uint64_t l_Lean_instInhabitedData__1;
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg___lam__2(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Data_KVMap_0__Lean_reprKVMap___redArg____x40_Lean_Data_KVMap___hyg_920_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArg_x21_x27(lean_object*, lean_object*);
lean_object* l_StateT_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_constName___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_hasLevelMVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprMVarId__1;
LEAN_EXPORT lean_object* l_Lean_mkLet(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Std_HashSet_instInhabited(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_betaRev_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_hasExprMVar(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_letBody_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getNumHeadLambdas(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArg_x21_x27___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_MVarIdSet_insert_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Expr_etaExpandedStrict_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_BinderInfo_hash___boxed(lean_object*);
static lean_object* _init_l_Lean_instInhabitedLiteral() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_beqLiteral____x40_Lean_Expr___hyg_34_(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_nat_dec_eq(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_box(0);
x_7 = lean_unbox(x_6);
return x_7;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_box(0);
x_9 = lean_unbox(x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_string_dec_eq(x_10, x_11);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_beqLiteral____x40_Lean_Expr___hyg_34____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Expr_0__Lean_beqLiteral____x40_Lean_Expr___hyg_34_(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_instBEqLiteral() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_beqLiteral____x40_Lean_Expr___hyg_34____boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_113_(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_19; uint8_t x_20; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_4 = x_1;
} else {
 lean_dec_ref(x_1);
 x_4 = lean_box(0);
}
x_19 = lean_unsigned_to_nat(1024u);
x_20 = lean_nat_dec_le(x_19, x_2);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_unsigned_to_nat(2u);
x_22 = lean_nat_to_int(x_21);
x_5 = x_22;
goto block_18;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_to_int(x_23);
x_5 = x_24;
goto block_18;
}
block_18:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_6 = lean_mk_string_unchecked("Lean.Literal.natVal", 19, 19);
if (lean_is_scalar(x_4)) {
 x_7 = lean_alloc_ctor(3, 1, 0);
} else {
 x_7 = x_4;
 lean_ctor_set_tag(x_7, 3);
}
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_box(1);
x_9 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = l___private_Init_Data_Repr_0__Nat_reprFast(x_3);
x_11 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_15, 0, x_13);
x_16 = lean_unbox(x_14);
lean_ctor_set_uint8(x_15, sizeof(void*)*1, x_16);
x_17 = l_Repr_addAppParen(x_15, x_2);
return x_17;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_41; uint8_t x_42; 
x_25 = lean_ctor_get(x_1, 0);
lean_inc(x_25);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_26 = x_1;
} else {
 lean_dec_ref(x_1);
 x_26 = lean_box(0);
}
x_41 = lean_unsigned_to_nat(1024u);
x_42 = lean_nat_dec_le(x_41, x_2);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_unsigned_to_nat(2u);
x_44 = lean_nat_to_int(x_43);
x_27 = x_44;
goto block_40;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_unsigned_to_nat(1u);
x_46 = lean_nat_to_int(x_45);
x_27 = x_46;
goto block_40;
}
block_40:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; 
x_28 = lean_mk_string_unchecked("Lean.Literal.strVal", 19, 19);
if (lean_is_scalar(x_26)) {
 x_29 = lean_alloc_ctor(3, 1, 0);
} else {
 x_29 = x_26;
 lean_ctor_set_tag(x_29, 3);
}
lean_ctor_set(x_29, 0, x_28);
x_30 = lean_box(1);
x_31 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_String_quote(x_25);
lean_dec(x_25);
x_33 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_35, 0, x_27);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_37, 0, x_35);
x_38 = lean_unbox(x_36);
lean_ctor_set_uint8(x_37, sizeof(void*)*1, x_38);
x_39 = l_Repr_addAppParen(x_37, x_2);
return x_39;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_113____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_113_(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instReprLiteral() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_113____boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT uint64_t l_Lean_Literal_hash(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; uint64_t x_3; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_uint64_of_nat(x_2);
return x_3;
}
else
{
lean_object* x_4; uint64_t x_5; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_string_hash(x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Literal_hash___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Lean_Literal_hash(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instHashableLiteral() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Literal_hash___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_Literal_lt(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_nat_dec_lt(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_box(1);
x_7 = lean_unbox(x_6);
return x_7;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_box(0);
x_9 = lean_unbox(x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_string_dec_lt(x_10, x_11);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Literal_lt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Literal_lt(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_instLTLiteral() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_instDecidableLtLiteral(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_Literal_lt(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instDecidableLtLiteral___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_instDecidableLtLiteral(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_toCtorIdx(uint8_t x_1) {
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
default: 
{
lean_object* x_5; 
x_5 = lean_unsigned_to_nat(3u);
return x_5;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_BinderInfo_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_noConfusion___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_noConfusion___redArg(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_BinderInfo_noConfusion___redArg___lam__0___boxed), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_noConfusion(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_BinderInfo_noConfusion___redArg(x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_noConfusion___redArg___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_BinderInfo_noConfusion___redArg___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_noConfusion___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lean_BinderInfo_noConfusion___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_noConfusion___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l_Lean_BinderInfo_noConfusion(x_1, x_5, x_6, x_4);
return x_7;
}
}
static uint8_t _init_l_Lean_instInhabitedBinderInfo() {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = lean_box(0);
x_2 = lean_unbox(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_BinderInfo_toCtorIdx(x_1);
x_4 = l_Lean_BinderInfo_toCtorIdx(x_2);
x_5 = lean_nat_dec_eq(x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_instBEqBinderInfo() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406____boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_424_(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_12; lean_object* x_21; lean_object* x_30; 
switch (x_1) {
case 0:
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_unsigned_to_nat(1024u);
x_40 = lean_nat_dec_le(x_39, x_2);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_unsigned_to_nat(2u);
x_42 = lean_nat_to_int(x_41);
x_3 = x_42;
goto block_11;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_unsigned_to_nat(1u);
x_44 = lean_nat_to_int(x_43);
x_3 = x_44;
goto block_11;
}
}
case 1:
{
lean_object* x_45; uint8_t x_46; 
x_45 = lean_unsigned_to_nat(1024u);
x_46 = lean_nat_dec_le(x_45, x_2);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_unsigned_to_nat(2u);
x_48 = lean_nat_to_int(x_47);
x_12 = x_48;
goto block_20;
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_unsigned_to_nat(1u);
x_50 = lean_nat_to_int(x_49);
x_12 = x_50;
goto block_20;
}
}
case 2:
{
lean_object* x_51; uint8_t x_52; 
x_51 = lean_unsigned_to_nat(1024u);
x_52 = lean_nat_dec_le(x_51, x_2);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_unsigned_to_nat(2u);
x_54 = lean_nat_to_int(x_53);
x_21 = x_54;
goto block_29;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_unsigned_to_nat(1u);
x_56 = lean_nat_to_int(x_55);
x_21 = x_56;
goto block_29;
}
}
default: 
{
lean_object* x_57; uint8_t x_58; 
x_57 = lean_unsigned_to_nat(1024u);
x_58 = lean_nat_dec_le(x_57, x_2);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_unsigned_to_nat(2u);
x_60 = lean_nat_to_int(x_59);
x_30 = x_60;
goto block_38;
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_unsigned_to_nat(1u);
x_62 = lean_nat_to_int(x_61);
x_30 = x_62;
goto block_38;
}
}
}
block_11:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_4 = lean_mk_string_unchecked("Lean.BinderInfo.default", 23, 23);
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
x_13 = lean_mk_string_unchecked("Lean.BinderInfo.implicit", 24, 24);
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
x_22 = lean_mk_string_unchecked("Lean.BinderInfo.strictImplicit", 30, 30);
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
x_31 = lean_mk_string_unchecked("Lean.BinderInfo.instImplicit", 28, 28);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_424____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_424_(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_instReprBinderInfo() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_424____boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT uint64_t l_Lean_BinderInfo_hash(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_2; uint64_t x_3; 
x_2 = lean_unsigned_to_nat(947u);
x_3 = lean_uint64_of_nat(x_2);
return x_3;
}
case 1:
{
lean_object* x_4; uint64_t x_5; 
x_4 = lean_unsigned_to_nat(1019u);
x_5 = lean_uint64_of_nat(x_4);
return x_5;
}
case 2:
{
lean_object* x_6; uint64_t x_7; 
x_6 = lean_unsigned_to_nat(1087u);
x_7 = lean_uint64_of_nat(x_6);
return x_7;
}
default: 
{
lean_object* x_8; uint64_t x_9; 
x_8 = lean_unsigned_to_nat(1153u);
x_9 = lean_uint64_of_nat(x_8);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_hash___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint64_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_BinderInfo_hash(x_2);
x_4 = lean_box_uint64(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_BinderInfo_isExplicit(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(x_1);
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
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = lean_unbox(x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_isExplicit___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_BinderInfo_isExplicit(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_instHashableBinderInfo() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_BinderInfo_hash___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_BinderInfo_isInstImplicit(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(x_1);
if (lean_obj_tag(x_2) == 3)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_box(1);
x_4 = lean_unbox(x_3);
return x_4;
}
else
{
lean_object* x_5; uint8_t x_6; 
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = lean_unbox(x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_isInstImplicit___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_BinderInfo_isInstImplicit(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_BinderInfo_isImplicit(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(x_1);
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_box(1);
x_4 = lean_unbox(x_3);
return x_4;
}
else
{
lean_object* x_5; uint8_t x_6; 
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = lean_unbox(x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_isImplicit___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_BinderInfo_isImplicit(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_BinderInfo_isStrictImplicit(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(x_1);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_box(1);
x_4 = lean_unbox(x_3);
return x_4;
}
else
{
lean_object* x_5; uint8_t x_6; 
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = lean_unbox(x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_isStrictImplicit___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_BinderInfo_isStrictImplicit(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_MData_empty() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static uint64_t _init_l_Lean_instInhabitedData__1() {
_start:
{
uint64_t x_1; 
x_1 = l_instInhabitedUInt64;
return x_1;
}
}
LEAN_EXPORT uint64_t l_Lean_Expr_Data_hash(uint64_t x_1) {
_start:
{
uint32_t x_2; uint64_t x_3; 
x_2 = lean_uint64_to_uint32(x_1);
x_3 = lean_uint32_to_uint64(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_Data_hash___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; uint64_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_3 = l_Lean_Expr_Data_hash(x_2);
x_4 = lean_box_uint64(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqData__1___lam__0(uint64_t x_1, uint64_t x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_uint64_dec_eq(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instBEqData__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_instBEqData__1___lam__0___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqData__1___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_5 = l_Lean_instBEqData__1___lam__0(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_Data_approxDepth(uint64_t x_1) {
_start:
{
lean_object* x_2; uint64_t x_3; uint64_t x_4; lean_object* x_5; uint64_t x_6; uint64_t x_7; uint8_t x_8; 
x_2 = lean_unsigned_to_nat(32u);
x_3 = lean_uint64_of_nat(x_2);
x_4 = lean_uint64_shift_right(x_1, x_3);
x_5 = lean_unsigned_to_nat(255u);
x_6 = lean_uint64_of_nat(x_5);
x_7 = lean_uint64_land(x_4, x_6);
x_8 = lean_uint64_to_uint8(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_Data_approxDepth___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_3 = l_Lean_Expr_Data_approxDepth(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint32_t l_Lean_Expr_Data_looseBVarRange(uint64_t x_1) {
_start:
{
lean_object* x_2; uint64_t x_3; uint64_t x_4; uint32_t x_5; 
x_2 = lean_unsigned_to_nat(44u);
x_3 = lean_uint64_of_nat(x_2);
x_4 = lean_uint64_shift_right(x_1, x_3);
x_5 = lean_uint64_to_uint32(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_Data_looseBVarRange___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; uint32_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_3 = l_Lean_Expr_Data_looseBVarRange(x_2);
x_4 = lean_box_uint32(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_Data_hasFVar(uint64_t x_1) {
_start:
{
lean_object* x_2; uint64_t x_3; uint64_t x_4; lean_object* x_5; uint64_t x_6; uint64_t x_7; uint8_t x_8; 
x_2 = lean_unsigned_to_nat(40u);
x_3 = lean_uint64_of_nat(x_2);
x_4 = lean_uint64_shift_right(x_1, x_3);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_uint64_of_nat(x_5);
x_7 = lean_uint64_land(x_4, x_6);
x_8 = lean_uint64_dec_eq(x_7, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_Data_hasFVar___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_3 = l_Lean_Expr_Data_hasFVar(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_Data_hasExprMVar(uint64_t x_1) {
_start:
{
lean_object* x_2; uint64_t x_3; uint64_t x_4; lean_object* x_5; uint64_t x_6; uint64_t x_7; uint8_t x_8; 
x_2 = lean_unsigned_to_nat(41u);
x_3 = lean_uint64_of_nat(x_2);
x_4 = lean_uint64_shift_right(x_1, x_3);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_uint64_of_nat(x_5);
x_7 = lean_uint64_land(x_4, x_6);
x_8 = lean_uint64_dec_eq(x_7, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_Data_hasExprMVar___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_3 = l_Lean_Expr_Data_hasExprMVar(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_Data_hasLevelMVar(uint64_t x_1) {
_start:
{
lean_object* x_2; uint64_t x_3; uint64_t x_4; lean_object* x_5; uint64_t x_6; uint64_t x_7; uint8_t x_8; 
x_2 = lean_unsigned_to_nat(42u);
x_3 = lean_uint64_of_nat(x_2);
x_4 = lean_uint64_shift_right(x_1, x_3);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_uint64_of_nat(x_5);
x_7 = lean_uint64_land(x_4, x_6);
x_8 = lean_uint64_dec_eq(x_7, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_Data_hasLevelMVar___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_3 = l_Lean_Expr_Data_hasLevelMVar(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_Data_hasLevelParam(uint64_t x_1) {
_start:
{
lean_object* x_2; uint64_t x_3; uint64_t x_4; lean_object* x_5; uint64_t x_6; uint64_t x_7; uint8_t x_8; 
x_2 = lean_unsigned_to_nat(43u);
x_3 = lean_uint64_of_nat(x_2);
x_4 = lean_uint64_shift_right(x_1, x_3);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_uint64_of_nat(x_5);
x_7 = lean_uint64_land(x_4, x_6);
x_8 = lean_uint64_dec_eq(x_7, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_Data_hasLevelParam___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_3 = l_Lean_Expr_Data_hasLevelParam(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_toUInt64___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint64_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = lean_uint8_to_uint64(x_2);
x_4 = lean_box_uint64(x_3);
return x_4;
}
}
static lean_object* _init_l_panic___at___Lean_Expr_mkData_spec__0___boxed__const__1() {
_start:
{
uint64_t x_1; lean_object* x_2; 
x_1 = l_instInhabitedUInt64;
x_2 = lean_box_uint64(x_1);
return x_2;
}
}
LEAN_EXPORT uint64_t l_panic___at___Lean_Expr_mkData_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint64_t x_4; 
x_2 = l_panic___at___Lean_Expr_mkData_spec__0___boxed__const__1;
x_3 = lean_panic_fn(x_2, x_1);
x_4 = lean_unbox_uint64(x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT uint64_t l_Lean_Expr_mkData(uint64_t x_1, lean_object* x_2, uint32_t x_3, uint8_t x_4, uint8_t x_5, uint8_t x_6, uint8_t x_7) {
_start:
{
uint8_t x_8; lean_object* x_54; uint32_t x_55; uint8_t x_56; 
x_54 = lean_unsigned_to_nat(255u);
x_55 = lean_uint32_of_nat(x_54);
x_56 = lean_uint32_dec_lt(x_55, x_3);
if (x_56 == 0)
{
uint8_t x_57; 
x_57 = lean_uint32_to_uint8(x_3);
x_8 = x_57;
goto block_53;
}
else
{
uint8_t x_58; 
x_58 = lean_uint8_of_nat(x_54);
x_8 = x_58;
goto block_53;
}
block_53:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_9 = lean_unsigned_to_nat(2u);
x_10 = lean_unsigned_to_nat(20u);
x_11 = lean_nat_pow(x_9, x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_11, x_12);
lean_dec(x_11);
x_14 = lean_nat_dec_le(x_2, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint64_t x_20; 
x_15 = lean_mk_string_unchecked("Lean.Expr", 9, 9);
x_16 = lean_mk_string_unchecked("Lean.Expr.mkData", 16, 16);
x_17 = lean_unsigned_to_nat(174u);
x_18 = lean_mk_string_unchecked("assertion violation: (looseBVarRange ≤ Nat.pow 2 20 - 1)\n  ", 61, 59);
x_19 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_15, x_16, x_17, x_9, x_18);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
x_20 = l_panic___at___Lean_Expr_mkData_spec__0(x_19);
return x_20;
}
else
{
uint32_t x_21; uint64_t x_22; uint64_t x_23; lean_object* x_24; uint64_t x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; lean_object* x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; lean_object* x_34; uint64_t x_35; uint64_t x_36; uint64_t x_37; uint64_t x_38; lean_object* x_39; uint64_t x_40; uint64_t x_41; uint64_t x_42; uint64_t x_43; lean_object* x_44; uint64_t x_45; uint64_t x_46; uint64_t x_47; uint64_t x_48; lean_object* x_49; uint64_t x_50; uint64_t x_51; uint64_t x_52; 
x_21 = lean_uint64_to_uint32(x_1);
x_22 = lean_uint32_to_uint64(x_21);
x_23 = lean_uint8_to_uint64(x_8);
x_24 = lean_unsigned_to_nat(32u);
x_25 = lean_uint64_of_nat(x_24);
x_26 = lean_uint64_shift_left(x_23, x_25);
x_27 = lean_uint64_add(x_22, x_26);
x_28 = lean_bool_to_uint64(x_4);
x_29 = lean_unsigned_to_nat(40u);
x_30 = lean_uint64_of_nat(x_29);
x_31 = lean_uint64_shift_left(x_28, x_30);
x_32 = lean_uint64_add(x_27, x_31);
x_33 = lean_bool_to_uint64(x_5);
x_34 = lean_unsigned_to_nat(41u);
x_35 = lean_uint64_of_nat(x_34);
x_36 = lean_uint64_shift_left(x_33, x_35);
x_37 = lean_uint64_add(x_32, x_36);
x_38 = lean_bool_to_uint64(x_6);
x_39 = lean_unsigned_to_nat(42u);
x_40 = lean_uint64_of_nat(x_39);
x_41 = lean_uint64_shift_left(x_38, x_40);
x_42 = lean_uint64_add(x_37, x_41);
x_43 = lean_bool_to_uint64(x_7);
x_44 = lean_unsigned_to_nat(43u);
x_45 = lean_uint64_of_nat(x_44);
x_46 = lean_uint64_shift_left(x_43, x_45);
x_47 = lean_uint64_add(x_42, x_46);
x_48 = lean_uint64_of_nat(x_2);
x_49 = lean_unsigned_to_nat(44u);
x_50 = lean_uint64_of_nat(x_49);
x_51 = lean_uint64_shift_left(x_48, x_50);
x_52 = lean_uint64_add(x_47, x_51);
return x_52;
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Expr_mkData_spec__0___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_panic___at___Lean_Expr_mkData_spec__0(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mkData___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint64_t x_8; uint32_t x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; uint64_t x_14; lean_object* x_15; 
x_8 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_9 = lean_unbox_uint32(x_3);
lean_dec(x_3);
x_10 = lean_unbox(x_4);
lean_dec(x_4);
x_11 = lean_unbox(x_5);
lean_dec(x_5);
x_12 = lean_unbox(x_6);
lean_dec(x_6);
x_13 = lean_unbox(x_7);
lean_dec(x_7);
x_14 = l_Lean_Expr_mkData(x_8, x_2, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_2);
x_15 = lean_box_uint64(x_14);
return x_15;
}
}
static lean_object* _init_l_Lean_Expr_mkAppData___boxed__const__1() {
_start:
{
uint64_t x_1; lean_object* x_2; 
x_1 = l_instInhabitedUInt64;
x_2 = lean_box_uint64(x_1);
return x_2;
}
}
LEAN_EXPORT uint64_t l_Lean_Expr_mkAppData(uint64_t x_1, uint64_t x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; uint32_t x_5; lean_object* x_42; uint8_t x_43; uint16_t x_48; uint8_t x_58; uint16_t x_59; uint8_t x_60; uint16_t x_61; uint8_t x_62; 
x_58 = l_Lean_Expr_Data_approxDepth(x_1);
x_59 = lean_uint8_to_uint16(x_58);
x_60 = l_Lean_Expr_Data_approxDepth(x_2);
x_61 = lean_uint8_to_uint16(x_60);
x_62 = lean_uint16_dec_le(x_59, x_61);
if (x_62 == 0)
{
x_48 = x_59;
goto block_57;
}
else
{
x_48 = x_61;
goto block_57;
}
block_41:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint32_t x_10; uint8_t x_11; 
x_6 = lean_unsigned_to_nat(2u);
x_7 = lean_unsigned_to_nat(20u);
x_8 = lean_nat_pow(x_6, x_7);
x_9 = lean_nat_sub(x_8, x_3);
lean_dec(x_8);
x_10 = lean_uint32_of_nat(x_9);
lean_dec(x_9);
x_11 = lean_uint32_dec_le(x_5, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint64_t x_19; 
x_12 = lean_mk_string_unchecked("Lean.Expr", 9, 9);
x_13 = lean_mk_string_unchecked("Lean.Expr.mkAppData", 19, 19);
x_14 = lean_unsigned_to_nat(193u);
x_15 = lean_mk_string_unchecked("assertion violation: (looseBVarRange ≤ (Nat.pow 2 20 - 1).toUInt32)\n  ", 72, 70);
x_16 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_12, x_13, x_14, x_6, x_15);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
x_17 = l_Lean_Expr_mkAppData___boxed__const__1;
x_18 = l_panic___redArg(x_17, x_16);
x_19 = lean_unbox_uint64(x_18);
lean_dec(x_18);
return x_19;
}
else
{
uint64_t x_20; uint64_t x_21; lean_object* x_22; uint64_t x_23; lean_object* x_24; uint64_t x_25; uint64_t x_26; uint64_t x_27; uint32_t x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; lean_object* x_32; uint64_t x_33; uint64_t x_34; uint64_t x_35; uint64_t x_36; lean_object* x_37; uint64_t x_38; uint64_t x_39; uint64_t x_40; 
x_20 = lean_uint64_mix_hash(x_1, x_2);
x_21 = lean_uint64_lor(x_1, x_2);
x_22 = lean_unsigned_to_nat(15u);
x_23 = lean_uint64_of_nat(x_22);
x_24 = lean_unsigned_to_nat(40u);
x_25 = lean_uint64_of_nat(x_24);
x_26 = lean_uint64_shift_left(x_23, x_25);
x_27 = lean_uint64_land(x_21, x_26);
x_28 = lean_uint64_to_uint32(x_20);
x_29 = lean_uint32_to_uint64(x_28);
x_30 = lean_uint64_lor(x_27, x_29);
x_31 = lean_uint8_to_uint64(x_4);
x_32 = lean_unsigned_to_nat(32u);
x_33 = lean_uint64_of_nat(x_32);
x_34 = lean_uint64_shift_left(x_31, x_33);
x_35 = lean_uint64_lor(x_30, x_34);
x_36 = lean_uint32_to_uint64(x_5);
x_37 = lean_unsigned_to_nat(44u);
x_38 = lean_uint64_of_nat(x_37);
x_39 = lean_uint64_shift_left(x_36, x_38);
x_40 = lean_uint64_lor(x_35, x_39);
return x_40;
}
}
block_47:
{
uint32_t x_44; uint32_t x_45; uint8_t x_46; 
x_44 = l_Lean_Expr_Data_looseBVarRange(x_1);
x_45 = l_Lean_Expr_Data_looseBVarRange(x_2);
x_46 = lean_uint32_dec_le(x_44, x_45);
if (x_46 == 0)
{
x_3 = x_42;
x_4 = x_43;
x_5 = x_44;
goto block_41;
}
else
{
x_3 = x_42;
x_4 = x_43;
x_5 = x_45;
goto block_41;
}
}
block_57:
{
lean_object* x_49; uint16_t x_50; uint16_t x_51; lean_object* x_52; uint16_t x_53; uint8_t x_54; 
x_49 = lean_unsigned_to_nat(1u);
x_50 = lean_uint16_of_nat(x_49);
x_51 = lean_uint16_add(x_48, x_50);
x_52 = lean_unsigned_to_nat(255u);
x_53 = lean_uint16_of_nat(x_52);
x_54 = lean_uint16_dec_lt(x_53, x_51);
if (x_54 == 0)
{
uint8_t x_55; 
x_55 = lean_uint16_to_uint8(x_51);
x_42 = x_49;
x_43 = x_55;
goto block_47;
}
else
{
uint8_t x_56; 
x_56 = lean_uint8_of_nat(x_52);
x_42 = x_49;
x_43 = x_56;
goto block_47;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mkAppData___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; uint64_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_5 = l_Lean_Expr_mkAppData(x_3, x_4);
x_6 = lean_box_uint64(x_5);
return x_6;
}
}
LEAN_EXPORT uint64_t l_Lean_Expr_mkDataForBinder(uint64_t x_1, lean_object* x_2, uint32_t x_3, uint8_t x_4, uint8_t x_5, uint8_t x_6, uint8_t x_7) {
_start:
{
uint64_t x_8; 
x_8 = l_Lean_Expr_mkData(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mkDataForBinder___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint64_t x_8; uint32_t x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; uint64_t x_14; lean_object* x_15; 
x_8 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_9 = lean_unbox_uint32(x_3);
lean_dec(x_3);
x_10 = lean_unbox(x_4);
lean_dec(x_4);
x_11 = lean_unbox(x_5);
lean_dec(x_5);
x_12 = lean_unbox(x_6);
lean_dec(x_6);
x_13 = lean_unbox(x_7);
lean_dec(x_7);
x_14 = l_Lean_Expr_mkDataForBinder(x_8, x_2, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_2);
x_15 = lean_box_uint64(x_14);
return x_15;
}
}
LEAN_EXPORT uint64_t l_Lean_Expr_mkDataForLet(uint64_t x_1, lean_object* x_2, uint32_t x_3, uint8_t x_4, uint8_t x_5, uint8_t x_6, uint8_t x_7) {
_start:
{
uint64_t x_8; 
x_8 = l_Lean_Expr_mkData(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mkDataForLet___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint64_t x_8; uint32_t x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; uint64_t x_14; lean_object* x_15; 
x_8 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_9 = lean_unbox_uint32(x_3);
lean_dec(x_3);
x_10 = lean_unbox(x_4);
lean_dec(x_4);
x_11 = lean_unbox(x_5);
lean_dec(x_5);
x_12 = lean_unbox(x_6);
lean_dec(x_6);
x_13 = lean_unbox(x_7);
lean_dec(x_7);
x_14 = l_Lean_Expr_mkDataForLet(x_8, x_2, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_2);
x_15 = lean_box_uint64(x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprData__1___lam__0(uint64_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_7; lean_object* x_8; lean_object* x_13; lean_object* x_20; lean_object* x_21; lean_object* x_26; lean_object* x_33; lean_object* x_34; lean_object* x_39; lean_object* x_46; lean_object* x_59; uint64_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint32_t x_64; lean_object* x_65; uint32_t x_66; uint8_t x_67; 
x_59 = lean_mk_string_unchecked("Expr.mkData ", 12, 12);
x_60 = l_Lean_Expr_Data_hash(x_1);
x_61 = lean_uint64_to_nat(x_60);
x_62 = l___private_Init_Data_Repr_0__Nat_reprFast(x_61);
x_63 = lean_string_append(x_59, x_62);
lean_dec(x_62);
x_64 = l_Lean_Expr_Data_looseBVarRange(x_1);
x_65 = lean_unsigned_to_nat(0u);
x_66 = lean_uint32_of_nat(x_65);
x_67 = lean_uint32_dec_eq(x_64, x_66);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_68 = lean_mk_string_unchecked(" (looseBVarRange := ", 20, 20);
x_69 = lean_string_append(x_63, x_68);
lean_dec(x_68);
x_70 = lean_uint32_to_nat(x_64);
x_71 = l___private_Init_Data_Repr_0__Nat_reprFast(x_70);
x_72 = lean_string_append(x_69, x_71);
lean_dec(x_71);
x_73 = lean_mk_string_unchecked(")", 1, 1);
x_74 = lean_string_append(x_72, x_73);
lean_dec(x_73);
x_46 = x_74;
goto block_58;
}
else
{
x_46 = x_63;
goto block_58;
}
block_6:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_4, 0, x_3);
x_5 = l_Repr_addAppParen(x_4, x_2);
return x_5;
}
block_12:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_string_append(x_7, x_8);
x_10 = lean_mk_string_unchecked(")", 1, 1);
x_11 = lean_string_append(x_9, x_10);
lean_dec(x_10);
x_3 = x_11;
goto block_6;
}
block_19:
{
uint8_t x_14; 
x_14 = l_Lean_Expr_Data_hasLevelMVar(x_1);
if (x_14 == 0)
{
x_3 = x_13;
goto block_6;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_mk_string_unchecked(" (hasLevelMVar := ", 18, 18);
x_16 = lean_string_append(x_13, x_15);
lean_dec(x_15);
if (x_14 == 0)
{
lean_object* x_17; 
x_17 = lean_mk_string_unchecked("false", 5, 5);
x_7 = x_16;
x_8 = x_17;
goto block_12;
}
else
{
lean_object* x_18; 
x_18 = lean_mk_string_unchecked("true", 4, 4);
x_7 = x_16;
x_8 = x_18;
goto block_12;
}
}
}
block_25:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_string_append(x_20, x_21);
x_23 = lean_mk_string_unchecked(")", 1, 1);
x_24 = lean_string_append(x_22, x_23);
lean_dec(x_23);
x_13 = x_24;
goto block_19;
}
block_32:
{
uint8_t x_27; 
x_27 = l_Lean_Expr_Data_hasExprMVar(x_1);
if (x_27 == 0)
{
x_13 = x_26;
goto block_19;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_mk_string_unchecked(" (hasExprMVar := ", 17, 17);
x_29 = lean_string_append(x_26, x_28);
lean_dec(x_28);
if (x_27 == 0)
{
lean_object* x_30; 
x_30 = lean_mk_string_unchecked("false", 5, 5);
x_20 = x_29;
x_21 = x_30;
goto block_25;
}
else
{
lean_object* x_31; 
x_31 = lean_mk_string_unchecked("true", 4, 4);
x_20 = x_29;
x_21 = x_31;
goto block_25;
}
}
}
block_38:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_string_append(x_33, x_34);
x_36 = lean_mk_string_unchecked(")", 1, 1);
x_37 = lean_string_append(x_35, x_36);
lean_dec(x_36);
x_26 = x_37;
goto block_32;
}
block_45:
{
uint8_t x_40; 
x_40 = l_Lean_Expr_Data_hasFVar(x_1);
if (x_40 == 0)
{
x_26 = x_39;
goto block_32;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_mk_string_unchecked(" (hasFVar := ", 13, 13);
x_42 = lean_string_append(x_39, x_41);
lean_dec(x_41);
if (x_40 == 0)
{
lean_object* x_43; 
x_43 = lean_mk_string_unchecked("false", 5, 5);
x_33 = x_42;
x_34 = x_43;
goto block_38;
}
else
{
lean_object* x_44; 
x_44 = lean_mk_string_unchecked("true", 4, 4);
x_33 = x_42;
x_34 = x_44;
goto block_38;
}
}
}
block_58:
{
uint8_t x_47; lean_object* x_48; uint8_t x_49; uint8_t x_50; 
x_47 = l_Lean_Expr_Data_approxDepth(x_1);
x_48 = lean_unsigned_to_nat(0u);
x_49 = lean_uint8_of_nat(x_48);
x_50 = lean_uint8_dec_eq(x_47, x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_51 = lean_mk_string_unchecked(" (approxDepth := ", 17, 17);
x_52 = lean_string_append(x_46, x_51);
lean_dec(x_51);
x_53 = lean_uint8_to_nat(x_47);
x_54 = l___private_Init_Data_Repr_0__Nat_reprFast(x_53);
x_55 = lean_string_append(x_52, x_54);
lean_dec(x_54);
x_56 = lean_mk_string_unchecked(")", 1, 1);
x_57 = lean_string_append(x_55, x_56);
lean_dec(x_56);
x_39 = x_57;
goto block_45;
}
else
{
x_39 = x_46;
goto block_45;
}
}
}
}
static lean_object* _init_l_Lean_instReprData__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_instReprData__1___lam__0___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprData__1___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = l_Lean_instReprData__1___lam__0(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_instInhabitedFVarId() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_beqFVarId____x40_Lean_Expr___hyg_1672_(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_name_eq(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_beqFVarId____x40_Lean_Expr___hyg_1672____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Expr_0__Lean_beqFVarId____x40_Lean_Expr___hyg_1672_(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_instBEqFVarId() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_beqFVarId____x40_Lean_Expr___hyg_1672____boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT uint64_t l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint64_t x_3; uint64_t x_4; uint64_t x_5; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_uint64_of_nat(x_2);
x_4 = l_Lean_Name_hash___override(x_1);
x_5 = lean_uint64_mix_hash(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730____boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instHashableFVarId() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730____boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprFVarId___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Name_reprPrec(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instReprFVarId() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_instReprFVarId___lam__0___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprFVarId___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_instReprFVarId___lam__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instFVarIdSetInhabited() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_instFVarIdSetEmptyCollection___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_Name_quickCmp(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instFVarIdSetEmptyCollection() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_alloc_closure((void*)(l_Lean_instFVarIdSetEmptyCollection___lam__0___boxed), 2, 0);
x_2 = l_Lean_instEmptyCollectionRBTree(lean_box(0), x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instFVarIdSetEmptyCollection___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_instFVarIdSetEmptyCollection___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInFVarIdSetFVarId(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_alloc_closure((void*)(l_Lean_instFVarIdSetEmptyCollection___lam__0___boxed), 2, 0);
x_3 = l_Lean_RBTree_instForIn(lean_box(0), x_2, lean_box(0));
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_FVarIdSet_insert_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_1);
x_6 = lean_unbox(x_4);
lean_ctor_set_uint8(x_5, sizeof(void*)*4, x_6);
return x_5;
}
else
{
uint8_t x_7; 
x_7 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_ctor_get(x_1, 2);
x_12 = lean_ctor_get(x_1, 3);
x_13 = l_Lean_Name_quickCmp(x_2, x_10);
switch (x_13) {
case 0:
{
lean_object* x_14; 
x_14 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_FVarIdSet_insert_spec__0_spec__0___redArg(x_9, x_2, x_3);
lean_ctor_set(x_1, 0, x_14);
return x_1;
}
case 1:
{
lean_dec(x_11);
lean_dec(x_10);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
return x_1;
}
default: 
{
lean_object* x_15; 
x_15 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_FVarIdSet_insert_spec__0_spec__0___redArg(x_12, x_2, x_3);
lean_ctor_set(x_1, 3, x_15);
return x_1;
}
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_ctor_get(x_1, 0);
x_17 = lean_ctor_get(x_1, 1);
x_18 = lean_ctor_get(x_1, 2);
x_19 = lean_ctor_get(x_1, 3);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_1);
x_20 = l_Lean_Name_quickCmp(x_2, x_17);
switch (x_20) {
case 0:
{
lean_object* x_21; lean_object* x_22; 
x_21 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_FVarIdSet_insert_spec__0_spec__0___redArg(x_16, x_2, x_3);
x_22 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_17);
lean_ctor_set(x_22, 2, x_18);
lean_ctor_set(x_22, 3, x_19);
lean_ctor_set_uint8(x_22, sizeof(void*)*4, x_7);
return x_22;
}
case 1:
{
lean_object* x_23; 
lean_dec(x_18);
lean_dec(x_17);
x_23 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_23, 0, x_16);
lean_ctor_set(x_23, 1, x_2);
lean_ctor_set(x_23, 2, x_3);
lean_ctor_set(x_23, 3, x_19);
lean_ctor_set_uint8(x_23, sizeof(void*)*4, x_7);
return x_23;
}
default: 
{
lean_object* x_24; lean_object* x_25; 
x_24 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_FVarIdSet_insert_spec__0_spec__0___redArg(x_19, x_2, x_3);
x_25 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_25, 0, x_16);
lean_ctor_set(x_25, 1, x_17);
lean_ctor_set(x_25, 2, x_18);
lean_ctor_set(x_25, 3, x_24);
lean_ctor_set_uint8(x_25, sizeof(void*)*4, x_7);
return x_25;
}
}
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_26 = lean_ctor_get(x_1, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_1, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_1, 2);
lean_inc(x_28);
x_29 = lean_ctor_get(x_1, 3);
lean_inc(x_29);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 x_30 = x_1;
} else {
 lean_dec_ref(x_1);
 x_30 = lean_box(0);
}
x_31 = l_Lean_Name_quickCmp(x_2, x_27);
switch (x_31) {
case 0:
{
lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_32 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_FVarIdSet_insert_spec__0_spec__0___redArg(x_26, x_2, x_3);
x_33 = lean_ctor_get_uint8(x_32, sizeof(void*)*4);
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_32, 2);
lean_inc(x_36);
x_37 = lean_ctor_get(x_32, 3);
lean_inc(x_37);
if (x_33 == 0)
{
if (lean_obj_tag(x_34) == 0)
{
if (lean_obj_tag(x_37) == 0)
{
uint8_t x_52; 
lean_dec(x_30);
x_52 = !lean_is_exclusive(x_32);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_53 = lean_ctor_get(x_32, 3);
lean_dec(x_53);
x_54 = lean_ctor_get(x_32, 2);
lean_dec(x_54);
x_55 = lean_ctor_get(x_32, 1);
lean_dec(x_55);
x_56 = lean_ctor_get(x_32, 0);
lean_dec(x_56);
lean_ctor_set(x_32, 0, x_37);
x_57 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_57, 0, x_32);
lean_ctor_set(x_57, 1, x_27);
lean_ctor_set(x_57, 2, x_28);
lean_ctor_set(x_57, 3, x_29);
lean_ctor_set_uint8(x_57, sizeof(void*)*4, x_7);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_32);
x_58 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_58, 0, x_37);
lean_ctor_set(x_58, 1, x_35);
lean_ctor_set(x_58, 2, x_36);
lean_ctor_set(x_58, 3, x_37);
lean_ctor_set_uint8(x_58, sizeof(void*)*4, x_33);
x_59 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_27);
lean_ctor_set(x_59, 2, x_28);
lean_ctor_set(x_59, 3, x_29);
lean_ctor_set_uint8(x_59, sizeof(void*)*4, x_7);
return x_59;
}
}
else
{
uint8_t x_60; 
x_60 = lean_ctor_get_uint8(x_37, sizeof(void*)*4);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_32);
x_61 = lean_ctor_get(x_37, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_37, 1);
lean_inc(x_62);
x_63 = lean_ctor_get(x_37, 2);
lean_inc(x_63);
x_64 = lean_ctor_get(x_37, 3);
lean_inc(x_64);
lean_dec(x_37);
x_38 = x_34;
x_39 = x_35;
x_40 = x_36;
x_41 = x_61;
x_42 = x_62;
x_43 = x_63;
x_44 = x_64;
x_45 = x_27;
x_46 = x_28;
x_47 = x_29;
goto block_51;
}
else
{
uint8_t x_65; 
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_30);
x_65 = !lean_is_exclusive(x_37);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_37, 3);
lean_dec(x_66);
x_67 = lean_ctor_get(x_37, 2);
lean_dec(x_67);
x_68 = lean_ctor_get(x_37, 1);
lean_dec(x_68);
x_69 = lean_ctor_get(x_37, 0);
lean_dec(x_69);
lean_ctor_set(x_37, 3, x_29);
lean_ctor_set(x_37, 2, x_28);
lean_ctor_set(x_37, 1, x_27);
lean_ctor_set(x_37, 0, x_32);
lean_ctor_set_uint8(x_37, sizeof(void*)*4, x_7);
return x_37;
}
else
{
lean_object* x_70; 
lean_dec(x_37);
x_70 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_70, 0, x_32);
lean_ctor_set(x_70, 1, x_27);
lean_ctor_set(x_70, 2, x_28);
lean_ctor_set(x_70, 3, x_29);
lean_ctor_set_uint8(x_70, sizeof(void*)*4, x_7);
return x_70;
}
}
}
}
else
{
uint8_t x_71; 
x_71 = lean_ctor_get_uint8(x_34, sizeof(void*)*4);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_32);
x_72 = lean_ctor_get(x_34, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_34, 1);
lean_inc(x_73);
x_74 = lean_ctor_get(x_34, 2);
lean_inc(x_74);
x_75 = lean_ctor_get(x_34, 3);
lean_inc(x_75);
lean_dec(x_34);
x_38 = x_72;
x_39 = x_73;
x_40 = x_74;
x_41 = x_75;
x_42 = x_35;
x_43 = x_36;
x_44 = x_37;
x_45 = x_27;
x_46 = x_28;
x_47 = x_29;
goto block_51;
}
else
{
if (lean_obj_tag(x_37) == 0)
{
uint8_t x_76; 
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_30);
x_76 = !lean_is_exclusive(x_34);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_77 = lean_ctor_get(x_34, 3);
lean_dec(x_77);
x_78 = lean_ctor_get(x_34, 2);
lean_dec(x_78);
x_79 = lean_ctor_get(x_34, 1);
lean_dec(x_79);
x_80 = lean_ctor_get(x_34, 0);
lean_dec(x_80);
lean_ctor_set(x_34, 3, x_29);
lean_ctor_set(x_34, 2, x_28);
lean_ctor_set(x_34, 1, x_27);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set_uint8(x_34, sizeof(void*)*4, x_7);
return x_34;
}
else
{
lean_object* x_81; 
lean_dec(x_34);
x_81 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_81, 0, x_32);
lean_ctor_set(x_81, 1, x_27);
lean_ctor_set(x_81, 2, x_28);
lean_ctor_set(x_81, 3, x_29);
lean_ctor_set_uint8(x_81, sizeof(void*)*4, x_7);
return x_81;
}
}
else
{
uint8_t x_82; 
x_82 = !lean_is_exclusive(x_32);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_83 = lean_ctor_get(x_32, 3);
lean_dec(x_83);
x_84 = lean_ctor_get(x_32, 2);
lean_dec(x_84);
x_85 = lean_ctor_get(x_32, 1);
lean_dec(x_85);
x_86 = lean_ctor_get(x_32, 0);
lean_dec(x_86);
x_87 = lean_ctor_get_uint8(x_37, sizeof(void*)*4);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_free_object(x_32);
x_88 = lean_ctor_get(x_37, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_37, 1);
lean_inc(x_89);
x_90 = lean_ctor_get(x_37, 2);
lean_inc(x_90);
x_91 = lean_ctor_get(x_37, 3);
lean_inc(x_91);
lean_dec(x_37);
x_38 = x_34;
x_39 = x_35;
x_40 = x_36;
x_41 = x_88;
x_42 = x_89;
x_43 = x_90;
x_44 = x_91;
x_45 = x_27;
x_46 = x_28;
x_47 = x_29;
goto block_51;
}
else
{
uint8_t x_92; 
lean_dec(x_30);
x_92 = !lean_is_exclusive(x_34);
if (x_92 == 0)
{
lean_object* x_93; 
lean_ctor_set_uint8(x_34, sizeof(void*)*4, x_87);
x_93 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_93, 0, x_32);
lean_ctor_set(x_93, 1, x_27);
lean_ctor_set(x_93, 2, x_28);
lean_ctor_set(x_93, 3, x_29);
lean_ctor_set_uint8(x_93, sizeof(void*)*4, x_7);
return x_93;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_94 = lean_ctor_get(x_34, 0);
x_95 = lean_ctor_get(x_34, 1);
x_96 = lean_ctor_get(x_34, 2);
x_97 = lean_ctor_get(x_34, 3);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_34);
x_98 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_98, 0, x_94);
lean_ctor_set(x_98, 1, x_95);
lean_ctor_set(x_98, 2, x_96);
lean_ctor_set(x_98, 3, x_97);
lean_ctor_set_uint8(x_98, sizeof(void*)*4, x_87);
lean_ctor_set(x_32, 0, x_98);
x_99 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_99, 0, x_32);
lean_ctor_set(x_99, 1, x_27);
lean_ctor_set(x_99, 2, x_28);
lean_ctor_set(x_99, 3, x_29);
lean_ctor_set_uint8(x_99, sizeof(void*)*4, x_7);
return x_99;
}
}
}
else
{
uint8_t x_100; 
lean_dec(x_32);
x_100 = lean_ctor_get_uint8(x_37, sizeof(void*)*4);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_101 = lean_ctor_get(x_37, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_37, 1);
lean_inc(x_102);
x_103 = lean_ctor_get(x_37, 2);
lean_inc(x_103);
x_104 = lean_ctor_get(x_37, 3);
lean_inc(x_104);
lean_dec(x_37);
x_38 = x_34;
x_39 = x_35;
x_40 = x_36;
x_41 = x_101;
x_42 = x_102;
x_43 = x_103;
x_44 = x_104;
x_45 = x_27;
x_46 = x_28;
x_47 = x_29;
goto block_51;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_30);
x_105 = lean_ctor_get(x_34, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_34, 1);
lean_inc(x_106);
x_107 = lean_ctor_get(x_34, 2);
lean_inc(x_107);
x_108 = lean_ctor_get(x_34, 3);
lean_inc(x_108);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 lean_ctor_release(x_34, 2);
 lean_ctor_release(x_34, 3);
 x_109 = x_34;
} else {
 lean_dec_ref(x_34);
 x_109 = lean_box(0);
}
if (lean_is_scalar(x_109)) {
 x_110 = lean_alloc_ctor(1, 4, 1);
} else {
 x_110 = x_109;
}
lean_ctor_set(x_110, 0, x_105);
lean_ctor_set(x_110, 1, x_106);
lean_ctor_set(x_110, 2, x_107);
lean_ctor_set(x_110, 3, x_108);
lean_ctor_set_uint8(x_110, sizeof(void*)*4, x_100);
x_111 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_35);
lean_ctor_set(x_111, 2, x_36);
lean_ctor_set(x_111, 3, x_37);
lean_ctor_set_uint8(x_111, sizeof(void*)*4, x_33);
x_112 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_27);
lean_ctor_set(x_112, 2, x_28);
lean_ctor_set(x_112, 3, x_29);
lean_ctor_set_uint8(x_112, sizeof(void*)*4, x_7);
return x_112;
}
}
}
}
}
}
else
{
lean_object* x_113; 
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_30);
x_113 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_113, 0, x_32);
lean_ctor_set(x_113, 1, x_27);
lean_ctor_set(x_113, 2, x_28);
lean_ctor_set(x_113, 3, x_29);
lean_ctor_set_uint8(x_113, sizeof(void*)*4, x_7);
return x_113;
}
block_51:
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
if (lean_is_scalar(x_30)) {
 x_48 = lean_alloc_ctor(1, 4, 1);
} else {
 x_48 = x_30;
}
lean_ctor_set(x_48, 0, x_38);
lean_ctor_set(x_48, 1, x_39);
lean_ctor_set(x_48, 2, x_40);
lean_ctor_set(x_48, 3, x_41);
lean_ctor_set_uint8(x_48, sizeof(void*)*4, x_7);
x_49 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_49, 0, x_44);
lean_ctor_set(x_49, 1, x_45);
lean_ctor_set(x_49, 2, x_46);
lean_ctor_set(x_49, 3, x_47);
lean_ctor_set_uint8(x_49, sizeof(void*)*4, x_7);
x_50 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_42);
lean_ctor_set(x_50, 2, x_43);
lean_ctor_set(x_50, 3, x_49);
lean_ctor_set_uint8(x_50, sizeof(void*)*4, x_33);
return x_50;
}
}
case 1:
{
lean_object* x_114; 
lean_dec(x_28);
lean_dec(x_27);
if (lean_is_scalar(x_30)) {
 x_114 = lean_alloc_ctor(1, 4, 1);
} else {
 x_114 = x_30;
}
lean_ctor_set(x_114, 0, x_26);
lean_ctor_set(x_114, 1, x_2);
lean_ctor_set(x_114, 2, x_3);
lean_ctor_set(x_114, 3, x_29);
lean_ctor_set_uint8(x_114, sizeof(void*)*4, x_7);
return x_114;
}
default: 
{
lean_object* x_115; uint8_t x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_115 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_FVarIdSet_insert_spec__0_spec__0___redArg(x_29, x_2, x_3);
x_116 = lean_ctor_get_uint8(x_115, sizeof(void*)*4);
x_117 = lean_ctor_get(x_115, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_115, 1);
lean_inc(x_118);
x_119 = lean_ctor_get(x_115, 2);
lean_inc(x_119);
x_120 = lean_ctor_get(x_115, 3);
lean_inc(x_120);
if (x_116 == 0)
{
if (lean_obj_tag(x_117) == 0)
{
if (lean_obj_tag(x_120) == 0)
{
uint8_t x_135; 
lean_dec(x_30);
x_135 = !lean_is_exclusive(x_115);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_136 = lean_ctor_get(x_115, 3);
lean_dec(x_136);
x_137 = lean_ctor_get(x_115, 2);
lean_dec(x_137);
x_138 = lean_ctor_get(x_115, 1);
lean_dec(x_138);
x_139 = lean_ctor_get(x_115, 0);
lean_dec(x_139);
lean_ctor_set(x_115, 0, x_120);
x_140 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_140, 0, x_26);
lean_ctor_set(x_140, 1, x_27);
lean_ctor_set(x_140, 2, x_28);
lean_ctor_set(x_140, 3, x_115);
lean_ctor_set_uint8(x_140, sizeof(void*)*4, x_7);
return x_140;
}
else
{
lean_object* x_141; lean_object* x_142; 
lean_dec(x_115);
x_141 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_141, 0, x_120);
lean_ctor_set(x_141, 1, x_118);
lean_ctor_set(x_141, 2, x_119);
lean_ctor_set(x_141, 3, x_120);
lean_ctor_set_uint8(x_141, sizeof(void*)*4, x_116);
x_142 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_142, 0, x_26);
lean_ctor_set(x_142, 1, x_27);
lean_ctor_set(x_142, 2, x_28);
lean_ctor_set(x_142, 3, x_141);
lean_ctor_set_uint8(x_142, sizeof(void*)*4, x_7);
return x_142;
}
}
else
{
uint8_t x_143; 
x_143 = lean_ctor_get_uint8(x_120, sizeof(void*)*4);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
lean_dec(x_115);
x_144 = lean_ctor_get(x_120, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_120, 1);
lean_inc(x_145);
x_146 = lean_ctor_get(x_120, 2);
lean_inc(x_146);
x_147 = lean_ctor_get(x_120, 3);
lean_inc(x_147);
lean_dec(x_120);
x_121 = x_26;
x_122 = x_27;
x_123 = x_28;
x_124 = x_117;
x_125 = x_118;
x_126 = x_119;
x_127 = x_144;
x_128 = x_145;
x_129 = x_146;
x_130 = x_147;
goto block_134;
}
else
{
uint8_t x_148; 
lean_dec(x_119);
lean_dec(x_118);
lean_dec(x_30);
x_148 = !lean_is_exclusive(x_120);
if (x_148 == 0)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_149 = lean_ctor_get(x_120, 3);
lean_dec(x_149);
x_150 = lean_ctor_get(x_120, 2);
lean_dec(x_150);
x_151 = lean_ctor_get(x_120, 1);
lean_dec(x_151);
x_152 = lean_ctor_get(x_120, 0);
lean_dec(x_152);
lean_ctor_set(x_120, 3, x_115);
lean_ctor_set(x_120, 2, x_28);
lean_ctor_set(x_120, 1, x_27);
lean_ctor_set(x_120, 0, x_26);
lean_ctor_set_uint8(x_120, sizeof(void*)*4, x_7);
return x_120;
}
else
{
lean_object* x_153; 
lean_dec(x_120);
x_153 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_153, 0, x_26);
lean_ctor_set(x_153, 1, x_27);
lean_ctor_set(x_153, 2, x_28);
lean_ctor_set(x_153, 3, x_115);
lean_ctor_set_uint8(x_153, sizeof(void*)*4, x_7);
return x_153;
}
}
}
}
else
{
uint8_t x_154; 
x_154 = lean_ctor_get_uint8(x_117, sizeof(void*)*4);
if (x_154 == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
lean_dec(x_115);
x_155 = lean_ctor_get(x_117, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_117, 1);
lean_inc(x_156);
x_157 = lean_ctor_get(x_117, 2);
lean_inc(x_157);
x_158 = lean_ctor_get(x_117, 3);
lean_inc(x_158);
lean_dec(x_117);
x_121 = x_26;
x_122 = x_27;
x_123 = x_28;
x_124 = x_155;
x_125 = x_156;
x_126 = x_157;
x_127 = x_158;
x_128 = x_118;
x_129 = x_119;
x_130 = x_120;
goto block_134;
}
else
{
if (lean_obj_tag(x_120) == 0)
{
uint8_t x_159; 
lean_dec(x_119);
lean_dec(x_118);
lean_dec(x_30);
x_159 = !lean_is_exclusive(x_117);
if (x_159 == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_160 = lean_ctor_get(x_117, 3);
lean_dec(x_160);
x_161 = lean_ctor_get(x_117, 2);
lean_dec(x_161);
x_162 = lean_ctor_get(x_117, 1);
lean_dec(x_162);
x_163 = lean_ctor_get(x_117, 0);
lean_dec(x_163);
lean_ctor_set(x_117, 3, x_115);
lean_ctor_set(x_117, 2, x_28);
lean_ctor_set(x_117, 1, x_27);
lean_ctor_set(x_117, 0, x_26);
lean_ctor_set_uint8(x_117, sizeof(void*)*4, x_7);
return x_117;
}
else
{
lean_object* x_164; 
lean_dec(x_117);
x_164 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_164, 0, x_26);
lean_ctor_set(x_164, 1, x_27);
lean_ctor_set(x_164, 2, x_28);
lean_ctor_set(x_164, 3, x_115);
lean_ctor_set_uint8(x_164, sizeof(void*)*4, x_7);
return x_164;
}
}
else
{
uint8_t x_165; 
x_165 = !lean_is_exclusive(x_115);
if (x_165 == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; 
x_166 = lean_ctor_get(x_115, 3);
lean_dec(x_166);
x_167 = lean_ctor_get(x_115, 2);
lean_dec(x_167);
x_168 = lean_ctor_get(x_115, 1);
lean_dec(x_168);
x_169 = lean_ctor_get(x_115, 0);
lean_dec(x_169);
x_170 = lean_ctor_get_uint8(x_120, sizeof(void*)*4);
if (x_170 == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
lean_free_object(x_115);
x_171 = lean_ctor_get(x_120, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_120, 1);
lean_inc(x_172);
x_173 = lean_ctor_get(x_120, 2);
lean_inc(x_173);
x_174 = lean_ctor_get(x_120, 3);
lean_inc(x_174);
lean_dec(x_120);
x_121 = x_26;
x_122 = x_27;
x_123 = x_28;
x_124 = x_117;
x_125 = x_118;
x_126 = x_119;
x_127 = x_171;
x_128 = x_172;
x_129 = x_173;
x_130 = x_174;
goto block_134;
}
else
{
uint8_t x_175; 
lean_dec(x_30);
x_175 = !lean_is_exclusive(x_117);
if (x_175 == 0)
{
lean_object* x_176; 
lean_ctor_set_uint8(x_117, sizeof(void*)*4, x_170);
x_176 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_176, 0, x_26);
lean_ctor_set(x_176, 1, x_27);
lean_ctor_set(x_176, 2, x_28);
lean_ctor_set(x_176, 3, x_115);
lean_ctor_set_uint8(x_176, sizeof(void*)*4, x_7);
return x_176;
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_177 = lean_ctor_get(x_117, 0);
x_178 = lean_ctor_get(x_117, 1);
x_179 = lean_ctor_get(x_117, 2);
x_180 = lean_ctor_get(x_117, 3);
lean_inc(x_180);
lean_inc(x_179);
lean_inc(x_178);
lean_inc(x_177);
lean_dec(x_117);
x_181 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_181, 0, x_177);
lean_ctor_set(x_181, 1, x_178);
lean_ctor_set(x_181, 2, x_179);
lean_ctor_set(x_181, 3, x_180);
lean_ctor_set_uint8(x_181, sizeof(void*)*4, x_170);
lean_ctor_set(x_115, 0, x_181);
x_182 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_182, 0, x_26);
lean_ctor_set(x_182, 1, x_27);
lean_ctor_set(x_182, 2, x_28);
lean_ctor_set(x_182, 3, x_115);
lean_ctor_set_uint8(x_182, sizeof(void*)*4, x_7);
return x_182;
}
}
}
else
{
uint8_t x_183; 
lean_dec(x_115);
x_183 = lean_ctor_get_uint8(x_120, sizeof(void*)*4);
if (x_183 == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_184 = lean_ctor_get(x_120, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_120, 1);
lean_inc(x_185);
x_186 = lean_ctor_get(x_120, 2);
lean_inc(x_186);
x_187 = lean_ctor_get(x_120, 3);
lean_inc(x_187);
lean_dec(x_120);
x_121 = x_26;
x_122 = x_27;
x_123 = x_28;
x_124 = x_117;
x_125 = x_118;
x_126 = x_119;
x_127 = x_184;
x_128 = x_185;
x_129 = x_186;
x_130 = x_187;
goto block_134;
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
lean_dec(x_30);
x_188 = lean_ctor_get(x_117, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_117, 1);
lean_inc(x_189);
x_190 = lean_ctor_get(x_117, 2);
lean_inc(x_190);
x_191 = lean_ctor_get(x_117, 3);
lean_inc(x_191);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 lean_ctor_release(x_117, 2);
 lean_ctor_release(x_117, 3);
 x_192 = x_117;
} else {
 lean_dec_ref(x_117);
 x_192 = lean_box(0);
}
if (lean_is_scalar(x_192)) {
 x_193 = lean_alloc_ctor(1, 4, 1);
} else {
 x_193 = x_192;
}
lean_ctor_set(x_193, 0, x_188);
lean_ctor_set(x_193, 1, x_189);
lean_ctor_set(x_193, 2, x_190);
lean_ctor_set(x_193, 3, x_191);
lean_ctor_set_uint8(x_193, sizeof(void*)*4, x_183);
x_194 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_194, 0, x_193);
lean_ctor_set(x_194, 1, x_118);
lean_ctor_set(x_194, 2, x_119);
lean_ctor_set(x_194, 3, x_120);
lean_ctor_set_uint8(x_194, sizeof(void*)*4, x_116);
x_195 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_195, 0, x_26);
lean_ctor_set(x_195, 1, x_27);
lean_ctor_set(x_195, 2, x_28);
lean_ctor_set(x_195, 3, x_194);
lean_ctor_set_uint8(x_195, sizeof(void*)*4, x_7);
return x_195;
}
}
}
}
}
}
else
{
lean_object* x_196; 
lean_dec(x_120);
lean_dec(x_119);
lean_dec(x_118);
lean_dec(x_117);
lean_dec(x_30);
x_196 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_196, 0, x_26);
lean_ctor_set(x_196, 1, x_27);
lean_ctor_set(x_196, 2, x_28);
lean_ctor_set(x_196, 3, x_115);
lean_ctor_set_uint8(x_196, sizeof(void*)*4, x_7);
return x_196;
}
block_134:
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
if (lean_is_scalar(x_30)) {
 x_131 = lean_alloc_ctor(1, 4, 1);
} else {
 x_131 = x_30;
}
lean_ctor_set(x_131, 0, x_121);
lean_ctor_set(x_131, 1, x_122);
lean_ctor_set(x_131, 2, x_123);
lean_ctor_set(x_131, 3, x_124);
lean_ctor_set_uint8(x_131, sizeof(void*)*4, x_7);
x_132 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_132, 0, x_127);
lean_ctor_set(x_132, 1, x_128);
lean_ctor_set(x_132, 2, x_129);
lean_ctor_set(x_132, 3, x_130);
lean_ctor_set_uint8(x_132, sizeof(void*)*4, x_7);
x_133 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_125);
lean_ctor_set(x_133, 2, x_126);
lean_ctor_set(x_133, 3, x_132);
lean_ctor_set_uint8(x_133, sizeof(void*)*4, x_116);
return x_133;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_FVarIdSet_insert_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_FVarIdSet_insert_spec__0_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at___Lean_FVarIdSet_insert_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_RBNode_isRed___redArg(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_FVarIdSet_insert_spec__0_spec__0___redArg(x_1, x_2, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_FVarIdSet_insert_spec__0_spec__0___redArg(x_1, x_2, x_3);
x_7 = l_Lean_RBNode_setBlack___redArg(x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at___Lean_FVarIdSet_insert_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_RBNode_insert___at___Lean_FVarIdSet_insert_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_FVarIdSet_insert(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = l_Lean_RBNode_insert___at___Lean_FVarIdSet_insert_spec__0___redArg(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_instFVarIdHashSetInhabited() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_beqFVarId____x40_Lean_Expr___hyg_1672____boxed), 2, 0);
x_2 = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730____boxed), 1, 0);
x_3 = l_Std_HashSet_instInhabited(lean_box(0), x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instFVarIdHashSetEmptyCollection() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_beqFVarId____x40_Lean_Expr___hyg_1672____boxed), 2, 0);
x_2 = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730____boxed), 1, 0);
x_3 = l_Std_HashSet_instEmptyCollection(lean_box(0), x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_FVarIdMap_insert___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_insert___at___Lean_FVarIdSet_insert_spec__0___redArg(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_FVarIdMap_insert(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_RBNode_insert___at___Lean_FVarIdSet_insert_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionFVarIdMap(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedFVarIdMap(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
static lean_object* _init_l_Lean_instInhabitedMVarId() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_beqMVarId____x40_Lean_Expr___hyg_1926_(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_name_eq(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_beqMVarId____x40_Lean_Expr___hyg_1926____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Expr_0__Lean_beqMVarId____x40_Lean_Expr___hyg_1926_(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_instBEqMVarId() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_beqMVarId____x40_Lean_Expr___hyg_1926____boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT uint64_t l___private_Lean_Expr_0__Lean_hashMVarId____x40_Lean_Expr___hyg_1984_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint64_t x_3; uint64_t x_4; uint64_t x_5; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_uint64_of_nat(x_2);
x_4 = l_Lean_Name_hash___override(x_1);
x_5 = lean_uint64_mix_hash(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_hashMVarId____x40_Lean_Expr___hyg_1984____boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Expr_0__Lean_hashMVarId____x40_Lean_Expr___hyg_1984_(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instHashableMVarId() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_hashMVarId____x40_Lean_Expr___hyg_1984____boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_reprMVarId___redArg____x40_Lean_Expr___hyg_2016_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_2 = lean_mk_string_unchecked("{ ", 2, 2);
x_3 = lean_box(0);
x_4 = lean_mk_string_unchecked("name", 4, 4);
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
x_10 = lean_unsigned_to_nat(8u);
x_11 = lean_nat_to_int(x_10);
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Lean_Name_reprPrec(x_1, x_12);
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
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_reprMVarId____x40_Lean_Expr___hyg_2016_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Expr_0__Lean_reprMVarId___redArg____x40_Lean_Expr___hyg_2016_(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_reprMVarId____x40_Lean_Expr___hyg_2016____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Expr_0__Lean_reprMVarId____x40_Lean_Expr___hyg_2016_(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instReprMVarId() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_reprMVarId____x40_Lean_Expr___hyg_2016____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_instReprMVarId__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_instReprFVarId___lam__0___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_instMVarIdSetInhabited() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_instMVarIdSetEmptyCollection() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_alloc_closure((void*)(l_Lean_instFVarIdSetEmptyCollection___lam__0___boxed), 2, 0);
x_2 = l_Lean_instEmptyCollectionRBTree(lean_box(0), x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_MVarIdSet_insert_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_1);
x_6 = lean_unbox(x_4);
lean_ctor_set_uint8(x_5, sizeof(void*)*4, x_6);
return x_5;
}
else
{
uint8_t x_7; 
x_7 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_ctor_get(x_1, 2);
x_12 = lean_ctor_get(x_1, 3);
x_13 = l_Lean_Name_quickCmp(x_2, x_10);
switch (x_13) {
case 0:
{
lean_object* x_14; 
x_14 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_MVarIdSet_insert_spec__0_spec__0___redArg(x_9, x_2, x_3);
lean_ctor_set(x_1, 0, x_14);
return x_1;
}
case 1:
{
lean_dec(x_11);
lean_dec(x_10);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
return x_1;
}
default: 
{
lean_object* x_15; 
x_15 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_MVarIdSet_insert_spec__0_spec__0___redArg(x_12, x_2, x_3);
lean_ctor_set(x_1, 3, x_15);
return x_1;
}
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_ctor_get(x_1, 0);
x_17 = lean_ctor_get(x_1, 1);
x_18 = lean_ctor_get(x_1, 2);
x_19 = lean_ctor_get(x_1, 3);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_1);
x_20 = l_Lean_Name_quickCmp(x_2, x_17);
switch (x_20) {
case 0:
{
lean_object* x_21; lean_object* x_22; 
x_21 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_MVarIdSet_insert_spec__0_spec__0___redArg(x_16, x_2, x_3);
x_22 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_17);
lean_ctor_set(x_22, 2, x_18);
lean_ctor_set(x_22, 3, x_19);
lean_ctor_set_uint8(x_22, sizeof(void*)*4, x_7);
return x_22;
}
case 1:
{
lean_object* x_23; 
lean_dec(x_18);
lean_dec(x_17);
x_23 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_23, 0, x_16);
lean_ctor_set(x_23, 1, x_2);
lean_ctor_set(x_23, 2, x_3);
lean_ctor_set(x_23, 3, x_19);
lean_ctor_set_uint8(x_23, sizeof(void*)*4, x_7);
return x_23;
}
default: 
{
lean_object* x_24; lean_object* x_25; 
x_24 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_MVarIdSet_insert_spec__0_spec__0___redArg(x_19, x_2, x_3);
x_25 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_25, 0, x_16);
lean_ctor_set(x_25, 1, x_17);
lean_ctor_set(x_25, 2, x_18);
lean_ctor_set(x_25, 3, x_24);
lean_ctor_set_uint8(x_25, sizeof(void*)*4, x_7);
return x_25;
}
}
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_26 = lean_ctor_get(x_1, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_1, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_1, 2);
lean_inc(x_28);
x_29 = lean_ctor_get(x_1, 3);
lean_inc(x_29);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 x_30 = x_1;
} else {
 lean_dec_ref(x_1);
 x_30 = lean_box(0);
}
x_31 = l_Lean_Name_quickCmp(x_2, x_27);
switch (x_31) {
case 0:
{
lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_32 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_MVarIdSet_insert_spec__0_spec__0___redArg(x_26, x_2, x_3);
x_33 = lean_ctor_get_uint8(x_32, sizeof(void*)*4);
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_32, 2);
lean_inc(x_36);
x_37 = lean_ctor_get(x_32, 3);
lean_inc(x_37);
if (x_33 == 0)
{
if (lean_obj_tag(x_34) == 0)
{
if (lean_obj_tag(x_37) == 0)
{
uint8_t x_52; 
lean_dec(x_30);
x_52 = !lean_is_exclusive(x_32);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_53 = lean_ctor_get(x_32, 3);
lean_dec(x_53);
x_54 = lean_ctor_get(x_32, 2);
lean_dec(x_54);
x_55 = lean_ctor_get(x_32, 1);
lean_dec(x_55);
x_56 = lean_ctor_get(x_32, 0);
lean_dec(x_56);
lean_ctor_set(x_32, 0, x_37);
x_57 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_57, 0, x_32);
lean_ctor_set(x_57, 1, x_27);
lean_ctor_set(x_57, 2, x_28);
lean_ctor_set(x_57, 3, x_29);
lean_ctor_set_uint8(x_57, sizeof(void*)*4, x_7);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_32);
x_58 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_58, 0, x_37);
lean_ctor_set(x_58, 1, x_35);
lean_ctor_set(x_58, 2, x_36);
lean_ctor_set(x_58, 3, x_37);
lean_ctor_set_uint8(x_58, sizeof(void*)*4, x_33);
x_59 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_27);
lean_ctor_set(x_59, 2, x_28);
lean_ctor_set(x_59, 3, x_29);
lean_ctor_set_uint8(x_59, sizeof(void*)*4, x_7);
return x_59;
}
}
else
{
uint8_t x_60; 
x_60 = lean_ctor_get_uint8(x_37, sizeof(void*)*4);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_32);
x_61 = lean_ctor_get(x_37, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_37, 1);
lean_inc(x_62);
x_63 = lean_ctor_get(x_37, 2);
lean_inc(x_63);
x_64 = lean_ctor_get(x_37, 3);
lean_inc(x_64);
lean_dec(x_37);
x_38 = x_34;
x_39 = x_35;
x_40 = x_36;
x_41 = x_61;
x_42 = x_62;
x_43 = x_63;
x_44 = x_64;
x_45 = x_27;
x_46 = x_28;
x_47 = x_29;
goto block_51;
}
else
{
uint8_t x_65; 
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_30);
x_65 = !lean_is_exclusive(x_37);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_37, 3);
lean_dec(x_66);
x_67 = lean_ctor_get(x_37, 2);
lean_dec(x_67);
x_68 = lean_ctor_get(x_37, 1);
lean_dec(x_68);
x_69 = lean_ctor_get(x_37, 0);
lean_dec(x_69);
lean_ctor_set(x_37, 3, x_29);
lean_ctor_set(x_37, 2, x_28);
lean_ctor_set(x_37, 1, x_27);
lean_ctor_set(x_37, 0, x_32);
lean_ctor_set_uint8(x_37, sizeof(void*)*4, x_7);
return x_37;
}
else
{
lean_object* x_70; 
lean_dec(x_37);
x_70 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_70, 0, x_32);
lean_ctor_set(x_70, 1, x_27);
lean_ctor_set(x_70, 2, x_28);
lean_ctor_set(x_70, 3, x_29);
lean_ctor_set_uint8(x_70, sizeof(void*)*4, x_7);
return x_70;
}
}
}
}
else
{
uint8_t x_71; 
x_71 = lean_ctor_get_uint8(x_34, sizeof(void*)*4);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_32);
x_72 = lean_ctor_get(x_34, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_34, 1);
lean_inc(x_73);
x_74 = lean_ctor_get(x_34, 2);
lean_inc(x_74);
x_75 = lean_ctor_get(x_34, 3);
lean_inc(x_75);
lean_dec(x_34);
x_38 = x_72;
x_39 = x_73;
x_40 = x_74;
x_41 = x_75;
x_42 = x_35;
x_43 = x_36;
x_44 = x_37;
x_45 = x_27;
x_46 = x_28;
x_47 = x_29;
goto block_51;
}
else
{
if (lean_obj_tag(x_37) == 0)
{
uint8_t x_76; 
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_30);
x_76 = !lean_is_exclusive(x_34);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_77 = lean_ctor_get(x_34, 3);
lean_dec(x_77);
x_78 = lean_ctor_get(x_34, 2);
lean_dec(x_78);
x_79 = lean_ctor_get(x_34, 1);
lean_dec(x_79);
x_80 = lean_ctor_get(x_34, 0);
lean_dec(x_80);
lean_ctor_set(x_34, 3, x_29);
lean_ctor_set(x_34, 2, x_28);
lean_ctor_set(x_34, 1, x_27);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set_uint8(x_34, sizeof(void*)*4, x_7);
return x_34;
}
else
{
lean_object* x_81; 
lean_dec(x_34);
x_81 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_81, 0, x_32);
lean_ctor_set(x_81, 1, x_27);
lean_ctor_set(x_81, 2, x_28);
lean_ctor_set(x_81, 3, x_29);
lean_ctor_set_uint8(x_81, sizeof(void*)*4, x_7);
return x_81;
}
}
else
{
uint8_t x_82; 
x_82 = !lean_is_exclusive(x_32);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_83 = lean_ctor_get(x_32, 3);
lean_dec(x_83);
x_84 = lean_ctor_get(x_32, 2);
lean_dec(x_84);
x_85 = lean_ctor_get(x_32, 1);
lean_dec(x_85);
x_86 = lean_ctor_get(x_32, 0);
lean_dec(x_86);
x_87 = lean_ctor_get_uint8(x_37, sizeof(void*)*4);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_free_object(x_32);
x_88 = lean_ctor_get(x_37, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_37, 1);
lean_inc(x_89);
x_90 = lean_ctor_get(x_37, 2);
lean_inc(x_90);
x_91 = lean_ctor_get(x_37, 3);
lean_inc(x_91);
lean_dec(x_37);
x_38 = x_34;
x_39 = x_35;
x_40 = x_36;
x_41 = x_88;
x_42 = x_89;
x_43 = x_90;
x_44 = x_91;
x_45 = x_27;
x_46 = x_28;
x_47 = x_29;
goto block_51;
}
else
{
uint8_t x_92; 
lean_dec(x_30);
x_92 = !lean_is_exclusive(x_34);
if (x_92 == 0)
{
lean_object* x_93; 
lean_ctor_set_uint8(x_34, sizeof(void*)*4, x_87);
x_93 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_93, 0, x_32);
lean_ctor_set(x_93, 1, x_27);
lean_ctor_set(x_93, 2, x_28);
lean_ctor_set(x_93, 3, x_29);
lean_ctor_set_uint8(x_93, sizeof(void*)*4, x_7);
return x_93;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_94 = lean_ctor_get(x_34, 0);
x_95 = lean_ctor_get(x_34, 1);
x_96 = lean_ctor_get(x_34, 2);
x_97 = lean_ctor_get(x_34, 3);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_34);
x_98 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_98, 0, x_94);
lean_ctor_set(x_98, 1, x_95);
lean_ctor_set(x_98, 2, x_96);
lean_ctor_set(x_98, 3, x_97);
lean_ctor_set_uint8(x_98, sizeof(void*)*4, x_87);
lean_ctor_set(x_32, 0, x_98);
x_99 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_99, 0, x_32);
lean_ctor_set(x_99, 1, x_27);
lean_ctor_set(x_99, 2, x_28);
lean_ctor_set(x_99, 3, x_29);
lean_ctor_set_uint8(x_99, sizeof(void*)*4, x_7);
return x_99;
}
}
}
else
{
uint8_t x_100; 
lean_dec(x_32);
x_100 = lean_ctor_get_uint8(x_37, sizeof(void*)*4);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_101 = lean_ctor_get(x_37, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_37, 1);
lean_inc(x_102);
x_103 = lean_ctor_get(x_37, 2);
lean_inc(x_103);
x_104 = lean_ctor_get(x_37, 3);
lean_inc(x_104);
lean_dec(x_37);
x_38 = x_34;
x_39 = x_35;
x_40 = x_36;
x_41 = x_101;
x_42 = x_102;
x_43 = x_103;
x_44 = x_104;
x_45 = x_27;
x_46 = x_28;
x_47 = x_29;
goto block_51;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_30);
x_105 = lean_ctor_get(x_34, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_34, 1);
lean_inc(x_106);
x_107 = lean_ctor_get(x_34, 2);
lean_inc(x_107);
x_108 = lean_ctor_get(x_34, 3);
lean_inc(x_108);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 lean_ctor_release(x_34, 2);
 lean_ctor_release(x_34, 3);
 x_109 = x_34;
} else {
 lean_dec_ref(x_34);
 x_109 = lean_box(0);
}
if (lean_is_scalar(x_109)) {
 x_110 = lean_alloc_ctor(1, 4, 1);
} else {
 x_110 = x_109;
}
lean_ctor_set(x_110, 0, x_105);
lean_ctor_set(x_110, 1, x_106);
lean_ctor_set(x_110, 2, x_107);
lean_ctor_set(x_110, 3, x_108);
lean_ctor_set_uint8(x_110, sizeof(void*)*4, x_100);
x_111 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_35);
lean_ctor_set(x_111, 2, x_36);
lean_ctor_set(x_111, 3, x_37);
lean_ctor_set_uint8(x_111, sizeof(void*)*4, x_33);
x_112 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_27);
lean_ctor_set(x_112, 2, x_28);
lean_ctor_set(x_112, 3, x_29);
lean_ctor_set_uint8(x_112, sizeof(void*)*4, x_7);
return x_112;
}
}
}
}
}
}
else
{
lean_object* x_113; 
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_30);
x_113 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_113, 0, x_32);
lean_ctor_set(x_113, 1, x_27);
lean_ctor_set(x_113, 2, x_28);
lean_ctor_set(x_113, 3, x_29);
lean_ctor_set_uint8(x_113, sizeof(void*)*4, x_7);
return x_113;
}
block_51:
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
if (lean_is_scalar(x_30)) {
 x_48 = lean_alloc_ctor(1, 4, 1);
} else {
 x_48 = x_30;
}
lean_ctor_set(x_48, 0, x_38);
lean_ctor_set(x_48, 1, x_39);
lean_ctor_set(x_48, 2, x_40);
lean_ctor_set(x_48, 3, x_41);
lean_ctor_set_uint8(x_48, sizeof(void*)*4, x_7);
x_49 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_49, 0, x_44);
lean_ctor_set(x_49, 1, x_45);
lean_ctor_set(x_49, 2, x_46);
lean_ctor_set(x_49, 3, x_47);
lean_ctor_set_uint8(x_49, sizeof(void*)*4, x_7);
x_50 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_42);
lean_ctor_set(x_50, 2, x_43);
lean_ctor_set(x_50, 3, x_49);
lean_ctor_set_uint8(x_50, sizeof(void*)*4, x_33);
return x_50;
}
}
case 1:
{
lean_object* x_114; 
lean_dec(x_28);
lean_dec(x_27);
if (lean_is_scalar(x_30)) {
 x_114 = lean_alloc_ctor(1, 4, 1);
} else {
 x_114 = x_30;
}
lean_ctor_set(x_114, 0, x_26);
lean_ctor_set(x_114, 1, x_2);
lean_ctor_set(x_114, 2, x_3);
lean_ctor_set(x_114, 3, x_29);
lean_ctor_set_uint8(x_114, sizeof(void*)*4, x_7);
return x_114;
}
default: 
{
lean_object* x_115; uint8_t x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_115 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_MVarIdSet_insert_spec__0_spec__0___redArg(x_29, x_2, x_3);
x_116 = lean_ctor_get_uint8(x_115, sizeof(void*)*4);
x_117 = lean_ctor_get(x_115, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_115, 1);
lean_inc(x_118);
x_119 = lean_ctor_get(x_115, 2);
lean_inc(x_119);
x_120 = lean_ctor_get(x_115, 3);
lean_inc(x_120);
if (x_116 == 0)
{
if (lean_obj_tag(x_117) == 0)
{
if (lean_obj_tag(x_120) == 0)
{
uint8_t x_135; 
lean_dec(x_30);
x_135 = !lean_is_exclusive(x_115);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_136 = lean_ctor_get(x_115, 3);
lean_dec(x_136);
x_137 = lean_ctor_get(x_115, 2);
lean_dec(x_137);
x_138 = lean_ctor_get(x_115, 1);
lean_dec(x_138);
x_139 = lean_ctor_get(x_115, 0);
lean_dec(x_139);
lean_ctor_set(x_115, 0, x_120);
x_140 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_140, 0, x_26);
lean_ctor_set(x_140, 1, x_27);
lean_ctor_set(x_140, 2, x_28);
lean_ctor_set(x_140, 3, x_115);
lean_ctor_set_uint8(x_140, sizeof(void*)*4, x_7);
return x_140;
}
else
{
lean_object* x_141; lean_object* x_142; 
lean_dec(x_115);
x_141 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_141, 0, x_120);
lean_ctor_set(x_141, 1, x_118);
lean_ctor_set(x_141, 2, x_119);
lean_ctor_set(x_141, 3, x_120);
lean_ctor_set_uint8(x_141, sizeof(void*)*4, x_116);
x_142 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_142, 0, x_26);
lean_ctor_set(x_142, 1, x_27);
lean_ctor_set(x_142, 2, x_28);
lean_ctor_set(x_142, 3, x_141);
lean_ctor_set_uint8(x_142, sizeof(void*)*4, x_7);
return x_142;
}
}
else
{
uint8_t x_143; 
x_143 = lean_ctor_get_uint8(x_120, sizeof(void*)*4);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
lean_dec(x_115);
x_144 = lean_ctor_get(x_120, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_120, 1);
lean_inc(x_145);
x_146 = lean_ctor_get(x_120, 2);
lean_inc(x_146);
x_147 = lean_ctor_get(x_120, 3);
lean_inc(x_147);
lean_dec(x_120);
x_121 = x_26;
x_122 = x_27;
x_123 = x_28;
x_124 = x_117;
x_125 = x_118;
x_126 = x_119;
x_127 = x_144;
x_128 = x_145;
x_129 = x_146;
x_130 = x_147;
goto block_134;
}
else
{
uint8_t x_148; 
lean_dec(x_119);
lean_dec(x_118);
lean_dec(x_30);
x_148 = !lean_is_exclusive(x_120);
if (x_148 == 0)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_149 = lean_ctor_get(x_120, 3);
lean_dec(x_149);
x_150 = lean_ctor_get(x_120, 2);
lean_dec(x_150);
x_151 = lean_ctor_get(x_120, 1);
lean_dec(x_151);
x_152 = lean_ctor_get(x_120, 0);
lean_dec(x_152);
lean_ctor_set(x_120, 3, x_115);
lean_ctor_set(x_120, 2, x_28);
lean_ctor_set(x_120, 1, x_27);
lean_ctor_set(x_120, 0, x_26);
lean_ctor_set_uint8(x_120, sizeof(void*)*4, x_7);
return x_120;
}
else
{
lean_object* x_153; 
lean_dec(x_120);
x_153 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_153, 0, x_26);
lean_ctor_set(x_153, 1, x_27);
lean_ctor_set(x_153, 2, x_28);
lean_ctor_set(x_153, 3, x_115);
lean_ctor_set_uint8(x_153, sizeof(void*)*4, x_7);
return x_153;
}
}
}
}
else
{
uint8_t x_154; 
x_154 = lean_ctor_get_uint8(x_117, sizeof(void*)*4);
if (x_154 == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
lean_dec(x_115);
x_155 = lean_ctor_get(x_117, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_117, 1);
lean_inc(x_156);
x_157 = lean_ctor_get(x_117, 2);
lean_inc(x_157);
x_158 = lean_ctor_get(x_117, 3);
lean_inc(x_158);
lean_dec(x_117);
x_121 = x_26;
x_122 = x_27;
x_123 = x_28;
x_124 = x_155;
x_125 = x_156;
x_126 = x_157;
x_127 = x_158;
x_128 = x_118;
x_129 = x_119;
x_130 = x_120;
goto block_134;
}
else
{
if (lean_obj_tag(x_120) == 0)
{
uint8_t x_159; 
lean_dec(x_119);
lean_dec(x_118);
lean_dec(x_30);
x_159 = !lean_is_exclusive(x_117);
if (x_159 == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_160 = lean_ctor_get(x_117, 3);
lean_dec(x_160);
x_161 = lean_ctor_get(x_117, 2);
lean_dec(x_161);
x_162 = lean_ctor_get(x_117, 1);
lean_dec(x_162);
x_163 = lean_ctor_get(x_117, 0);
lean_dec(x_163);
lean_ctor_set(x_117, 3, x_115);
lean_ctor_set(x_117, 2, x_28);
lean_ctor_set(x_117, 1, x_27);
lean_ctor_set(x_117, 0, x_26);
lean_ctor_set_uint8(x_117, sizeof(void*)*4, x_7);
return x_117;
}
else
{
lean_object* x_164; 
lean_dec(x_117);
x_164 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_164, 0, x_26);
lean_ctor_set(x_164, 1, x_27);
lean_ctor_set(x_164, 2, x_28);
lean_ctor_set(x_164, 3, x_115);
lean_ctor_set_uint8(x_164, sizeof(void*)*4, x_7);
return x_164;
}
}
else
{
uint8_t x_165; 
x_165 = !lean_is_exclusive(x_115);
if (x_165 == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; 
x_166 = lean_ctor_get(x_115, 3);
lean_dec(x_166);
x_167 = lean_ctor_get(x_115, 2);
lean_dec(x_167);
x_168 = lean_ctor_get(x_115, 1);
lean_dec(x_168);
x_169 = lean_ctor_get(x_115, 0);
lean_dec(x_169);
x_170 = lean_ctor_get_uint8(x_120, sizeof(void*)*4);
if (x_170 == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
lean_free_object(x_115);
x_171 = lean_ctor_get(x_120, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_120, 1);
lean_inc(x_172);
x_173 = lean_ctor_get(x_120, 2);
lean_inc(x_173);
x_174 = lean_ctor_get(x_120, 3);
lean_inc(x_174);
lean_dec(x_120);
x_121 = x_26;
x_122 = x_27;
x_123 = x_28;
x_124 = x_117;
x_125 = x_118;
x_126 = x_119;
x_127 = x_171;
x_128 = x_172;
x_129 = x_173;
x_130 = x_174;
goto block_134;
}
else
{
uint8_t x_175; 
lean_dec(x_30);
x_175 = !lean_is_exclusive(x_117);
if (x_175 == 0)
{
lean_object* x_176; 
lean_ctor_set_uint8(x_117, sizeof(void*)*4, x_170);
x_176 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_176, 0, x_26);
lean_ctor_set(x_176, 1, x_27);
lean_ctor_set(x_176, 2, x_28);
lean_ctor_set(x_176, 3, x_115);
lean_ctor_set_uint8(x_176, sizeof(void*)*4, x_7);
return x_176;
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_177 = lean_ctor_get(x_117, 0);
x_178 = lean_ctor_get(x_117, 1);
x_179 = lean_ctor_get(x_117, 2);
x_180 = lean_ctor_get(x_117, 3);
lean_inc(x_180);
lean_inc(x_179);
lean_inc(x_178);
lean_inc(x_177);
lean_dec(x_117);
x_181 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_181, 0, x_177);
lean_ctor_set(x_181, 1, x_178);
lean_ctor_set(x_181, 2, x_179);
lean_ctor_set(x_181, 3, x_180);
lean_ctor_set_uint8(x_181, sizeof(void*)*4, x_170);
lean_ctor_set(x_115, 0, x_181);
x_182 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_182, 0, x_26);
lean_ctor_set(x_182, 1, x_27);
lean_ctor_set(x_182, 2, x_28);
lean_ctor_set(x_182, 3, x_115);
lean_ctor_set_uint8(x_182, sizeof(void*)*4, x_7);
return x_182;
}
}
}
else
{
uint8_t x_183; 
lean_dec(x_115);
x_183 = lean_ctor_get_uint8(x_120, sizeof(void*)*4);
if (x_183 == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_184 = lean_ctor_get(x_120, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_120, 1);
lean_inc(x_185);
x_186 = lean_ctor_get(x_120, 2);
lean_inc(x_186);
x_187 = lean_ctor_get(x_120, 3);
lean_inc(x_187);
lean_dec(x_120);
x_121 = x_26;
x_122 = x_27;
x_123 = x_28;
x_124 = x_117;
x_125 = x_118;
x_126 = x_119;
x_127 = x_184;
x_128 = x_185;
x_129 = x_186;
x_130 = x_187;
goto block_134;
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
lean_dec(x_30);
x_188 = lean_ctor_get(x_117, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_117, 1);
lean_inc(x_189);
x_190 = lean_ctor_get(x_117, 2);
lean_inc(x_190);
x_191 = lean_ctor_get(x_117, 3);
lean_inc(x_191);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 lean_ctor_release(x_117, 2);
 lean_ctor_release(x_117, 3);
 x_192 = x_117;
} else {
 lean_dec_ref(x_117);
 x_192 = lean_box(0);
}
if (lean_is_scalar(x_192)) {
 x_193 = lean_alloc_ctor(1, 4, 1);
} else {
 x_193 = x_192;
}
lean_ctor_set(x_193, 0, x_188);
lean_ctor_set(x_193, 1, x_189);
lean_ctor_set(x_193, 2, x_190);
lean_ctor_set(x_193, 3, x_191);
lean_ctor_set_uint8(x_193, sizeof(void*)*4, x_183);
x_194 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_194, 0, x_193);
lean_ctor_set(x_194, 1, x_118);
lean_ctor_set(x_194, 2, x_119);
lean_ctor_set(x_194, 3, x_120);
lean_ctor_set_uint8(x_194, sizeof(void*)*4, x_116);
x_195 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_195, 0, x_26);
lean_ctor_set(x_195, 1, x_27);
lean_ctor_set(x_195, 2, x_28);
lean_ctor_set(x_195, 3, x_194);
lean_ctor_set_uint8(x_195, sizeof(void*)*4, x_7);
return x_195;
}
}
}
}
}
}
else
{
lean_object* x_196; 
lean_dec(x_120);
lean_dec(x_119);
lean_dec(x_118);
lean_dec(x_117);
lean_dec(x_30);
x_196 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_196, 0, x_26);
lean_ctor_set(x_196, 1, x_27);
lean_ctor_set(x_196, 2, x_28);
lean_ctor_set(x_196, 3, x_115);
lean_ctor_set_uint8(x_196, sizeof(void*)*4, x_7);
return x_196;
}
block_134:
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
if (lean_is_scalar(x_30)) {
 x_131 = lean_alloc_ctor(1, 4, 1);
} else {
 x_131 = x_30;
}
lean_ctor_set(x_131, 0, x_121);
lean_ctor_set(x_131, 1, x_122);
lean_ctor_set(x_131, 2, x_123);
lean_ctor_set(x_131, 3, x_124);
lean_ctor_set_uint8(x_131, sizeof(void*)*4, x_7);
x_132 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_132, 0, x_127);
lean_ctor_set(x_132, 1, x_128);
lean_ctor_set(x_132, 2, x_129);
lean_ctor_set(x_132, 3, x_130);
lean_ctor_set_uint8(x_132, sizeof(void*)*4, x_7);
x_133 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_125);
lean_ctor_set(x_133, 2, x_126);
lean_ctor_set(x_133, 3, x_132);
lean_ctor_set_uint8(x_133, sizeof(void*)*4, x_116);
return x_133;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_MVarIdSet_insert_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_MVarIdSet_insert_spec__0_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at___Lean_MVarIdSet_insert_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_RBNode_isRed___redArg(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_MVarIdSet_insert_spec__0_spec__0___redArg(x_1, x_2, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_MVarIdSet_insert_spec__0_spec__0___redArg(x_1, x_2, x_3);
x_7 = l_Lean_RBNode_setBlack___redArg(x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at___Lean_MVarIdSet_insert_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_RBNode_insert___at___Lean_MVarIdSet_insert_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarIdSet_insert(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = l_Lean_RBNode_insert___at___Lean_MVarIdSet_insert_spec__0___redArg(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdSetMVarId(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_alloc_closure((void*)(l_Lean_instFVarIdSetEmptyCollection___lam__0___boxed), 2, 0);
x_3 = l_Lean_RBTree_instForIn(lean_box(0), x_2, lean_box(0));
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarIdMap_insert___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_insert___at___Lean_MVarIdSet_insert_spec__0___redArg(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarIdMap_insert(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_RBNode_insert___at___Lean_MVarIdSet_insert_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionMVarIdMap(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdMapProdMVarId(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l_Lean_instFVarIdSetEmptyCollection___lam__0___boxed), 2, 0);
x_4 = l_Lean_RBMap_instForInProd(lean_box(0), lean_box(0), x_3, lean_box(0));
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMVarIdMap(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_data___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = lean_expr_data(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_casesOn___override___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_apply_1(x_2, x_14);
return x_15;
}
case 1:
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
lean_dec(x_1);
x_17 = lean_apply_1(x_3, x_16);
return x_17;
}
case 2:
{
lean_object* x_18; lean_object* x_19; 
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
lean_dec(x_2);
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
lean_dec(x_1);
x_19 = lean_apply_1(x_4, x_18);
return x_19;
}
case 3:
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
lean_dec(x_1);
x_21 = lean_apply_1(x_5, x_20);
return x_21;
}
case 4:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
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
x_22 = lean_ctor_get(x_1, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_1, 1);
lean_inc(x_23);
lean_dec(x_1);
x_24 = lean_apply_2(x_6, x_22, x_23);
return x_24;
}
case 5:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_25 = lean_ctor_get(x_1, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_1, 1);
lean_inc(x_26);
lean_dec(x_1);
x_27 = lean_apply_2(x_7, x_25, x_26);
return x_27;
}
case 6:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_28 = lean_ctor_get(x_1, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_1, 1);
lean_inc(x_29);
x_30 = lean_ctor_get(x_1, 2);
lean_inc(x_30);
x_31 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec(x_1);
x_32 = lean_box(x_31);
x_33 = lean_apply_4(x_8, x_28, x_29, x_30, x_32);
return x_33;
}
case 7:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; 
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
x_34 = lean_ctor_get(x_1, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_1, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_1, 2);
lean_inc(x_36);
x_37 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec(x_1);
x_38 = lean_box(x_37);
x_39 = lean_apply_4(x_9, x_34, x_35, x_36, x_38);
return x_39;
}
case 8:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_40 = lean_ctor_get(x_1, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_1, 1);
lean_inc(x_41);
x_42 = lean_ctor_get(x_1, 2);
lean_inc(x_42);
x_43 = lean_ctor_get(x_1, 3);
lean_inc(x_43);
x_44 = lean_ctor_get_uint8(x_1, sizeof(void*)*4 + 8);
lean_dec(x_1);
x_45 = lean_box(x_44);
x_46 = lean_apply_5(x_10, x_40, x_41, x_42, x_43, x_45);
return x_46;
}
case 9:
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_47 = lean_ctor_get(x_1, 0);
lean_inc(x_47);
lean_dec(x_1);
x_48 = lean_apply_1(x_11, x_47);
return x_48;
}
case 10:
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_49 = lean_ctor_get(x_1, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_1, 1);
lean_inc(x_50);
lean_dec(x_1);
x_51 = lean_apply_2(x_12, x_49, x_50);
return x_51;
}
default: 
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_52 = lean_ctor_get(x_1, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_1, 1);
lean_inc(x_53);
x_54 = lean_ctor_get(x_1, 2);
lean_inc(x_54);
lean_dec(x_1);
x_55 = lean_apply_3(x_13, x_52, x_53, x_54);
return x_55;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_casesOn___override(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_15; lean_object* x_16; 
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
lean_dec(x_4);
x_15 = lean_ctor_get(x_2, 0);
lean_inc(x_15);
lean_dec(x_2);
x_16 = lean_apply_1(x_3, x_15);
return x_16;
}
case 1:
{
lean_object* x_17; lean_object* x_18; 
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
x_17 = lean_ctor_get(x_2, 0);
lean_inc(x_17);
lean_dec(x_2);
x_18 = lean_apply_1(x_4, x_17);
return x_18;
}
case 2:
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_19 = lean_ctor_get(x_2, 0);
lean_inc(x_19);
lean_dec(x_2);
x_20 = lean_apply_1(x_5, x_19);
return x_20;
}
case 3:
{
lean_object* x_21; lean_object* x_22; 
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
x_21 = lean_ctor_get(x_2, 0);
lean_inc(x_21);
lean_dec(x_2);
x_22 = lean_apply_1(x_6, x_21);
return x_22;
}
case 4:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_23 = lean_ctor_get(x_2, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_2, 1);
lean_inc(x_24);
lean_dec(x_2);
x_25 = lean_apply_2(x_7, x_23, x_24);
return x_25;
}
case 5:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_26 = lean_ctor_get(x_2, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_2, 1);
lean_inc(x_27);
lean_dec(x_2);
x_28 = lean_apply_2(x_8, x_26, x_27);
return x_28;
}
case 6:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_14);
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
x_29 = lean_ctor_get(x_2, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_2, 1);
lean_inc(x_30);
x_31 = lean_ctor_get(x_2, 2);
lean_inc(x_31);
x_32 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_dec(x_2);
x_33 = lean_box(x_32);
x_34 = lean_apply_4(x_9, x_29, x_30, x_31, x_33);
return x_34;
}
case 7:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_35 = lean_ctor_get(x_2, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_2, 1);
lean_inc(x_36);
x_37 = lean_ctor_get(x_2, 2);
lean_inc(x_37);
x_38 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_dec(x_2);
x_39 = lean_box(x_38);
x_40 = lean_apply_4(x_10, x_35, x_36, x_37, x_39);
return x_40;
}
case 8:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_41 = lean_ctor_get(x_2, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_2, 1);
lean_inc(x_42);
x_43 = lean_ctor_get(x_2, 2);
lean_inc(x_43);
x_44 = lean_ctor_get(x_2, 3);
lean_inc(x_44);
x_45 = lean_ctor_get_uint8(x_2, sizeof(void*)*4 + 8);
lean_dec(x_2);
x_46 = lean_box(x_45);
x_47 = lean_apply_5(x_11, x_41, x_42, x_43, x_44, x_46);
return x_47;
}
case 9:
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_48 = lean_ctor_get(x_2, 0);
lean_inc(x_48);
lean_dec(x_2);
x_49 = lean_apply_1(x_12, x_48);
return x_49;
}
case 10:
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_50 = lean_ctor_get(x_2, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_2, 1);
lean_inc(x_51);
lean_dec(x_2);
x_52 = lean_apply_2(x_13, x_50, x_51);
return x_52;
}
default: 
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_53 = lean_ctor_get(x_2, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_2, 1);
lean_inc(x_54);
x_55 = lean_ctor_get(x_2, 2);
lean_inc(x_55);
lean_dec(x_2);
x_56 = lean_apply_3(x_14, x_53, x_54, x_55);
return x_56;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bvar___override(lean_object* x_1) {
_start:
{
lean_object* x_2; uint64_t x_3; uint64_t x_4; uint64_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint32_t x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; uint64_t x_15; lean_object* x_16; 
x_2 = lean_unsigned_to_nat(7u);
x_3 = lean_uint64_of_nat(x_2);
x_4 = lean_uint64_of_nat(x_1);
x_5 = lean_uint64_mix_hash(x_3, x_4);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_add(x_1, x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_uint32_of_nat(x_8);
x_10 = lean_box(0);
x_11 = lean_unbox(x_10);
x_12 = lean_unbox(x_10);
x_13 = lean_unbox(x_10);
x_14 = lean_unbox(x_10);
x_15 = l_Lean_Expr_mkData(x_5, x_7, x_9, x_11, x_12, x_13, x_14);
lean_dec(x_7);
x_16 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set_uint64(x_16, sizeof(void*)*1, x_15);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_fvar___override(lean_object* x_1) {
_start:
{
lean_object* x_2; uint64_t x_3; uint64_t x_4; uint64_t x_5; lean_object* x_6; uint32_t x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; uint64_t x_14; lean_object* x_15; 
x_2 = lean_unsigned_to_nat(13u);
x_3 = lean_uint64_of_nat(x_2);
x_4 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_1);
x_5 = lean_uint64_mix_hash(x_3, x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_uint32_of_nat(x_6);
x_8 = lean_box(1);
x_9 = lean_box(0);
x_10 = lean_unbox(x_8);
x_11 = lean_unbox(x_9);
x_12 = lean_unbox(x_9);
x_13 = lean_unbox(x_9);
x_14 = l_Lean_Expr_mkData(x_5, x_6, x_7, x_10, x_11, x_12, x_13);
x_15 = lean_alloc_ctor(1, 1, 8);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set_uint64(x_15, sizeof(void*)*1, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mvar___override(lean_object* x_1) {
_start:
{
lean_object* x_2; uint64_t x_3; uint64_t x_4; uint64_t x_5; lean_object* x_6; uint32_t x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; uint64_t x_14; lean_object* x_15; 
x_2 = lean_unsigned_to_nat(17u);
x_3 = lean_uint64_of_nat(x_2);
x_4 = l___private_Lean_Expr_0__Lean_hashMVarId____x40_Lean_Expr___hyg_1984_(x_1);
x_5 = lean_uint64_mix_hash(x_3, x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_uint32_of_nat(x_6);
x_8 = lean_box(0);
x_9 = lean_box(1);
x_10 = lean_unbox(x_8);
x_11 = lean_unbox(x_9);
x_12 = lean_unbox(x_8);
x_13 = lean_unbox(x_8);
x_14 = l_Lean_Expr_mkData(x_5, x_6, x_7, x_10, x_11, x_12, x_13);
x_15 = lean_alloc_ctor(2, 1, 8);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set_uint64(x_15, sizeof(void*)*1, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_sort___override(lean_object* x_1) {
_start:
{
lean_object* x_2; uint64_t x_3; uint64_t x_4; uint64_t x_5; lean_object* x_6; uint32_t x_7; lean_object* x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; uint64_t x_13; lean_object* x_14; 
x_2 = lean_unsigned_to_nat(11u);
x_3 = lean_uint64_of_nat(x_2);
x_4 = l_Lean_Level_hash(x_1);
x_5 = lean_uint64_mix_hash(x_3, x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_uint32_of_nat(x_6);
x_8 = lean_box(0);
x_9 = l_Lean_Level_hasMVar(x_1);
x_10 = l_Lean_Level_hasParam(x_1);
x_11 = lean_unbox(x_8);
x_12 = lean_unbox(x_8);
x_13 = l_Lean_Expr_mkData(x_5, x_6, x_7, x_11, x_12, x_9, x_10);
x_14 = lean_alloc_ctor(3, 1, 8);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set_uint64(x_14, sizeof(void*)*1, x_13);
return x_14;
}
}
LEAN_EXPORT uint64_t l_List_foldl___at___Lean_Expr_const___override_spec__0(uint64_t x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; uint64_t x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = l_Lean_Level_hash(x_3);
x_6 = lean_uint64_mix_hash(x_1, x_5);
x_1 = x_6;
x_2 = x_4;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_const___override(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint64_t x_4; uint64_t x_5; lean_object* x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; lean_object* x_11; uint32_t x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; uint64_t x_20; lean_object* x_21; 
x_3 = lean_unsigned_to_nat(5u);
x_4 = lean_uint64_of_nat(x_3);
x_5 = l_Lean_Name_hash___override(x_1);
x_6 = lean_unsigned_to_nat(7u);
x_7 = lean_uint64_of_nat(x_6);
x_8 = l_List_foldl___at___Lean_Expr_const___override_spec__0(x_7, x_2);
x_9 = lean_uint64_mix_hash(x_5, x_8);
x_10 = lean_uint64_mix_hash(x_4, x_9);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_uint32_of_nat(x_11);
x_13 = lean_box(0);
x_14 = lean_alloc_closure((void*)(l_Lean_Level_hasMVar___boxed), 1, 0);
lean_inc(x_2);
x_15 = l_List_any___redArg(x_2, x_14);
x_16 = lean_alloc_closure((void*)(l_Lean_Level_hasParam___boxed), 1, 0);
lean_inc(x_2);
x_17 = l_List_any___redArg(x_2, x_16);
x_18 = lean_unbox(x_13);
x_19 = lean_unbox(x_13);
x_20 = l_Lean_Expr_mkData(x_10, x_11, x_12, x_18, x_19, x_15, x_17);
x_21 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_21, 0, x_1);
lean_ctor_set(x_21, 1, x_2);
lean_ctor_set_uint64(x_21, sizeof(void*)*2, x_20);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_app___override(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; lean_object* x_5; uint8_t x_6; uint32_t x_7; lean_object* x_44; uint8_t x_45; uint16_t x_50; uint8_t x_60; uint16_t x_61; uint8_t x_62; uint16_t x_63; uint8_t x_64; 
x_3 = lean_expr_data(x_1);
x_4 = lean_expr_data(x_2);
x_60 = l_Lean_Expr_Data_approxDepth(x_3);
x_61 = lean_uint8_to_uint16(x_60);
x_62 = l_Lean_Expr_Data_approxDepth(x_4);
x_63 = lean_uint8_to_uint16(x_62);
x_64 = lean_uint16_dec_le(x_61, x_63);
if (x_64 == 0)
{
x_50 = x_61;
goto block_59;
}
else
{
x_50 = x_63;
goto block_59;
}
block_43:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint32_t x_12; uint8_t x_13; 
x_8 = lean_unsigned_to_nat(2u);
x_9 = lean_unsigned_to_nat(20u);
x_10 = lean_nat_pow(x_8, x_9);
x_11 = lean_nat_sub(x_10, x_5);
lean_dec(x_10);
x_12 = lean_uint32_of_nat(x_11);
lean_dec(x_11);
x_13 = lean_uint32_dec_le(x_7, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint64_t x_19; lean_object* x_20; 
x_14 = lean_mk_string_unchecked("Lean.Expr", 9, 9);
x_15 = lean_mk_string_unchecked("Lean.Expr.mkAppData", 19, 19);
x_16 = lean_unsigned_to_nat(193u);
x_17 = lean_mk_string_unchecked("assertion violation: (looseBVarRange ≤ (Nat.pow 2 20 - 1).toUInt32)\n  ", 72, 70);
x_18 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_14, x_15, x_16, x_8, x_17);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
x_19 = l_panic___at___Lean_Expr_mkData_spec__0(x_18);
x_20 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_2);
lean_ctor_set_uint64(x_20, sizeof(void*)*2, x_19);
return x_20;
}
else
{
uint64_t x_21; uint64_t x_22; lean_object* x_23; uint64_t x_24; lean_object* x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; uint32_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; lean_object* x_33; uint64_t x_34; uint64_t x_35; uint64_t x_36; uint64_t x_37; lean_object* x_38; uint64_t x_39; uint64_t x_40; uint64_t x_41; lean_object* x_42; 
x_21 = lean_uint64_mix_hash(x_3, x_4);
x_22 = lean_uint64_lor(x_3, x_4);
x_23 = lean_unsigned_to_nat(15u);
x_24 = lean_uint64_of_nat(x_23);
x_25 = lean_unsigned_to_nat(40u);
x_26 = lean_uint64_of_nat(x_25);
x_27 = lean_uint64_shift_left(x_24, x_26);
x_28 = lean_uint64_land(x_22, x_27);
x_29 = lean_uint64_to_uint32(x_21);
x_30 = lean_uint32_to_uint64(x_29);
x_31 = lean_uint64_lor(x_28, x_30);
x_32 = lean_uint8_to_uint64(x_6);
x_33 = lean_unsigned_to_nat(32u);
x_34 = lean_uint64_of_nat(x_33);
x_35 = lean_uint64_shift_left(x_32, x_34);
x_36 = lean_uint64_lor(x_31, x_35);
x_37 = lean_uint32_to_uint64(x_7);
x_38 = lean_unsigned_to_nat(44u);
x_39 = lean_uint64_of_nat(x_38);
x_40 = lean_uint64_shift_left(x_37, x_39);
x_41 = lean_uint64_lor(x_36, x_40);
x_42 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_42, 0, x_1);
lean_ctor_set(x_42, 1, x_2);
lean_ctor_set_uint64(x_42, sizeof(void*)*2, x_41);
return x_42;
}
}
block_49:
{
uint32_t x_46; uint32_t x_47; uint8_t x_48; 
x_46 = l_Lean_Expr_Data_looseBVarRange(x_3);
x_47 = l_Lean_Expr_Data_looseBVarRange(x_4);
x_48 = lean_uint32_dec_le(x_46, x_47);
if (x_48 == 0)
{
x_5 = x_44;
x_6 = x_45;
x_7 = x_46;
goto block_43;
}
else
{
x_5 = x_44;
x_6 = x_45;
x_7 = x_47;
goto block_43;
}
}
block_59:
{
lean_object* x_51; uint16_t x_52; uint16_t x_53; lean_object* x_54; uint16_t x_55; uint8_t x_56; 
x_51 = lean_unsigned_to_nat(1u);
x_52 = lean_uint16_of_nat(x_51);
x_53 = lean_uint16_add(x_50, x_52);
x_54 = lean_unsigned_to_nat(255u);
x_55 = lean_uint16_of_nat(x_54);
x_56 = lean_uint16_dec_lt(x_55, x_53);
if (x_56 == 0)
{
uint8_t x_57; 
x_57 = lean_uint16_to_uint8(x_53);
x_44 = x_51;
x_45 = x_57;
goto block_49;
}
else
{
uint8_t x_58; 
x_58 = lean_uint8_of_nat(x_54);
x_44 = x_51;
x_45 = x_58;
goto block_49;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lam___override(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
uint64_t x_5; uint8_t x_6; uint8_t x_7; uint32_t x_8; uint8_t x_9; lean_object* x_10; uint8_t x_11; uint64_t x_15; uint8_t x_16; uint32_t x_17; uint64_t x_18; uint64_t x_19; uint32_t x_20; uint8_t x_21; uint8_t x_22; lean_object* x_23; uint8_t x_24; uint64_t x_28; uint8_t x_29; uint32_t x_30; lean_object* x_31; uint8_t x_32; uint64_t x_36; uint32_t x_37; lean_object* x_38; uint8_t x_39; uint64_t x_43; uint32_t x_44; lean_object* x_45; uint32_t x_49; uint8_t x_65; uint32_t x_66; uint8_t x_67; 
x_15 = lean_expr_data(x_2);
x_16 = l_Lean_Expr_Data_approxDepth(x_15);
x_17 = lean_uint8_to_uint32(x_16);
x_18 = lean_expr_data(x_3);
x_65 = l_Lean_Expr_Data_approxDepth(x_18);
x_66 = lean_uint8_to_uint32(x_65);
x_67 = lean_uint32_dec_le(x_17, x_66);
if (x_67 == 0)
{
x_49 = x_17;
goto block_64;
}
else
{
x_49 = x_66;
goto block_64;
}
block_14:
{
uint64_t x_12; lean_object* x_13; 
x_12 = l_Lean_Expr_mkData(x_5, x_10, x_8, x_7, x_9, x_6, x_11);
lean_dec(x_10);
x_13 = lean_alloc_ctor(6, 3, 9);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_2);
lean_ctor_set(x_13, 2, x_3);
lean_ctor_set_uint64(x_13, sizeof(void*)*3, x_12);
lean_ctor_set_uint8(x_13, sizeof(void*)*3 + 8, x_4);
return x_13;
}
block_27:
{
uint8_t x_25; 
x_25 = l_Lean_Expr_Data_hasLevelParam(x_15);
if (x_25 == 0)
{
uint8_t x_26; 
x_26 = l_Lean_Expr_Data_hasLevelParam(x_18);
x_5 = x_19;
x_6 = x_24;
x_7 = x_21;
x_8 = x_20;
x_9 = x_22;
x_10 = x_23;
x_11 = x_26;
goto block_14;
}
else
{
x_5 = x_19;
x_6 = x_24;
x_7 = x_21;
x_8 = x_20;
x_9 = x_22;
x_10 = x_23;
x_11 = x_25;
goto block_14;
}
}
block_35:
{
uint8_t x_33; 
x_33 = l_Lean_Expr_Data_hasLevelMVar(x_15);
if (x_33 == 0)
{
uint8_t x_34; 
x_34 = l_Lean_Expr_Data_hasLevelMVar(x_18);
x_19 = x_28;
x_20 = x_30;
x_21 = x_29;
x_22 = x_32;
x_23 = x_31;
x_24 = x_34;
goto block_27;
}
else
{
x_19 = x_28;
x_20 = x_30;
x_21 = x_29;
x_22 = x_32;
x_23 = x_31;
x_24 = x_33;
goto block_27;
}
}
block_42:
{
uint8_t x_40; 
x_40 = l_Lean_Expr_Data_hasExprMVar(x_15);
if (x_40 == 0)
{
uint8_t x_41; 
x_41 = l_Lean_Expr_Data_hasExprMVar(x_18);
x_28 = x_36;
x_29 = x_39;
x_30 = x_37;
x_31 = x_38;
x_32 = x_41;
goto block_35;
}
else
{
x_28 = x_36;
x_29 = x_39;
x_30 = x_37;
x_31 = x_38;
x_32 = x_40;
goto block_35;
}
}
block_48:
{
uint8_t x_46; 
x_46 = l_Lean_Expr_Data_hasFVar(x_15);
if (x_46 == 0)
{
uint8_t x_47; 
x_47 = l_Lean_Expr_Data_hasFVar(x_18);
x_36 = x_43;
x_37 = x_44;
x_38 = x_45;
x_39 = x_47;
goto block_42;
}
else
{
x_36 = x_43;
x_37 = x_44;
x_38 = x_45;
x_39 = x_46;
goto block_42;
}
}
block_64:
{
lean_object* x_50; uint32_t x_51; uint32_t x_52; uint64_t x_53; uint64_t x_54; uint64_t x_55; uint64_t x_56; uint64_t x_57; uint32_t x_58; lean_object* x_59; uint32_t x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_50 = lean_unsigned_to_nat(1u);
x_51 = lean_uint32_of_nat(x_50);
x_52 = lean_uint32_add(x_49, x_51);
x_53 = lean_uint32_to_uint64(x_52);
x_54 = l_Lean_Expr_Data_hash(x_15);
x_55 = l_Lean_Expr_Data_hash(x_18);
x_56 = lean_uint64_mix_hash(x_54, x_55);
x_57 = lean_uint64_mix_hash(x_53, x_56);
x_58 = l_Lean_Expr_Data_looseBVarRange(x_15);
x_59 = lean_uint32_to_nat(x_58);
x_60 = l_Lean_Expr_Data_looseBVarRange(x_18);
x_61 = lean_uint32_to_nat(x_60);
x_62 = lean_nat_sub(x_61, x_50);
lean_dec(x_61);
x_63 = lean_nat_dec_le(x_59, x_62);
if (x_63 == 0)
{
lean_dec(x_62);
x_43 = x_57;
x_44 = x_52;
x_45 = x_59;
goto block_48;
}
else
{
lean_dec(x_59);
x_43 = x_57;
x_44 = x_52;
x_45 = x_62;
goto block_48;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallE___override(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
uint8_t x_5; uint64_t x_6; lean_object* x_7; uint32_t x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; uint64_t x_15; uint8_t x_16; uint32_t x_17; uint64_t x_18; uint8_t x_19; uint64_t x_20; lean_object* x_21; uint32_t x_22; uint8_t x_23; uint8_t x_24; uint64_t x_28; lean_object* x_29; uint32_t x_30; uint8_t x_31; uint8_t x_32; uint64_t x_36; lean_object* x_37; uint32_t x_38; uint8_t x_39; uint64_t x_43; uint32_t x_44; lean_object* x_45; uint32_t x_49; uint8_t x_65; uint32_t x_66; uint8_t x_67; 
x_15 = lean_expr_data(x_2);
x_16 = l_Lean_Expr_Data_approxDepth(x_15);
x_17 = lean_uint8_to_uint32(x_16);
x_18 = lean_expr_data(x_3);
x_65 = l_Lean_Expr_Data_approxDepth(x_18);
x_66 = lean_uint8_to_uint32(x_65);
x_67 = lean_uint32_dec_le(x_17, x_66);
if (x_67 == 0)
{
x_49 = x_17;
goto block_64;
}
else
{
x_49 = x_66;
goto block_64;
}
block_14:
{
uint64_t x_12; lean_object* x_13; 
x_12 = l_Lean_Expr_mkData(x_6, x_7, x_8, x_10, x_5, x_9, x_11);
lean_dec(x_7);
x_13 = lean_alloc_ctor(7, 3, 9);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_2);
lean_ctor_set(x_13, 2, x_3);
lean_ctor_set_uint64(x_13, sizeof(void*)*3, x_12);
lean_ctor_set_uint8(x_13, sizeof(void*)*3 + 8, x_4);
return x_13;
}
block_27:
{
uint8_t x_25; 
x_25 = l_Lean_Expr_Data_hasLevelParam(x_15);
if (x_25 == 0)
{
uint8_t x_26; 
x_26 = l_Lean_Expr_Data_hasLevelParam(x_18);
x_5 = x_19;
x_6 = x_20;
x_7 = x_21;
x_8 = x_22;
x_9 = x_24;
x_10 = x_23;
x_11 = x_26;
goto block_14;
}
else
{
x_5 = x_19;
x_6 = x_20;
x_7 = x_21;
x_8 = x_22;
x_9 = x_24;
x_10 = x_23;
x_11 = x_25;
goto block_14;
}
}
block_35:
{
uint8_t x_33; 
x_33 = l_Lean_Expr_Data_hasLevelMVar(x_15);
if (x_33 == 0)
{
uint8_t x_34; 
x_34 = l_Lean_Expr_Data_hasLevelMVar(x_18);
x_19 = x_32;
x_20 = x_28;
x_21 = x_29;
x_22 = x_30;
x_23 = x_31;
x_24 = x_34;
goto block_27;
}
else
{
x_19 = x_32;
x_20 = x_28;
x_21 = x_29;
x_22 = x_30;
x_23 = x_31;
x_24 = x_33;
goto block_27;
}
}
block_42:
{
uint8_t x_40; 
x_40 = l_Lean_Expr_Data_hasExprMVar(x_15);
if (x_40 == 0)
{
uint8_t x_41; 
x_41 = l_Lean_Expr_Data_hasExprMVar(x_18);
x_28 = x_36;
x_29 = x_37;
x_30 = x_38;
x_31 = x_39;
x_32 = x_41;
goto block_35;
}
else
{
x_28 = x_36;
x_29 = x_37;
x_30 = x_38;
x_31 = x_39;
x_32 = x_40;
goto block_35;
}
}
block_48:
{
uint8_t x_46; 
x_46 = l_Lean_Expr_Data_hasFVar(x_15);
if (x_46 == 0)
{
uint8_t x_47; 
x_47 = l_Lean_Expr_Data_hasFVar(x_18);
x_36 = x_43;
x_37 = x_45;
x_38 = x_44;
x_39 = x_47;
goto block_42;
}
else
{
x_36 = x_43;
x_37 = x_45;
x_38 = x_44;
x_39 = x_46;
goto block_42;
}
}
block_64:
{
lean_object* x_50; uint32_t x_51; uint32_t x_52; uint64_t x_53; uint64_t x_54; uint64_t x_55; uint64_t x_56; uint64_t x_57; uint32_t x_58; lean_object* x_59; uint32_t x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_50 = lean_unsigned_to_nat(1u);
x_51 = lean_uint32_of_nat(x_50);
x_52 = lean_uint32_add(x_49, x_51);
x_53 = lean_uint32_to_uint64(x_52);
x_54 = l_Lean_Expr_Data_hash(x_15);
x_55 = l_Lean_Expr_Data_hash(x_18);
x_56 = lean_uint64_mix_hash(x_54, x_55);
x_57 = lean_uint64_mix_hash(x_53, x_56);
x_58 = l_Lean_Expr_Data_looseBVarRange(x_15);
x_59 = lean_uint32_to_nat(x_58);
x_60 = l_Lean_Expr_Data_looseBVarRange(x_18);
x_61 = lean_uint32_to_nat(x_60);
x_62 = lean_nat_sub(x_61, x_50);
lean_dec(x_61);
x_63 = lean_nat_dec_le(x_59, x_62);
if (x_63 == 0)
{
lean_dec(x_62);
x_43 = x_57;
x_44 = x_52;
x_45 = x_59;
goto block_48;
}
else
{
lean_dec(x_59);
x_43 = x_57;
x_44 = x_52;
x_45 = x_62;
goto block_48;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letE___override(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5) {
_start:
{
uint8_t x_6; uint8_t x_7; uint64_t x_8; uint8_t x_9; lean_object* x_10; uint32_t x_11; uint8_t x_12; uint8_t x_16; uint8_t x_17; uint64_t x_18; uint8_t x_19; lean_object* x_20; uint64_t x_21; uint32_t x_22; uint8_t x_23; uint64_t x_26; uint8_t x_27; uint32_t x_28; uint64_t x_29; uint8_t x_30; uint8_t x_31; uint64_t x_32; lean_object* x_33; uint64_t x_34; uint32_t x_35; uint8_t x_36; uint8_t x_40; uint8_t x_41; uint64_t x_42; lean_object* x_43; uint64_t x_44; uint32_t x_45; uint8_t x_46; uint8_t x_49; uint64_t x_50; lean_object* x_51; uint64_t x_52; uint32_t x_53; uint8_t x_54; uint8_t x_58; uint64_t x_59; lean_object* x_60; uint64_t x_61; uint32_t x_62; uint8_t x_63; uint64_t x_66; lean_object* x_67; uint64_t x_68; uint32_t x_69; uint8_t x_70; uint64_t x_74; lean_object* x_75; uint64_t x_76; uint32_t x_77; uint8_t x_78; uint64_t x_81; uint64_t x_82; uint32_t x_83; lean_object* x_84; uint64_t x_88; uint64_t x_89; uint32_t x_90; lean_object* x_91; lean_object* x_92; uint64_t x_98; uint32_t x_99; uint32_t x_116; uint8_t x_122; uint32_t x_123; uint8_t x_124; 
x_26 = lean_expr_data(x_2);
x_27 = l_Lean_Expr_Data_approxDepth(x_26);
x_28 = lean_uint8_to_uint32(x_27);
x_29 = lean_expr_data(x_3);
x_122 = l_Lean_Expr_Data_approxDepth(x_29);
x_123 = lean_uint8_to_uint32(x_122);
x_124 = lean_uint32_dec_le(x_28, x_123);
if (x_124 == 0)
{
x_116 = x_28;
goto block_121;
}
else
{
x_116 = x_123;
goto block_121;
}
block_15:
{
uint64_t x_13; lean_object* x_14; 
x_13 = l_Lean_Expr_mkData(x_8, x_10, x_11, x_6, x_7, x_9, x_12);
lean_dec(x_10);
x_14 = lean_alloc_ctor(8, 4, 9);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_2);
lean_ctor_set(x_14, 2, x_3);
lean_ctor_set(x_14, 3, x_4);
lean_ctor_set_uint64(x_14, sizeof(void*)*4, x_13);
lean_ctor_set_uint8(x_14, sizeof(void*)*4 + 8, x_5);
return x_14;
}
block_25:
{
if (x_23 == 0)
{
uint8_t x_24; 
x_24 = l_Lean_Expr_Data_hasLevelParam(x_21);
x_6 = x_16;
x_7 = x_17;
x_8 = x_18;
x_9 = x_19;
x_10 = x_20;
x_11 = x_22;
x_12 = x_24;
goto block_15;
}
else
{
x_6 = x_16;
x_7 = x_17;
x_8 = x_18;
x_9 = x_19;
x_10 = x_20;
x_11 = x_22;
x_12 = x_23;
goto block_15;
}
}
block_39:
{
uint8_t x_37; 
x_37 = l_Lean_Expr_Data_hasLevelParam(x_26);
if (x_37 == 0)
{
uint8_t x_38; 
x_38 = l_Lean_Expr_Data_hasLevelParam(x_29);
x_16 = x_30;
x_17 = x_31;
x_18 = x_32;
x_19 = x_36;
x_20 = x_33;
x_21 = x_34;
x_22 = x_35;
x_23 = x_38;
goto block_25;
}
else
{
x_16 = x_30;
x_17 = x_31;
x_18 = x_32;
x_19 = x_36;
x_20 = x_33;
x_21 = x_34;
x_22 = x_35;
x_23 = x_37;
goto block_25;
}
}
block_48:
{
if (x_46 == 0)
{
uint8_t x_47; 
x_47 = l_Lean_Expr_Data_hasLevelMVar(x_44);
x_30 = x_40;
x_31 = x_41;
x_32 = x_42;
x_33 = x_43;
x_34 = x_44;
x_35 = x_45;
x_36 = x_47;
goto block_39;
}
else
{
x_30 = x_40;
x_31 = x_41;
x_32 = x_42;
x_33 = x_43;
x_34 = x_44;
x_35 = x_45;
x_36 = x_46;
goto block_39;
}
}
block_57:
{
uint8_t x_55; 
x_55 = l_Lean_Expr_Data_hasLevelMVar(x_26);
if (x_55 == 0)
{
uint8_t x_56; 
x_56 = l_Lean_Expr_Data_hasLevelMVar(x_29);
x_40 = x_49;
x_41 = x_54;
x_42 = x_50;
x_43 = x_51;
x_44 = x_52;
x_45 = x_53;
x_46 = x_56;
goto block_48;
}
else
{
x_40 = x_49;
x_41 = x_54;
x_42 = x_50;
x_43 = x_51;
x_44 = x_52;
x_45 = x_53;
x_46 = x_55;
goto block_48;
}
}
block_65:
{
if (x_63 == 0)
{
uint8_t x_64; 
x_64 = l_Lean_Expr_Data_hasExprMVar(x_61);
x_49 = x_58;
x_50 = x_59;
x_51 = x_60;
x_52 = x_61;
x_53 = x_62;
x_54 = x_64;
goto block_57;
}
else
{
x_49 = x_58;
x_50 = x_59;
x_51 = x_60;
x_52 = x_61;
x_53 = x_62;
x_54 = x_63;
goto block_57;
}
}
block_73:
{
uint8_t x_71; 
x_71 = l_Lean_Expr_Data_hasExprMVar(x_26);
if (x_71 == 0)
{
uint8_t x_72; 
x_72 = l_Lean_Expr_Data_hasExprMVar(x_29);
x_58 = x_70;
x_59 = x_66;
x_60 = x_67;
x_61 = x_68;
x_62 = x_69;
x_63 = x_72;
goto block_65;
}
else
{
x_58 = x_70;
x_59 = x_66;
x_60 = x_67;
x_61 = x_68;
x_62 = x_69;
x_63 = x_71;
goto block_65;
}
}
block_80:
{
if (x_78 == 0)
{
uint8_t x_79; 
x_79 = l_Lean_Expr_Data_hasFVar(x_76);
x_66 = x_74;
x_67 = x_75;
x_68 = x_76;
x_69 = x_77;
x_70 = x_79;
goto block_73;
}
else
{
x_66 = x_74;
x_67 = x_75;
x_68 = x_76;
x_69 = x_77;
x_70 = x_78;
goto block_73;
}
}
block_87:
{
uint8_t x_85; 
x_85 = l_Lean_Expr_Data_hasFVar(x_26);
if (x_85 == 0)
{
uint8_t x_86; 
x_86 = l_Lean_Expr_Data_hasFVar(x_29);
x_74 = x_81;
x_75 = x_84;
x_76 = x_82;
x_77 = x_83;
x_78 = x_86;
goto block_80;
}
else
{
x_74 = x_81;
x_75 = x_84;
x_76 = x_82;
x_77 = x_83;
x_78 = x_85;
goto block_80;
}
}
block_97:
{
uint32_t x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_93 = l_Lean_Expr_Data_looseBVarRange(x_89);
x_94 = lean_uint32_to_nat(x_93);
x_95 = lean_nat_sub(x_94, x_91);
lean_dec(x_94);
x_96 = lean_nat_dec_le(x_92, x_95);
if (x_96 == 0)
{
lean_dec(x_95);
x_81 = x_88;
x_82 = x_89;
x_83 = x_90;
x_84 = x_92;
goto block_87;
}
else
{
lean_dec(x_92);
x_81 = x_88;
x_82 = x_89;
x_83 = x_90;
x_84 = x_95;
goto block_87;
}
}
block_115:
{
lean_object* x_100; uint32_t x_101; uint32_t x_102; uint64_t x_103; uint64_t x_104; uint64_t x_105; uint64_t x_106; uint64_t x_107; uint64_t x_108; uint64_t x_109; uint32_t x_110; lean_object* x_111; uint32_t x_112; lean_object* x_113; uint8_t x_114; 
x_100 = lean_unsigned_to_nat(1u);
x_101 = lean_uint32_of_nat(x_100);
x_102 = lean_uint32_add(x_99, x_101);
x_103 = lean_uint32_to_uint64(x_102);
x_104 = l_Lean_Expr_Data_hash(x_26);
x_105 = l_Lean_Expr_Data_hash(x_29);
x_106 = l_Lean_Expr_Data_hash(x_98);
x_107 = lean_uint64_mix_hash(x_105, x_106);
x_108 = lean_uint64_mix_hash(x_104, x_107);
x_109 = lean_uint64_mix_hash(x_103, x_108);
x_110 = l_Lean_Expr_Data_looseBVarRange(x_26);
x_111 = lean_uint32_to_nat(x_110);
x_112 = l_Lean_Expr_Data_looseBVarRange(x_29);
x_113 = lean_uint32_to_nat(x_112);
x_114 = lean_nat_dec_le(x_111, x_113);
if (x_114 == 0)
{
lean_dec(x_113);
x_88 = x_109;
x_89 = x_98;
x_90 = x_102;
x_91 = x_100;
x_92 = x_111;
goto block_97;
}
else
{
lean_dec(x_111);
x_88 = x_109;
x_89 = x_98;
x_90 = x_102;
x_91 = x_100;
x_92 = x_113;
goto block_97;
}
}
block_121:
{
uint64_t x_117; uint8_t x_118; uint32_t x_119; uint8_t x_120; 
x_117 = lean_expr_data(x_4);
x_118 = l_Lean_Expr_Data_approxDepth(x_117);
x_119 = lean_uint8_to_uint32(x_118);
x_120 = lean_uint32_dec_le(x_116, x_119);
if (x_120 == 0)
{
x_98 = x_117;
x_99 = x_116;
goto block_115;
}
else
{
x_98 = x_117;
x_99 = x_119;
goto block_115;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lit___override(lean_object* x_1) {
_start:
{
lean_object* x_2; uint64_t x_3; uint64_t x_4; uint64_t x_5; lean_object* x_6; uint32_t x_7; lean_object* x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; uint64_t x_13; lean_object* x_14; 
x_2 = lean_unsigned_to_nat(3u);
x_3 = lean_uint64_of_nat(x_2);
x_4 = l_Lean_Literal_hash(x_1);
x_5 = lean_uint64_mix_hash(x_3, x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_uint32_of_nat(x_6);
x_8 = lean_box(0);
x_9 = lean_unbox(x_8);
x_10 = lean_unbox(x_8);
x_11 = lean_unbox(x_8);
x_12 = lean_unbox(x_8);
x_13 = l_Lean_Expr_mkData(x_5, x_6, x_7, x_9, x_10, x_11, x_12);
x_14 = lean_alloc_ctor(9, 1, 8);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set_uint64(x_14, sizeof(void*)*1, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mdata___override(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint8_t x_4; uint32_t x_5; lean_object* x_6; uint32_t x_7; uint32_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint32_t x_12; lean_object* x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; uint64_t x_18; lean_object* x_19; 
x_3 = lean_expr_data(x_2);
x_4 = l_Lean_Expr_Data_approxDepth(x_3);
x_5 = lean_uint8_to_uint32(x_4);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_uint32_of_nat(x_6);
x_8 = lean_uint32_add(x_5, x_7);
x_9 = lean_uint32_to_uint64(x_8);
x_10 = l_Lean_Expr_Data_hash(x_3);
x_11 = lean_uint64_mix_hash(x_9, x_10);
x_12 = l_Lean_Expr_Data_looseBVarRange(x_3);
x_13 = lean_uint32_to_nat(x_12);
x_14 = l_Lean_Expr_Data_hasFVar(x_3);
x_15 = l_Lean_Expr_Data_hasExprMVar(x_3);
x_16 = l_Lean_Expr_Data_hasLevelMVar(x_3);
x_17 = l_Lean_Expr_Data_hasLevelParam(x_3);
x_18 = l_Lean_Expr_mkData(x_11, x_13, x_8, x_14, x_15, x_16, x_17);
lean_dec(x_13);
x_19 = lean_alloc_ctor(10, 2, 8);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_2);
lean_ctor_set_uint64(x_19, sizeof(void*)*2, x_18);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_proj___override(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; uint8_t x_5; uint32_t x_6; lean_object* x_7; uint32_t x_8; uint32_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; uint32_t x_17; lean_object* x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; uint64_t x_23; lean_object* x_24; 
x_4 = lean_expr_data(x_3);
x_5 = l_Lean_Expr_Data_approxDepth(x_4);
x_6 = lean_uint8_to_uint32(x_5);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_uint32_of_nat(x_7);
x_9 = lean_uint32_add(x_6, x_8);
x_10 = lean_uint32_to_uint64(x_9);
x_11 = l_Lean_Name_hash___override(x_1);
x_12 = lean_uint64_of_nat(x_2);
x_13 = l_Lean_Expr_Data_hash(x_4);
x_14 = lean_uint64_mix_hash(x_12, x_13);
x_15 = lean_uint64_mix_hash(x_11, x_14);
x_16 = lean_uint64_mix_hash(x_10, x_15);
x_17 = l_Lean_Expr_Data_looseBVarRange(x_4);
x_18 = lean_uint32_to_nat(x_17);
x_19 = l_Lean_Expr_Data_hasFVar(x_4);
x_20 = l_Lean_Expr_Data_hasExprMVar(x_4);
x_21 = l_Lean_Expr_Data_hasLevelMVar(x_4);
x_22 = l_Lean_Expr_Data_hasLevelParam(x_4);
x_23 = l_Lean_Expr_mkData(x_16, x_18, x_9, x_19, x_20, x_21, x_22);
lean_dec(x_18);
x_24 = lean_alloc_ctor(11, 3, 8);
lean_ctor_set(x_24, 0, x_1);
lean_ctor_set(x_24, 1, x_2);
lean_ctor_set(x_24, 2, x_3);
lean_ctor_set_uint64(x_24, sizeof(void*)*3, x_23);
return x_24;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___Lean_Expr_const___override_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; lean_object* x_5; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = l_List_foldl___at___Lean_Expr_const___override_spec__0(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box_uint64(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lam___override___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_4);
lean_dec(x_4);
x_6 = l_Lean_Expr_lam___override(x_1, x_2, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallE___override___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_4);
lean_dec(x_4);
x_6 = l_Lean_Expr_forallE___override(x_1, x_2, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letE___override___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_5);
lean_dec(x_5);
x_7 = l_Lean_Expr_letE___override(x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_repr___at_____private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3026__spec__0___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1017_(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_repr___at_____private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3026__spec__0___redArg(lean_object* x_1) {
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
x_4 = lean_alloc_closure((void*)(l_List_repr___at_____private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3026__spec__0___redArg___lam__0), 1, 0);
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
LEAN_EXPORT lean_object* l_List_repr___at_____private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3026__spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_repr___at_____private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3026__spec__0___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3026_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_13; lean_object* x_14; lean_object* x_28; uint8_t x_29; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_28 = lean_unsigned_to_nat(1024u);
x_29 = lean_nat_dec_le(x_28, x_2);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_unsigned_to_nat(2u);
x_31 = lean_nat_to_int(x_30);
x_14 = x_31;
goto block_27;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_to_int(x_32);
x_14 = x_33;
goto block_27;
}
block_27:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_15 = lean_mk_string_unchecked("Lean.Expr.bvar", 14, 14);
x_16 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_box(1);
x_18 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = l___private_Init_Data_Repr_0__Nat_reprFast(x_13);
x_20 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_22, 0, x_14);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_24, 0, x_22);
x_25 = lean_unbox(x_23);
lean_ctor_set_uint8(x_24, sizeof(void*)*1, x_25);
x_26 = l_Repr_addAppParen(x_24, x_2);
return x_26;
}
}
case 1:
{
lean_object* x_34; lean_object* x_35; lean_object* x_49; uint8_t x_50; 
x_34 = lean_ctor_get(x_1, 0);
lean_inc(x_34);
lean_dec(x_1);
x_49 = lean_unsigned_to_nat(1024u);
x_50 = lean_nat_dec_le(x_49, x_2);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_unsigned_to_nat(2u);
x_52 = lean_nat_to_int(x_51);
x_35 = x_52;
goto block_48;
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_unsigned_to_nat(1u);
x_54 = lean_nat_to_int(x_53);
x_35 = x_54;
goto block_48;
}
block_48:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; 
x_36 = lean_mk_string_unchecked("Lean.Expr.fvar", 14, 14);
x_37 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = lean_box(1);
x_39 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_unsigned_to_nat(1024u);
x_41 = l_Lean_Name_reprPrec(x_34, x_40);
x_42 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_43, 0, x_35);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_45, 0, x_43);
x_46 = lean_unbox(x_44);
lean_ctor_set_uint8(x_45, sizeof(void*)*1, x_46);
x_47 = l_Repr_addAppParen(x_45, x_2);
return x_47;
}
}
case 2:
{
lean_object* x_55; lean_object* x_56; lean_object* x_70; uint8_t x_71; 
x_55 = lean_ctor_get(x_1, 0);
lean_inc(x_55);
lean_dec(x_1);
x_70 = lean_unsigned_to_nat(1024u);
x_71 = lean_nat_dec_le(x_70, x_2);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_unsigned_to_nat(2u);
x_73 = lean_nat_to_int(x_72);
x_56 = x_73;
goto block_69;
}
else
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_unsigned_to_nat(1u);
x_75 = lean_nat_to_int(x_74);
x_56 = x_75;
goto block_69;
}
block_69:
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; 
x_57 = lean_mk_string_unchecked("Lean.Expr.mvar", 14, 14);
x_58 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_58, 0, x_57);
x_59 = lean_box(1);
x_60 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_unsigned_to_nat(1024u);
x_62 = l_Lean_Name_reprPrec(x_55, x_61);
x_63 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_62);
x_64 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_64, 0, x_56);
lean_ctor_set(x_64, 1, x_63);
x_65 = lean_box(0);
x_66 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_66, 0, x_64);
x_67 = lean_unbox(x_65);
lean_ctor_set_uint8(x_66, sizeof(void*)*1, x_67);
x_68 = l_Repr_addAppParen(x_66, x_2);
return x_68;
}
}
case 3:
{
lean_object* x_76; lean_object* x_77; lean_object* x_91; uint8_t x_92; 
x_76 = lean_ctor_get(x_1, 0);
lean_inc(x_76);
lean_dec(x_1);
x_91 = lean_unsigned_to_nat(1024u);
x_92 = lean_nat_dec_le(x_91, x_2);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_unsigned_to_nat(2u);
x_94 = lean_nat_to_int(x_93);
x_77 = x_94;
goto block_90;
}
else
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_unsigned_to_nat(1u);
x_96 = lean_nat_to_int(x_95);
x_77 = x_96;
goto block_90;
}
block_90:
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; lean_object* x_89; 
x_78 = lean_mk_string_unchecked("Lean.Expr.sort", 14, 14);
x_79 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_79, 0, x_78);
x_80 = lean_box(1);
x_81 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
x_82 = lean_unsigned_to_nat(1024u);
x_83 = l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1017_(x_76, x_82);
x_84 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_84, 0, x_81);
lean_ctor_set(x_84, 1, x_83);
x_85 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_85, 0, x_77);
lean_ctor_set(x_85, 1, x_84);
x_86 = lean_box(0);
x_87 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_87, 0, x_85);
x_88 = lean_unbox(x_86);
lean_ctor_set_uint8(x_87, sizeof(void*)*1, x_88);
x_89 = l_Repr_addAppParen(x_87, x_2);
return x_89;
}
}
case 4:
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_116; uint8_t x_117; 
x_97 = lean_ctor_get(x_1, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_1, 1);
lean_inc(x_98);
lean_dec(x_1);
x_116 = lean_unsigned_to_nat(1024u);
x_117 = lean_nat_dec_le(x_116, x_2);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; 
x_118 = lean_unsigned_to_nat(2u);
x_119 = lean_nat_to_int(x_118);
x_99 = x_119;
goto block_115;
}
else
{
lean_object* x_120; lean_object* x_121; 
x_120 = lean_unsigned_to_nat(1u);
x_121 = lean_nat_to_int(x_120);
x_99 = x_121;
goto block_115;
}
block_115:
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; lean_object* x_114; 
x_100 = lean_mk_string_unchecked("Lean.Expr.const", 15, 15);
x_101 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_101, 0, x_100);
x_102 = lean_box(1);
x_103 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
x_104 = lean_unsigned_to_nat(1024u);
x_105 = l_Lean_Name_reprPrec(x_97, x_104);
x_106 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_106, 0, x_103);
lean_ctor_set(x_106, 1, x_105);
x_107 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_102);
x_108 = l_List_repr___at_____private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3026__spec__0___redArg(x_98);
x_109 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
x_110 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_110, 0, x_99);
lean_ctor_set(x_110, 1, x_109);
x_111 = lean_box(0);
x_112 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_112, 0, x_110);
x_113 = lean_unbox(x_111);
lean_ctor_set_uint8(x_112, sizeof(void*)*1, x_113);
x_114 = l_Repr_addAppParen(x_112, x_2);
return x_114;
}
}
case 5:
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_141; 
x_122 = lean_ctor_get(x_1, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_1, 1);
lean_inc(x_123);
lean_dec(x_1);
x_124 = lean_unsigned_to_nat(1024u);
x_141 = lean_nat_dec_le(x_124, x_2);
if (x_141 == 0)
{
lean_object* x_142; lean_object* x_143; 
x_142 = lean_unsigned_to_nat(2u);
x_143 = lean_nat_to_int(x_142);
x_125 = x_143;
goto block_140;
}
else
{
lean_object* x_144; lean_object* x_145; 
x_144 = lean_unsigned_to_nat(1u);
x_145 = lean_nat_to_int(x_144);
x_125 = x_145;
goto block_140;
}
block_140:
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; lean_object* x_139; 
x_126 = lean_mk_string_unchecked("Lean.Expr.app", 13, 13);
x_127 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_127, 0, x_126);
x_128 = lean_box(1);
x_129 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
x_130 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3026_(x_122, x_124);
x_131 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
x_132 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_128);
x_133 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3026_(x_123, x_124);
x_134 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_134, 0, x_132);
lean_ctor_set(x_134, 1, x_133);
x_135 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_135, 0, x_125);
lean_ctor_set(x_135, 1, x_134);
x_136 = lean_box(0);
x_137 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_137, 0, x_135);
x_138 = lean_unbox(x_136);
lean_ctor_set_uint8(x_137, sizeof(void*)*1, x_138);
x_139 = l_Repr_addAppParen(x_137, x_2);
return x_139;
}
}
case 6:
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; lean_object* x_150; lean_object* x_151; uint8_t x_173; 
x_146 = lean_ctor_get(x_1, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_1, 1);
lean_inc(x_147);
x_148 = lean_ctor_get(x_1, 2);
lean_inc(x_148);
x_149 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec(x_1);
x_150 = lean_unsigned_to_nat(1024u);
x_173 = lean_nat_dec_le(x_150, x_2);
if (x_173 == 0)
{
lean_object* x_174; lean_object* x_175; 
x_174 = lean_unsigned_to_nat(2u);
x_175 = lean_nat_to_int(x_174);
x_151 = x_175;
goto block_172;
}
else
{
lean_object* x_176; lean_object* x_177; 
x_176 = lean_unsigned_to_nat(1u);
x_177 = lean_nat_to_int(x_176);
x_151 = x_177;
goto block_172;
}
block_172:
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; lean_object* x_171; 
x_152 = lean_mk_string_unchecked("Lean.Expr.lam", 13, 13);
x_153 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_153, 0, x_152);
x_154 = lean_box(1);
x_155 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set(x_155, 1, x_154);
x_156 = l_Lean_Name_reprPrec(x_146, x_150);
x_157 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_157, 0, x_155);
lean_ctor_set(x_157, 1, x_156);
x_158 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_154);
x_159 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3026_(x_147, x_150);
x_160 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_160, 0, x_158);
lean_ctor_set(x_160, 1, x_159);
x_161 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_161, 1, x_154);
x_162 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3026_(x_148, x_150);
x_163 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_163, 0, x_161);
lean_ctor_set(x_163, 1, x_162);
x_164 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_164, 1, x_154);
x_165 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_424_(x_149, x_150);
x_166 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_166, 0, x_164);
lean_ctor_set(x_166, 1, x_165);
x_167 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_167, 0, x_151);
lean_ctor_set(x_167, 1, x_166);
x_168 = lean_box(0);
x_169 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_169, 0, x_167);
x_170 = lean_unbox(x_168);
lean_ctor_set_uint8(x_169, sizeof(void*)*1, x_170);
x_171 = l_Repr_addAppParen(x_169, x_2);
return x_171;
}
}
case 7:
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; uint8_t x_181; lean_object* x_182; lean_object* x_183; uint8_t x_205; 
x_178 = lean_ctor_get(x_1, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_1, 1);
lean_inc(x_179);
x_180 = lean_ctor_get(x_1, 2);
lean_inc(x_180);
x_181 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec(x_1);
x_182 = lean_unsigned_to_nat(1024u);
x_205 = lean_nat_dec_le(x_182, x_2);
if (x_205 == 0)
{
lean_object* x_206; lean_object* x_207; 
x_206 = lean_unsigned_to_nat(2u);
x_207 = lean_nat_to_int(x_206);
x_183 = x_207;
goto block_204;
}
else
{
lean_object* x_208; lean_object* x_209; 
x_208 = lean_unsigned_to_nat(1u);
x_209 = lean_nat_to_int(x_208);
x_183 = x_209;
goto block_204;
}
block_204:
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; uint8_t x_202; lean_object* x_203; 
x_184 = lean_mk_string_unchecked("Lean.Expr.forallE", 17, 17);
x_185 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_185, 0, x_184);
x_186 = lean_box(1);
x_187 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_187, 0, x_185);
lean_ctor_set(x_187, 1, x_186);
x_188 = l_Lean_Name_reprPrec(x_178, x_182);
x_189 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_189, 0, x_187);
lean_ctor_set(x_189, 1, x_188);
x_190 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_190, 0, x_189);
lean_ctor_set(x_190, 1, x_186);
x_191 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3026_(x_179, x_182);
x_192 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_192, 0, x_190);
lean_ctor_set(x_192, 1, x_191);
x_193 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set(x_193, 1, x_186);
x_194 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3026_(x_180, x_182);
x_195 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_195, 0, x_193);
lean_ctor_set(x_195, 1, x_194);
x_196 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set(x_196, 1, x_186);
x_197 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_424_(x_181, x_182);
x_198 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_198, 0, x_196);
lean_ctor_set(x_198, 1, x_197);
x_199 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_199, 0, x_183);
lean_ctor_set(x_199, 1, x_198);
x_200 = lean_box(0);
x_201 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_201, 0, x_199);
x_202 = lean_unbox(x_200);
lean_ctor_set_uint8(x_201, sizeof(void*)*1, x_202);
x_203 = l_Repr_addAppParen(x_201, x_2);
return x_203;
}
}
case 8:
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; uint8_t x_214; lean_object* x_215; lean_object* x_216; uint8_t x_238; 
x_210 = lean_ctor_get(x_1, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_1, 1);
lean_inc(x_211);
x_212 = lean_ctor_get(x_1, 2);
lean_inc(x_212);
x_213 = lean_ctor_get(x_1, 3);
lean_inc(x_213);
x_214 = lean_ctor_get_uint8(x_1, sizeof(void*)*4 + 8);
lean_dec(x_1);
x_215 = lean_unsigned_to_nat(1024u);
x_238 = lean_nat_dec_le(x_215, x_2);
if (x_238 == 0)
{
lean_object* x_239; lean_object* x_240; 
x_239 = lean_unsigned_to_nat(2u);
x_240 = lean_nat_to_int(x_239);
x_216 = x_240;
goto block_237;
}
else
{
lean_object* x_241; lean_object* x_242; 
x_241 = lean_unsigned_to_nat(1u);
x_242 = lean_nat_to_int(x_241);
x_216 = x_242;
goto block_237;
}
block_237:
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_217 = lean_mk_string_unchecked("Lean.Expr.letE", 14, 14);
x_218 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_218, 0, x_217);
x_219 = lean_box(1);
x_220 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_220, 0, x_218);
lean_ctor_set(x_220, 1, x_219);
x_221 = l_Lean_Name_reprPrec(x_210, x_215);
x_222 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_222, 0, x_220);
lean_ctor_set(x_222, 1, x_221);
x_223 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_223, 0, x_222);
lean_ctor_set(x_223, 1, x_219);
x_224 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3026_(x_211, x_215);
x_225 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_225, 0, x_223);
lean_ctor_set(x_225, 1, x_224);
x_226 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_226, 0, x_225);
lean_ctor_set(x_226, 1, x_219);
x_227 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3026_(x_212, x_215);
x_228 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_228, 0, x_226);
lean_ctor_set(x_228, 1, x_227);
x_229 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_229, 0, x_228);
lean_ctor_set(x_229, 1, x_219);
x_230 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3026_(x_213, x_215);
x_231 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_231, 0, x_229);
lean_ctor_set(x_231, 1, x_230);
x_232 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_232, 0, x_231);
lean_ctor_set(x_232, 1, x_219);
if (x_214 == 0)
{
lean_object* x_233; lean_object* x_234; 
x_233 = lean_mk_string_unchecked("false", 5, 5);
x_234 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_234, 0, x_233);
x_3 = x_232;
x_4 = x_216;
x_5 = x_234;
goto block_12;
}
else
{
lean_object* x_235; lean_object* x_236; 
x_235 = lean_mk_string_unchecked("true", 4, 4);
x_236 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_236, 0, x_235);
x_3 = x_232;
x_4 = x_216;
x_5 = x_236;
goto block_12;
}
}
}
case 9:
{
lean_object* x_243; lean_object* x_244; lean_object* x_258; uint8_t x_259; 
x_243 = lean_ctor_get(x_1, 0);
lean_inc(x_243);
lean_dec(x_1);
x_258 = lean_unsigned_to_nat(1024u);
x_259 = lean_nat_dec_le(x_258, x_2);
if (x_259 == 0)
{
lean_object* x_260; lean_object* x_261; 
x_260 = lean_unsigned_to_nat(2u);
x_261 = lean_nat_to_int(x_260);
x_244 = x_261;
goto block_257;
}
else
{
lean_object* x_262; lean_object* x_263; 
x_262 = lean_unsigned_to_nat(1u);
x_263 = lean_nat_to_int(x_262);
x_244 = x_263;
goto block_257;
}
block_257:
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; uint8_t x_255; lean_object* x_256; 
x_245 = lean_mk_string_unchecked("Lean.Expr.lit", 13, 13);
x_246 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_246, 0, x_245);
x_247 = lean_box(1);
x_248 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_248, 0, x_246);
lean_ctor_set(x_248, 1, x_247);
x_249 = lean_unsigned_to_nat(1024u);
x_250 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_113_(x_243, x_249);
x_251 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_251, 0, x_248);
lean_ctor_set(x_251, 1, x_250);
x_252 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_252, 0, x_244);
lean_ctor_set(x_252, 1, x_251);
x_253 = lean_box(0);
x_254 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_254, 0, x_252);
x_255 = lean_unbox(x_253);
lean_ctor_set_uint8(x_254, sizeof(void*)*1, x_255);
x_256 = l_Repr_addAppParen(x_254, x_2);
return x_256;
}
}
case 10:
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; uint8_t x_283; 
x_264 = lean_ctor_get(x_1, 0);
lean_inc(x_264);
x_265 = lean_ctor_get(x_1, 1);
lean_inc(x_265);
lean_dec(x_1);
x_266 = lean_unsigned_to_nat(1024u);
x_283 = lean_nat_dec_le(x_266, x_2);
if (x_283 == 0)
{
lean_object* x_284; lean_object* x_285; 
x_284 = lean_unsigned_to_nat(2u);
x_285 = lean_nat_to_int(x_284);
x_267 = x_285;
goto block_282;
}
else
{
lean_object* x_286; lean_object* x_287; 
x_286 = lean_unsigned_to_nat(1u);
x_287 = lean_nat_to_int(x_286);
x_267 = x_287;
goto block_282;
}
block_282:
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; uint8_t x_280; lean_object* x_281; 
x_268 = lean_mk_string_unchecked("Lean.Expr.mdata", 15, 15);
x_269 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_269, 0, x_268);
x_270 = lean_box(1);
x_271 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_271, 0, x_269);
lean_ctor_set(x_271, 1, x_270);
x_272 = l___private_Lean_Data_KVMap_0__Lean_reprKVMap___redArg____x40_Lean_Data_KVMap___hyg_920_(x_264);
x_273 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_273, 0, x_271);
lean_ctor_set(x_273, 1, x_272);
x_274 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_274, 0, x_273);
lean_ctor_set(x_274, 1, x_270);
x_275 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3026_(x_265, x_266);
x_276 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_276, 0, x_274);
lean_ctor_set(x_276, 1, x_275);
x_277 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_277, 0, x_267);
lean_ctor_set(x_277, 1, x_276);
x_278 = lean_box(0);
x_279 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_279, 0, x_277);
x_280 = lean_unbox(x_278);
lean_ctor_set_uint8(x_279, sizeof(void*)*1, x_280);
x_281 = l_Repr_addAppParen(x_279, x_2);
return x_281;
}
}
default: 
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; uint8_t x_312; 
x_288 = lean_ctor_get(x_1, 0);
lean_inc(x_288);
x_289 = lean_ctor_get(x_1, 1);
lean_inc(x_289);
x_290 = lean_ctor_get(x_1, 2);
lean_inc(x_290);
lean_dec(x_1);
x_291 = lean_unsigned_to_nat(1024u);
x_312 = lean_nat_dec_le(x_291, x_2);
if (x_312 == 0)
{
lean_object* x_313; lean_object* x_314; 
x_313 = lean_unsigned_to_nat(2u);
x_314 = lean_nat_to_int(x_313);
x_292 = x_314;
goto block_311;
}
else
{
lean_object* x_315; lean_object* x_316; 
x_315 = lean_unsigned_to_nat(1u);
x_316 = lean_nat_to_int(x_315);
x_292 = x_316;
goto block_311;
}
block_311:
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; uint8_t x_309; lean_object* x_310; 
x_293 = lean_mk_string_unchecked("Lean.Expr.proj", 14, 14);
x_294 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_294, 0, x_293);
x_295 = lean_box(1);
x_296 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_296, 0, x_294);
lean_ctor_set(x_296, 1, x_295);
x_297 = l_Lean_Name_reprPrec(x_288, x_291);
x_298 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_298, 0, x_296);
lean_ctor_set(x_298, 1, x_297);
x_299 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_299, 0, x_298);
lean_ctor_set(x_299, 1, x_295);
x_300 = l___private_Init_Data_Repr_0__Nat_reprFast(x_289);
x_301 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_301, 0, x_300);
x_302 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_302, 0, x_299);
lean_ctor_set(x_302, 1, x_301);
x_303 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_303, 0, x_302);
lean_ctor_set(x_303, 1, x_295);
x_304 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3026_(x_290, x_291);
x_305 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_305, 0, x_303);
lean_ctor_set(x_305, 1, x_304);
x_306 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_306, 0, x_292);
lean_ctor_set(x_306, 1, x_305);
x_307 = lean_box(0);
x_308 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_308, 0, x_306);
x_309 = lean_unbox(x_307);
lean_ctor_set_uint8(x_308, sizeof(void*)*1, x_309);
x_310 = l_Repr_addAppParen(x_308, x_2);
return x_310;
}
}
}
block_12:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_6 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_9, 0, x_7);
x_10 = lean_unbox(x_8);
lean_ctor_set_uint8(x_9, sizeof(void*)*1, x_10);
x_11 = l_Repr_addAppParen(x_9, x_2);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_List_repr___at_____private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3026__spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_repr___at_____private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3026__spec__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3026____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3026_(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instReprExpr() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3026____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_instInhabitedExpr() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_mk_string_unchecked("_inhabitedExprDummy", 19, 19);
x_2 = l_Lean_Name_mkStr1(x_1);
x_3 = lean_box(0);
x_4 = l_Lean_Expr_const___override(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ctorName(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = lean_mk_string_unchecked("bvar", 4, 4);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_mk_string_unchecked("fvar", 4, 4);
return x_3;
}
case 2:
{
lean_object* x_4; 
x_4 = lean_mk_string_unchecked("mvar", 4, 4);
return x_4;
}
case 3:
{
lean_object* x_5; 
x_5 = lean_mk_string_unchecked("sort", 4, 4);
return x_5;
}
case 4:
{
lean_object* x_6; 
x_6 = lean_mk_string_unchecked("const", 5, 5);
return x_6;
}
case 5:
{
lean_object* x_7; 
x_7 = lean_mk_string_unchecked("app", 3, 3);
return x_7;
}
case 6:
{
lean_object* x_8; 
x_8 = lean_mk_string_unchecked("lam", 3, 3);
return x_8;
}
case 7:
{
lean_object* x_9; 
x_9 = lean_mk_string_unchecked("forallE", 7, 7);
return x_9;
}
case 8:
{
lean_object* x_10; 
x_10 = lean_mk_string_unchecked("letE", 4, 4);
return x_10;
}
case 9:
{
lean_object* x_11; 
x_11 = lean_mk_string_unchecked("lit", 3, 3);
return x_11;
}
case 10:
{
lean_object* x_12; 
x_12 = lean_mk_string_unchecked("mdata", 5, 5);
return x_12;
}
default: 
{
lean_object* x_13; 
x_13 = lean_mk_string_unchecked("proj", 4, 4);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ctorName___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_ctorName(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint64_t l_Lean_Expr_hash(lean_object* x_1) {
_start:
{
uint64_t x_2; uint64_t x_3; 
x_2 = lean_expr_data(x_1);
x_3 = l_Lean_Expr_Data_hash(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hash___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_hash(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Expr_instHashable() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Expr_hash___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasFVar(lean_object* x_1) {
_start:
{
uint64_t x_2; uint8_t x_3; 
x_2 = lean_expr_data(x_1);
x_3 = l_Lean_Expr_Data_hasFVar(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasFVar___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_hasFVar(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasExprMVar(lean_object* x_1) {
_start:
{
uint64_t x_2; uint8_t x_3; 
x_2 = lean_expr_data(x_1);
x_3 = l_Lean_Expr_Data_hasExprMVar(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasExprMVar___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_hasExprMVar(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasLevelMVar(lean_object* x_1) {
_start:
{
uint64_t x_2; uint8_t x_3; 
x_2 = lean_expr_data(x_1);
x_3 = l_Lean_Expr_Data_hasLevelMVar(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasLevelMVar___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_hasLevelMVar(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasMVar(lean_object* x_1) {
_start:
{
uint64_t x_2; uint8_t x_3; 
x_2 = lean_expr_data(x_1);
x_3 = l_Lean_Expr_Data_hasExprMVar(x_2);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = l_Lean_Expr_Data_hasLevelMVar(x_2);
return x_4;
}
else
{
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasMVar___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_hasMVar(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasLevelParam(lean_object* x_1) {
_start:
{
uint64_t x_2; uint8_t x_3; 
x_2 = lean_expr_data(x_1);
x_3 = l_Lean_Expr_Data_hasLevelParam(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasLevelParam___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_hasLevelParam(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint32_t l_Lean_Expr_approxDepth(lean_object* x_1) {
_start:
{
uint64_t x_2; uint8_t x_3; uint32_t x_4; 
x_2 = lean_expr_data(x_1);
x_3 = l_Lean_Expr_Data_approxDepth(x_2);
x_4 = lean_uint8_to_uint32(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_approxDepth___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_approxDepth(x_1);
lean_dec(x_1);
x_3 = lean_box_uint32(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_looseBVarRange(lean_object* x_1) {
_start:
{
uint64_t x_2; uint32_t x_3; lean_object* x_4; 
x_2 = lean_expr_data(x_1);
x_3 = l_Lean_Expr_Data_looseBVarRange(x_2);
x_4 = lean_uint32_to_nat(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_looseBVarRange___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_looseBVarRange(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_binderInfo(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 6:
{
uint8_t x_2; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
return x_2;
}
case 7:
{
uint8_t x_3; 
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
return x_3;
}
default: 
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_box(0);
x_5 = lean_unbox(x_4);
return x_5;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_binderInfo___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_binderInfo(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint64_t lean_expr_hash(lean_object* x_1) {
_start:
{
uint64_t x_2; 
x_2 = l_Lean_Expr_hash(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hashEx___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = lean_expr_hash(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t lean_expr_has_fvar(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_Expr_hasFVar(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasFVarEx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_expr_has_fvar(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t lean_expr_has_expr_mvar(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_Expr_hasExprMVar(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasExprMVarEx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_expr_has_expr_mvar(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t lean_expr_has_level_mvar(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_Expr_hasLevelMVar(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasLevelMVarEx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_expr_has_level_mvar(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t lean_expr_has_mvar(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_Expr_hasMVar(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasMVarEx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_expr_has_mvar(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t lean_expr_has_level_param(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_Expr_hasLevelParam(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasLevelParamEx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_expr_has_level_param(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint32_t lean_expr_loose_bvar_range(lean_object* x_1) {
_start:
{
uint64_t x_2; uint32_t x_3; 
x_2 = lean_expr_data(x_1);
lean_dec(x_1);
x_3 = l_Lean_Expr_Data_looseBVarRange(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_looseBVarRangeEx___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = lean_expr_loose_bvar_range(x_1);
x_3 = lean_box_uint32(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t lean_expr_binder_info(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_Expr_binderInfo(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_binderInfoEx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_expr_binder_info(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_mkConst(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Expr_const___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Literal_type(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_mk_string_unchecked("Nat", 3, 3);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_box(0);
x_5 = l_Lean_Expr_const___override(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_mk_string_unchecked("String", 6, 6);
x_7 = l_Lean_Name_mkStr1(x_6);
x_8 = lean_box(0);
x_9 = l_Lean_Expr_const___override(x_7, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Literal_type___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Literal_type(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lean_lit_type(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Literal_type(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_mkBVar(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_bvar___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_mkSort(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFVar(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_fvar___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMVar(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_mvar___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMData(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Expr_mdata___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_mkProj(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Expr_proj___override(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Expr_app___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLambda(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Expr_lam___override(x_1, x_3, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLambda___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_mkLambda(x_1, x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_mkForall(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Expr_forallE___override(x_1, x_3, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_mkForall___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_mkForall(x_1, x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_mkSimpleThunkType(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_box(0);
x_3 = lean_box(0);
x_4 = lean_mk_string_unchecked("Unit", 4, 4);
x_5 = l_Lean_Name_mkStr1(x_4);
x_6 = lean_box(0);
x_7 = l_Lean_Expr_const___override(x_5, x_6);
x_8 = lean_unbox(x_3);
x_9 = l_Lean_Expr_forallE___override(x_2, x_7, x_1, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_mkSimpleThunk(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_2 = lean_mk_string_unchecked("_", 1, 1);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_box(0);
x_5 = lean_mk_string_unchecked("Unit", 4, 4);
x_6 = l_Lean_Name_mkStr1(x_5);
x_7 = lean_box(0);
x_8 = l_Lean_Expr_const___override(x_6, x_7);
x_9 = lean_unbox(x_4);
x_10 = l_Lean_Expr_lam___override(x_3, x_8, x_1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLet(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Expr_letE___override(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLet___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_5);
lean_dec(x_5);
x_7 = l_Lean_mkLet(x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppB(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Expr_app___override(x_1, x_2);
x_5 = l_Lean_Expr_app___override(x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_mkAppB(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_mkAppB(x_1, x_2, x_3);
x_6 = l_Lean_Expr_app___override(x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_mkAppB(x_1, x_2, x_3);
x_7 = l_Lean_mkAppB(x_6, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_mkApp4(x_1, x_2, x_3, x_4, x_5);
x_8 = l_Lean_Expr_app___override(x_7, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_mkApp4(x_1, x_2, x_3, x_4, x_5);
x_9 = l_Lean_mkAppB(x_8, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Lean_mkApp4(x_1, x_2, x_3, x_4, x_5);
x_10 = l_Lean_mkApp3(x_9, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_mkApp4(x_1, x_2, x_3, x_4, x_5);
x_11 = l_Lean_mkApp4(x_10, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Lean_mkApp4(x_1, x_2, x_3, x_4, x_5);
x_12 = l_Lean_mkApp5(x_11, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Lean_mkApp4(x_1, x_2, x_3, x_4, x_5);
x_13 = l_Lean_mkApp6(x_12, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLit(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_lit___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_mkRawNatLit(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
x_3 = l_Lean_Expr_lit___override(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatLit(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_2 = l_Lean_mkRawNatLit(x_1);
x_3 = lean_mk_string_unchecked("OfNat", 5, 5);
x_4 = lean_mk_string_unchecked("ofNat", 5, 5);
x_5 = l_Lean_Name_mkStr2(x_3, x_4);
x_6 = lean_box(0);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
x_9 = l_Lean_Expr_const___override(x_5, x_8);
x_10 = lean_mk_string_unchecked("Nat", 3, 3);
x_11 = l_Lean_Name_mkStr1(x_10);
x_12 = l_Lean_Expr_const___override(x_11, x_7);
x_13 = lean_mk_string_unchecked("instOfNatNat", 12, 12);
x_14 = l_Lean_Name_mkStr1(x_13);
x_15 = l_Lean_Expr_const___override(x_14, x_7);
lean_inc(x_2);
x_16 = l_Lean_Expr_app___override(x_15, x_2);
x_17 = l_Lean_mkApp3(x_9, x_12, x_2, x_16);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_mkStrLit(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
x_3 = l_Lean_Expr_lit___override(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_bvar(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_bvar___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_fvar(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_fvar___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_mvar(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_mvar___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_sort(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_const(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Expr_const___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_app(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Expr_app___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_lambda(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Expr_lam___override(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLambdaEx___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_4);
lean_dec(x_4);
x_6 = lean_expr_mk_lambda(x_1, x_2, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_forall(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Expr_forallE___override(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_mkForallEx___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_4);
lean_dec(x_4);
x_6 = lean_expr_mk_forall(x_1, x_2, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_let(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_box(0);
x_6 = lean_unbox(x_5);
x_7 = l_Lean_Expr_letE___override(x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_lit(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_lit___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_mdata(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Expr_mdata___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_proj(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Expr_proj___override(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_mkAppN_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Lean_Expr_app___override(x_4, x_6);
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
LEAN_EXPORT lean_object* l_Lean_mkAppN(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
lean_dec(x_4);
return x_1;
}
else
{
uint8_t x_6; 
x_6 = lean_nat_dec_le(x_4, x_4);
if (x_6 == 0)
{
lean_dec(x_4);
return x_1;
}
else
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_usize_of_nat(x_3);
x_8 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_9 = l_Array_foldlMUnsafe_fold___at___Lean_mkAppN_spec__0(x_2, x_7, x_8, x_1);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_mkAppN_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Lean_mkAppN_spec__0(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppN___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkAppN(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_mkAppRangeAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_lt(x_3, x_1);
if (x_5 == 0)
{
lean_dec(x_3);
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_add(x_3, x_6);
x_8 = l_Lean_instInhabitedExpr;
x_9 = lean_array_get(x_8, x_2, x_3);
lean_dec(x_3);
x_10 = l_Lean_Expr_app___override(x_4, x_9);
x_3 = x_7;
x_4 = x_10;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_mkAppRangeAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Expr_0__Lean_mkAppRangeAux(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppRange(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Expr_0__Lean_mkAppRangeAux(x_3, x_4, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppRange___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_mkAppRange(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_mkAppRev_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
x_10 = l_Lean_Expr_app___override(x_4, x_9);
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
LEAN_EXPORT lean_object* l_Lean_mkAppRev(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
lean_dec(x_3);
return x_1;
}
else
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_7 = lean_usize_of_nat(x_4);
x_8 = l_Array_foldrMUnsafe_fold___at___Lean_mkAppRev_spec__0(x_2, x_6, x_7, x_1);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_mkAppRev_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldrMUnsafe_fold___at___Lean_mkAppRev_spec__0(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppRev___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkAppRev(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_dbgToString___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_expr_dbg_to_string(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_quickLt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_expr_quick_lt(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_expr_lt(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_quickComp(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_expr_quick_lt(x_1, x_2);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = lean_expr_quick_lt(x_2, x_1);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_box(1);
x_6 = lean_unbox(x_5);
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_box(2);
x_8 = lean_unbox(x_7);
return x_8;
}
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_box(0);
x_10 = lean_unbox(x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_quickComp___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Expr_quickComp(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_eqv___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_expr_eqv(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Expr_instBEq() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Expr_eqv___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_equal___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_expr_equal(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isSort(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 3)
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(1);
x_3 = lean_unbox(x_2);
return x_3;
}
else
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_box(0);
x_5 = lean_unbox(x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isSort___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_isSort(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isType(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 3)
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_box(0);
switch (lean_obj_tag(x_2)) {
case 0:
{
uint8_t x_4; 
x_4 = lean_unbox(x_3);
return x_4;
}
case 1:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_box(1);
x_6 = lean_unbox(x_5);
return x_6;
}
default: 
{
uint8_t x_7; 
x_7 = lean_unbox(x_3);
return x_7;
}
}
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
LEAN_EXPORT lean_object* l_Lean_Expr_isType___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_isType(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isType0(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 3)
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_box(0);
switch (lean_obj_tag(x_2)) {
case 0:
{
uint8_t x_4; 
x_4 = lean_unbox(x_3);
return x_4;
}
case 1:
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_2, 0);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_box(1);
x_7 = lean_unbox(x_6);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = lean_unbox(x_3);
return x_8;
}
}
default: 
{
uint8_t x_9; 
x_9 = lean_unbox(x_3);
return x_9;
}
}
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
LEAN_EXPORT lean_object* l_Lean_Expr_isType0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_isType0(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isProp(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 3)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
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
lean_object* x_7; uint8_t x_8; 
x_7 = lean_box(0);
x_8 = lean_unbox(x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isProp___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_isProp(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isBVar(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(1);
x_3 = lean_unbox(x_2);
return x_3;
}
else
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_box(0);
x_5 = lean_unbox(x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isBVar___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_isBVar(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isMVar(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 2)
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(1);
x_3 = lean_unbox(x_2);
return x_3;
}
else
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_box(0);
x_5 = lean_unbox(x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isMVar___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_isMVar(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isFVar(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(1);
x_3 = lean_unbox(x_2);
return x_3;
}
else
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_box(0);
x_5 = lean_unbox(x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isFVar___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_isFVar(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isApp(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(1);
x_3 = lean_unbox(x_2);
return x_3;
}
else
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_box(0);
x_5 = lean_unbox(x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isApp___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_isApp(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isProj(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 11)
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(1);
x_3 = lean_unbox(x_2);
return x_3;
}
else
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_box(0);
x_5 = lean_unbox(x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isProj___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_isProj(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isConst(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 4)
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(1);
x_3 = lean_unbox(x_2);
return x_3;
}
else
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_box(0);
x_5 = lean_unbox(x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isConst___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_isConst(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isConstOf(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 4)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_name_eq(x_3, x_2);
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
}
LEAN_EXPORT lean_object* l_Lean_Expr_isConstOf___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Expr_isConstOf(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isFVarOf(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_name_eq(x_3, x_2);
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
}
LEAN_EXPORT lean_object* l_Lean_Expr_isFVarOf___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Expr_isFVarOf(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isForall(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 7)
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(1);
x_3 = lean_unbox(x_2);
return x_3;
}
else
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_box(0);
x_5 = lean_unbox(x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isForall___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_isForall(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isLambda(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 6)
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(1);
x_3 = lean_unbox(x_2);
return x_3;
}
else
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_box(0);
x_5 = lean_unbox(x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isLambda___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_isLambda(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isBinding(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 6:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(1);
x_3 = lean_unbox(x_2);
return x_3;
}
case 7:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_box(1);
x_5 = lean_unbox(x_4);
return x_5;
}
default: 
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_box(0);
x_7 = lean_unbox(x_6);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isBinding___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_isBinding(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isLet(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 8)
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(1);
x_3 = lean_unbox(x_2);
return x_3;
}
else
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_box(0);
x_5 = lean_unbox(x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isLet___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_isLet(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isMData(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 10)
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(1);
x_3 = lean_unbox(x_2);
return x_3;
}
else
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_box(0);
x_5 = lean_unbox(x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isMData___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_isMData(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isLit(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 9)
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(1);
x_3 = lean_unbox(x_2);
return x_3;
}
else
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_box(0);
x_5 = lean_unbox(x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isLit___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_isLit(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Expr_appFn_x21_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_instInhabitedExpr;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn_x21(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_mk_string_unchecked("Lean.Expr", 9, 9);
x_4 = lean_mk_string_unchecked("Lean.Expr.appFn!", 16, 16);
x_5 = lean_unsigned_to_nat(903u);
x_6 = lean_unsigned_to_nat(15u);
x_7 = lean_mk_string_unchecked("application expected", 20, 20);
x_8 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_9 = l_panic___at___Lean_Expr_appFn_x21_spec__0(x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn_x21___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_appFn_x21(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg_x21(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_mk_string_unchecked("Lean.Expr", 9, 9);
x_4 = lean_mk_string_unchecked("Lean.Expr.appArg!", 17, 17);
x_5 = lean_unsigned_to_nat(907u);
x_6 = lean_unsigned_to_nat(15u);
x_7 = lean_mk_string_unchecked("application expected", 20, 20);
x_8 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_9 = l_panic___at___Lean_Expr_appFn_x21_spec__0(x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg_x21___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_appArg_x21(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn_x21_x27(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 5:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
case 10:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 1);
x_1 = x_3;
goto _start;
}
default: 
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_mk_string_unchecked("Lean.Expr", 9, 9);
x_6 = lean_mk_string_unchecked("Lean.Expr.appFn!'", 17, 17);
x_7 = lean_unsigned_to_nat(912u);
x_8 = lean_unsigned_to_nat(17u);
x_9 = lean_mk_string_unchecked("application expected", 20, 20);
x_10 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
x_11 = l_panic___at___Lean_Expr_appFn_x21_spec__0(x_10);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn_x21_x27___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_appFn_x21_x27(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg_x21_x27(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 5:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
return x_2;
}
case 10:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 1);
x_1 = x_3;
goto _start;
}
default: 
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_mk_string_unchecked("Lean.Expr", 9, 9);
x_6 = lean_mk_string_unchecked("Lean.Expr.appArg!'", 18, 18);
x_7 = lean_unsigned_to_nat(917u);
x_8 = lean_unsigned_to_nat(17u);
x_9 = lean_mk_string_unchecked("application expected", 20, 20);
x_10 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
x_11 = l_panic___at___Lean_Expr_appFn_x21_spec__0(x_10);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg_x21_x27___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_appArg_x21_x27(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_appArg___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Expr_appArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_appFn___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Expr_appFn(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_sortLevel_x21(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 3)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_mk_string_unchecked("Lean.Expr", 9, 9);
x_4 = lean_mk_string_unchecked("Lean.Expr.sortLevel!", 20, 20);
x_5 = lean_unsigned_to_nat(929u);
x_6 = lean_unsigned_to_nat(14u);
x_7 = lean_mk_string_unchecked("sort expected", 13, 13);
x_8 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_9 = l_panic___at___Lean_Level_normalize_spec__0(x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_sortLevel_x21___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_sortLevel_x21(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Expr_litValue_x21_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_instInhabitedLiteral;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_litValue_x21(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 9)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_mk_string_unchecked("Lean.Expr", 9, 9);
x_4 = lean_mk_string_unchecked("Lean.Expr.litValue!", 19, 19);
x_5 = lean_unsigned_to_nat(933u);
x_6 = lean_unsigned_to_nat(13u);
x_7 = lean_mk_string_unchecked("literal expected", 16, 16);
x_8 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_9 = l_panic___at___Lean_Expr_litValue_x21_spec__0(x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_litValue_x21___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_litValue_x21(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isRawNatLit(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 9)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
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
lean_object* x_7; uint8_t x_8; 
x_7 = lean_box(0);
x_8 = lean_unbox(x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isRawNatLit___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_isRawNatLit(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_rawNatLit_x3f(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 9)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_ctor_set_tag(x_2, 1);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
else
{
lean_object* x_6; 
lean_dec(x_2);
x_6 = lean_box(0);
return x_6;
}
}
else
{
lean_object* x_7; 
lean_dec(x_1);
x_7 = lean_box(0);
return x_7;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isStringLit(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 9)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
if (lean_obj_tag(x_2) == 0)
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
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_box(0);
x_8 = lean_unbox(x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isStringLit___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_isStringLit(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isCharLit(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
if (lean_obj_tag(x_2) == 4)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_mk_string_unchecked("Char", 4, 4);
x_6 = lean_mk_string_unchecked("ofNat", 5, 5);
x_7 = l_Lean_Name_mkStr2(x_5, x_6);
x_8 = lean_name_eq(x_4, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
return x_8;
}
else
{
uint8_t x_9; 
x_9 = l_Lean_Expr_isRawNatLit(x_3);
return x_9;
}
}
else
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_box(0);
x_11 = lean_unbox(x_10);
return x_11;
}
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_box(0);
x_13 = lean_unbox(x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isCharLit___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_isCharLit(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constName_x21(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 4)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_mk_string_unchecked("Lean.Expr", 9, 9);
x_4 = lean_mk_string_unchecked("Lean.Expr.constName!", 20, 20);
x_5 = lean_unsigned_to_nat(953u);
x_6 = lean_unsigned_to_nat(17u);
x_7 = lean_mk_string_unchecked("constant expected", 17, 17);
x_8 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_9 = l_panic___at_____private_Init_Prelude_0__Lean_assembleParts_spec__0(x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constName_x21___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_constName_x21(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constName_x3f(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 4)
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constName_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_constName_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constName(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_constName_x3f(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constName___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_constName(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Expr_constLevels_x21_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_instInhabitedList(lean_box(0));
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constLevels_x21(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 4)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_mk_string_unchecked("Lean.Expr", 9, 9);
x_4 = lean_mk_string_unchecked("Lean.Expr.constLevels!", 22, 22);
x_5 = lean_unsigned_to_nat(965u);
x_6 = lean_unsigned_to_nat(18u);
x_7 = lean_mk_string_unchecked("constant expected", 17, 17);
x_8 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_9 = l_panic___at___Lean_Expr_constLevels_x21_spec__0(x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constLevels_x21___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_constLevels_x21(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bvarIdx_x21(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_mk_string_unchecked("Lean.Expr", 9, 9);
x_4 = lean_mk_string_unchecked("Lean.Expr.bvarIdx!", 18, 18);
x_5 = lean_unsigned_to_nat(969u);
x_6 = lean_unsigned_to_nat(16u);
x_7 = lean_mk_string_unchecked("bvar expected", 13, 13);
x_8 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_9 = l_panic___at___String_toNat_x21_spec__0(x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bvarIdx_x21___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_bvarIdx_x21(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Expr_fvarId_x21_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_fvarId_x21(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_mk_string_unchecked("Lean.Expr", 9, 9);
x_4 = lean_mk_string_unchecked("Lean.Expr.fvarId!", 17, 17);
x_5 = lean_unsigned_to_nat(973u);
x_6 = lean_unsigned_to_nat(14u);
x_7 = lean_mk_string_unchecked("fvar expected", 13, 13);
x_8 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_9 = l_panic___at___Lean_Expr_fvarId_x21_spec__0(x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_fvarId_x21___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_fvarId_x21(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_fvarId_x3f(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_fvarId_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_fvarId_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Expr_mvarId_x21_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mvarId_x21(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 2)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_mk_string_unchecked("Lean.Expr", 9, 9);
x_4 = lean_mk_string_unchecked("Lean.Expr.mvarId!", 17, 17);
x_5 = lean_unsigned_to_nat(981u);
x_6 = lean_unsigned_to_nat(14u);
x_7 = lean_mk_string_unchecked("mvar expected", 13, 13);
x_8 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_9 = l_panic___at___Lean_Expr_mvarId_x21_spec__0(x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mvarId_x21___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_mvarId_x21(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingName_x21(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 6:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
case 7:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
return x_3;
}
default: 
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_mk_string_unchecked("Lean.Expr", 9, 9);
x_5 = lean_mk_string_unchecked("Lean.Expr.bindingName!", 22, 22);
x_6 = lean_unsigned_to_nat(986u);
x_7 = lean_unsigned_to_nat(23u);
x_8 = lean_mk_string_unchecked("binding expected", 16, 16);
x_9 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
x_10 = l_panic___at_____private_Init_Prelude_0__Lean_assembleParts_spec__0(x_9);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingName_x21___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_bindingName_x21(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingDomain_x21(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 6:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
return x_2;
}
case 7:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
return x_3;
}
default: 
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_mk_string_unchecked("Lean.Expr", 9, 9);
x_5 = lean_mk_string_unchecked("Lean.Expr.bindingDomain!", 24, 24);
x_6 = lean_unsigned_to_nat(991u);
x_7 = lean_unsigned_to_nat(23u);
x_8 = lean_mk_string_unchecked("binding expected", 16, 16);
x_9 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
x_10 = l_panic___at___Lean_Expr_appFn_x21_spec__0(x_9);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingDomain_x21___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_bindingDomain_x21(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingBody_x21(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 6:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 2);
lean_inc(x_2);
return x_2;
}
case 7:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 2);
lean_inc(x_3);
return x_3;
}
default: 
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_mk_string_unchecked("Lean.Expr", 9, 9);
x_5 = lean_mk_string_unchecked("Lean.Expr.bindingBody!", 22, 22);
x_6 = lean_unsigned_to_nat(996u);
x_7 = lean_unsigned_to_nat(23u);
x_8 = lean_mk_string_unchecked("binding expected", 16, 16);
x_9 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
x_10 = l_panic___at___Lean_Expr_appFn_x21_spec__0(x_9);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingBody_x21___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_bindingBody_x21(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_panic___at___Lean_Expr_bindingInfo_x21_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_box(0);
x_3 = lean_panic_fn(x_2, x_1);
x_4 = lean_unbox(x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_bindingInfo_x21(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 6:
{
uint8_t x_2; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
return x_2;
}
case 7:
{
uint8_t x_3; 
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
return x_3;
}
default: 
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_4 = lean_mk_string_unchecked("Lean.Expr", 9, 9);
x_5 = lean_mk_string_unchecked("Lean.Expr.bindingInfo!", 22, 22);
x_6 = lean_unsigned_to_nat(1001u);
x_7 = lean_unsigned_to_nat(24u);
x_8 = lean_mk_string_unchecked("binding expected", 16, 16);
x_9 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
x_10 = l_panic___at___Lean_Expr_bindingInfo_x21_spec__0(x_9);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Expr_bindingInfo_x21_spec__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_panic___at___Lean_Expr_bindingInfo_x21_spec__0(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingInfo_x21___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_bindingInfo_x21(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallName___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallName(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallName___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_forallName___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallName___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Expr_forallName(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallDomain___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallDomain(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallDomain___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_forallDomain___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallDomain___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Expr_forallDomain(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallBody___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 2);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallBody(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 2);
lean_inc(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallBody___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_forallBody___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallBody___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Expr_forallBody(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_forallInfo___redArg(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_forallInfo(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallInfo___redArg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_forallInfo___redArg(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallInfo___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Expr_forallInfo(x_1, x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letName_x21(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 8)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_mk_string_unchecked("Lean.Expr", 9, 9);
x_4 = lean_mk_string_unchecked("Lean.Expr.letName!", 18, 18);
x_5 = lean_unsigned_to_nat(1017u);
x_6 = lean_unsigned_to_nat(17u);
x_7 = lean_mk_string_unchecked("let expression expected", 23, 23);
x_8 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_9 = l_panic___at_____private_Init_Prelude_0__Lean_assembleParts_spec__0(x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letName_x21___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_letName_x21(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letType_x21(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 8)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_mk_string_unchecked("Lean.Expr", 9, 9);
x_4 = lean_mk_string_unchecked("Lean.Expr.letType!", 18, 18);
x_5 = lean_unsigned_to_nat(1021u);
x_6 = lean_unsigned_to_nat(19u);
x_7 = lean_mk_string_unchecked("let expression expected", 23, 23);
x_8 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_9 = l_panic___at___Lean_Expr_appFn_x21_spec__0(x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letType_x21___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_letType_x21(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letValue_x21(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 8)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 2);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_mk_string_unchecked("Lean.Expr", 9, 9);
x_4 = lean_mk_string_unchecked("Lean.Expr.letValue!", 19, 19);
x_5 = lean_unsigned_to_nat(1025u);
x_6 = lean_unsigned_to_nat(21u);
x_7 = lean_mk_string_unchecked("let expression expected", 23, 23);
x_8 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_9 = l_panic___at___Lean_Expr_appFn_x21_spec__0(x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letValue_x21___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_letValue_x21(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letBody_x21(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 8)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 3);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_mk_string_unchecked("Lean.Expr", 9, 9);
x_4 = lean_mk_string_unchecked("Lean.Expr.letBody!", 18, 18);
x_5 = lean_unsigned_to_nat(1029u);
x_6 = lean_unsigned_to_nat(23u);
x_7 = lean_mk_string_unchecked("let expression expected", 23, 23);
x_8 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_9 = l_panic___at___Lean_Expr_appFn_x21_spec__0(x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letBody_x21___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_letBody_x21(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_consumeMData(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 10)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
x_1 = x_2;
goto _start;
}
else
{
lean_inc(x_1);
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_consumeMData___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_consumeMData(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mdataExpr_x21(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 10)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_mk_string_unchecked("Lean.Expr", 9, 9);
x_4 = lean_mk_string_unchecked("Lean.Expr.mdataExpr!", 20, 20);
x_5 = lean_unsigned_to_nat(1037u);
x_6 = lean_unsigned_to_nat(17u);
x_7 = lean_mk_string_unchecked("mdata expression expected", 25, 25);
x_8 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_9 = l_panic___at___Lean_Expr_appFn_x21_spec__0(x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mdataExpr_x21___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_mdataExpr_x21(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_projExpr_x21(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 11)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 2);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_mk_string_unchecked("Lean.Expr", 9, 9);
x_4 = lean_mk_string_unchecked("Lean.Expr.projExpr!", 19, 19);
x_5 = lean_unsigned_to_nat(1041u);
x_6 = lean_unsigned_to_nat(18u);
x_7 = lean_mk_string_unchecked("proj expression expected", 24, 24);
x_8 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_9 = l_panic___at___Lean_Expr_appFn_x21_spec__0(x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_projExpr_x21___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_projExpr_x21(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_projIdx_x21(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 11)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_mk_string_unchecked("Lean.Expr", 9, 9);
x_4 = lean_mk_string_unchecked("Lean.Expr.projIdx!", 18, 18);
x_5 = lean_unsigned_to_nat(1045u);
x_6 = lean_unsigned_to_nat(18u);
x_7 = lean_mk_string_unchecked("proj expression expected", 24, 24);
x_8 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_9 = l_panic___at___String_toNat_x21_spec__0(x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_projIdx_x21___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_projIdx_x21(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBody(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 7)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 2);
x_1 = x_2;
goto _start;
}
else
{
lean_inc(x_1);
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBody___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_getForallBody(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBodyMaxDepth(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_1, x_3);
if (x_4 == 1)
{
lean_dec(x_1);
lean_inc(x_2);
return x_2;
}
else
{
if (lean_obj_tag(x_2) == 7)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_1, x_6);
lean_dec(x_1);
x_1 = x_7;
x_2 = x_5;
goto _start;
}
else
{
lean_dec(x_1);
lean_inc(x_2);
return x_2;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBodyMaxDepth___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Expr_getForallBodyMaxDepth(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBinderNames(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 7)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 2);
x_4 = l_Lean_Expr_getForallBinderNames(x_3);
lean_inc(x_2);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = lean_box(0);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBinderNames___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_getForallBinderNames(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getNumHeadForalls(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 7:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 2);
x_3 = l_Lean_Expr_getNumHeadForalls(x_2);
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_add(x_3, x_4);
lean_dec(x_3);
return x_5;
}
case 10:
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_1, 1);
x_1 = x_6;
goto _start;
}
default: 
{
lean_object* x_8; 
x_8 = lean_unsigned_to_nat(0u);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getNumHeadForalls___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_getNumHeadForalls(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppFn(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
x_1 = x_2;
goto _start;
}
else
{
lean_inc(x_1);
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppFn___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_getAppFn(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppFn_x27(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 5:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
x_1 = x_2;
goto _start;
}
case 10:
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 1);
x_1 = x_4;
goto _start;
}
default: 
{
lean_inc(x_1);
return x_1;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppFn_x27___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_getAppFn_x27(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isAppOf(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Expr_getAppFn(x_1);
if (lean_obj_tag(x_3) == 4)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_name_eq(x_4, x_2);
lean_dec(x_4);
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
lean_dec(x_3);
x_6 = lean_box(0);
x_7 = lean_unbox(x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isAppOf___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Expr_isAppOf(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isAppOfArity(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 4:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_3, x_5);
lean_dec(x_3);
if (x_6 == 0)
{
return x_6;
}
else
{
uint8_t x_7; 
x_7 = lean_name_eq(x_4, x_2);
return x_7;
}
}
case 5:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_eq(x_3, x_9);
if (x_10 == 1)
{
lean_object* x_11; uint8_t x_12; 
lean_dec(x_3);
x_11 = lean_box(0);
x_12 = lean_unbox(x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_sub(x_3, x_13);
lean_dec(x_3);
x_1 = x_8;
x_3 = x_14;
goto _start;
}
}
default: 
{
lean_object* x_16; uint8_t x_17; 
lean_dec(x_3);
x_16 = lean_box(0);
x_17 = lean_unbox(x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isAppOfArity___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_Expr_isAppOfArity(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isAppOfArity_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 4:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_3, x_5);
lean_dec(x_3);
if (x_6 == 0)
{
return x_6;
}
else
{
uint8_t x_7; 
x_7 = lean_name_eq(x_4, x_2);
return x_7;
}
}
case 5:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_eq(x_3, x_9);
if (x_10 == 1)
{
lean_object* x_11; uint8_t x_12; 
lean_dec(x_3);
x_11 = lean_box(0);
x_12 = lean_unbox(x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_sub(x_3, x_13);
lean_dec(x_3);
x_1 = x_8;
x_3 = x_14;
goto _start;
}
}
case 10:
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_1, 1);
x_1 = x_16;
goto _start;
}
default: 
{
lean_object* x_18; uint8_t x_19; 
lean_dec(x_3);
x_18 = lean_box(0);
x_19 = lean_unbox(x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isAppOfArity_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_Expr_isAppOfArity_x27(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_add(x_2, x_4);
lean_dec(x_2);
x_1 = x_3;
x_2 = x_5;
goto _start;
}
else
{
return x_2;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppNumArgs(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppNumArgs___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_getAppNumArgs(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppNumArgs_x27_go(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 5:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_add(x_2, x_4);
lean_dec(x_2);
x_1 = x_3;
x_2 = x_5;
goto _start;
}
case 10:
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_1, 1);
x_1 = x_7;
goto _start;
}
default: 
{
return x_2;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppNumArgs_x27_go___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Expr_getAppNumArgs_x27_go(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppNumArgs_x27(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Expr_getAppNumArgs_x27_go(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppNumArgs_x27___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_getAppNumArgs_x27(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getBoundedAppFn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_1, x_3);
if (x_4 == 1)
{
lean_dec(x_1);
lean_inc(x_2);
return x_2;
}
else
{
if (lean_obj_tag(x_2) == 5)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_1, x_6);
lean_dec(x_1);
x_1 = x_7;
x_2 = x_5;
goto _start;
}
else
{
lean_dec(x_1);
lean_inc(x_2);
return x_2;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getBoundedAppFn___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Expr_getBoundedAppFn(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_array_set(x_2, x_3, x_5);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_3, x_7);
lean_dec(x_3);
x_1 = x_4;
x_2 = x_6;
x_3 = x_8;
goto _start;
}
else
{
lean_dec(x_3);
lean_dec(x_1);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppArgs(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_box(0);
x_3 = l_Lean_Expr_sort___override(x_2);
x_4 = l_Lean_Expr_getAppNumArgs(x_1);
lean_inc(x_4);
x_5 = lean_mk_array(x_4, x_3);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_4, x_6);
lean_dec(x_4);
x_8 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_5, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getBoundedAppArgsAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_3, x_6);
if (x_7 == 1)
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_2;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_3, x_8);
lean_dec(x_3);
x_10 = lean_array_set(x_2, x_9, x_5);
x_1 = x_4;
x_2 = x_10;
x_3 = x_9;
goto _start;
}
}
else
{
lean_dec(x_3);
lean_dec(x_1);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getBoundedAppArgs(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_9; uint8_t x_10; 
x_3 = lean_box(0);
x_4 = l_Lean_Expr_sort___override(x_3);
x_9 = l_Lean_Expr_getAppNumArgs(x_2);
x_10 = lean_nat_dec_le(x_1, x_9);
if (x_10 == 0)
{
lean_dec(x_1);
x_5 = x_9;
goto block_8;
}
else
{
lean_dec(x_9);
x_5 = x_1;
goto block_8;
}
block_8:
{
lean_object* x_6; lean_object* x_7; 
lean_inc(x_5);
x_6 = lean_mk_array(x_5, x_4);
x_7 = l___private_Lean_Expr_0__Lean_Expr_getBoundedAppArgsAux(x_2, x_6, x_5);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_array_push(x_2, x_4);
x_1 = x_3;
x_2 = x_5;
goto _start;
}
else
{
lean_dec(x_1);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppRevArgs(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Expr_getAppNumArgs(x_1);
x_3 = lean_mk_empty_array_with_capacity(x_2);
lean_dec(x_2);
x_4 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 5)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_array_set(x_3, x_4, x_6);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_4, x_8);
lean_dec(x_4);
x_2 = x_5;
x_3 = x_7;
x_4 = x_9;
goto _start;
}
else
{
lean_object* x_11; 
lean_dec(x_4);
x_11 = lean_apply_2(x_1, x_2, x_3);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Expr_withAppAux___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withApp___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_box(0);
x_4 = l_Lean_Expr_sort___override(x_3);
x_5 = l_Lean_Expr_getAppNumArgs(x_1);
lean_inc(x_5);
x_6 = lean_mk_array(x_5, x_4);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_5, x_7);
lean_dec(x_5);
x_9 = l_Lean_Expr_withAppAux___redArg(x_2, x_1, x_6, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withApp(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_box(0);
x_5 = l_Lean_Expr_sort___override(x_4);
x_6 = l_Lean_Expr_getAppNumArgs(x_2);
lean_inc(x_6);
x_7 = lean_mk_array(x_6, x_5);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_6, x_8);
lean_dec(x_6);
x_10 = l_Lean_Expr_withAppAux___redArg(x_3, x_2, x_7, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Expr_getAppFnArgs_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_array_set(x_2, x_3, x_5);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_3, x_7);
lean_dec(x_3);
x_1 = x_4;
x_2 = x_6;
x_3 = x_8;
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_3);
x_10 = l_Lean_Expr_constName(x_1);
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_2);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppFnArgs(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_box(0);
x_3 = l_Lean_Expr_sort___override(x_2);
x_4 = l_Lean_Expr_getAppNumArgs(x_1);
lean_inc(x_4);
x_5 = lean_mk_array(x_4, x_3);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_4, x_6);
lean_dec(x_4);
x_8 = l_Lean_Expr_withAppAux___at___Lean_Expr_getAppFnArgs_spec__0(x_1, x_5, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Expr_getAppArgsN_loop_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Array_instInhabited(lean_box(0));
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppArgsN_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_1, x_4);
if (x_5 == 1)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
if (lean_obj_tag(x_2) == 5)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_1, x_8);
lean_dec(x_1);
x_10 = lean_array_set(x_3, x_9, x_7);
x_1 = x_9;
x_2 = x_6;
x_3 = x_10;
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_mk_string_unchecked("Lean.Expr", 9, 9);
x_13 = lean_mk_string_unchecked("Lean.Expr.getAppArgsN.loop", 26, 26);
x_14 = lean_unsigned_to_nat(1202u);
x_15 = lean_unsigned_to_nat(27u);
x_16 = lean_mk_string_unchecked("too few arguments at", 20, 20);
x_17 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_12, x_13, x_14, x_15, x_16);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_12);
x_18 = l_panic___at___Lean_Expr_getAppArgsN_loop_spec__0(x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppArgsN(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_box(0);
x_4 = l_Lean_Expr_sort___override(x_3);
lean_inc(x_2);
x_5 = lean_mk_array(x_2, x_4);
x_6 = l_Lean_Expr_getAppArgsN_loop(x_2, x_1, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_stripArgsN(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 1)
{
lean_dec(x_2);
lean_inc(x_1);
return x_1;
}
else
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_2, x_6);
lean_dec(x_2);
x_1 = x_5;
x_2 = x_7;
goto _start;
}
else
{
lean_dec(x_2);
lean_inc(x_1);
return x_1;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_stripArgsN___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Expr_stripArgsN(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppPrefix(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_Expr_getAppNumArgs(x_1);
x_4 = lean_nat_sub(x_3, x_2);
lean_dec(x_3);
x_5 = l_Lean_Expr_stripArgsN(x_1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppPrefix___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Expr_getAppPrefix(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseApp___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; size_t x_7; lean_object* x_8; 
x_5 = lean_array_size(x_1);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_usize_of_nat(x_6);
x_8 = l_Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), x_2, x_3, x_5, x_7, x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseApp___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_inc(x_2);
x_7 = lean_alloc_closure((void*)(l_Lean_Expr_traverseApp___redArg___lam__0___boxed), 4, 3);
lean_closure_set(x_7, 0, x_6);
lean_closure_set(x_7, 1, x_1);
lean_closure_set(x_7, 2, x_2);
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
lean_dec(x_3);
x_9 = lean_alloc_closure((void*)(l_Lean_mkAppN___boxed), 2, 0);
x_10 = lean_apply_1(x_2, x_5);
x_11 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_9, x_10);
x_12 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_11, x_7);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseApp___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_4, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_alloc_closure((void*)(l_Lean_Expr_traverseApp___redArg___lam__1), 6, 4);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_2);
lean_closure_set(x_7, 2, x_6);
lean_closure_set(x_7, 3, x_5);
x_8 = lean_box(0);
x_9 = l_Lean_Expr_sort___override(x_8);
x_10 = l_Lean_Expr_getAppNumArgs(x_3);
lean_inc(x_10);
x_11 = lean_mk_array(x_10, x_9);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_10, x_12);
lean_dec(x_10);
x_14 = l_Lean_Expr_withAppAux___redArg(x_7, x_3, x_11, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseApp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Expr_traverseApp___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseApp___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Expr_traverseApp___redArg___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 5)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_array_push(x_3, x_5);
x_2 = x_4;
x_3 = x_6;
goto _start;
}
else
{
lean_object* x_8; 
x_8 = lean_apply_2(x_1, x_2, x_3);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_withAppRevAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppRev___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_Expr_getAppNumArgs(x_1);
x_4 = lean_mk_empty_array_with_capacity(x_3);
lean_dec(x_3);
x_5 = l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___redArg(x_2, x_1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppRev(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_Lean_Expr_getAppNumArgs(x_2);
x_5 = lean_mk_empty_array_with_capacity(x_4);
lean_dec(x_4);
x_6 = l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___redArg(x_3, x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArgD(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_2, x_6);
if (x_7 == 1)
{
lean_dec(x_2);
lean_inc(x_5);
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_2, x_8);
lean_dec(x_2);
x_1 = x_4;
x_2 = x_9;
goto _start;
}
}
else
{
lean_dec(x_2);
lean_inc(x_3);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArgD___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Expr_getRevArgD(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArg_x21(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_2, x_5);
if (x_6 == 1)
{
lean_dec(x_2);
lean_inc(x_4);
return x_4;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_2, x_7);
lean_dec(x_2);
x_1 = x_3;
x_2 = x_8;
goto _start;
}
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_2);
x_10 = lean_mk_string_unchecked("Lean.Expr", 9, 9);
x_11 = lean_mk_string_unchecked("Lean.Expr.getRevArg!", 20, 20);
x_12 = lean_unsigned_to_nat(1243u);
x_13 = lean_unsigned_to_nat(20u);
x_14 = lean_mk_string_unchecked("invalid index", 13, 13);
x_15 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_10, x_11, x_12, x_13, x_14);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
x_16 = l_panic___at___Lean_Expr_appFn_x21_spec__0(x_15);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArg_x21___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Expr_getRevArg_x21(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArg_x21_x27(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 5:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_2, x_5);
if (x_6 == 1)
{
lean_dec(x_2);
lean_inc(x_4);
return x_4;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_2, x_7);
lean_dec(x_2);
x_1 = x_3;
x_2 = x_8;
goto _start;
}
}
case 10:
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_1, 1);
x_1 = x_10;
goto _start;
}
default: 
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_2);
x_12 = lean_mk_string_unchecked("Lean.Expr", 9, 9);
x_13 = lean_mk_string_unchecked("Lean.Expr.getRevArg!'", 21, 21);
x_14 = lean_unsigned_to_nat(1250u);
x_15 = lean_unsigned_to_nat(20u);
x_16 = lean_mk_string_unchecked("invalid index", 13, 13);
x_17 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_12, x_13, x_14, x_15, x_16);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_12);
x_18 = l_panic___at___Lean_Expr_appFn_x21_spec__0(x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArg_x21_x27___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Expr_getRevArg_x21_x27(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getArg_x21(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_nat_sub(x_3, x_2);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_sub(x_4, x_5);
lean_dec(x_4);
x_7 = l_Lean_Expr_getRevArg_x21(x_1, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getArg_x21___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Expr_getArg_x21(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getArg_x21_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_nat_sub(x_3, x_2);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_sub(x_4, x_5);
lean_dec(x_4);
x_7 = l_Lean_Expr_getRevArg_x21_x27(x_1, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getArg_x21_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Expr_getArg_x21_x27(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getArgD(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_nat_sub(x_4, x_2);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_5, x_6);
lean_dec(x_5);
x_8 = l_Lean_Expr_getRevArgD(x_1, x_7, x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getArgD___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Expr_getArgD(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasLooseBVars(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Expr_looseBVarRange(x_1);
x_4 = lean_nat_dec_lt(x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasLooseBVars___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_hasLooseBVars(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isArrow(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 7)
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_ctor_get(x_1, 2);
x_3 = l_Lean_Expr_hasLooseBVars(x_2);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_box(1);
x_5 = lean_unbox(x_4);
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_box(0);
x_7 = lean_unbox(x_6);
return x_7;
}
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
LEAN_EXPORT lean_object* l_Lean_Expr_isArrow___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_isArrow(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasLooseBVar___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_expr_has_loose_bvar(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasLooseBVarInExplicitDomain(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
if (lean_obj_tag(x_1) == 7)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_7; uint8_t x_12; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
x_6 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
x_12 = lean_expr_has_loose_bvar(x_4, x_2);
if (x_12 == 0)
{
x_7 = x_12;
goto block_11;
}
else
{
uint8_t x_13; 
x_13 = l_Lean_BinderInfo_isExplicit(x_6);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_Lean_Expr_hasLooseBVarInExplicitDomain(x_5, x_14, x_3);
x_7 = x_15;
goto block_11;
}
else
{
x_7 = x_13;
goto block_11;
}
}
block_11:
{
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_2, x_8);
lean_dec(x_2);
x_1 = x_5;
x_2 = x_9;
goto _start;
}
else
{
lean_dec(x_2);
return x_7;
}
}
}
else
{
if (x_3 == 0)
{
lean_dec(x_2);
return x_3;
}
else
{
uint8_t x_16; 
x_16 = lean_expr_has_loose_bvar(x_1, x_2);
lean_dec(x_2);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasLooseBVarInExplicitDomain___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_3);
lean_dec(x_3);
x_5 = l_Lean_Expr_hasLooseBVarInExplicitDomain(x_1, x_2, x_4);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lowerLooseBVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_expr_lower_loose_bvars(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_liftLooseBVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_expr_lift_loose_bvars(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_inferImplicit(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
if (lean_obj_tag(x_1) == 7)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec(x_1);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_2, x_8);
if (x_9 == 1)
{
lean_object* x_10; 
x_10 = l_Lean_Expr_forallE___override(x_4, x_5, x_6, x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_20; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_2, x_11);
x_13 = l_Lean_Expr_inferImplicit(x_6, x_12, x_3);
lean_dec(x_12);
x_20 = l_Lean_BinderInfo_isExplicit(x_7);
if (x_20 == 0)
{
x_14 = x_20;
goto block_19;
}
else
{
uint8_t x_21; 
x_21 = l_Lean_Expr_hasLooseBVarInExplicitDomain(x_13, x_8, x_3);
x_14 = x_21;
goto block_19;
}
block_19:
{
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = l_Lean_Expr_forallE___override(x_4, x_5, x_13, x_7);
return x_15;
}
else
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_16 = lean_box(1);
x_17 = lean_unbox(x_16);
x_18 = l_Lean_Expr_forallE___override(x_4, x_5, x_13, x_17);
return x_18;
}
}
}
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_inferImplicit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
lean_dec(x_3);
x_5 = l_Lean_Expr_inferImplicit(x_1, x_2, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateForallBinderInfos(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 7)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
x_6 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec(x_1);
x_7 = l_Lean_Expr_forallE___override(x_3, x_4, x_5, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 2);
lean_inc(x_10);
x_11 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec(x_1);
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
lean_dec(x_2);
x_14 = l_Lean_Expr_updateForallBinderInfos(x_10, x_13);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_15; 
x_15 = l_Lean_Expr_forallE___override(x_8, x_9, x_14, x_11);
return x_15;
}
else
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_12, 0);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
x_18 = l_Lean_Expr_forallE___override(x_8, x_9, x_14, x_17);
return x_18;
}
}
}
else
{
lean_dec(x_2);
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiate___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_expr_instantiate(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiate1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_expr_instantiate1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateRev___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_expr_instantiate_rev(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateRange___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_expr_instantiate_range(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateRevRange___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_expr_instantiate_rev_range(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_abstract___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_expr_abstract(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_abstractRange___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_expr_abstract_range(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVar(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_mk_empty_array_with_capacity(x_4);
x_6 = lean_array_push(x_5, x_2);
x_7 = lean_expr_abstract(x_1, x_6);
lean_dec(x_6);
x_8 = lean_expr_instantiate1(x_7, x_3);
lean_dec(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Expr_replaceFVar(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVarId(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Expr_fvar___override(x_2);
x_5 = l_Lean_Expr_replaceFVar(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVarId___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Expr_replaceFVarId(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVars(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_expr_abstract(x_1, x_2);
x_5 = lean_expr_instantiate_rev(x_4, x_3);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Expr_replaceFVars(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Expr_instToString() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Expr_dbgToString___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isAtomic(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 5:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
case 6:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_box(0);
x_5 = lean_unbox(x_4);
return x_5;
}
case 7:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_box(0);
x_7 = lean_unbox(x_6);
return x_7;
}
case 8:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_box(0);
x_9 = lean_unbox(x_8);
return x_9;
}
case 10:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_box(0);
x_11 = lean_unbox(x_10);
return x_11;
}
case 11:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_box(0);
x_13 = lean_unbox(x_12);
return x_13;
}
default: 
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_box(1);
x_15 = lean_unbox(x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isAtomic___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_isAtomic(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDecIsTrue(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_mk_string_unchecked("Decidable", 9, 9);
x_4 = lean_mk_string_unchecked("isTrue", 6, 6);
x_5 = l_Lean_Name_mkStr2(x_3, x_4);
x_6 = lean_box(0);
x_7 = l_Lean_Expr_const___override(x_5, x_6);
x_8 = l_Lean_mkAppB(x_7, x_1, x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDecIsFalse(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_mk_string_unchecked("Decidable", 9, 9);
x_4 = lean_mk_string_unchecked("isFalse", 7, 7);
x_5 = l_Lean_Name_mkStr2(x_3, x_4);
x_6 = lean_box(0);
x_7 = l_Lean_Expr_const___override(x_5, x_6);
x_8 = l_Lean_mkAppB(x_7, x_1, x_2);
return x_8;
}
}
static lean_object* _init_l_Lean_instInhabitedExprStructEq() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_mk_string_unchecked("_inhabitedExprDummy", 19, 19);
x_2 = l_Lean_Name_mkStr1(x_1);
x_3 = lean_box(0);
x_4 = l_Lean_Expr_const___override(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instCoeExprExprStructEq___lam__0(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
static lean_object* _init_l_Lean_instCoeExprExprStructEq() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_instCoeExprExprStructEq___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_instCoeExprExprStructEq___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_instCoeExprExprStructEq___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Lean_ExprStructEq_beq(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_expr_equal(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_ExprStructEq_beq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_ExprStructEq_beq(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint64_t l_Lean_ExprStructEq_hash(lean_object* x_1) {
_start:
{
uint64_t x_2; 
x_2 = l_Lean_Expr_hash(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_ExprStructEq_hash___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Lean_ExprStructEq_hash(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_ExprStructEq_instBEq() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_ExprStructEq_beq___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_ExprStructEq_instHashable() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_ExprStructEq_hash___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_ExprStructEq_instToString___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_expr_dbg_to_string(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_ExprStructEq_instToString() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_ExprStructEq_instToString___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_ExprStructEq_instToString___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_ExprStructEq_instToString___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_mkAppRevRangeAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_eq(x_4, x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_4, x_6);
lean_dec(x_4);
x_8 = l_Lean_instInhabitedExpr;
x_9 = lean_array_get(x_8, x_1, x_7);
x_10 = l_Lean_Expr_app___override(x_3, x_9);
x_3 = x_10;
x_4 = x_7;
goto _start;
}
else
{
lean_dec(x_4);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_mkAppRevRangeAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Expr_0__Lean_Expr_mkAppRevRangeAux(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mkAppRevRange(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Expr_0__Lean_Expr_mkAppRevRangeAux(x_4, x_2, x_1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mkAppRevRange___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Expr_mkAppRevRange(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_betaRev_go___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_nat_sub(x_1, x_2);
x_7 = lean_expr_instantiate_range(x_3, x_6, x_1, x_4);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l___private_Lean_Expr_0__Lean_Expr_mkAppRevRangeAux(x_4, x_8, x_7, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_betaRev_go(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_5)) {
case 6:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_5, 2);
lean_inc(x_10);
lean_dec(x_5);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_6, x_11);
lean_dec(x_6);
x_13 = lean_nat_dec_lt(x_12, x_4);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_12);
x_14 = lean_expr_instantiate(x_10, x_1);
lean_dec(x_10);
return x_14;
}
else
{
x_5 = x_10;
x_6 = x_12;
goto _start;
}
}
case 8:
{
if (x_2 == 0)
{
goto block_9;
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_5, 2);
lean_inc(x_16);
x_17 = lean_ctor_get(x_5, 3);
lean_inc(x_17);
x_18 = lean_nat_dec_lt(x_6, x_4);
if (x_18 == 0)
{
lean_dec(x_17);
lean_dec(x_16);
goto block_9;
}
else
{
lean_object* x_19; 
lean_dec(x_5);
x_19 = lean_expr_instantiate1(x_17, x_16);
lean_dec(x_16);
lean_dec(x_17);
x_5 = x_19;
goto _start;
}
}
}
case 10:
{
if (x_3 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_5, 1);
lean_inc(x_21);
lean_dec(x_5);
x_5 = x_21;
goto _start;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_box(0);
x_24 = l_Lean_Expr_betaRev_go___lam__0(x_4, x_6, x_5, x_1, x_23);
lean_dec(x_5);
lean_dec(x_6);
return x_24;
}
}
default: 
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_box(0);
x_26 = l_Lean_Expr_betaRev_go___lam__0(x_4, x_6, x_5, x_1, x_25);
lean_dec(x_5);
lean_dec(x_6);
return x_26;
}
}
block_9:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
x_8 = l_Lean_Expr_betaRev_go___lam__0(x_4, x_6, x_5, x_1, x_7);
lean_dec(x_5);
lean_dec(x_6);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_betaRev_go___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Expr_betaRev_go___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_betaRev_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; uint8_t x_8; lean_object* x_9; 
x_7 = lean_unbox(x_2);
lean_dec(x_2);
x_8 = lean_unbox(x_3);
lean_dec(x_3);
x_9 = l_Lean_Expr_betaRev_go(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_betaRev(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = l_Lean_Expr_betaRev_go(x_2, x_3, x_4, x_5, x_1, x_6);
lean_dec(x_5);
return x_8;
}
else
{
lean_dec(x_5);
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_betaRev___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_3);
lean_dec(x_3);
x_6 = lean_unbox(x_4);
lean_dec(x_4);
x_7 = l_Lean_Expr_betaRev(x_1, x_2, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_beta(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_3 = l_Array_reverse(lean_box(0), x_2);
x_4 = lean_box(0);
x_5 = lean_unbox(x_4);
x_6 = lean_unbox(x_4);
x_7 = l_Lean_Expr_betaRev(x_1, x_3, x_5, x_6);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getNumHeadLambdas(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 6:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 2);
x_3 = l_Lean_Expr_getNumHeadLambdas(x_2);
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_add(x_3, x_4);
lean_dec(x_3);
return x_5;
}
case 10:
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_1, 1);
x_1 = x_6;
goto _start;
}
default: 
{
lean_object* x_8; 
x_8 = lean_unsigned_to_nat(0u);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getNumHeadLambdas___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_getNumHeadLambdas(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isHeadBetaTargetFn(uint8_t x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 6:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_box(1);
x_4 = lean_unbox(x_3);
return x_4;
}
case 8:
{
if (x_1 == 0)
{
return x_1;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_2, 3);
x_2 = x_5;
goto _start;
}
}
case 10:
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_2, 1);
x_2 = x_7;
goto _start;
}
default: 
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_box(0);
x_10 = lean_unbox(x_9);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isHeadBetaTargetFn___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_Expr_isHeadBetaTargetFn(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_headBeta(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; uint8_t x_5; 
x_2 = l_Lean_Expr_getAppFn(x_1);
x_3 = lean_box(0);
x_4 = lean_unbox(x_3);
x_5 = l_Lean_Expr_isHeadBetaTargetFn(x_4, x_2);
if (x_5 == 0)
{
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_6 = l_Lean_Expr_getAppNumArgs(x_1);
x_7 = lean_mk_empty_array_with_capacity(x_6);
lean_dec(x_6);
x_8 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_1, x_7);
x_9 = lean_unbox(x_3);
x_10 = lean_unbox(x_3);
x_11 = l_Lean_Expr_betaRev(x_2, x_8, x_9, x_10);
lean_dec(x_8);
return x_11;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isHeadBetaTarget(lean_object* x_1, uint8_t x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_Expr_isApp(x_1);
if (x_3 == 0)
{
return x_3;
}
else
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Expr_getAppFn(x_1);
x_5 = l_Lean_Expr_isHeadBetaTargetFn(x_2, x_4);
lean_dec(x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isHeadBetaTarget___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_2);
lean_dec(x_2);
x_4 = l_Lean_Expr_isHeadBetaTarget(x_1, x_3);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_etaExpandedBody___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_Expr_hasLooseBVars(x_1);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_1);
return x_4;
}
else
{
lean_object* x_5; 
lean_dec(x_1);
x_5 = lean_box(0);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_etaExpandedBody(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_2, x_5);
lean_dec(x_2);
if (x_6 == 1)
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Expr_bvar___override(x_4);
x_8 = l___private_Lean_Expr_0__Lean_Expr_etaExpandedBody___lam__0(x_7, x_3);
lean_dec(x_3);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_3);
x_9 = lean_box(0);
return x_9;
}
}
case 1:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_dec_eq(x_2, x_11);
lean_dec(x_2);
if (x_12 == 1)
{
lean_object* x_13; lean_object* x_14; 
x_13 = l_Lean_Expr_fvar___override(x_10);
x_14 = l___private_Lean_Expr_0__Lean_Expr_etaExpandedBody___lam__0(x_13, x_3);
lean_dec(x_3);
return x_14;
}
else
{
lean_object* x_15; 
lean_dec(x_10);
lean_dec(x_3);
x_15 = lean_box(0);
return x_15;
}
}
case 2:
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
lean_dec(x_1);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_dec_eq(x_2, x_17);
lean_dec(x_2);
if (x_18 == 1)
{
lean_object* x_19; lean_object* x_20; 
x_19 = l_Lean_Expr_mvar___override(x_16);
x_20 = l___private_Lean_Expr_0__Lean_Expr_etaExpandedBody___lam__0(x_19, x_3);
lean_dec(x_3);
return x_20;
}
else
{
lean_object* x_21; 
lean_dec(x_16);
lean_dec(x_3);
x_21 = lean_box(0);
return x_21;
}
}
case 3:
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_1, 0);
lean_inc(x_22);
lean_dec(x_1);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_nat_dec_eq(x_2, x_23);
lean_dec(x_2);
if (x_24 == 1)
{
lean_object* x_25; lean_object* x_26; 
x_25 = l_Lean_Expr_sort___override(x_22);
x_26 = l___private_Lean_Expr_0__Lean_Expr_etaExpandedBody___lam__0(x_25, x_3);
lean_dec(x_3);
return x_26;
}
else
{
lean_object* x_27; 
lean_dec(x_22);
lean_dec(x_3);
x_27 = lean_box(0);
return x_27;
}
}
case 4:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_28 = lean_ctor_get(x_1, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_1, 1);
lean_inc(x_29);
lean_dec(x_1);
x_30 = lean_unsigned_to_nat(0u);
x_31 = lean_nat_dec_eq(x_2, x_30);
lean_dec(x_2);
if (x_31 == 1)
{
lean_object* x_32; lean_object* x_33; 
x_32 = l_Lean_Expr_const___override(x_28, x_29);
x_33 = l___private_Lean_Expr_0__Lean_Expr_etaExpandedBody___lam__0(x_32, x_3);
lean_dec(x_3);
return x_33;
}
else
{
lean_object* x_34; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_3);
x_34 = lean_box(0);
return x_34;
}
}
case 5:
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_1, 1);
lean_inc(x_35);
switch (lean_obj_tag(x_35)) {
case 0:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_36 = lean_ctor_get(x_1, 0);
lean_inc(x_36);
lean_dec(x_1);
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_unsigned_to_nat(0u);
x_39 = lean_nat_dec_eq(x_2, x_38);
if (x_39 == 1)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_2);
x_40 = l_Lean_Expr_bvar___override(x_37);
x_41 = l_Lean_Expr_app___override(x_36, x_40);
x_42 = l___private_Lean_Expr_0__Lean_Expr_etaExpandedBody___lam__0(x_41, x_3);
lean_dec(x_3);
return x_42;
}
else
{
uint8_t x_43; 
x_43 = lean_nat_dec_eq(x_37, x_3);
lean_dec(x_37);
if (x_43 == 0)
{
lean_object* x_44; 
lean_dec(x_36);
lean_dec(x_3);
lean_dec(x_2);
x_44 = lean_box(0);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_unsigned_to_nat(1u);
x_46 = lean_nat_sub(x_2, x_45);
lean_dec(x_2);
x_47 = lean_nat_add(x_3, x_45);
lean_dec(x_3);
x_1 = x_36;
x_2 = x_46;
x_3 = x_47;
goto _start;
}
}
}
case 1:
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_49 = lean_ctor_get(x_1, 0);
lean_inc(x_49);
lean_dec(x_1);
x_50 = lean_ctor_get(x_35, 0);
lean_inc(x_50);
lean_dec(x_35);
x_51 = lean_unsigned_to_nat(0u);
x_52 = lean_nat_dec_eq(x_2, x_51);
lean_dec(x_2);
if (x_52 == 1)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = l_Lean_Expr_fvar___override(x_50);
x_54 = l_Lean_Expr_app___override(x_49, x_53);
x_55 = l___private_Lean_Expr_0__Lean_Expr_etaExpandedBody___lam__0(x_54, x_3);
lean_dec(x_3);
return x_55;
}
else
{
lean_object* x_56; 
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_3);
x_56 = lean_box(0);
return x_56;
}
}
case 2:
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_57 = lean_ctor_get(x_1, 0);
lean_inc(x_57);
lean_dec(x_1);
x_58 = lean_ctor_get(x_35, 0);
lean_inc(x_58);
lean_dec(x_35);
x_59 = lean_unsigned_to_nat(0u);
x_60 = lean_nat_dec_eq(x_2, x_59);
lean_dec(x_2);
if (x_60 == 1)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = l_Lean_Expr_mvar___override(x_58);
x_62 = l_Lean_Expr_app___override(x_57, x_61);
x_63 = l___private_Lean_Expr_0__Lean_Expr_etaExpandedBody___lam__0(x_62, x_3);
lean_dec(x_3);
return x_63;
}
else
{
lean_object* x_64; 
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_3);
x_64 = lean_box(0);
return x_64;
}
}
case 3:
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_65 = lean_ctor_get(x_1, 0);
lean_inc(x_65);
lean_dec(x_1);
x_66 = lean_ctor_get(x_35, 0);
lean_inc(x_66);
lean_dec(x_35);
x_67 = lean_unsigned_to_nat(0u);
x_68 = lean_nat_dec_eq(x_2, x_67);
lean_dec(x_2);
if (x_68 == 1)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = l_Lean_Expr_sort___override(x_66);
x_70 = l_Lean_Expr_app___override(x_65, x_69);
x_71 = l___private_Lean_Expr_0__Lean_Expr_etaExpandedBody___lam__0(x_70, x_3);
lean_dec(x_3);
return x_71;
}
else
{
lean_object* x_72; 
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_3);
x_72 = lean_box(0);
return x_72;
}
}
case 4:
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_73 = lean_ctor_get(x_1, 0);
lean_inc(x_73);
lean_dec(x_1);
x_74 = lean_ctor_get(x_35, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_35, 1);
lean_inc(x_75);
lean_dec(x_35);
x_76 = lean_unsigned_to_nat(0u);
x_77 = lean_nat_dec_eq(x_2, x_76);
lean_dec(x_2);
if (x_77 == 1)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = l_Lean_Expr_const___override(x_74, x_75);
x_79 = l_Lean_Expr_app___override(x_73, x_78);
x_80 = l___private_Lean_Expr_0__Lean_Expr_etaExpandedBody___lam__0(x_79, x_3);
lean_dec(x_3);
return x_80;
}
else
{
lean_object* x_81; 
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_3);
x_81 = lean_box(0);
return x_81;
}
}
case 5:
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_82 = lean_ctor_get(x_1, 0);
lean_inc(x_82);
lean_dec(x_1);
x_83 = lean_ctor_get(x_35, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_35, 1);
lean_inc(x_84);
lean_dec(x_35);
x_85 = lean_unsigned_to_nat(0u);
x_86 = lean_nat_dec_eq(x_2, x_85);
lean_dec(x_2);
if (x_86 == 1)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = l_Lean_Expr_app___override(x_83, x_84);
x_88 = l_Lean_Expr_app___override(x_82, x_87);
x_89 = l___private_Lean_Expr_0__Lean_Expr_etaExpandedBody___lam__0(x_88, x_3);
lean_dec(x_3);
return x_89;
}
else
{
lean_object* x_90; 
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_3);
x_90 = lean_box(0);
return x_90;
}
}
case 6:
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; lean_object* x_96; uint8_t x_97; 
x_91 = lean_ctor_get(x_1, 0);
lean_inc(x_91);
lean_dec(x_1);
x_92 = lean_ctor_get(x_35, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_35, 1);
lean_inc(x_93);
x_94 = lean_ctor_get(x_35, 2);
lean_inc(x_94);
x_95 = lean_ctor_get_uint8(x_35, sizeof(void*)*3 + 8);
lean_dec(x_35);
x_96 = lean_unsigned_to_nat(0u);
x_97 = lean_nat_dec_eq(x_2, x_96);
lean_dec(x_2);
if (x_97 == 1)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = l_Lean_Expr_lam___override(x_92, x_93, x_94, x_95);
x_99 = l_Lean_Expr_app___override(x_91, x_98);
x_100 = l___private_Lean_Expr_0__Lean_Expr_etaExpandedBody___lam__0(x_99, x_3);
lean_dec(x_3);
return x_100;
}
else
{
lean_object* x_101; 
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_3);
x_101 = lean_box(0);
return x_101;
}
}
case 7:
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; lean_object* x_107; uint8_t x_108; 
x_102 = lean_ctor_get(x_1, 0);
lean_inc(x_102);
lean_dec(x_1);
x_103 = lean_ctor_get(x_35, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_35, 1);
lean_inc(x_104);
x_105 = lean_ctor_get(x_35, 2);
lean_inc(x_105);
x_106 = lean_ctor_get_uint8(x_35, sizeof(void*)*3 + 8);
lean_dec(x_35);
x_107 = lean_unsigned_to_nat(0u);
x_108 = lean_nat_dec_eq(x_2, x_107);
lean_dec(x_2);
if (x_108 == 1)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = l_Lean_Expr_forallE___override(x_103, x_104, x_105, x_106);
x_110 = l_Lean_Expr_app___override(x_102, x_109);
x_111 = l___private_Lean_Expr_0__Lean_Expr_etaExpandedBody___lam__0(x_110, x_3);
lean_dec(x_3);
return x_111;
}
else
{
lean_object* x_112; 
lean_dec(x_105);
lean_dec(x_104);
lean_dec(x_103);
lean_dec(x_102);
lean_dec(x_3);
x_112 = lean_box(0);
return x_112;
}
}
case 8:
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; lean_object* x_119; uint8_t x_120; 
x_113 = lean_ctor_get(x_1, 0);
lean_inc(x_113);
lean_dec(x_1);
x_114 = lean_ctor_get(x_35, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_35, 1);
lean_inc(x_115);
x_116 = lean_ctor_get(x_35, 2);
lean_inc(x_116);
x_117 = lean_ctor_get(x_35, 3);
lean_inc(x_117);
x_118 = lean_ctor_get_uint8(x_35, sizeof(void*)*4 + 8);
lean_dec(x_35);
x_119 = lean_unsigned_to_nat(0u);
x_120 = lean_nat_dec_eq(x_2, x_119);
lean_dec(x_2);
if (x_120 == 1)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = l_Lean_Expr_letE___override(x_114, x_115, x_116, x_117, x_118);
x_122 = l_Lean_Expr_app___override(x_113, x_121);
x_123 = l___private_Lean_Expr_0__Lean_Expr_etaExpandedBody___lam__0(x_122, x_3);
lean_dec(x_3);
return x_123;
}
else
{
lean_object* x_124; 
lean_dec(x_117);
lean_dec(x_116);
lean_dec(x_115);
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_3);
x_124 = lean_box(0);
return x_124;
}
}
case 9:
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; 
x_125 = lean_ctor_get(x_1, 0);
lean_inc(x_125);
lean_dec(x_1);
x_126 = lean_ctor_get(x_35, 0);
lean_inc(x_126);
lean_dec(x_35);
x_127 = lean_unsigned_to_nat(0u);
x_128 = lean_nat_dec_eq(x_2, x_127);
lean_dec(x_2);
if (x_128 == 1)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = l_Lean_Expr_lit___override(x_126);
x_130 = l_Lean_Expr_app___override(x_125, x_129);
x_131 = l___private_Lean_Expr_0__Lean_Expr_etaExpandedBody___lam__0(x_130, x_3);
lean_dec(x_3);
return x_131;
}
else
{
lean_object* x_132; 
lean_dec(x_126);
lean_dec(x_125);
lean_dec(x_3);
x_132 = lean_box(0);
return x_132;
}
}
case 10:
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; 
x_133 = lean_ctor_get(x_1, 0);
lean_inc(x_133);
lean_dec(x_1);
x_134 = lean_ctor_get(x_35, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_35, 1);
lean_inc(x_135);
lean_dec(x_35);
x_136 = lean_unsigned_to_nat(0u);
x_137 = lean_nat_dec_eq(x_2, x_136);
lean_dec(x_2);
if (x_137 == 1)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_138 = l_Lean_Expr_mdata___override(x_134, x_135);
x_139 = l_Lean_Expr_app___override(x_133, x_138);
x_140 = l___private_Lean_Expr_0__Lean_Expr_etaExpandedBody___lam__0(x_139, x_3);
lean_dec(x_3);
return x_140;
}
else
{
lean_object* x_141; 
lean_dec(x_135);
lean_dec(x_134);
lean_dec(x_133);
lean_dec(x_3);
x_141 = lean_box(0);
return x_141;
}
}
default: 
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; 
x_142 = lean_ctor_get(x_1, 0);
lean_inc(x_142);
lean_dec(x_1);
x_143 = lean_ctor_get(x_35, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_35, 1);
lean_inc(x_144);
x_145 = lean_ctor_get(x_35, 2);
lean_inc(x_145);
lean_dec(x_35);
x_146 = lean_unsigned_to_nat(0u);
x_147 = lean_nat_dec_eq(x_2, x_146);
lean_dec(x_2);
if (x_147 == 1)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_148 = l_Lean_Expr_proj___override(x_143, x_144, x_145);
x_149 = l_Lean_Expr_app___override(x_142, x_148);
x_150 = l___private_Lean_Expr_0__Lean_Expr_etaExpandedBody___lam__0(x_149, x_3);
lean_dec(x_3);
return x_150;
}
else
{
lean_object* x_151; 
lean_dec(x_145);
lean_dec(x_144);
lean_dec(x_143);
lean_dec(x_142);
lean_dec(x_3);
x_151 = lean_box(0);
return x_151;
}
}
}
}
case 6:
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; uint8_t x_155; lean_object* x_156; uint8_t x_157; 
x_152 = lean_ctor_get(x_1, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_1, 1);
lean_inc(x_153);
x_154 = lean_ctor_get(x_1, 2);
lean_inc(x_154);
x_155 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec(x_1);
x_156 = lean_unsigned_to_nat(0u);
x_157 = lean_nat_dec_eq(x_2, x_156);
lean_dec(x_2);
if (x_157 == 1)
{
lean_object* x_158; lean_object* x_159; 
x_158 = l_Lean_Expr_lam___override(x_152, x_153, x_154, x_155);
x_159 = l___private_Lean_Expr_0__Lean_Expr_etaExpandedBody___lam__0(x_158, x_3);
lean_dec(x_3);
return x_159;
}
else
{
lean_object* x_160; 
lean_dec(x_154);
lean_dec(x_153);
lean_dec(x_152);
lean_dec(x_3);
x_160 = lean_box(0);
return x_160;
}
}
case 7:
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; uint8_t x_164; lean_object* x_165; uint8_t x_166; 
x_161 = lean_ctor_get(x_1, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_1, 1);
lean_inc(x_162);
x_163 = lean_ctor_get(x_1, 2);
lean_inc(x_163);
x_164 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec(x_1);
x_165 = lean_unsigned_to_nat(0u);
x_166 = lean_nat_dec_eq(x_2, x_165);
lean_dec(x_2);
if (x_166 == 1)
{
lean_object* x_167; lean_object* x_168; 
x_167 = l_Lean_Expr_forallE___override(x_161, x_162, x_163, x_164);
x_168 = l___private_Lean_Expr_0__Lean_Expr_etaExpandedBody___lam__0(x_167, x_3);
lean_dec(x_3);
return x_168;
}
else
{
lean_object* x_169; 
lean_dec(x_163);
lean_dec(x_162);
lean_dec(x_161);
lean_dec(x_3);
x_169 = lean_box(0);
return x_169;
}
}
case 8:
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; uint8_t x_174; lean_object* x_175; uint8_t x_176; 
x_170 = lean_ctor_get(x_1, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_1, 1);
lean_inc(x_171);
x_172 = lean_ctor_get(x_1, 2);
lean_inc(x_172);
x_173 = lean_ctor_get(x_1, 3);
lean_inc(x_173);
x_174 = lean_ctor_get_uint8(x_1, sizeof(void*)*4 + 8);
lean_dec(x_1);
x_175 = lean_unsigned_to_nat(0u);
x_176 = lean_nat_dec_eq(x_2, x_175);
lean_dec(x_2);
if (x_176 == 1)
{
lean_object* x_177; lean_object* x_178; 
x_177 = l_Lean_Expr_letE___override(x_170, x_171, x_172, x_173, x_174);
x_178 = l___private_Lean_Expr_0__Lean_Expr_etaExpandedBody___lam__0(x_177, x_3);
lean_dec(x_3);
return x_178;
}
else
{
lean_object* x_179; 
lean_dec(x_173);
lean_dec(x_172);
lean_dec(x_171);
lean_dec(x_170);
lean_dec(x_3);
x_179 = lean_box(0);
return x_179;
}
}
case 9:
{
lean_object* x_180; lean_object* x_181; uint8_t x_182; 
x_180 = lean_ctor_get(x_1, 0);
lean_inc(x_180);
lean_dec(x_1);
x_181 = lean_unsigned_to_nat(0u);
x_182 = lean_nat_dec_eq(x_2, x_181);
lean_dec(x_2);
if (x_182 == 1)
{
lean_object* x_183; lean_object* x_184; 
x_183 = l_Lean_Expr_lit___override(x_180);
x_184 = l___private_Lean_Expr_0__Lean_Expr_etaExpandedBody___lam__0(x_183, x_3);
lean_dec(x_3);
return x_184;
}
else
{
lean_object* x_185; 
lean_dec(x_180);
lean_dec(x_3);
x_185 = lean_box(0);
return x_185;
}
}
case 10:
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; uint8_t x_189; 
x_186 = lean_ctor_get(x_1, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_1, 1);
lean_inc(x_187);
lean_dec(x_1);
x_188 = lean_unsigned_to_nat(0u);
x_189 = lean_nat_dec_eq(x_2, x_188);
lean_dec(x_2);
if (x_189 == 1)
{
lean_object* x_190; lean_object* x_191; 
x_190 = l_Lean_Expr_mdata___override(x_186, x_187);
x_191 = l___private_Lean_Expr_0__Lean_Expr_etaExpandedBody___lam__0(x_190, x_3);
lean_dec(x_3);
return x_191;
}
else
{
lean_object* x_192; 
lean_dec(x_187);
lean_dec(x_186);
lean_dec(x_3);
x_192 = lean_box(0);
return x_192;
}
}
default: 
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; uint8_t x_197; 
x_193 = lean_ctor_get(x_1, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_1, 1);
lean_inc(x_194);
x_195 = lean_ctor_get(x_1, 2);
lean_inc(x_195);
lean_dec(x_1);
x_196 = lean_unsigned_to_nat(0u);
x_197 = lean_nat_dec_eq(x_2, x_196);
lean_dec(x_2);
if (x_197 == 1)
{
lean_object* x_198; lean_object* x_199; 
x_198 = l_Lean_Expr_proj___override(x_193, x_194, x_195);
x_199 = l___private_Lean_Expr_0__Lean_Expr_etaExpandedBody___lam__0(x_198, x_3);
lean_dec(x_3);
return x_199;
}
else
{
lean_object* x_200; 
lean_dec(x_195);
lean_dec(x_194);
lean_dec(x_193);
lean_dec(x_3);
x_200 = lean_box(0);
return x_200;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_etaExpandedBody___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Expr_0__Lean_Expr_etaExpandedBody___lam__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_etaExpandedAux(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 6)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 2);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_add(x_2, x_4);
lean_dec(x_2);
x_1 = x_3;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = l___private_Lean_Expr_0__Lean_Expr_etaExpandedBody(x_1, x_2, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_etaExpanded_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Expr_0__Lean_Expr_etaExpandedAux(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_etaExpandedStrict_x3f(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 6)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 2);
lean_inc(x_2);
lean_dec(x_1);
x_3 = lean_unsigned_to_nat(1u);
x_4 = l___private_Lean_Expr_0__Lean_Expr_etaExpandedAux(x_2, x_3);
return x_4;
}
else
{
lean_object* x_5; 
lean_dec(x_1);
x_5 = lean_box(0);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getOptParamDefault_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_mk_string_unchecked("optParam", 8, 8);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_unsigned_to_nat(2u);
x_5 = l_Lean_Expr_isAppOfArity(x_1, x_3, x_4);
lean_dec(x_3);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Expr_appArg_x21(x_1);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getOptParamDefault_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_getOptParamDefault_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAutoParamTactic_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_mk_string_unchecked("autoParam", 9, 9);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_unsigned_to_nat(2u);
x_5 = l_Lean_Expr_isAppOfArity(x_1, x_3, x_4);
lean_dec(x_3);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Expr_appArg_x21(x_1);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAutoParamTactic_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_getAutoParamTactic_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t lean_is_out_param(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_mk_string_unchecked("outParam", 8, 8);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_unsigned_to_nat(1u);
x_5 = l_Lean_Expr_isAppOfArity(x_1, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isOutParam___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_is_out_param(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isSemiOutParam(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_mk_string_unchecked("semiOutParam", 12, 12);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_unsigned_to_nat(1u);
x_5 = l_Lean_Expr_isAppOfArity(x_1, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isSemiOutParam___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_isSemiOutParam(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isOptParam(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_mk_string_unchecked("optParam", 8, 8);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_unsigned_to_nat(2u);
x_5 = l_Lean_Expr_isAppOfArity(x_1, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isOptParam___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_isOptParam(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isAutoParam(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_mk_string_unchecked("autoParam", 9, 9);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_unsigned_to_nat(2u);
x_5 = l_Lean_Expr_isAppOfArity(x_1, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isAutoParam___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_isAutoParam(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lean_expr_consume_type_annotations(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_6; uint8_t x_13; 
x_13 = l_Lean_Expr_isOptParam(x_1);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = l_Lean_Expr_isAutoParam(x_1);
x_6 = x_14;
goto block_12;
}
else
{
x_6 = x_13;
goto block_12;
}
block_5:
{
if (x_2 == 0)
{
return x_1;
}
else
{
lean_object* x_3; 
x_3 = l_Lean_Expr_appArg_x21(x_1);
lean_dec(x_1);
x_1 = x_3;
goto _start;
}
}
block_12:
{
if (x_6 == 0)
{
uint8_t x_7; 
lean_inc(x_1);
x_7 = lean_is_out_param(x_1);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = l_Lean_Expr_isSemiOutParam(x_1);
x_2 = x_8;
goto block_5;
}
else
{
x_2 = x_7;
goto block_5;
}
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Lean_Expr_appFn_x21(x_1);
lean_dec(x_1);
x_10 = l_Lean_Expr_appArg_x21(x_9);
lean_dec(x_9);
x_1 = x_10;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_cleanupAnnotations(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = l_Lean_Expr_consumeMData(x_1);
x_3 = lean_expr_consume_type_annotations(x_2);
x_4 = lean_expr_eqv(x_3, x_1);
if (x_4 == 0)
{
lean_dec(x_1);
x_1 = x_3;
goto _start;
}
else
{
lean_dec(x_3);
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec(x_1);
x_3 = l_Lean_Expr_cleanupAnnotations(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFnCleanup(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Expr_appFnCleanup___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isFalse(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = l_Lean_Expr_cleanupAnnotations(x_1);
x_3 = lean_mk_string_unchecked("False", 5, 5);
x_4 = l_Lean_Name_mkStr1(x_3);
x_5 = l_Lean_Expr_isConstOf(x_2, x_4);
lean_dec(x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isFalse___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_isFalse(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isTrue(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = l_Lean_Expr_cleanupAnnotations(x_1);
x_3 = lean_mk_string_unchecked("True", 4, 4);
x_4 = l_Lean_Name_mkStr1(x_3);
x_5 = l_Lean_Expr_isConstOf(x_2, x_4);
lean_dec(x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isTrue___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_isTrue(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallArity(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 7:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 2);
lean_inc(x_2);
lean_dec(x_1);
x_3 = l_Lean_Expr_getForallArity(x_2);
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_add(x_3, x_4);
lean_dec(x_3);
return x_5;
}
case 10:
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_1 = x_6;
goto _start;
}
default: 
{
lean_object* x_8; uint8_t x_9; uint8_t x_10; 
x_8 = lean_box(0);
x_9 = lean_unbox(x_8);
x_10 = l_Lean_Expr_isHeadBetaTarget(x_1, x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
lean_inc(x_1);
x_11 = l_Lean_Expr_cleanupAnnotations(x_1);
x_12 = lean_expr_eqv(x_1, x_11);
lean_dec(x_1);
if (x_12 == 0)
{
x_1 = x_11;
goto _start;
}
else
{
lean_object* x_14; 
lean_dec(x_11);
x_14 = lean_unsigned_to_nat(0u);
return x_14;
}
}
else
{
lean_object* x_15; 
x_15 = l_Lean_Expr_headBeta(x_1);
x_1 = x_15;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_nat_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Expr_cleanupAnnotations(x_1);
x_3 = l_Lean_Expr_isApp(x_2);
if (x_3 == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Expr_appFnCleanup___redArg(x_2);
x_6 = l_Lean_Expr_isApp(x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_5);
x_7 = lean_box(0);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
lean_inc(x_5);
x_8 = l_Lean_Expr_appFnCleanup___redArg(x_5);
x_9 = l_Lean_Expr_isApp(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_8);
lean_dec(x_5);
x_10 = lean_box(0);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = l_Lean_Expr_appFnCleanup___redArg(x_8);
x_12 = lean_mk_string_unchecked("OfNat", 5, 5);
x_13 = lean_mk_string_unchecked("ofNat", 5, 5);
x_14 = l_Lean_Name_mkStr2(x_12, x_13);
x_15 = l_Lean_Expr_isConstOf(x_11, x_14);
lean_dec(x_14);
lean_dec(x_11);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_5);
x_16 = lean_box(0);
return x_16;
}
else
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_5, 1);
lean_inc(x_17);
lean_dec(x_5);
if (lean_obj_tag(x_17) == 9)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_ctor_set_tag(x_18, 1);
return x_18;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
else
{
lean_object* x_22; 
lean_dec(x_18);
x_22 = lean_box(0);
return x_22;
}
}
else
{
lean_object* x_23; 
lean_dec(x_17);
x_23 = lean_box(0);
return x_23;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_int_x3f(lean_object* x_1) {
_start:
{
lean_object* x_11; uint8_t x_12; 
lean_inc(x_1);
x_11 = l_Lean_Expr_cleanupAnnotations(x_1);
x_12 = l_Lean_Expr_isApp(x_11);
if (x_12 == 0)
{
lean_dec(x_11);
goto block_10;
}
else
{
lean_object* x_13; uint8_t x_14; 
lean_inc(x_11);
x_13 = l_Lean_Expr_appFnCleanup___redArg(x_11);
x_14 = l_Lean_Expr_isApp(x_13);
if (x_14 == 0)
{
lean_dec(x_13);
lean_dec(x_11);
goto block_10;
}
else
{
lean_object* x_15; uint8_t x_16; 
x_15 = l_Lean_Expr_appFnCleanup___redArg(x_13);
x_16 = l_Lean_Expr_isApp(x_15);
if (x_16 == 0)
{
lean_dec(x_15);
lean_dec(x_11);
goto block_10;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_17 = l_Lean_Expr_appFnCleanup___redArg(x_15);
x_18 = lean_mk_string_unchecked("Neg", 3, 3);
x_19 = lean_mk_string_unchecked("neg", 3, 3);
x_20 = l_Lean_Name_mkStr2(x_18, x_19);
x_21 = l_Lean_Expr_isConstOf(x_17, x_20);
lean_dec(x_20);
lean_dec(x_17);
if (x_21 == 0)
{
lean_dec(x_11);
goto block_10;
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_1);
x_22 = lean_ctor_get(x_11, 1);
lean_inc(x_22);
lean_dec(x_11);
x_23 = l_Lean_Expr_nat_x3f(x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
x_24 = lean_box(0);
return x_24;
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_23);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_23, 0);
x_27 = lean_unsigned_to_nat(0u);
x_28 = lean_nat_dec_eq(x_26, x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_nat_to_int(x_26);
x_30 = lean_int_neg(x_29);
lean_dec(x_29);
lean_ctor_set(x_23, 0, x_30);
return x_23;
}
else
{
lean_object* x_31; 
lean_free_object(x_23);
lean_dec(x_26);
x_31 = lean_box(0);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = lean_ctor_get(x_23, 0);
lean_inc(x_32);
lean_dec(x_23);
x_33 = lean_unsigned_to_nat(0u);
x_34 = lean_nat_dec_eq(x_32, x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_nat_to_int(x_32);
x_36 = lean_int_neg(x_35);
lean_dec(x_35);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
return x_37;
}
else
{
lean_object* x_38; 
lean_dec(x_32);
x_38 = lean_box(0);
return x_38;
}
}
}
}
}
}
}
block_10:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_nat_x3f(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_nat_to_int(x_5);
lean_ctor_set(x_2, 0, x_6);
return x_2;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_nat_to_int(x_7);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasAnyFVar_visit___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6) {
_start:
{
uint8_t x_7; 
lean_inc(x_1);
x_7 = l_Lean_Expr_hasAnyFVar_visit(x_1, x_4);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = l_Lean_Expr_hasAnyFVar_visit(x_1, x_5);
return x_8;
}
else
{
lean_dec(x_5);
lean_dec(x_1);
return x_2;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasAnyFVar_visit(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_Expr_hasFVar(x_2);
if (x_3 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
switch (lean_obj_tag(x_2)) {
case 1:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_apply_1(x_1, x_4);
x_6 = lean_unbox(x_5);
lean_dec(x_5);
return x_6;
}
case 5:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_dec(x_2);
lean_inc(x_1);
x_9 = l_Lean_Expr_hasAnyFVar_visit(x_1, x_7);
if (x_9 == 0)
{
x_2 = x_8;
goto _start;
}
else
{
lean_dec(x_8);
lean_dec(x_1);
return x_3;
}
}
case 6:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 2);
lean_inc(x_13);
x_14 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_dec(x_2);
x_15 = l_Lean_Expr_hasAnyFVar_visit___lam__0(x_1, x_3, x_11, x_12, x_13, x_14);
lean_dec(x_11);
return x_15;
}
case 7:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_20; 
x_16 = lean_ctor_get(x_2, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_2, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_2, 2);
lean_inc(x_18);
x_19 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_dec(x_2);
x_20 = l_Lean_Expr_hasAnyFVar_visit___lam__0(x_1, x_3, x_16, x_17, x_18, x_19);
lean_dec(x_16);
return x_20;
}
case 8:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_ctor_get(x_2, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_2, 2);
lean_inc(x_22);
x_23 = lean_ctor_get(x_2, 3);
lean_inc(x_23);
lean_dec(x_2);
lean_inc(x_1);
x_24 = l_Lean_Expr_hasAnyFVar_visit(x_1, x_21);
if (x_24 == 0)
{
uint8_t x_25; 
lean_inc(x_1);
x_25 = l_Lean_Expr_hasAnyFVar_visit(x_1, x_22);
if (x_25 == 0)
{
x_2 = x_23;
goto _start;
}
else
{
lean_dec(x_23);
lean_dec(x_1);
return x_3;
}
}
else
{
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_1);
return x_3;
}
}
case 10:
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_2, 1);
lean_inc(x_27);
lean_dec(x_2);
x_2 = x_27;
goto _start;
}
case 11:
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_2, 2);
lean_inc(x_29);
lean_dec(x_2);
x_2 = x_29;
goto _start;
}
default: 
{
lean_object* x_31; uint8_t x_32; 
lean_dec(x_2);
lean_dec(x_1);
x_31 = lean_box(0);
x_32 = lean_unbox(x_31);
return x_32;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasAnyFVar_visit___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_7 = lean_unbox(x_2);
lean_dec(x_2);
x_8 = lean_unbox(x_6);
lean_dec(x_6);
x_9 = l_Lean_Expr_hasAnyFVar_visit___lam__0(x_1, x_7, x_3, x_4, x_5, x_8);
lean_dec(x_3);
x_10 = lean_box(x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasAnyFVar_visit___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Expr_hasAnyFVar_visit(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasAnyFVar(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_Expr_hasAnyFVar_visit(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasAnyFVar___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Expr_hasAnyFVar(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasAnyFVar_visit___at___Lean_Expr_containsFVar_spec__0___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6) {
_start:
{
uint8_t x_7; 
x_7 = l_Lean_Expr_hasAnyFVar_visit___at___Lean_Expr_containsFVar_spec__0(x_1, x_4);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = l_Lean_Expr_hasAnyFVar_visit___at___Lean_Expr_containsFVar_spec__0(x_1, x_5);
return x_8;
}
else
{
return x_2;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasAnyFVar_visit___at___Lean_Expr_containsFVar_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_Expr_hasFVar(x_2);
if (x_3 == 0)
{
return x_3;
}
else
{
switch (lean_obj_tag(x_2)) {
case 1:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_name_eq(x_4, x_1);
return x_5;
}
case 5:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = l_Lean_Expr_hasAnyFVar_visit___at___Lean_Expr_containsFVar_spec__0(x_1, x_6);
if (x_8 == 0)
{
x_2 = x_7;
goto _start;
}
else
{
return x_3;
}
}
case 6:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
x_12 = lean_ctor_get(x_2, 2);
x_13 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
x_14 = l_Lean_Expr_hasAnyFVar_visit___at___Lean_Expr_containsFVar_spec__0___lam__0(x_1, x_3, x_10, x_11, x_12, x_13);
return x_14;
}
case 7:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_19; 
x_15 = lean_ctor_get(x_2, 0);
x_16 = lean_ctor_get(x_2, 1);
x_17 = lean_ctor_get(x_2, 2);
x_18 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
x_19 = l_Lean_Expr_hasAnyFVar_visit___at___Lean_Expr_containsFVar_spec__0___lam__0(x_1, x_3, x_15, x_16, x_17, x_18);
return x_19;
}
case 8:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_2, 1);
x_21 = lean_ctor_get(x_2, 2);
x_22 = lean_ctor_get(x_2, 3);
x_23 = l_Lean_Expr_hasAnyFVar_visit___at___Lean_Expr_containsFVar_spec__0(x_1, x_20);
if (x_23 == 0)
{
uint8_t x_24; 
x_24 = l_Lean_Expr_hasAnyFVar_visit___at___Lean_Expr_containsFVar_spec__0(x_1, x_21);
if (x_24 == 0)
{
x_2 = x_22;
goto _start;
}
else
{
return x_3;
}
}
else
{
return x_3;
}
}
case 10:
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_2, 1);
x_2 = x_26;
goto _start;
}
case 11:
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_2, 2);
x_2 = x_28;
goto _start;
}
default: 
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_box(0);
x_31 = lean_unbox(x_30);
return x_31;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_containsFVar(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_Expr_hasAnyFVar_visit___at___Lean_Expr_containsFVar_spec__0(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasAnyFVar_visit___at___Lean_Expr_containsFVar_spec__0___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_7 = lean_unbox(x_2);
lean_dec(x_2);
x_8 = lean_unbox(x_6);
lean_dec(x_6);
x_9 = l_Lean_Expr_hasAnyFVar_visit___at___Lean_Expr_containsFVar_spec__0___lam__0(x_1, x_7, x_3, x_4, x_5, x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_10 = lean_box(x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasAnyFVar_visit___at___Lean_Expr_containsFVar_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Expr_hasAnyFVar_visit___at___Lean_Expr_containsFVar_spec__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_containsFVar___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Expr_containsFVar(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; uint8_t x_11; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
x_9 = lean_ptr_addr(x_7);
x_10 = lean_ptr_addr(x_2);
x_11 = lean_usize_dec_eq(x_9, x_10);
if (x_11 == 0)
{
x_4 = x_11;
goto block_6;
}
else
{
size_t x_12; size_t x_13; uint8_t x_14; 
x_12 = lean_ptr_addr(x_8);
x_13 = lean_ptr_addr(x_3);
x_14 = lean_usize_dec_eq(x_12, x_13);
x_4 = x_14;
goto block_6;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_3);
lean_dec(x_2);
x_15 = l_Lean_instInhabitedExpr;
x_16 = lean_mk_string_unchecked("Lean.Expr", 9, 9);
x_17 = lean_mk_string_unchecked("_private.Lean.Expr.0.Lean.Expr.updateApp!Impl", 45, 45);
x_18 = lean_unsigned_to_nat(1764u);
x_19 = lean_unsigned_to_nat(18u);
x_20 = lean_mk_string_unchecked("application expected", 20, 20);
x_21 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_16, x_17, x_18, x_19, x_20);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_16);
x_22 = l_panic___redArg(x_15, x_21);
return x_22;
}
block_6:
{
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = l_Lean_Expr_app___override(x_2, x_3);
return x_5;
}
else
{
lean_dec(x_3);
lean_dec(x_2);
lean_inc(x_1);
return x_1;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateFVar_x21(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_name_eq(x_3, x_2);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = l_Lean_Expr_fvar___override(x_2);
return x_5;
}
else
{
lean_dec(x_2);
lean_inc(x_1);
return x_1;
}
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_2);
x_6 = l_Lean_instInhabitedExpr;
x_7 = lean_mk_string_unchecked("Lean.Expr", 9, 9);
x_8 = lean_mk_string_unchecked("Lean.Expr.updateFVar!", 21, 21);
x_9 = lean_unsigned_to_nat(1775u);
x_10 = lean_unsigned_to_nat(20u);
x_11 = lean_mk_string_unchecked("fvar expected", 13, 13);
x_12 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
x_13 = l_panic___redArg(x_6, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateFVar_x21___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Expr_updateFVar_x21(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 4)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = l_ptrEqList___redArg(x_4, x_2);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_1);
x_6 = l_Lean_Expr_const___override(x_3, x_2);
return x_6;
}
else
{
lean_dec(x_3);
lean_dec(x_2);
return x_1;
}
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_2);
lean_dec(x_1);
x_7 = l_Lean_instInhabitedExpr;
x_8 = lean_mk_string_unchecked("Lean.Expr", 9, 9);
x_9 = lean_mk_string_unchecked("_private.Lean.Expr.0.Lean.Expr.updateConst!Impl", 47, 47);
x_10 = lean_unsigned_to_nat(1780u);
x_11 = lean_unsigned_to_nat(18u);
x_12 = lean_mk_string_unchecked("constant expected", 17, 17);
x_13 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
x_14 = l_panic___redArg(x_7, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 3)
{
lean_object* x_3; size_t x_4; size_t x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ptr_addr(x_3);
x_5 = lean_ptr_addr(x_2);
x_6 = lean_usize_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = l_Lean_Expr_sort___override(x_2);
return x_7;
}
else
{
lean_dec(x_2);
lean_inc(x_1);
return x_1;
}
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_2);
x_8 = l_Lean_instInhabitedExpr;
x_9 = lean_mk_string_unchecked("Lean.Expr", 9, 9);
x_10 = lean_mk_string_unchecked("_private.Lean.Expr.0.Lean.Expr.updateSort!Impl", 46, 46);
x_11 = lean_unsigned_to_nat(1791u);
x_12 = lean_unsigned_to_nat(14u);
x_13 = lean_mk_string_unchecked("level expected", 14, 14);
x_14 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
x_15 = l_panic___redArg(x_8, x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 10)
{
lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ptr_addr(x_4);
lean_dec(x_4);
x_6 = lean_ptr_addr(x_2);
x_7 = lean_usize_dec_eq(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_1);
x_8 = l_Lean_Expr_mdata___override(x_3, x_2);
return x_8;
}
else
{
lean_dec(x_3);
lean_dec(x_2);
return x_1;
}
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_2);
lean_dec(x_1);
x_9 = l_Lean_instInhabitedExpr;
x_10 = lean_mk_string_unchecked("Lean.Expr", 9, 9);
x_11 = lean_mk_string_unchecked("_private.Lean.Expr.0.Lean.Expr.updateMData!Impl", 47, 47);
x_12 = lean_unsigned_to_nat(1802u);
x_13 = lean_unsigned_to_nat(17u);
x_14 = lean_mk_string_unchecked("mdata expected", 14, 14);
x_15 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_10, x_11, x_12, x_13, x_14);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
x_16 = l_panic___redArg(x_9, x_15);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 11)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; size_t x_6; size_t x_7; uint8_t x_8; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
x_6 = lean_ptr_addr(x_5);
lean_dec(x_5);
x_7 = lean_ptr_addr(x_2);
x_8 = lean_usize_dec_eq(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_1);
x_9 = l_Lean_Expr_proj___override(x_3, x_4, x_2);
return x_9;
}
else
{
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_1;
}
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_2);
lean_dec(x_1);
x_10 = l_Lean_instInhabitedExpr;
x_11 = lean_mk_string_unchecked("Lean.Expr", 9, 9);
x_12 = lean_mk_string_unchecked("_private.Lean.Expr.0.Lean.Expr.updateProj!Impl", 46, 46);
x_13 = lean_unsigned_to_nat(1813u);
x_14 = lean_unsigned_to_nat(18u);
x_15 = lean_mk_string_unchecked("proj expected", 13, 13);
x_16 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_11, x_12, x_13, x_14, x_15);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
x_17 = l_panic___redArg(x_10, x_16);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 7)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; size_t x_14; size_t x_15; uint8_t x_16; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
x_8 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
x_14 = lean_ptr_addr(x_6);
lean_dec(x_6);
x_15 = lean_ptr_addr(x_3);
x_16 = lean_usize_dec_eq(x_14, x_15);
if (x_16 == 0)
{
lean_dec(x_7);
x_9 = x_16;
goto block_13;
}
else
{
size_t x_17; size_t x_18; uint8_t x_19; 
x_17 = lean_ptr_addr(x_7);
lean_dec(x_7);
x_18 = lean_ptr_addr(x_4);
x_19 = lean_usize_dec_eq(x_17, x_18);
x_9 = x_19;
goto block_13;
}
block_13:
{
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_1);
x_10 = l_Lean_Expr_forallE___override(x_5, x_3, x_4, x_2);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(x_8, x_2);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_1);
x_12 = l_Lean_Expr_forallE___override(x_5, x_3, x_4, x_2);
return x_12;
}
else
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_1;
}
}
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_20 = l_Lean_instInhabitedExpr;
x_21 = lean_mk_string_unchecked("Lean.Expr", 9, 9);
x_22 = lean_mk_string_unchecked("_private.Lean.Expr.0.Lean.Expr.updateForall!Impl", 48, 48);
x_23 = lean_unsigned_to_nat(1828u);
x_24 = lean_unsigned_to_nat(23u);
x_25 = lean_mk_string_unchecked("forall expected", 15, 15);
x_26 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_21, x_22, x_23, x_24, x_25);
lean_dec(x_25);
lean_dec(x_22);
lean_dec(x_21);
x_27 = l_panic___redArg(x_20, x_26);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl(x_1, x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateForallE_x21(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_instInhabitedExpr;
if (lean_obj_tag(x_1) == 7)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
x_8 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec(x_1);
x_9 = l_Lean_Expr_forallE___override(x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 7)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; size_t x_19; size_t x_20; uint8_t x_21; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 2);
lean_inc(x_12);
x_13 = lean_ctor_get_uint8(x_9, sizeof(void*)*3 + 8);
x_19 = lean_ptr_addr(x_11);
lean_dec(x_11);
x_20 = lean_ptr_addr(x_2);
x_21 = lean_usize_dec_eq(x_19, x_20);
if (x_21 == 0)
{
lean_dec(x_12);
x_14 = x_21;
goto block_18;
}
else
{
size_t x_22; size_t x_23; uint8_t x_24; 
x_22 = lean_ptr_addr(x_12);
lean_dec(x_12);
x_23 = lean_ptr_addr(x_3);
x_24 = lean_usize_dec_eq(x_22, x_23);
x_14 = x_24;
goto block_18;
}
block_18:
{
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_9);
x_15 = l_Lean_Expr_forallE___override(x_10, x_2, x_3, x_8);
return x_15;
}
else
{
uint8_t x_16; 
x_16 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(x_13, x_8);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_9);
x_17 = l_Lean_Expr_forallE___override(x_10, x_2, x_3, x_8);
return x_17;
}
else
{
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
x_25 = lean_mk_string_unchecked("Lean.Expr", 9, 9);
x_26 = lean_mk_string_unchecked("_private.Lean.Expr.0.Lean.Expr.updateForall!Impl", 48, 48);
x_27 = lean_unsigned_to_nat(1828u);
x_28 = lean_unsigned_to_nat(23u);
x_29 = lean_mk_string_unchecked("forall expected", 15, 15);
x_30 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_25, x_26, x_27, x_28, x_29);
lean_dec(x_29);
lean_dec(x_26);
lean_dec(x_25);
x_31 = l_panic___redArg(x_4, x_30);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_32 = lean_mk_string_unchecked("Lean.Expr", 9, 9);
x_33 = lean_mk_string_unchecked("Lean.Expr.updateForallE!", 24, 24);
x_34 = lean_unsigned_to_nat(1839u);
x_35 = lean_unsigned_to_nat(24u);
x_36 = lean_mk_string_unchecked("forall expected", 15, 15);
x_37 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_32, x_33, x_34, x_35, x_36);
lean_dec(x_36);
lean_dec(x_33);
lean_dec(x_32);
x_38 = l_panic___redArg(x_4, x_37);
return x_38;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 6)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; size_t x_14; size_t x_15; uint8_t x_16; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
x_8 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
x_14 = lean_ptr_addr(x_6);
lean_dec(x_6);
x_15 = lean_ptr_addr(x_3);
x_16 = lean_usize_dec_eq(x_14, x_15);
if (x_16 == 0)
{
lean_dec(x_7);
x_9 = x_16;
goto block_13;
}
else
{
size_t x_17; size_t x_18; uint8_t x_19; 
x_17 = lean_ptr_addr(x_7);
lean_dec(x_7);
x_18 = lean_ptr_addr(x_4);
x_19 = lean_usize_dec_eq(x_17, x_18);
x_9 = x_19;
goto block_13;
}
block_13:
{
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_1);
x_10 = l_Lean_Expr_lam___override(x_5, x_3, x_4, x_2);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(x_8, x_2);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_1);
x_12 = l_Lean_Expr_lam___override(x_5, x_3, x_4, x_2);
return x_12;
}
else
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_1;
}
}
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_20 = l_Lean_instInhabitedExpr;
x_21 = lean_mk_string_unchecked("Lean.Expr", 9, 9);
x_22 = lean_mk_string_unchecked("_private.Lean.Expr.0.Lean.Expr.updateLambda!Impl", 48, 48);
x_23 = lean_unsigned_to_nat(1848u);
x_24 = lean_unsigned_to_nat(19u);
x_25 = lean_mk_string_unchecked("lambda expected", 15, 15);
x_26 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_21, x_22, x_23, x_24, x_25);
lean_dec(x_25);
lean_dec(x_22);
lean_dec(x_21);
x_27 = l_panic___redArg(x_20, x_26);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl(x_1, x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateLambdaE_x21(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_instInhabitedExpr;
if (lean_obj_tag(x_1) == 6)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
x_8 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec(x_1);
x_9 = l_Lean_Expr_lam___override(x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 6)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; size_t x_19; size_t x_20; uint8_t x_21; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 2);
lean_inc(x_12);
x_13 = lean_ctor_get_uint8(x_9, sizeof(void*)*3 + 8);
x_19 = lean_ptr_addr(x_11);
lean_dec(x_11);
x_20 = lean_ptr_addr(x_2);
x_21 = lean_usize_dec_eq(x_19, x_20);
if (x_21 == 0)
{
lean_dec(x_12);
x_14 = x_21;
goto block_18;
}
else
{
size_t x_22; size_t x_23; uint8_t x_24; 
x_22 = lean_ptr_addr(x_12);
lean_dec(x_12);
x_23 = lean_ptr_addr(x_3);
x_24 = lean_usize_dec_eq(x_22, x_23);
x_14 = x_24;
goto block_18;
}
block_18:
{
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_9);
x_15 = l_Lean_Expr_lam___override(x_10, x_2, x_3, x_8);
return x_15;
}
else
{
uint8_t x_16; 
x_16 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(x_13, x_8);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_9);
x_17 = l_Lean_Expr_lam___override(x_10, x_2, x_3, x_8);
return x_17;
}
else
{
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
x_25 = lean_mk_string_unchecked("Lean.Expr", 9, 9);
x_26 = lean_mk_string_unchecked("_private.Lean.Expr.0.Lean.Expr.updateLambda!Impl", 48, 48);
x_27 = lean_unsigned_to_nat(1848u);
x_28 = lean_unsigned_to_nat(19u);
x_29 = lean_mk_string_unchecked("lambda expected", 15, 15);
x_30 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_25, x_26, x_27, x_28, x_29);
lean_dec(x_29);
lean_dec(x_26);
lean_dec(x_25);
x_31 = l_panic___redArg(x_4, x_30);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_32 = lean_mk_string_unchecked("Lean.Expr", 9, 9);
x_33 = lean_mk_string_unchecked("Lean.Expr.updateLambdaE!", 24, 24);
x_34 = lean_unsigned_to_nat(1859u);
x_35 = lean_unsigned_to_nat(20u);
x_36 = lean_mk_string_unchecked("lambda expected", 15, 15);
x_37 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_32, x_33, x_34, x_35, x_36);
lean_dec(x_36);
lean_dec(x_33);
lean_dec(x_32);
x_38 = l_panic___redArg(x_4, x_37);
return x_38;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 8)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_10; size_t x_17; size_t x_18; uint8_t x_19; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 3);
lean_inc(x_8);
x_9 = lean_ctor_get_uint8(x_1, sizeof(void*)*4 + 8);
x_17 = lean_ptr_addr(x_6);
lean_dec(x_6);
x_18 = lean_ptr_addr(x_2);
x_19 = lean_usize_dec_eq(x_17, x_18);
if (x_19 == 0)
{
lean_dec(x_7);
x_10 = x_19;
goto block_16;
}
else
{
size_t x_20; size_t x_21; uint8_t x_22; 
x_20 = lean_ptr_addr(x_7);
lean_dec(x_7);
x_21 = lean_ptr_addr(x_3);
x_22 = lean_usize_dec_eq(x_20, x_21);
x_10 = x_22;
goto block_16;
}
block_16:
{
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_1);
x_11 = l_Lean_Expr_letE___override(x_5, x_2, x_3, x_4, x_9);
return x_11;
}
else
{
size_t x_12; size_t x_13; uint8_t x_14; 
x_12 = lean_ptr_addr(x_8);
lean_dec(x_8);
x_13 = lean_ptr_addr(x_4);
x_14 = lean_usize_dec_eq(x_12, x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_1);
x_15 = l_Lean_Expr_letE___override(x_5, x_2, x_3, x_4, x_9);
return x_15;
}
else
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_1;
}
}
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_23 = l_Lean_instInhabitedExpr;
x_24 = lean_mk_string_unchecked("Lean.Expr", 9, 9);
x_25 = lean_mk_string_unchecked("_private.Lean.Expr.0.Lean.Expr.updateLet!Impl", 45, 45);
x_26 = lean_unsigned_to_nat(1868u);
x_27 = lean_unsigned_to_nat(22u);
x_28 = lean_mk_string_unchecked("let expression expected", 23, 23);
x_29 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_24, x_25, x_26, x_27, x_28);
lean_dec(x_28);
lean_dec(x_25);
lean_dec(x_24);
x_30 = l_panic___redArg(x_23, x_29);
return x_30;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateFn(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; size_t x_9; size_t x_10; uint8_t x_11; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_inc(x_3);
x_5 = l_Lean_Expr_updateFn(x_3, x_2);
x_9 = lean_ptr_addr(x_3);
lean_dec(x_3);
x_10 = lean_ptr_addr(x_5);
x_11 = lean_usize_dec_eq(x_9, x_10);
if (x_11 == 0)
{
x_6 = x_11;
goto block_8;
}
else
{
size_t x_12; uint8_t x_13; 
x_12 = lean_ptr_addr(x_4);
x_13 = lean_usize_dec_eq(x_12, x_12);
x_6 = x_13;
goto block_8;
}
block_8:
{
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_1);
x_7 = l_Lean_Expr_app___override(x_5, x_4);
return x_7;
}
else
{
lean_dec(x_5);
lean_dec(x_4);
return x_1;
}
}
}
else
{
lean_dec(x_1);
lean_inc(x_2);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateFn___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Expr_updateFn(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_eta___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_2);
x_7 = l_Lean_Expr_lam___override(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_7) == 6)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; size_t x_17; size_t x_18; uint8_t x_19; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_7, 2);
lean_inc(x_10);
x_11 = lean_ctor_get_uint8(x_7, sizeof(void*)*3 + 8);
x_17 = lean_ptr_addr(x_9);
lean_dec(x_9);
x_18 = lean_ptr_addr(x_2);
x_19 = lean_usize_dec_eq(x_17, x_18);
if (x_19 == 0)
{
lean_dec(x_10);
x_12 = x_19;
goto block_16;
}
else
{
size_t x_20; size_t x_21; uint8_t x_22; 
x_20 = lean_ptr_addr(x_10);
lean_dec(x_10);
x_21 = lean_ptr_addr(x_5);
x_22 = lean_usize_dec_eq(x_20, x_21);
x_12 = x_22;
goto block_16;
}
block_16:
{
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_7);
x_13 = l_Lean_Expr_lam___override(x_8, x_2, x_5, x_4);
return x_13;
}
else
{
uint8_t x_14; 
x_14 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(x_11, x_4);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_7);
x_15 = l_Lean_Expr_lam___override(x_8, x_2, x_5, x_4);
return x_15;
}
else
{
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_2);
return x_7;
}
}
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
x_23 = lean_mk_string_unchecked("Lean.Expr", 9, 9);
x_24 = lean_mk_string_unchecked("_private.Lean.Expr.0.Lean.Expr.updateLambda!Impl", 48, 48);
x_25 = lean_unsigned_to_nat(1848u);
x_26 = lean_unsigned_to_nat(19u);
x_27 = lean_mk_string_unchecked("lambda expected", 15, 15);
x_28 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_23, x_24, x_25, x_26, x_27);
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_23);
x_29 = l_panic___at___Lean_Expr_appFn_x21_spec__0(x_28);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_eta(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 6)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
x_5 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec(x_1);
lean_inc(x_4);
x_6 = l_Lean_Expr_eta(x_4);
if (lean_obj_tag(x_6) == 5)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
switch (lean_obj_tag(x_7)) {
case 0:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_eq(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = l_Lean_Expr_bvar___override(x_9);
x_13 = l_Lean_Expr_app___override(x_8, x_12);
x_14 = l_Lean_Expr_eta___lam__0(x_2, x_3, x_4, x_5, x_6, x_13);
lean_dec(x_13);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_9);
x_15 = lean_expr_has_loose_bvar(x_8, x_10);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_expr_lower_loose_bvars(x_8, x_16, x_16);
lean_dec(x_8);
return x_17;
}
else
{
lean_object* x_18; 
lean_dec(x_8);
lean_inc(x_3);
x_18 = l_Lean_Expr_lam___override(x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_18) == 6)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_23; size_t x_28; size_t x_29; uint8_t x_30; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_18, 2);
lean_inc(x_21);
x_22 = lean_ctor_get_uint8(x_18, sizeof(void*)*3 + 8);
x_28 = lean_ptr_addr(x_20);
lean_dec(x_20);
x_29 = lean_ptr_addr(x_3);
x_30 = lean_usize_dec_eq(x_28, x_29);
if (x_30 == 0)
{
lean_dec(x_21);
x_23 = x_30;
goto block_27;
}
else
{
size_t x_31; size_t x_32; uint8_t x_33; 
x_31 = lean_ptr_addr(x_21);
lean_dec(x_21);
x_32 = lean_ptr_addr(x_6);
x_33 = lean_usize_dec_eq(x_31, x_32);
x_23 = x_33;
goto block_27;
}
block_27:
{
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec(x_18);
x_24 = l_Lean_Expr_lam___override(x_19, x_3, x_6, x_5);
return x_24;
}
else
{
uint8_t x_25; 
x_25 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(x_22, x_5);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_18);
x_26 = l_Lean_Expr_lam___override(x_19, x_3, x_6, x_5);
return x_26;
}
else
{
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_3);
return x_18;
}
}
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_18);
lean_dec(x_6);
lean_dec(x_3);
x_34 = lean_mk_string_unchecked("Lean.Expr", 9, 9);
x_35 = lean_mk_string_unchecked("_private.Lean.Expr.0.Lean.Expr.updateLambda!Impl", 48, 48);
x_36 = lean_unsigned_to_nat(1848u);
x_37 = lean_unsigned_to_nat(19u);
x_38 = lean_mk_string_unchecked("lambda expected", 15, 15);
x_39 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_34, x_35, x_36, x_37, x_38);
lean_dec(x_38);
lean_dec(x_35);
lean_dec(x_34);
x_40 = l_panic___at___Lean_Expr_appFn_x21_spec__0(x_39);
return x_40;
}
}
}
}
case 1:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_41 = lean_ctor_get(x_6, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_7, 0);
lean_inc(x_42);
lean_dec(x_7);
x_43 = l_Lean_Expr_fvar___override(x_42);
x_44 = l_Lean_Expr_app___override(x_41, x_43);
x_45 = l_Lean_Expr_eta___lam__0(x_2, x_3, x_4, x_5, x_6, x_44);
lean_dec(x_44);
return x_45;
}
case 2:
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_46 = lean_ctor_get(x_6, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_7, 0);
lean_inc(x_47);
lean_dec(x_7);
x_48 = l_Lean_Expr_mvar___override(x_47);
x_49 = l_Lean_Expr_app___override(x_46, x_48);
x_50 = l_Lean_Expr_eta___lam__0(x_2, x_3, x_4, x_5, x_6, x_49);
lean_dec(x_49);
return x_50;
}
case 3:
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_51 = lean_ctor_get(x_6, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_7, 0);
lean_inc(x_52);
lean_dec(x_7);
x_53 = l_Lean_Expr_sort___override(x_52);
x_54 = l_Lean_Expr_app___override(x_51, x_53);
x_55 = l_Lean_Expr_eta___lam__0(x_2, x_3, x_4, x_5, x_6, x_54);
lean_dec(x_54);
return x_55;
}
case 4:
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_56 = lean_ctor_get(x_6, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_7, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_7, 1);
lean_inc(x_58);
lean_dec(x_7);
x_59 = l_Lean_Expr_const___override(x_57, x_58);
x_60 = l_Lean_Expr_app___override(x_56, x_59);
x_61 = l_Lean_Expr_eta___lam__0(x_2, x_3, x_4, x_5, x_6, x_60);
lean_dec(x_60);
return x_61;
}
case 5:
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_62 = lean_ctor_get(x_6, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_7, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_7, 1);
lean_inc(x_64);
lean_dec(x_7);
x_65 = l_Lean_Expr_app___override(x_63, x_64);
x_66 = l_Lean_Expr_app___override(x_62, x_65);
x_67 = l_Lean_Expr_eta___lam__0(x_2, x_3, x_4, x_5, x_6, x_66);
lean_dec(x_66);
return x_67;
}
case 6:
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_68 = lean_ctor_get(x_6, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_7, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_7, 1);
lean_inc(x_70);
x_71 = lean_ctor_get(x_7, 2);
lean_inc(x_71);
x_72 = lean_ctor_get_uint8(x_7, sizeof(void*)*3 + 8);
lean_dec(x_7);
x_73 = l_Lean_Expr_lam___override(x_69, x_70, x_71, x_72);
x_74 = l_Lean_Expr_app___override(x_68, x_73);
x_75 = l_Lean_Expr_eta___lam__0(x_2, x_3, x_4, x_5, x_6, x_74);
lean_dec(x_74);
return x_75;
}
case 7:
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_76 = lean_ctor_get(x_6, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_7, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_7, 1);
lean_inc(x_78);
x_79 = lean_ctor_get(x_7, 2);
lean_inc(x_79);
x_80 = lean_ctor_get_uint8(x_7, sizeof(void*)*3 + 8);
lean_dec(x_7);
x_81 = l_Lean_Expr_forallE___override(x_77, x_78, x_79, x_80);
x_82 = l_Lean_Expr_app___override(x_76, x_81);
x_83 = l_Lean_Expr_eta___lam__0(x_2, x_3, x_4, x_5, x_6, x_82);
lean_dec(x_82);
return x_83;
}
case 8:
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_84 = lean_ctor_get(x_6, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_7, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_7, 1);
lean_inc(x_86);
x_87 = lean_ctor_get(x_7, 2);
lean_inc(x_87);
x_88 = lean_ctor_get(x_7, 3);
lean_inc(x_88);
x_89 = lean_ctor_get_uint8(x_7, sizeof(void*)*4 + 8);
lean_dec(x_7);
x_90 = l_Lean_Expr_letE___override(x_85, x_86, x_87, x_88, x_89);
x_91 = l_Lean_Expr_app___override(x_84, x_90);
x_92 = l_Lean_Expr_eta___lam__0(x_2, x_3, x_4, x_5, x_6, x_91);
lean_dec(x_91);
return x_92;
}
case 9:
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_93 = lean_ctor_get(x_6, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_7, 0);
lean_inc(x_94);
lean_dec(x_7);
x_95 = l_Lean_Expr_lit___override(x_94);
x_96 = l_Lean_Expr_app___override(x_93, x_95);
x_97 = l_Lean_Expr_eta___lam__0(x_2, x_3, x_4, x_5, x_6, x_96);
lean_dec(x_96);
return x_97;
}
case 10:
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_98 = lean_ctor_get(x_6, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_7, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_7, 1);
lean_inc(x_100);
lean_dec(x_7);
x_101 = l_Lean_Expr_mdata___override(x_99, x_100);
x_102 = l_Lean_Expr_app___override(x_98, x_101);
x_103 = l_Lean_Expr_eta___lam__0(x_2, x_3, x_4, x_5, x_6, x_102);
lean_dec(x_102);
return x_103;
}
default: 
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_104 = lean_ctor_get(x_6, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_7, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_7, 1);
lean_inc(x_106);
x_107 = lean_ctor_get(x_7, 2);
lean_inc(x_107);
lean_dec(x_7);
x_108 = l_Lean_Expr_proj___override(x_105, x_106, x_107);
x_109 = l_Lean_Expr_app___override(x_104, x_108);
x_110 = l_Lean_Expr_eta___lam__0(x_2, x_3, x_4, x_5, x_6, x_109);
lean_dec(x_109);
return x_110;
}
}
}
else
{
lean_object* x_111; 
lean_inc(x_6);
x_111 = l_Lean_Expr_eta___lam__0(x_2, x_3, x_4, x_5, x_6, x_6);
lean_dec(x_6);
return x_111;
}
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_eta___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_4);
lean_dec(x_4);
x_8 = l_Lean_Expr_eta___lam__0(x_1, x_2, x_3, x_7, x_5, x_6);
lean_dec(x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setOption___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_box(0);
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_apply_1(x_6, x_4);
x_8 = l_Lean_KVMap_insert(x_5, x_2, x_7);
x_9 = l_Lean_Expr_mdata___override(x_8, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setOption(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Expr_setOption___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setOption___at___Lean_Expr_setPPExplicit_spec__0(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_5, 0, x_3);
x_6 = l_Lean_KVMap_insert(x_4, x_2, x_5);
x_7 = l_Lean_Expr_mdata___override(x_6, x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPExplicit(lean_object* x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_mk_string_unchecked("pp", 2, 2);
x_4 = lean_mk_string_unchecked("explicit", 8, 8);
x_5 = l_Lean_Name_mkStr2(x_3, x_4);
x_6 = l_Lean_Expr_setOption___at___Lean_Expr_setPPExplicit_spec__0(x_1, x_5, x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setOption___at___Lean_Expr_setPPExplicit_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
lean_dec(x_3);
x_5 = l_Lean_Expr_setOption___at___Lean_Expr_setPPExplicit_spec__0(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPExplicit___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
lean_dec(x_2);
x_4 = l_Lean_Expr_setPPExplicit(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPUniverses(lean_object* x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_mk_string_unchecked("pp", 2, 2);
x_4 = lean_mk_string_unchecked("universes", 9, 9);
x_5 = l_Lean_Name_mkStr2(x_3, x_4);
x_6 = l_Lean_Expr_setOption___at___Lean_Expr_setPPExplicit_spec__0(x_1, x_5, x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPUniverses___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
lean_dec(x_2);
x_4 = l_Lean_Expr_setPPUniverses(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPPiBinderTypes(lean_object* x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_mk_string_unchecked("pp", 2, 2);
x_4 = lean_mk_string_unchecked("piBinderTypes", 13, 13);
x_5 = l_Lean_Name_mkStr2(x_3, x_4);
x_6 = l_Lean_Expr_setOption___at___Lean_Expr_setPPExplicit_spec__0(x_1, x_5, x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPPiBinderTypes___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
lean_dec(x_2);
x_4 = l_Lean_Expr_setPPPiBinderTypes(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPFunBinderTypes(lean_object* x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_mk_string_unchecked("pp", 2, 2);
x_4 = lean_mk_string_unchecked("funBinderTypes", 14, 14);
x_5 = l_Lean_Name_mkStr2(x_3, x_4);
x_6 = l_Lean_Expr_setOption___at___Lean_Expr_setPPExplicit_spec__0(x_1, x_5, x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPFunBinderTypes___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
lean_dec(x_2);
x_4 = l_Lean_Expr_setPPFunBinderTypes(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPNumericTypes(lean_object* x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_mk_string_unchecked("pp", 2, 2);
x_4 = lean_mk_string_unchecked("numericTypes", 12, 12);
x_5 = l_Lean_Name_mkStr2(x_3, x_4);
x_6 = l_Lean_Expr_setOption___at___Lean_Expr_setPPExplicit_spec__0(x_1, x_5, x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPNumericTypes___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
lean_dec(x_2);
x_4 = l_Lean_Expr_setPPNumericTypes(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Expr_setAppPPExplicit_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_5 = lean_box(0);
x_6 = lean_array_uget(x_3, x_2);
x_7 = lean_box(0);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = lean_unbox(x_5);
x_10 = l_Lean_Expr_setPPExplicit(x_6, x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_usize_of_nat(x_11);
x_13 = lean_usize_add(x_2, x_12);
x_14 = lean_array_uset(x_8, x_2, x_10);
x_2 = x_13;
x_3 = x_14;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setAppPPExplicit(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; lean_object* x_14; size_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_2 = l_Lean_Expr_getAppFn(x_1);
x_3 = lean_box(0);
x_4 = lean_unbox(x_3);
x_5 = l_Lean_Expr_setPPExplicit(x_2, x_4);
x_6 = lean_box(0);
x_7 = l_Lean_Expr_sort___override(x_6);
x_8 = l_Lean_Expr_getAppNumArgs(x_1);
lean_inc(x_8);
x_9 = lean_mk_array(x_8, x_7);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_8, x_10);
lean_dec(x_8);
x_12 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_9, x_11);
x_13 = lean_array_size(x_12);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_usize_of_nat(x_14);
x_16 = l_Array_mapMUnsafe_map___at___Lean_Expr_setAppPPExplicit_spec__0(x_13, x_15, x_12);
x_17 = l_Lean_mkAppN(x_5, x_16);
lean_dec(x_16);
x_18 = lean_box(1);
x_19 = lean_unbox(x_18);
x_20 = l_Lean_Expr_setPPExplicit(x_17, x_19);
return x_20;
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Expr_setAppPPExplicit_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Lean_Expr_setAppPPExplicit_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Expr_setAppPPExplicitForExposingMVars_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_15; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_box(0);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_15 = l_Lean_Expr_hasMVar(x_5);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = l_Lean_Expr_setPPExplicit(x_5, x_15);
x_8 = x_16;
goto block_14;
}
else
{
x_8 = x_5;
goto block_14;
}
block_14:
{
lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
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
}
LEAN_EXPORT lean_object* l_Lean_Expr_setAppPPExplicitForExposingMVars(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; lean_object* x_14; size_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_2 = l_Lean_Expr_getAppFn(x_1);
x_3 = lean_box(0);
x_4 = lean_unbox(x_3);
x_5 = l_Lean_Expr_setPPExplicit(x_2, x_4);
x_6 = lean_box(0);
x_7 = l_Lean_Expr_sort___override(x_6);
x_8 = l_Lean_Expr_getAppNumArgs(x_1);
lean_inc(x_8);
x_9 = lean_mk_array(x_8, x_7);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_8, x_10);
lean_dec(x_8);
x_12 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_9, x_11);
x_13 = lean_array_size(x_12);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_usize_of_nat(x_14);
x_16 = l_Array_mapMUnsafe_map___at___Lean_Expr_setAppPPExplicitForExposingMVars_spec__0(x_13, x_15, x_12);
x_17 = l_Lean_mkAppN(x_5, x_16);
lean_dec(x_16);
x_18 = lean_box(1);
x_19 = lean_unbox(x_18);
x_20 = l_Lean_Expr_setPPExplicit(x_17, x_19);
return x_20;
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Expr_setAppPPExplicitForExposingMVars_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Lean_Expr_setAppPPExplicitForExposingMVars_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isLetFun(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_mk_string_unchecked("letFun", 6, 6);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_unsigned_to_nat(4u);
x_5 = l_Lean_Expr_isAppOfArity(x_1, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isLetFun___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_isLetFun(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letFun_x3f(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
if (lean_obj_tag(x_2) == 5)
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
if (lean_obj_tag(x_3) == 5)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_4) == 5)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 4)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
lean_dec(x_4);
x_9 = lean_ctor_get(x_5, 0);
lean_inc(x_9);
lean_dec(x_5);
x_10 = lean_box(0);
if (lean_obj_tag(x_9) == 1)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_mk_string_unchecked("letFun", 6, 6);
x_14 = lean_string_dec_eq(x_12, x_13);
lean_dec(x_13);
lean_dec(x_12);
if (x_14 == 0)
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
if (lean_obj_tag(x_11) == 0)
{
return x_10;
}
else
{
lean_dec(x_11);
return x_10;
}
}
else
{
if (lean_obj_tag(x_6) == 6)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_6, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_6, 2);
lean_inc(x_16);
lean_dec(x_6);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_7);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_8);
lean_ctor_set(x_18, 1, x_17);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_15);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
else
{
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_11);
return x_10;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_box(0);
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_Lean_Expr_bvar___override(x_22);
x_24 = l_Lean_Expr_app___override(x_6, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_7);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_8);
lean_ctor_set(x_26, 1, x_25);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_21);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
else
{
lean_dec(x_26);
lean_dec(x_11);
return x_10;
}
}
}
}
else
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_10;
}
}
else
{
lean_object* x_29; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_29 = lean_box(0);
return x_29;
}
}
else
{
lean_object* x_30; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_30 = lean_box(0);
return x_30;
}
}
else
{
lean_object* x_31; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_31 = lean_box(0);
return x_31;
}
}
else
{
lean_object* x_32; 
lean_dec(x_2);
lean_dec(x_1);
x_32 = lean_box(0);
return x_32;
}
}
else
{
lean_object* x_33; 
lean_dec(x_1);
x_33 = lean_box(0);
return x_33;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letFunAppArgs_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_unsigned_to_nat(4u);
x_3 = l_Lean_Expr_getAppNumArgs(x_1);
x_4 = lean_nat_dec_le(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; 
lean_dec(x_3);
lean_dec(x_1);
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_mk_string_unchecked("letFun", 6, 6);
x_7 = l_Lean_Name_mkStr1(x_6);
x_8 = l_Lean_Expr_isAppOf(x_1, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_3);
lean_dec(x_1);
x_9 = lean_box(0);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_10 = l_Lean_instInhabitedExpr;
x_11 = lean_box(0);
x_12 = l_Lean_Expr_sort___override(x_11);
lean_inc(x_3);
x_13 = lean_mk_array(x_3, x_12);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_3, x_14);
lean_dec(x_3);
x_16 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_13, x_15);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_array_get(x_10, x_16, x_17);
x_19 = lean_unsigned_to_nat(2u);
x_20 = lean_array_get(x_10, x_16, x_19);
x_21 = lean_unsigned_to_nat(3u);
x_22 = lean_array_get(x_10, x_16, x_21);
x_23 = lean_array_get_size(x_16);
x_24 = l_Array_extract(lean_box(0), x_16, x_2, x_23);
lean_dec(x_16);
if (lean_obj_tag(x_22) == 6)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_25 = lean_ctor_get(x_22, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_22, 2);
lean_inc(x_26);
lean_dec(x_22);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_20);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_18);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_25);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_24);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_32 = lean_box(0);
x_33 = l_Lean_Expr_bvar___override(x_17);
x_34 = l_Lean_Expr_app___override(x_22, x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_20);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_18);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_32);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_24);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_38);
return x_39;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_1(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_1(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_1(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_1(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_1(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_1(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 5:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
lean_inc(x_2);
x_8 = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_8, 0, x_2);
lean_closure_set(x_8, 1, x_7);
x_9 = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__1___boxed), 3, 2);
lean_closure_set(x_9, 0, x_2);
lean_closure_set(x_9, 1, x_6);
x_10 = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___boxed), 3, 1);
lean_closure_set(x_10, 0, x_3);
x_11 = lean_apply_2(x_5, lean_box(0), x_10);
lean_inc(x_4);
x_12 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_11, x_9);
x_13 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_12, x_8);
return x_13;
}
case 6:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_14 = lean_ctor_get(x_1, 2);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
lean_dec(x_1);
x_16 = lean_ctor_get(x_3, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_3, 2);
lean_inc(x_17);
lean_inc(x_2);
x_18 = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__2___boxed), 3, 2);
lean_closure_set(x_18, 0, x_2);
lean_closure_set(x_18, 1, x_17);
x_19 = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__3___boxed), 3, 2);
lean_closure_set(x_19, 0, x_2);
lean_closure_set(x_19, 1, x_16);
x_20 = lean_alloc_closure((void*)(l_Lean_Expr_updateLambdaE_x21), 3, 1);
lean_closure_set(x_20, 0, x_3);
x_21 = lean_apply_2(x_15, lean_box(0), x_20);
lean_inc(x_14);
x_22 = lean_apply_4(x_14, lean_box(0), lean_box(0), x_21, x_19);
x_23 = lean_apply_4(x_14, lean_box(0), lean_box(0), x_22, x_18);
return x_23;
}
case 7:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_24 = lean_ctor_get(x_1, 2);
lean_inc(x_24);
x_25 = lean_ctor_get(x_1, 1);
lean_inc(x_25);
lean_dec(x_1);
x_26 = lean_ctor_get(x_3, 1);
lean_inc(x_26);
x_27 = lean_ctor_get(x_3, 2);
lean_inc(x_27);
lean_inc(x_2);
x_28 = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__2___boxed), 3, 2);
lean_closure_set(x_28, 0, x_2);
lean_closure_set(x_28, 1, x_27);
x_29 = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__3___boxed), 3, 2);
lean_closure_set(x_29, 0, x_2);
lean_closure_set(x_29, 1, x_26);
x_30 = lean_alloc_closure((void*)(l_Lean_Expr_updateForallE_x21), 3, 1);
lean_closure_set(x_30, 0, x_3);
x_31 = lean_apply_2(x_25, lean_box(0), x_30);
lean_inc(x_24);
x_32 = lean_apply_4(x_24, lean_box(0), lean_box(0), x_31, x_29);
x_33 = lean_apply_4(x_24, lean_box(0), lean_box(0), x_32, x_28);
return x_33;
}
case 8:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_34 = lean_ctor_get(x_1, 2);
lean_inc(x_34);
x_35 = lean_ctor_get(x_1, 1);
lean_inc(x_35);
lean_dec(x_1);
x_36 = lean_ctor_get(x_3, 1);
lean_inc(x_36);
x_37 = lean_ctor_get(x_3, 2);
lean_inc(x_37);
x_38 = lean_ctor_get(x_3, 3);
lean_inc(x_38);
lean_inc(x_2);
x_39 = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__2___boxed), 3, 2);
lean_closure_set(x_39, 0, x_2);
lean_closure_set(x_39, 1, x_38);
lean_inc(x_2);
x_40 = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__7___boxed), 3, 2);
lean_closure_set(x_40, 0, x_2);
lean_closure_set(x_40, 1, x_37);
x_41 = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__4___boxed), 3, 2);
lean_closure_set(x_41, 0, x_2);
lean_closure_set(x_41, 1, x_36);
x_42 = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl), 4, 1);
lean_closure_set(x_42, 0, x_3);
x_43 = lean_apply_2(x_35, lean_box(0), x_42);
lean_inc(x_34);
x_44 = lean_apply_4(x_34, lean_box(0), lean_box(0), x_43, x_41);
lean_inc(x_34);
x_45 = lean_apply_4(x_34, lean_box(0), lean_box(0), x_44, x_40);
x_46 = lean_apply_4(x_34, lean_box(0), lean_box(0), x_45, x_39);
return x_46;
}
case 10:
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_47 = lean_ctor_get(x_1, 0);
lean_inc(x_47);
lean_dec(x_1);
x_48 = lean_ctor_get(x_3, 1);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 0);
lean_inc(x_49);
lean_dec(x_47);
x_50 = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl), 2, 1);
lean_closure_set(x_50, 0, x_3);
x_51 = lean_apply_1(x_2, x_48);
x_52 = lean_apply_4(x_49, lean_box(0), lean_box(0), x_50, x_51);
return x_52;
}
case 11:
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_53 = lean_ctor_get(x_1, 0);
lean_inc(x_53);
lean_dec(x_1);
x_54 = lean_ctor_get(x_3, 2);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 0);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl), 2, 1);
lean_closure_set(x_56, 0, x_3);
x_57 = lean_apply_1(x_2, x_54);
x_58 = lean_apply_4(x_55, lean_box(0), lean_box(0), x_56, x_57);
return x_58;
}
default: 
{
lean_object* x_59; lean_object* x_60; 
lean_dec(x_2);
x_59 = lean_ctor_get(x_1, 1);
lean_inc(x_59);
lean_dec(x_1);
x_60 = lean_apply_2(x_59, lean_box(0), x_3);
return x_60;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Expr_traverseChildren___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Expr_traverseChildren___redArg___lam__0(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Expr_traverseChildren___redArg___lam__1(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Expr_traverseChildren___redArg___lam__2(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Expr_traverseChildren___redArg___lam__3(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Expr_traverseChildren___redArg___lam__7(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Expr_traverseChildren___redArg___lam__4(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_2(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_alloc_closure((void*)(l_Lean_Expr_foldlM___redArg___lam__0), 2, 1);
lean_closure_set(x_7, 0, x_5);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_apply_1(x_4, x_6);
x_10 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_9, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_3, 0);
lean_dec(x_5);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
lean_ctor_set(x_3, 0, x_2);
x_8 = lean_apply_2(x_7, lean_box(0), x_3);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_dec(x_3);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_9);
x_13 = lean_apply_2(x_11, lean_box(0), x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(l_Lean_Expr_foldlM___redArg___lam__2), 3, 2);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_4);
x_7 = lean_box(0);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_apply_2(x_2, x_7, x_5);
x_10 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_9, x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_inc(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_Expr_foldlM___redArg___lam__3), 3, 2);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_5);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_apply_1(x_4, x_6);
x_10 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_9, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg___lam__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_apply_1(x_1, x_5);
lean_ctor_set(x_3, 0, x_6);
x_7 = lean_apply_2(x_2, lean_box(0), x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_3);
x_10 = lean_apply_1(x_1, x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = lean_apply_2(x_2, lean_box(0), x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg___lam__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_box(0);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_apply_2(x_2, x_6, x_5);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Expr_foldlM___redArg___lam__5), 3, 2);
lean_closure_set(x_11, 0, x_4);
lean_closure_set(x_11, 1, x_10);
x_12 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_8, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg___lam__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_inc(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_Expr_foldlM___redArg___lam__6), 3, 2);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_5);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_apply_1(x_4, x_6);
x_10 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_9, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg___lam__8(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
lean_dec(x_5);
lean_ctor_set(x_3, 0, x_1);
x_6 = lean_apply_2(x_2, lean_box(0), x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
lean_dec(x_3);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_apply_2(x_2, lean_box(0), x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg___lam__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_apply_1(x_5, x_6);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Expr_foldlM___redArg___lam__8), 3, 2);
lean_closure_set(x_11, 0, x_4);
lean_closure_set(x_11, 1, x_10);
x_12 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_8, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg___lam__10(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg___lam__11(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg___lam__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_inc(x_3);
x_5 = lean_alloc_closure((void*)(l_Lean_Expr_foldlM___redArg___lam__11), 2, 1);
lean_closure_set(x_5, 0, x_3);
x_6 = lean_apply_2(x_1, x_4, x_3);
x_7 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_inc(x_1);
x_5 = lean_alloc_closure((void*)(l_Lean_Expr_foldlM___redArg___lam__1), 6, 1);
lean_closure_set(x_5, 0, x_1);
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(l_Lean_Expr_foldlM___redArg___lam__4), 6, 1);
lean_closure_set(x_6, 0, x_1);
lean_inc(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_Expr_foldlM___redArg___lam__7), 6, 1);
lean_closure_set(x_7, 0, x_1);
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Lean_Expr_foldlM___redArg___lam__9), 6, 1);
lean_closure_set(x_8, 0, x_1);
x_9 = lean_alloc_closure((void*)(l_Lean_Expr_foldlM___redArg___lam__10___boxed), 1, 0);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
lean_inc(x_12);
x_13 = lean_alloc_closure((void*)(l_Lean_Expr_foldlM___redArg___lam__12), 4, 2);
lean_closure_set(x_13, 0, x_2);
lean_closure_set(x_13, 1, x_12);
lean_inc(x_1);
x_14 = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(x_14, 0, lean_box(0));
lean_closure_set(x_14, 1, lean_box(0));
lean_closure_set(x_14, 2, x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_8);
x_16 = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(x_16, 0, lean_box(0));
lean_closure_set(x_16, 1, lean_box(0));
lean_closure_set(x_16, 2, x_1);
x_17 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set(x_17, 2, x_7);
lean_ctor_set(x_17, 3, x_6);
lean_ctor_set(x_17, 4, x_5);
x_18 = l_Lean_Expr_traverseChildren___redArg(x_17, x_13, x_4);
x_19 = lean_apply_1(x_18, x_3);
x_20 = lean_apply_4(x_12, lean_box(0), lean_box(0), x_9, x_19);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Expr_foldlM___redArg(x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg___lam__10___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_foldlM___redArg___lam__10(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_sizeWithoutSharing___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = l_Lean_Expr_sizeWithoutSharing(x_2);
x_7 = lean_nat_add(x_5, x_6);
lean_dec(x_6);
x_8 = l_Lean_Expr_sizeWithoutSharing(x_3);
x_9 = lean_nat_add(x_7, x_8);
lean_dec(x_8);
lean_dec(x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_sizeWithoutSharing(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 5:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_unsigned_to_nat(1u);
x_5 = l_Lean_Expr_sizeWithoutSharing(x_2);
x_6 = lean_nat_add(x_4, x_5);
lean_dec(x_5);
x_7 = l_Lean_Expr_sizeWithoutSharing(x_3);
x_8 = lean_nat_add(x_6, x_7);
lean_dec(x_7);
lean_dec(x_6);
return x_8;
}
case 6:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_ctor_get(x_1, 2);
x_12 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
x_13 = l_Lean_Expr_sizeWithoutSharing___lam__0(x_9, x_10, x_11, x_12);
return x_13;
}
case 7:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_1, 0);
x_15 = lean_ctor_get(x_1, 1);
x_16 = lean_ctor_get(x_1, 2);
x_17 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
x_18 = l_Lean_Expr_sizeWithoutSharing___lam__0(x_14, x_15, x_16, x_17);
return x_18;
}
case 8:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_19 = lean_ctor_get(x_1, 1);
x_20 = lean_ctor_get(x_1, 2);
x_21 = lean_ctor_get(x_1, 3);
x_22 = lean_unsigned_to_nat(1u);
x_23 = l_Lean_Expr_sizeWithoutSharing(x_19);
x_24 = lean_nat_add(x_22, x_23);
lean_dec(x_23);
x_25 = l_Lean_Expr_sizeWithoutSharing(x_20);
x_26 = lean_nat_add(x_24, x_25);
lean_dec(x_25);
lean_dec(x_24);
x_27 = l_Lean_Expr_sizeWithoutSharing(x_21);
x_28 = lean_nat_add(x_26, x_27);
lean_dec(x_27);
lean_dec(x_26);
return x_28;
}
case 10:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_1, 1);
x_30 = lean_unsigned_to_nat(1u);
x_31 = l_Lean_Expr_sizeWithoutSharing(x_29);
x_32 = lean_nat_add(x_30, x_31);
lean_dec(x_31);
return x_32;
}
case 11:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_1, 2);
x_34 = lean_unsigned_to_nat(1u);
x_35 = l_Lean_Expr_sizeWithoutSharing(x_33);
x_36 = lean_nat_add(x_34, x_35);
lean_dec(x_35);
return x_36;
}
default: 
{
lean_object* x_37; 
x_37 = lean_unsigned_to_nat(1u);
return x_37;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_sizeWithoutSharing___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_4);
lean_dec(x_4);
x_6 = l_Lean_Expr_sizeWithoutSharing___lam__0(x_1, x_2, x_3, x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_sizeWithoutSharing___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_sizeWithoutSharing(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAnnotation(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_3 = l_Lean_KVMap_empty;
x_4 = lean_box(1);
x_5 = lean_alloc_ctor(1, 0, 1);
x_6 = lean_unbox(x_4);
lean_ctor_set_uint8(x_5, 0, x_6);
x_7 = l_Lean_KVMap_insert(x_3, x_1, x_5);
x_8 = l_Lean_Expr_mdata___override(x_7, x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_annotation_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 10)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_9 = l_List_lengthTR(lean_box(0), x_3);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_dec_eq(x_9, x_10);
lean_dec(x_9);
if (x_11 == 0)
{
x_5 = x_11;
goto block_8;
}
else
{
lean_object* x_12; uint8_t x_13; uint8_t x_14; 
x_12 = lean_box(0);
x_13 = lean_unbox(x_12);
x_14 = l_Lean_KVMap_getBool(x_3, x_1, x_13);
x_5 = x_14;
goto block_8;
}
block_8:
{
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; 
lean_inc(x_4);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_4);
return x_7;
}
}
}
else
{
lean_object* x_15; 
x_15 = lean_box(0);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_annotation_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_annotation_x3f(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_mkInaccessible(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_mk_string_unchecked("_inaccessible", 13, 13);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = l_Lean_mkAnnotation(x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_inaccessible_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_mk_string_unchecked("_inaccessible", 13, 13);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = l_Lean_annotation_x3f(x_3, x_1);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_inaccessible_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_inaccessible_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_patternRefAnnotationKey() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_mk_string_unchecked("_patWithRef", 11, 11);
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_patternWithRef_x3f(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 10)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = l___private_Lean_Expr_0__Lean_patternRefAnnotationKey;
x_4 = l_Lean_KVMap_findCore(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
x_5 = lean_box(0);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_4, 0);
if (lean_obj_tag(x_7) == 5)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_Expr_mdataExpr_x21(x_1);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
lean_ctor_set(x_4, 0, x_10);
return x_4;
}
else
{
lean_object* x_11; 
lean_free_object(x_4);
lean_dec(x_7);
x_11 = lean_box(0);
return x_11;
}
}
else
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_4, 0);
lean_inc(x_12);
lean_dec(x_4);
if (lean_obj_tag(x_12) == 5)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l_Lean_Expr_mdataExpr_x21(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
else
{
lean_object* x_17; 
lean_dec(x_12);
x_17 = lean_box(0);
return x_17;
}
}
}
}
else
{
lean_object* x_18; 
x_18 = lean_box(0);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_patternWithRef_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_patternWithRef_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Lean_isPatternWithRef(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_patternWithRef_x3f(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_box(0);
x_4 = lean_unbox(x_3);
return x_4;
}
else
{
lean_object* x_5; uint8_t x_6; 
lean_dec(x_2);
x_5 = lean_box(1);
x_6 = lean_unbox(x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isPatternWithRef___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_isPatternWithRef(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPatternWithRef(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_patternWithRef_x3f(x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = l_Lean_KVMap_empty;
x_5 = l___private_Lean_Expr_0__Lean_patternRefAnnotationKey;
x_6 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_6, 0, x_2);
x_7 = l_Lean_KVMap_insert(x_4, x_5, x_6);
x_8 = l_Lean_Expr_mdata___override(x_7, x_1);
return x_8;
}
else
{
lean_dec(x_3);
lean_dec(x_2);
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Lean_patternAnnotation_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_inaccessible_x3f(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = l_Lean_patternWithRef_x3f(x_1);
if (lean_obj_tag(x_3) == 0)
{
return x_2;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
lean_ctor_set(x_3, 0, x_6);
return x_3;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
lean_dec(x_3);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
}
else
{
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Lean_patternAnnotation_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_patternAnnotation_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLHSGoalRaw(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_mk_string_unchecked("_lhsGoal", 8, 8);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = l_Lean_mkAnnotation(x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isLHSGoal_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_mk_string_unchecked("_lhsGoal", 8, 8);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = l_Lean_annotation_x3f(x_3, x_1);
lean_dec(x_3);
if (lean_obj_tag(x_4) == 0)
{
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_mk_string_unchecked("Eq", 2, 2);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_unsigned_to_nat(3u);
x_10 = l_Lean_Expr_isAppOfArity(x_6, x_8, x_9);
lean_dec(x_8);
if (x_10 == 0)
{
lean_object* x_11; 
lean_free_object(x_4);
lean_dec(x_6);
x_11 = lean_box(0);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Lean_Expr_appFn_x21(x_6);
lean_dec(x_6);
x_13 = l_Lean_Expr_appArg_x21(x_12);
lean_dec(x_12);
lean_ctor_set(x_4, 0, x_13);
return x_4;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_ctor_get(x_4, 0);
lean_inc(x_14);
lean_dec(x_4);
x_15 = lean_mk_string_unchecked("Eq", 2, 2);
x_16 = l_Lean_Name_mkStr1(x_15);
x_17 = lean_unsigned_to_nat(3u);
x_18 = l_Lean_Expr_isAppOfArity(x_14, x_16, x_17);
lean_dec(x_16);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_14);
x_19 = lean_box(0);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = l_Lean_Expr_appFn_x21(x_14);
lean_dec(x_14);
x_21 = l_Lean_Expr_appArg_x21(x_20);
lean_dec(x_20);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isLHSGoal_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_isLHSGoal_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_2(x_1, lean_box(0), x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_inc(x_1);
x_4 = l_Lean_mkFreshId(lean_box(0), x_1, x_2);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_alloc_closure((void*)(l_Lean_mkFreshFVarId___redArg___lam__0), 2, 1);
lean_closure_set(x_7, 0, x_6);
x_8 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_4, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_mkFreshFVarId___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshMVarId___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_inc(x_1);
x_4 = l_Lean_mkFreshId(lean_box(0), x_1, x_2);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_alloc_closure((void*)(l_Lean_mkFreshFVarId___redArg___lam__0), 2, 1);
lean_closure_set(x_7, 0, x_6);
x_8 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_4, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshMVarId(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_mkFreshMVarId___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshLMVarId___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_inc(x_1);
x_4 = l_Lean_mkFreshId(lean_box(0), x_1, x_2);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_alloc_closure((void*)(l_Lean_mkFreshFVarId___redArg___lam__0), 2, 1);
lean_closure_set(x_7, 0, x_6);
x_8 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_4, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshLMVarId(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_mkFreshLMVarId___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNot(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_mk_string_unchecked("Not", 3, 3);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_box(0);
x_5 = l_Lean_Expr_const___override(x_3, x_4);
x_6 = l_Lean_Expr_app___override(x_5, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_mkOr(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_mk_string_unchecked("Or", 2, 2);
x_4 = l_Lean_Name_mkStr1(x_3);
x_5 = lean_box(0);
x_6 = l_Lean_Expr_const___override(x_4, x_5);
x_7 = l_Lean_mkAppB(x_6, x_1, x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAnd(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_mk_string_unchecked("And", 3, 3);
x_4 = l_Lean_Name_mkStr1(x_3);
x_5 = lean_box(0);
x_6 = l_Lean_Expr_const___override(x_4, x_5);
x_7 = l_Lean_mkAppB(x_6, x_1, x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAndN(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_mk_string_unchecked("True", 4, 4);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_box(0);
x_5 = l_Lean_Expr_const___override(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = l_Lean_mkAndN(x_6);
x_10 = l_Lean_mkAnd(x_8, x_9);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkEM(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_mk_string_unchecked("Classical", 9, 9);
x_3 = lean_mk_string_unchecked("em", 2, 2);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(0);
x_6 = l_Lean_Expr_const___override(x_4, x_5);
x_7 = l_Lean_Expr_app___override(x_6, x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIff(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_mk_string_unchecked("Iff", 3, 3);
x_4 = l_Lean_Name_mkStr1(x_3);
x_5 = lean_box(0);
x_6 = l_Lean_Expr_const___override(x_4, x_5);
x_7 = l_Lean_mkAppB(x_6, x_1, x_2);
return x_7;
}
}
static lean_object* _init_l_Lean_Nat_mkType() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_mk_string_unchecked("Nat", 3, 3);
x_2 = l_Lean_Name_mkStr1(x_1);
x_3 = lean_box(0);
x_4 = l_Lean_Expr_const___override(x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Nat_mkInstAdd() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_mk_string_unchecked("instAddNat", 10, 10);
x_2 = l_Lean_Name_mkStr1(x_1);
x_3 = lean_box(0);
x_4 = l_Lean_Expr_const___override(x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHAdd() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_1 = lean_mk_string_unchecked("instHAdd", 8, 8);
x_2 = l_Lean_Name_mkStr1(x_1);
x_3 = lean_box(0);
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
x_6 = l_Lean_Expr_const___override(x_2, x_5);
x_7 = l_Lean_Nat_mkType;
x_8 = l_Lean_Nat_mkInstAdd;
x_9 = l_Lean_mkAppB(x_6, x_7, x_8);
return x_9;
}
}
static lean_object* _init_l_Lean_Nat_mkInstSub() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_mk_string_unchecked("instSubNat", 10, 10);
x_2 = l_Lean_Name_mkStr1(x_1);
x_3 = lean_box(0);
x_4 = l_Lean_Expr_const___override(x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHSub() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_1 = lean_mk_string_unchecked("instHSub", 8, 8);
x_2 = l_Lean_Name_mkStr1(x_1);
x_3 = lean_box(0);
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
x_6 = l_Lean_Expr_const___override(x_2, x_5);
x_7 = l_Lean_Nat_mkType;
x_8 = l_Lean_Nat_mkInstSub;
x_9 = l_Lean_mkAppB(x_6, x_7, x_8);
return x_9;
}
}
static lean_object* _init_l_Lean_Nat_mkInstMul() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_mk_string_unchecked("instMulNat", 10, 10);
x_2 = l_Lean_Name_mkStr1(x_1);
x_3 = lean_box(0);
x_4 = l_Lean_Expr_const___override(x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHMul() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_1 = lean_mk_string_unchecked("instHMul", 8, 8);
x_2 = l_Lean_Name_mkStr1(x_1);
x_3 = lean_box(0);
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
x_6 = l_Lean_Expr_const___override(x_2, x_5);
x_7 = l_Lean_Nat_mkType;
x_8 = l_Lean_Nat_mkInstMul;
x_9 = l_Lean_mkAppB(x_6, x_7, x_8);
return x_9;
}
}
static lean_object* _init_l_Lean_Nat_mkInstDiv() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_mk_string_unchecked("Nat", 3, 3);
x_2 = lean_mk_string_unchecked("instDiv", 7, 7);
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
x_4 = lean_box(0);
x_5 = l_Lean_Expr_const___override(x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHDiv() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_1 = lean_mk_string_unchecked("instHDiv", 8, 8);
x_2 = l_Lean_Name_mkStr1(x_1);
x_3 = lean_box(0);
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
x_6 = l_Lean_Expr_const___override(x_2, x_5);
x_7 = l_Lean_Nat_mkType;
x_8 = l_Lean_Nat_mkInstDiv;
x_9 = l_Lean_mkAppB(x_6, x_7, x_8);
return x_9;
}
}
static lean_object* _init_l_Lean_Nat_mkInstMod() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_mk_string_unchecked("Nat", 3, 3);
x_2 = lean_mk_string_unchecked("instMod", 7, 7);
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
x_4 = lean_box(0);
x_5 = l_Lean_Expr_const___override(x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHMod() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_1 = lean_mk_string_unchecked("instHMod", 8, 8);
x_2 = l_Lean_Name_mkStr1(x_1);
x_3 = lean_box(0);
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
x_6 = l_Lean_Expr_const___override(x_2, x_5);
x_7 = l_Lean_Nat_mkType;
x_8 = l_Lean_Nat_mkInstMod;
x_9 = l_Lean_mkAppB(x_6, x_7, x_8);
return x_9;
}
}
static lean_object* _init_l_Lean_Nat_mkInstNatPow() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_mk_string_unchecked("instNatPowNat", 13, 13);
x_2 = l_Lean_Name_mkStr1(x_1);
x_3 = lean_box(0);
x_4 = l_Lean_Expr_const___override(x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Nat_mkInstPow() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_1 = lean_mk_string_unchecked("instPowNat", 10, 10);
x_2 = l_Lean_Name_mkStr1(x_1);
x_3 = lean_box(0);
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
x_6 = l_Lean_Expr_const___override(x_2, x_5);
x_7 = l_Lean_Nat_mkType;
x_8 = l_Lean_Nat_mkInstNatPow;
x_9 = l_Lean_mkAppB(x_6, x_7, x_8);
return x_9;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHPow() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_1 = lean_mk_string_unchecked("instHPow", 8, 8);
x_2 = l_Lean_Name_mkStr1(x_1);
x_3 = lean_box(0);
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
x_7 = l_Lean_Expr_const___override(x_2, x_6);
x_8 = l_Lean_Nat_mkType;
x_9 = l_Lean_Nat_mkInstPow;
x_10 = l_Lean_mkApp3(x_7, x_8, x_8, x_9);
return x_10;
}
}
static lean_object* _init_l_Lean_Nat_mkInstLT() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_mk_string_unchecked("instLTNat", 9, 9);
x_2 = l_Lean_Name_mkStr1(x_1);
x_3 = lean_box(0);
x_4 = l_Lean_Expr_const___override(x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Nat_mkInstLE() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_mk_string_unchecked("instLENat", 9, 9);
x_2 = l_Lean_Name_mkStr1(x_1);
x_3 = lean_box(0);
x_4 = l_Lean_Expr_const___override(x_2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natAddFn() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_1 = lean_mk_string_unchecked("HAdd", 4, 4);
x_2 = lean_mk_string_unchecked("hAdd", 4, 4);
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_Level_ofNat(x_4);
x_6 = lean_box(0);
lean_inc(x_5);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
lean_inc(x_5);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Lean_Expr_const___override(x_3, x_9);
x_11 = l_Lean_Nat_mkType;
x_12 = l_Lean_Nat_mkInstHAdd;
x_13 = l_Lean_mkApp4(x_10, x_11, x_11, x_11, x_12);
return x_13;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natSubFn() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_1 = lean_mk_string_unchecked("HSub", 4, 4);
x_2 = lean_mk_string_unchecked("hSub", 4, 4);
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_Level_ofNat(x_4);
x_6 = lean_box(0);
lean_inc(x_5);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
lean_inc(x_5);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Lean_Expr_const___override(x_3, x_9);
x_11 = l_Lean_Nat_mkType;
x_12 = l_Lean_Nat_mkInstHSub;
x_13 = l_Lean_mkApp4(x_10, x_11, x_11, x_11, x_12);
return x_13;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natMulFn() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_1 = lean_mk_string_unchecked("HMul", 4, 4);
x_2 = lean_mk_string_unchecked("hMul", 4, 4);
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_Level_ofNat(x_4);
x_6 = lean_box(0);
lean_inc(x_5);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
lean_inc(x_5);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Lean_Expr_const___override(x_3, x_9);
x_11 = l_Lean_Nat_mkType;
x_12 = l_Lean_Nat_mkInstHMul;
x_13 = l_Lean_mkApp4(x_10, x_11, x_11, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatSucc(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_mk_string_unchecked("Nat", 3, 3);
x_3 = lean_mk_string_unchecked("succ", 4, 4);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(0);
x_6 = l_Lean_Expr_const___override(x_4, x_5);
x_7 = l_Lean_Expr_app___override(x_6, x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatAdd(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l___private_Lean_Expr_0__Lean_natAddFn;
x_4 = l_Lean_mkAppB(x_3, x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatSub(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l___private_Lean_Expr_0__Lean_natSubFn;
x_4 = l_Lean_mkAppB(x_3, x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatMul(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l___private_Lean_Expr_0__Lean_natMulFn;
x_4 = l_Lean_mkAppB(x_3, x_1, x_2);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natLEPred() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_1 = lean_mk_string_unchecked("LE", 2, 2);
x_2 = lean_mk_string_unchecked("le", 2, 2);
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_Level_ofNat(x_4);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
x_8 = l_Lean_Expr_const___override(x_3, x_7);
x_9 = l_Lean_Nat_mkType;
x_10 = l_Lean_Nat_mkInstLE;
x_11 = l_Lean_mkAppB(x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatLE(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l___private_Lean_Expr_0__Lean_natLEPred;
x_4 = l_Lean_mkAppB(x_3, x_1, x_2);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natEqPred() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_1 = lean_mk_string_unchecked("Eq", 2, 2);
x_2 = l_Lean_Name_mkStr1(x_1);
x_3 = lean_unsigned_to_nat(1u);
x_4 = l_Lean_Level_ofNat(x_3);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
x_7 = l_Lean_Expr_const___override(x_2, x_6);
x_8 = l_Lean_Nat_mkType;
x_9 = l_Lean_Expr_app___override(x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatEq(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l___private_Lean_Expr_0__Lean_natEqPred;
x_4 = l_Lean_mkAppB(x_3, x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPropEq(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_3 = lean_mk_string_unchecked("Eq", 2, 2);
x_4 = l_Lean_Name_mkStr1(x_3);
x_5 = l_Lean_levelOne;
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
x_8 = l_Lean_Expr_const___override(x_4, x_7);
x_9 = lean_box(0);
x_10 = l_Lean_Expr_sort___override(x_9);
x_11 = l_Lean_mkApp3(x_8, x_10, x_1, x_2);
return x_11;
}
}
static lean_object* _init_l_Lean_Int_mkType() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_mk_string_unchecked("Int", 3, 3);
x_2 = l_Lean_Name_mkStr1(x_1);
x_3 = lean_box(0);
x_4 = l_Lean_Expr_const___override(x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Int_mkInstNeg() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_mk_string_unchecked("Int", 3, 3);
x_2 = lean_mk_string_unchecked("instNegInt", 10, 10);
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
x_4 = lean_box(0);
x_5 = l_Lean_Expr_const___override(x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Int_mkInstAdd() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_mk_string_unchecked("Int", 3, 3);
x_2 = lean_mk_string_unchecked("instAdd", 7, 7);
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
x_4 = lean_box(0);
x_5 = l_Lean_Expr_const___override(x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Int_mkInstHAdd() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_1 = lean_mk_string_unchecked("instHAdd", 8, 8);
x_2 = l_Lean_Name_mkStr1(x_1);
x_3 = lean_box(0);
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
x_6 = l_Lean_Expr_const___override(x_2, x_5);
x_7 = l_Lean_Int_mkType;
x_8 = l_Lean_Int_mkInstAdd;
x_9 = l_Lean_mkAppB(x_6, x_7, x_8);
return x_9;
}
}
static lean_object* _init_l_Lean_Int_mkInstSub() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_mk_string_unchecked("Int", 3, 3);
x_2 = lean_mk_string_unchecked("instSub", 7, 7);
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
x_4 = lean_box(0);
x_5 = l_Lean_Expr_const___override(x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Int_mkInstHSub() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_1 = lean_mk_string_unchecked("instHSub", 8, 8);
x_2 = l_Lean_Name_mkStr1(x_1);
x_3 = lean_box(0);
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
x_6 = l_Lean_Expr_const___override(x_2, x_5);
x_7 = l_Lean_Int_mkType;
x_8 = l_Lean_Int_mkInstSub;
x_9 = l_Lean_mkAppB(x_6, x_7, x_8);
return x_9;
}
}
static lean_object* _init_l_Lean_Int_mkInstMul() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_mk_string_unchecked("Int", 3, 3);
x_2 = lean_mk_string_unchecked("instMul", 7, 7);
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
x_4 = lean_box(0);
x_5 = l_Lean_Expr_const___override(x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Int_mkInstHMul() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_1 = lean_mk_string_unchecked("instHMul", 8, 8);
x_2 = l_Lean_Name_mkStr1(x_1);
x_3 = lean_box(0);
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
x_6 = l_Lean_Expr_const___override(x_2, x_5);
x_7 = l_Lean_Int_mkType;
x_8 = l_Lean_Int_mkInstMul;
x_9 = l_Lean_mkAppB(x_6, x_7, x_8);
return x_9;
}
}
static lean_object* _init_l_Lean_Int_mkInstDiv() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_mk_string_unchecked("Int", 3, 3);
x_2 = lean_mk_string_unchecked("instDiv", 7, 7);
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
x_4 = lean_box(0);
x_5 = l_Lean_Expr_const___override(x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Int_mkInstHDiv() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_1 = lean_mk_string_unchecked("instHDiv", 8, 8);
x_2 = l_Lean_Name_mkStr1(x_1);
x_3 = lean_box(0);
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
x_6 = l_Lean_Expr_const___override(x_2, x_5);
x_7 = l_Lean_Int_mkType;
x_8 = l_Lean_Int_mkInstDiv;
x_9 = l_Lean_mkAppB(x_6, x_7, x_8);
return x_9;
}
}
static lean_object* _init_l_Lean_Int_mkInstMod() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_mk_string_unchecked("Int", 3, 3);
x_2 = lean_mk_string_unchecked("instMod", 7, 7);
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
x_4 = lean_box(0);
x_5 = l_Lean_Expr_const___override(x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Int_mkInstHMod() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_1 = lean_mk_string_unchecked("instHMod", 8, 8);
x_2 = l_Lean_Name_mkStr1(x_1);
x_3 = lean_box(0);
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
x_6 = l_Lean_Expr_const___override(x_2, x_5);
x_7 = l_Lean_Int_mkType;
x_8 = l_Lean_Int_mkInstMod;
x_9 = l_Lean_mkAppB(x_6, x_7, x_8);
return x_9;
}
}
static lean_object* _init_l_Lean_Int_mkInstPow() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_mk_string_unchecked("Int", 3, 3);
x_2 = lean_mk_string_unchecked("instNatPow", 10, 10);
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
x_4 = lean_box(0);
x_5 = l_Lean_Expr_const___override(x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Int_mkInstPowNat() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_1 = lean_mk_string_unchecked("instPowNat", 10, 10);
x_2 = l_Lean_Name_mkStr1(x_1);
x_3 = lean_box(0);
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
x_6 = l_Lean_Expr_const___override(x_2, x_5);
x_7 = l_Lean_Int_mkType;
x_8 = l_Lean_Int_mkInstPow;
x_9 = l_Lean_mkAppB(x_6, x_7, x_8);
return x_9;
}
}
static lean_object* _init_l_Lean_Int_mkInstHPow() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_1 = lean_mk_string_unchecked("instHPow", 8, 8);
x_2 = l_Lean_Name_mkStr1(x_1);
x_3 = lean_box(0);
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
x_7 = l_Lean_Expr_const___override(x_2, x_6);
x_8 = l_Lean_Int_mkType;
x_9 = l_Lean_Nat_mkType;
x_10 = l_Lean_Int_mkInstPowNat;
x_11 = l_Lean_mkApp3(x_7, x_8, x_9, x_10);
return x_11;
}
}
static lean_object* _init_l_Lean_Int_mkInstLT() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_mk_string_unchecked("Int", 3, 3);
x_2 = lean_mk_string_unchecked("instLTInt", 9, 9);
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
x_4 = lean_box(0);
x_5 = l_Lean_Expr_const___override(x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Int_mkInstLE() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_mk_string_unchecked("Int", 3, 3);
x_2 = lean_mk_string_unchecked("instLEInt", 9, 9);
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
x_4 = lean_box(0);
x_5 = l_Lean_Expr_const___override(x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Int_mkInstNatCast() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_mk_string_unchecked("instNatCastInt", 14, 14);
x_2 = l_Lean_Name_mkStr1(x_1);
x_3 = lean_box(0);
x_4 = l_Lean_Expr_const___override(x_2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intNegFn() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_1 = lean_mk_string_unchecked("Neg", 3, 3);
x_2 = lean_mk_string_unchecked("neg", 3, 3);
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_Level_ofNat(x_4);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
x_8 = l_Lean_Expr_const___override(x_3, x_7);
x_9 = l_Lean_Int_mkType;
x_10 = l_Lean_Int_mkInstNeg;
x_11 = l_Lean_mkAppB(x_8, x_9, x_10);
return x_11;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intAddFn() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_1 = lean_mk_string_unchecked("HAdd", 4, 4);
x_2 = lean_mk_string_unchecked("hAdd", 4, 4);
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_Level_ofNat(x_4);
x_6 = lean_box(0);
lean_inc(x_5);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
lean_inc(x_5);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Lean_Expr_const___override(x_3, x_9);
x_11 = l_Lean_Int_mkType;
x_12 = l_Lean_Int_mkInstHAdd;
x_13 = l_Lean_mkApp4(x_10, x_11, x_11, x_11, x_12);
return x_13;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intSubFn() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_1 = lean_mk_string_unchecked("HSub", 4, 4);
x_2 = lean_mk_string_unchecked("hSub", 4, 4);
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_Level_ofNat(x_4);
x_6 = lean_box(0);
lean_inc(x_5);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
lean_inc(x_5);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Lean_Expr_const___override(x_3, x_9);
x_11 = l_Lean_Int_mkType;
x_12 = l_Lean_Int_mkInstHSub;
x_13 = l_Lean_mkApp4(x_10, x_11, x_11, x_11, x_12);
return x_13;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intMulFn() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_1 = lean_mk_string_unchecked("HMul", 4, 4);
x_2 = lean_mk_string_unchecked("hMul", 4, 4);
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_Level_ofNat(x_4);
x_6 = lean_box(0);
lean_inc(x_5);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
lean_inc(x_5);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Lean_Expr_const___override(x_3, x_9);
x_11 = l_Lean_Int_mkType;
x_12 = l_Lean_Int_mkInstHMul;
x_13 = l_Lean_mkApp4(x_10, x_11, x_11, x_11, x_12);
return x_13;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intDivFn() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_1 = lean_mk_string_unchecked("HDiv", 4, 4);
x_2 = lean_mk_string_unchecked("hDiv", 4, 4);
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_Level_ofNat(x_4);
x_6 = lean_box(0);
lean_inc(x_5);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
lean_inc(x_5);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Lean_Expr_const___override(x_3, x_9);
x_11 = l_Lean_Int_mkType;
x_12 = l_Lean_Int_mkInstHDiv;
x_13 = l_Lean_mkApp4(x_10, x_11, x_11, x_11, x_12);
return x_13;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intModFn() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_1 = lean_mk_string_unchecked("HMod", 4, 4);
x_2 = lean_mk_string_unchecked("hMod", 4, 4);
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_Level_ofNat(x_4);
x_6 = lean_box(0);
lean_inc(x_5);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
lean_inc(x_5);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Lean_Expr_const___override(x_3, x_9);
x_11 = l_Lean_Int_mkType;
x_12 = l_Lean_Int_mkInstHMod;
x_13 = l_Lean_mkApp4(x_10, x_11, x_11, x_11, x_12);
return x_13;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intNatCastFn() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_1 = lean_mk_string_unchecked("NatCast", 7, 7);
x_2 = lean_mk_string_unchecked("natCast", 7, 7);
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_Level_ofNat(x_4);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
x_8 = l_Lean_Expr_const___override(x_3, x_7);
x_9 = l_Lean_Int_mkType;
x_10 = l_Lean_Int_mkInstNatCast;
x_11 = l_Lean_mkAppB(x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntNeg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l___private_Lean_Expr_0__Lean_intNegFn;
x_3 = l_Lean_Expr_app___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntAdd(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l___private_Lean_Expr_0__Lean_intAddFn;
x_4 = l_Lean_mkAppB(x_3, x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntSub(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l___private_Lean_Expr_0__Lean_intSubFn;
x_4 = l_Lean_mkAppB(x_3, x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntMul(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l___private_Lean_Expr_0__Lean_intMulFn;
x_4 = l_Lean_mkAppB(x_3, x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntDiv(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l___private_Lean_Expr_0__Lean_intDivFn;
x_4 = l_Lean_mkAppB(x_3, x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntMod(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l___private_Lean_Expr_0__Lean_intModFn;
x_4 = l_Lean_mkAppB(x_3, x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntNatCast(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l___private_Lean_Expr_0__Lean_intNatCastFn;
x_3 = l_Lean_Expr_app___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intLEPred() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_1 = lean_mk_string_unchecked("LE", 2, 2);
x_2 = lean_mk_string_unchecked("le", 2, 2);
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_Level_ofNat(x_4);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
x_8 = l_Lean_Expr_const___override(x_3, x_7);
x_9 = l_Lean_Int_mkType;
x_10 = l_Lean_Int_mkInstLE;
x_11 = l_Lean_mkAppB(x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntLE(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l___private_Lean_Expr_0__Lean_intLEPred;
x_4 = l_Lean_mkAppB(x_3, x_1, x_2);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intEqPred() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_1 = lean_mk_string_unchecked("Eq", 2, 2);
x_2 = l_Lean_Name_mkStr1(x_1);
x_3 = lean_unsigned_to_nat(1u);
x_4 = l_Lean_Level_ofNat(x_3);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
x_7 = l_Lean_Expr_const___override(x_2, x_6);
x_8 = l_Lean_Int_mkType;
x_9 = l_Lean_Expr_app___override(x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntEq(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l___private_Lean_Expr_0__Lean_intEqPred;
x_4 = l_Lean_mkAppB(x_3, x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntDvd(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_3 = lean_mk_string_unchecked("Dvd", 3, 3);
x_4 = lean_mk_string_unchecked("dvd", 3, 3);
x_5 = l_Lean_Name_mkStr2(x_3, x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Lean_Level_ofNat(x_6);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Lean_Expr_const___override(x_5, x_9);
x_11 = l_Lean_Int_mkType;
x_12 = lean_mk_string_unchecked("Int", 3, 3);
x_13 = lean_mk_string_unchecked("instDvd", 7, 7);
x_14 = l_Lean_Name_mkStr2(x_12, x_13);
x_15 = l_Lean_Expr_const___override(x_14, x_8);
x_16 = l_Lean_mkApp4(x_10, x_11, x_15, x_1, x_2);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntLit(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_2 = lean_nat_abs(x_1);
x_3 = l_Lean_mkRawNatLit(x_2);
x_4 = lean_mk_string_unchecked("OfNat", 5, 5);
x_5 = lean_mk_string_unchecked("ofNat", 5, 5);
x_6 = l_Lean_Name_mkStr2(x_4, x_5);
x_7 = lean_box(0);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Lean_Expr_const___override(x_6, x_9);
x_11 = l_Lean_Int_mkType;
x_12 = lean_mk_string_unchecked("instOfNat", 9, 9);
x_13 = l_Lean_Name_mkStr1(x_12);
x_14 = l_Lean_Expr_const___override(x_13, x_8);
lean_inc(x_3);
x_15 = l_Lean_Expr_app___override(x_14, x_3);
x_16 = l_Lean_mkApp3(x_10, x_11, x_3, x_15);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_to_int(x_17);
x_19 = lean_int_dec_lt(x_1, x_18);
lean_dec(x_18);
if (x_19 == 0)
{
return x_16;
}
else
{
lean_object* x_20; 
x_20 = l_Lean_mkIntNeg(x_16);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntLit___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_mkIntLit(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_reflBoolTrue() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_1 = lean_mk_string_unchecked("Eq", 2, 2);
x_2 = lean_mk_string_unchecked("refl", 4, 4);
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
x_4 = l_Lean_levelOne;
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
x_7 = l_Lean_Expr_const___override(x_3, x_6);
x_8 = lean_mk_string_unchecked("Bool", 4, 4);
lean_inc(x_8);
x_9 = l_Lean_Name_mkStr1(x_8);
x_10 = l_Lean_Expr_const___override(x_9, x_5);
x_11 = lean_mk_string_unchecked("true", 4, 4);
x_12 = l_Lean_Name_mkStr2(x_8, x_11);
x_13 = l_Lean_Expr_const___override(x_12, x_5);
x_14 = l_Lean_mkAppB(x_7, x_10, x_13);
return x_14;
}
}
lean_object* initialize_Init_Data_Hashable(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Int(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_KVMap(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_SMap(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Level(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Data_HashSet_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Expr(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Hashable(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_KVMap(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_SMap(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Level(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_HashSet_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_instInhabitedLiteral = _init_l_Lean_instInhabitedLiteral();
lean_mark_persistent(l_Lean_instInhabitedLiteral);
l_Lean_instBEqLiteral = _init_l_Lean_instBEqLiteral();
lean_mark_persistent(l_Lean_instBEqLiteral);
l_Lean_instReprLiteral = _init_l_Lean_instReprLiteral();
lean_mark_persistent(l_Lean_instReprLiteral);
l_Lean_instHashableLiteral = _init_l_Lean_instHashableLiteral();
lean_mark_persistent(l_Lean_instHashableLiteral);
l_Lean_instLTLiteral = _init_l_Lean_instLTLiteral();
lean_mark_persistent(l_Lean_instLTLiteral);
l_Lean_instInhabitedBinderInfo = _init_l_Lean_instInhabitedBinderInfo();
l_Lean_instBEqBinderInfo = _init_l_Lean_instBEqBinderInfo();
lean_mark_persistent(l_Lean_instBEqBinderInfo);
l_Lean_instReprBinderInfo = _init_l_Lean_instReprBinderInfo();
lean_mark_persistent(l_Lean_instReprBinderInfo);
l_Lean_instHashableBinderInfo = _init_l_Lean_instHashableBinderInfo();
lean_mark_persistent(l_Lean_instHashableBinderInfo);
l_Lean_MData_empty = _init_l_Lean_MData_empty();
lean_mark_persistent(l_Lean_MData_empty);
l_Lean_instInhabitedData__1 = _init_l_Lean_instInhabitedData__1();
l_Lean_instBEqData__1 = _init_l_Lean_instBEqData__1();
lean_mark_persistent(l_Lean_instBEqData__1);
l_panic___at___Lean_Expr_mkData_spec__0___boxed__const__1 = _init_l_panic___at___Lean_Expr_mkData_spec__0___boxed__const__1();
lean_mark_persistent(l_panic___at___Lean_Expr_mkData_spec__0___boxed__const__1);
l_Lean_Expr_mkAppData___boxed__const__1 = _init_l_Lean_Expr_mkAppData___boxed__const__1();
lean_mark_persistent(l_Lean_Expr_mkAppData___boxed__const__1);
l_Lean_instReprData__1 = _init_l_Lean_instReprData__1();
lean_mark_persistent(l_Lean_instReprData__1);
l_Lean_instInhabitedFVarId = _init_l_Lean_instInhabitedFVarId();
lean_mark_persistent(l_Lean_instInhabitedFVarId);
l_Lean_instBEqFVarId = _init_l_Lean_instBEqFVarId();
lean_mark_persistent(l_Lean_instBEqFVarId);
l_Lean_instHashableFVarId = _init_l_Lean_instHashableFVarId();
lean_mark_persistent(l_Lean_instHashableFVarId);
l_Lean_instReprFVarId = _init_l_Lean_instReprFVarId();
lean_mark_persistent(l_Lean_instReprFVarId);
l_Lean_instFVarIdSetInhabited = _init_l_Lean_instFVarIdSetInhabited();
lean_mark_persistent(l_Lean_instFVarIdSetInhabited);
l_Lean_instFVarIdSetEmptyCollection = _init_l_Lean_instFVarIdSetEmptyCollection();
lean_mark_persistent(l_Lean_instFVarIdSetEmptyCollection);
l_Lean_instFVarIdHashSetInhabited = _init_l_Lean_instFVarIdHashSetInhabited();
lean_mark_persistent(l_Lean_instFVarIdHashSetInhabited);
l_Lean_instFVarIdHashSetEmptyCollection = _init_l_Lean_instFVarIdHashSetEmptyCollection();
lean_mark_persistent(l_Lean_instFVarIdHashSetEmptyCollection);
l_Lean_instInhabitedMVarId = _init_l_Lean_instInhabitedMVarId();
lean_mark_persistent(l_Lean_instInhabitedMVarId);
l_Lean_instBEqMVarId = _init_l_Lean_instBEqMVarId();
lean_mark_persistent(l_Lean_instBEqMVarId);
l_Lean_instHashableMVarId = _init_l_Lean_instHashableMVarId();
lean_mark_persistent(l_Lean_instHashableMVarId);
l_Lean_instReprMVarId = _init_l_Lean_instReprMVarId();
lean_mark_persistent(l_Lean_instReprMVarId);
l_Lean_instReprMVarId__1 = _init_l_Lean_instReprMVarId__1();
lean_mark_persistent(l_Lean_instReprMVarId__1);
l_Lean_instMVarIdSetInhabited = _init_l_Lean_instMVarIdSetInhabited();
lean_mark_persistent(l_Lean_instMVarIdSetInhabited);
l_Lean_instMVarIdSetEmptyCollection = _init_l_Lean_instMVarIdSetEmptyCollection();
lean_mark_persistent(l_Lean_instMVarIdSetEmptyCollection);
l_Lean_instReprExpr = _init_l_Lean_instReprExpr();
lean_mark_persistent(l_Lean_instReprExpr);
l_Lean_instInhabitedExpr = _init_l_Lean_instInhabitedExpr();
lean_mark_persistent(l_Lean_instInhabitedExpr);
l_Lean_Expr_instHashable = _init_l_Lean_Expr_instHashable();
lean_mark_persistent(l_Lean_Expr_instHashable);
l_Lean_Expr_instBEq = _init_l_Lean_Expr_instBEq();
lean_mark_persistent(l_Lean_Expr_instBEq);
l_Lean_Expr_instToString = _init_l_Lean_Expr_instToString();
lean_mark_persistent(l_Lean_Expr_instToString);
l_Lean_instInhabitedExprStructEq = _init_l_Lean_instInhabitedExprStructEq();
lean_mark_persistent(l_Lean_instInhabitedExprStructEq);
l_Lean_instCoeExprExprStructEq = _init_l_Lean_instCoeExprExprStructEq();
lean_mark_persistent(l_Lean_instCoeExprExprStructEq);
l_Lean_ExprStructEq_instBEq = _init_l_Lean_ExprStructEq_instBEq();
lean_mark_persistent(l_Lean_ExprStructEq_instBEq);
l_Lean_ExprStructEq_instHashable = _init_l_Lean_ExprStructEq_instHashable();
lean_mark_persistent(l_Lean_ExprStructEq_instHashable);
l_Lean_ExprStructEq_instToString = _init_l_Lean_ExprStructEq_instToString();
lean_mark_persistent(l_Lean_ExprStructEq_instToString);
l___private_Lean_Expr_0__Lean_patternRefAnnotationKey = _init_l___private_Lean_Expr_0__Lean_patternRefAnnotationKey();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_patternRefAnnotationKey);
l_Lean_Nat_mkType = _init_l_Lean_Nat_mkType();
lean_mark_persistent(l_Lean_Nat_mkType);
l_Lean_Nat_mkInstAdd = _init_l_Lean_Nat_mkInstAdd();
lean_mark_persistent(l_Lean_Nat_mkInstAdd);
l_Lean_Nat_mkInstHAdd = _init_l_Lean_Nat_mkInstHAdd();
lean_mark_persistent(l_Lean_Nat_mkInstHAdd);
l_Lean_Nat_mkInstSub = _init_l_Lean_Nat_mkInstSub();
lean_mark_persistent(l_Lean_Nat_mkInstSub);
l_Lean_Nat_mkInstHSub = _init_l_Lean_Nat_mkInstHSub();
lean_mark_persistent(l_Lean_Nat_mkInstHSub);
l_Lean_Nat_mkInstMul = _init_l_Lean_Nat_mkInstMul();
lean_mark_persistent(l_Lean_Nat_mkInstMul);
l_Lean_Nat_mkInstHMul = _init_l_Lean_Nat_mkInstHMul();
lean_mark_persistent(l_Lean_Nat_mkInstHMul);
l_Lean_Nat_mkInstDiv = _init_l_Lean_Nat_mkInstDiv();
lean_mark_persistent(l_Lean_Nat_mkInstDiv);
l_Lean_Nat_mkInstHDiv = _init_l_Lean_Nat_mkInstHDiv();
lean_mark_persistent(l_Lean_Nat_mkInstHDiv);
l_Lean_Nat_mkInstMod = _init_l_Lean_Nat_mkInstMod();
lean_mark_persistent(l_Lean_Nat_mkInstMod);
l_Lean_Nat_mkInstHMod = _init_l_Lean_Nat_mkInstHMod();
lean_mark_persistent(l_Lean_Nat_mkInstHMod);
l_Lean_Nat_mkInstNatPow = _init_l_Lean_Nat_mkInstNatPow();
lean_mark_persistent(l_Lean_Nat_mkInstNatPow);
l_Lean_Nat_mkInstPow = _init_l_Lean_Nat_mkInstPow();
lean_mark_persistent(l_Lean_Nat_mkInstPow);
l_Lean_Nat_mkInstHPow = _init_l_Lean_Nat_mkInstHPow();
lean_mark_persistent(l_Lean_Nat_mkInstHPow);
l_Lean_Nat_mkInstLT = _init_l_Lean_Nat_mkInstLT();
lean_mark_persistent(l_Lean_Nat_mkInstLT);
l_Lean_Nat_mkInstLE = _init_l_Lean_Nat_mkInstLE();
lean_mark_persistent(l_Lean_Nat_mkInstLE);
l___private_Lean_Expr_0__Lean_natAddFn = _init_l___private_Lean_Expr_0__Lean_natAddFn();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_natAddFn);
l___private_Lean_Expr_0__Lean_natSubFn = _init_l___private_Lean_Expr_0__Lean_natSubFn();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_natSubFn);
l___private_Lean_Expr_0__Lean_natMulFn = _init_l___private_Lean_Expr_0__Lean_natMulFn();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_natMulFn);
l___private_Lean_Expr_0__Lean_natLEPred = _init_l___private_Lean_Expr_0__Lean_natLEPred();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_natLEPred);
l___private_Lean_Expr_0__Lean_natEqPred = _init_l___private_Lean_Expr_0__Lean_natEqPred();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_natEqPred);
l_Lean_Int_mkType = _init_l_Lean_Int_mkType();
lean_mark_persistent(l_Lean_Int_mkType);
l_Lean_Int_mkInstNeg = _init_l_Lean_Int_mkInstNeg();
lean_mark_persistent(l_Lean_Int_mkInstNeg);
l_Lean_Int_mkInstAdd = _init_l_Lean_Int_mkInstAdd();
lean_mark_persistent(l_Lean_Int_mkInstAdd);
l_Lean_Int_mkInstHAdd = _init_l_Lean_Int_mkInstHAdd();
lean_mark_persistent(l_Lean_Int_mkInstHAdd);
l_Lean_Int_mkInstSub = _init_l_Lean_Int_mkInstSub();
lean_mark_persistent(l_Lean_Int_mkInstSub);
l_Lean_Int_mkInstHSub = _init_l_Lean_Int_mkInstHSub();
lean_mark_persistent(l_Lean_Int_mkInstHSub);
l_Lean_Int_mkInstMul = _init_l_Lean_Int_mkInstMul();
lean_mark_persistent(l_Lean_Int_mkInstMul);
l_Lean_Int_mkInstHMul = _init_l_Lean_Int_mkInstHMul();
lean_mark_persistent(l_Lean_Int_mkInstHMul);
l_Lean_Int_mkInstDiv = _init_l_Lean_Int_mkInstDiv();
lean_mark_persistent(l_Lean_Int_mkInstDiv);
l_Lean_Int_mkInstHDiv = _init_l_Lean_Int_mkInstHDiv();
lean_mark_persistent(l_Lean_Int_mkInstHDiv);
l_Lean_Int_mkInstMod = _init_l_Lean_Int_mkInstMod();
lean_mark_persistent(l_Lean_Int_mkInstMod);
l_Lean_Int_mkInstHMod = _init_l_Lean_Int_mkInstHMod();
lean_mark_persistent(l_Lean_Int_mkInstHMod);
l_Lean_Int_mkInstPow = _init_l_Lean_Int_mkInstPow();
lean_mark_persistent(l_Lean_Int_mkInstPow);
l_Lean_Int_mkInstPowNat = _init_l_Lean_Int_mkInstPowNat();
lean_mark_persistent(l_Lean_Int_mkInstPowNat);
l_Lean_Int_mkInstHPow = _init_l_Lean_Int_mkInstHPow();
lean_mark_persistent(l_Lean_Int_mkInstHPow);
l_Lean_Int_mkInstLT = _init_l_Lean_Int_mkInstLT();
lean_mark_persistent(l_Lean_Int_mkInstLT);
l_Lean_Int_mkInstLE = _init_l_Lean_Int_mkInstLE();
lean_mark_persistent(l_Lean_Int_mkInstLE);
l_Lean_Int_mkInstNatCast = _init_l_Lean_Int_mkInstNatCast();
lean_mark_persistent(l_Lean_Int_mkInstNatCast);
l___private_Lean_Expr_0__Lean_intNegFn = _init_l___private_Lean_Expr_0__Lean_intNegFn();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_intNegFn);
l___private_Lean_Expr_0__Lean_intAddFn = _init_l___private_Lean_Expr_0__Lean_intAddFn();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_intAddFn);
l___private_Lean_Expr_0__Lean_intSubFn = _init_l___private_Lean_Expr_0__Lean_intSubFn();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_intSubFn);
l___private_Lean_Expr_0__Lean_intMulFn = _init_l___private_Lean_Expr_0__Lean_intMulFn();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_intMulFn);
l___private_Lean_Expr_0__Lean_intDivFn = _init_l___private_Lean_Expr_0__Lean_intDivFn();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_intDivFn);
l___private_Lean_Expr_0__Lean_intModFn = _init_l___private_Lean_Expr_0__Lean_intModFn();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_intModFn);
l___private_Lean_Expr_0__Lean_intNatCastFn = _init_l___private_Lean_Expr_0__Lean_intNatCastFn();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_intNatCastFn);
l___private_Lean_Expr_0__Lean_intLEPred = _init_l___private_Lean_Expr_0__Lean_intLEPred();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_intLEPred);
l___private_Lean_Expr_0__Lean_intEqPred = _init_l___private_Lean_Expr_0__Lean_intEqPred();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_intEqPred);
l_Lean_reflBoolTrue = _init_l_Lean_reflBoolTrue();
lean_mark_persistent(l_Lean_reflBoolTrue);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
