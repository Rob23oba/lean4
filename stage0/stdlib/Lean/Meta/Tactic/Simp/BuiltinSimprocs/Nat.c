// Lean compiler output
// Module: Lean.Meta.Tactic.Simp.BuiltinSimprocs.Nat
// Imports: Init.Simproc Init.Data.Nat.Simproc Lean.Util.SafeExponentiation Lean.Meta.LitValues Lean.Meta.Offset Lean.Meta.Tactic.Simp.Simproc Lean.Meta.Tactic.Simp.BuiltinSimprocs.Util
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
lean_object* lean_nat_gcd(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceMod(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceBoolPred___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_applyEqLemma(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceSub_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_675_(lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceDvd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_evalPropStep___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceAnd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1208_(lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceSub___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceLT___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceUnary___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceNatEqExpr___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceBNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1541_(lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceLT___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_asOffset___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceDvd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_5975_(lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceBoolPred___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceSucc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceXor___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getNatValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceGcd___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceXor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceDiv_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_715_(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceBeqDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4101_(lean_object*);
LEAN_EXPORT lean_object* l_Nat_reducePow___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceOr___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceNatEqExpr___redArg___lam__4(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Nat_mkInstAdd;
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceEqDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_3868_(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceGT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1464_(lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_asOffset___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceLeDiff___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceUnary(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_applySimprocConst___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceShiftLeft_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1326_(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceXor_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1250_(lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceXor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceNatEqExpr___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceLeDiff___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reducePow_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1172_(lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceShiftLeft___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceShiftRight(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_isValue_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1715_(lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceBoolPred(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceLeDiff(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceBneDiff___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceMod___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_563_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNat(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceEqDiff___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceBin___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_isValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceBinPred___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceSubDiff___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceGcd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1384_(lean_object*);
LEAN_EXPORT lean_object* l_Nat_applySimprocConst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceBEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceBEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1499_(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceEqDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_3866_(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceMod_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_749_(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceMod_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_751_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_asOffset___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceSubDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_5562_(lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceMul_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_635_(lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceOr___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_checkExponent(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceSucc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExpr_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_559_(lean_object*);
LEAN_EXPORT lean_object* l_Nat_isValue___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceBNe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceSubDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_5564_(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceLT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1423_(lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceDvd___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_fromExpr_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceAnd___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_applyEqLemma___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceAdd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceNatEqExpr___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceOr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceOr_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1288_(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceOr_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1286_(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceBneDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4344_(lean_object*);
LEAN_EXPORT lean_object* l_Nat_applyEqLemma___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceSubDiff(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceShiftRight___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceShiftLeft_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1322_(lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceAnd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1210_(lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceGcd___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_561_(lean_object*);
LEAN_EXPORT lean_object* l_Nat_fromExpr_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceGT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1460_(lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceDiv___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceBNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1537_(lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceOr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceSucc___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceSub___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_asOffset(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceLT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1421_(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceBEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1501_(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceSub_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_673_(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_597_(lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceLT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceNatEqExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceShiftRight_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1364_(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceXor_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1246_(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceBeqDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4103_(lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceBeqDiff___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceSubDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_5560_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkGTNat(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceGT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_isValue___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceShiftLeft_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1324_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance;
lean_object* l_Lean_Meta_mkDecide(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceAdd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceXor_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1248_(lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceGT___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceGT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1462_(lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceAnd___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceAnd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1212_(lean_object*);
lean_object* lean_nat_land(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceAdd___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceBoolPred___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceShiftRight_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1362_(lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceBneDiff(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceLeDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4970_(lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceMul___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_applySimprocConst___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceBin___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceNatEqExpr___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceDvd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceMod___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceBeqDiff___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceShiftRight___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceLTLE(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceSucc___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Nat_mkInstHAdd;
LEAN_EXPORT lean_object* l_Nat_reduceEqDiff___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceBEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Nat_reduceDiv___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceBneDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4342_(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceMul_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_637_(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceMod_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_753_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExprAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_601_(lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceBNe___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceSub_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_677_(lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceAdd___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBneNat(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceEqDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_3864_(lean_object*);
LEAN_EXPORT lean_object* l_Nat_applyEqLemma___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceDiv_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_713_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExpr_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_lxor(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reducePow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkGENat(lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceLTLE___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceBin___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceBneDiff___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceEqDiff(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_registerBuiltinSimproc(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceGcd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceMul___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceShiftRight_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1360_(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceNatEqExpr___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceBEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1503_(lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceGcd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1386_(lean_object*);
LEAN_EXPORT lean_object* l_Nat_applySimprocConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_registerBuiltinDSimproc(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_matchesInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceXor___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceAnd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceBneDiff___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_isValue_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1713_(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceBeqDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4105_(lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceDiv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceGcd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceBinPred___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceBeqDiff(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_fromExpr_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reducePow_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1170_(lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceBNe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_levelOne;
lean_object* lean_nat_mul(lean_object*, lean_object*);
extern lean_object* l_Lean_reflBoolTrue;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExprAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceLTLE___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceSub(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceShiftLeft___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceBinPred(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceDiv___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceOr_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1284_(lean_object*);
lean_object* l_Lean_Meta_Simp_addSimprocBuiltinAttr(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceUnary___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_isValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceMul___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceNatEqExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reducePow___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceBneDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4346_(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_599_(lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceBinPred___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceSubDiff___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceMul_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_639_(lean_object*);
LEAN_EXPORT lean_object* l_Nat_reducePow___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceShiftLeft___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_fromExpr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceDiv_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_711_(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceLeDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4974_(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceGcd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1382_(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceBNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1539_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExprAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceBNe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reducePow_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1174_(lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceBin(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceMod___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceGT___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceLT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1425_(lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceBeqDiff___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceSubDiff___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceSub___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceShiftRight___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_consumeMData(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceDvd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_5973_(lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceAnd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceLTLE___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceMul(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExpr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceUnary___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceBEq___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceDvd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_5971_(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceLeDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4972_(lean_object*);
lean_object* lean_nat_lor(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceBEq___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceShiftLeft(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_fromExpr_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_getNatValue_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Nat_fromExpr_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_getNatValue_x3f(x_1, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Nat_fromExpr_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Nat_fromExpr_x3f___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Nat_fromExpr_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Nat_fromExpr_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceUnary___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = l_Lean_Expr_isAppOfArity(x_4, x_1, x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_9);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Lean_Expr_appArg_x21(x_4);
x_15 = l_Lean_Meta_getNatValue_x3f(x_14, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
lean_dec(x_3);
x_17 = !lean_is_exclusive(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_15, 0);
lean_dec(x_18);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_15, 0, x_20);
return x_15;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_dec(x_15);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_21);
return x_24;
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_15);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_15, 0);
lean_dec(x_26);
x_27 = !lean_is_exclusive(x_16);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_16, 0);
x_29 = lean_apply_1(x_3, x_28);
x_30 = l_Lean_mkNatLit(x_29);
lean_ctor_set_tag(x_16, 0);
lean_ctor_set(x_16, 0, x_30);
return x_15;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_16, 0);
lean_inc(x_31);
lean_dec(x_16);
x_32 = lean_apply_1(x_3, x_31);
x_33 = l_Lean_mkNatLit(x_32);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_15, 0, x_34);
return x_15;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_35 = lean_ctor_get(x_15, 1);
lean_inc(x_35);
lean_dec(x_15);
x_36 = lean_ctor_get(x_16, 0);
lean_inc(x_36);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 x_37 = x_16;
} else {
 lean_dec_ref(x_16);
 x_37 = lean_box(0);
}
x_38 = lean_apply_1(x_3, x_36);
x_39 = l_Lean_mkNatLit(x_38);
if (lean_is_scalar(x_37)) {
 x_40 = lean_alloc_ctor(0, 1, 0);
} else {
 x_40 = x_37;
 lean_ctor_set_tag(x_40, 0);
}
lean_ctor_set(x_40, 0, x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_35);
return x_41;
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_3);
x_42 = !lean_is_exclusive(x_15);
if (x_42 == 0)
{
return x_15;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_15, 0);
x_44 = lean_ctor_get(x_15, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_15);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceUnary(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = l_Lean_Expr_isAppOfArity(x_4, x_1, x_2);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_12);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = l_Lean_Expr_appArg_x21(x_4);
x_18 = l_Lean_Meta_getNatValue_x3f(x_17, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
lean_dec(x_3);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_18, 0);
lean_dec(x_21);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_18, 0, x_23);
return x_18;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_18, 1);
lean_inc(x_24);
lean_dec(x_18);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_24);
return x_27;
}
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_18);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_18, 0);
lean_dec(x_29);
x_30 = !lean_is_exclusive(x_19);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_19, 0);
x_32 = lean_apply_1(x_3, x_31);
x_33 = l_Lean_mkNatLit(x_32);
lean_ctor_set_tag(x_19, 0);
lean_ctor_set(x_19, 0, x_33);
return x_18;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_19, 0);
lean_inc(x_34);
lean_dec(x_19);
x_35 = lean_apply_1(x_3, x_34);
x_36 = l_Lean_mkNatLit(x_35);
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_18, 0, x_37);
return x_18;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_38 = lean_ctor_get(x_18, 1);
lean_inc(x_38);
lean_dec(x_18);
x_39 = lean_ctor_get(x_19, 0);
lean_inc(x_39);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 x_40 = x_19;
} else {
 lean_dec_ref(x_19);
 x_40 = lean_box(0);
}
x_41 = lean_apply_1(x_3, x_39);
x_42 = l_Lean_mkNatLit(x_41);
if (lean_is_scalar(x_40)) {
 x_43 = lean_alloc_ctor(0, 1, 0);
} else {
 x_43 = x_40;
 lean_ctor_set_tag(x_43, 0);
}
lean_ctor_set(x_43, 0, x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_38);
return x_44;
}
}
}
else
{
uint8_t x_45; 
lean_dec(x_3);
x_45 = !lean_is_exclusive(x_18);
if (x_45 == 0)
{
return x_18;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_18, 0);
x_47 = lean_ctor_get(x_18, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_18);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceUnary___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Nat_reduceUnary___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceUnary___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Nat_reduceUnary(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBin___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = l_Lean_Expr_isAppOfArity(x_4, x_1, x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_9);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = l_Lean_Expr_appFn_x21(x_4);
x_15 = l_Lean_Expr_appArg_x21(x_14);
lean_dec(x_14);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_16 = l_Lean_Meta_getNatValue_x3f(x_15, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_16, 0);
lean_dec(x_19);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_16, 0, x_21);
return x_16;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_16, 1);
lean_inc(x_22);
lean_dec(x_16);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_22);
return x_25;
}
}
else
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_16, 1);
lean_inc(x_26);
lean_dec(x_16);
x_27 = !lean_is_exclusive(x_17);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_17, 0);
x_29 = l_Lean_Expr_appArg_x21(x_4);
x_30 = l_Lean_Meta_getNatValue_x3f(x_29, x_5, x_6, x_7, x_8, x_26);
lean_dec(x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
lean_dec(x_28);
lean_dec(x_3);
x_32 = !lean_is_exclusive(x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_30, 0);
lean_dec(x_33);
x_34 = lean_box(0);
lean_ctor_set_tag(x_17, 2);
lean_ctor_set(x_17, 0, x_34);
lean_ctor_set(x_30, 0, x_17);
return x_30;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_30, 1);
lean_inc(x_35);
lean_dec(x_30);
x_36 = lean_box(0);
lean_ctor_set_tag(x_17, 2);
lean_ctor_set(x_17, 0, x_36);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_17);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
else
{
uint8_t x_38; 
lean_free_object(x_17);
x_38 = !lean_is_exclusive(x_30);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_30, 0);
lean_dec(x_39);
x_40 = !lean_is_exclusive(x_31);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_31, 0);
x_42 = lean_apply_2(x_3, x_28, x_41);
x_43 = l_Lean_mkNatLit(x_42);
lean_ctor_set_tag(x_31, 0);
lean_ctor_set(x_31, 0, x_43);
return x_30;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_44 = lean_ctor_get(x_31, 0);
lean_inc(x_44);
lean_dec(x_31);
x_45 = lean_apply_2(x_3, x_28, x_44);
x_46 = l_Lean_mkNatLit(x_45);
x_47 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_30, 0, x_47);
return x_30;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_48 = lean_ctor_get(x_30, 1);
lean_inc(x_48);
lean_dec(x_30);
x_49 = lean_ctor_get(x_31, 0);
lean_inc(x_49);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 x_50 = x_31;
} else {
 lean_dec_ref(x_31);
 x_50 = lean_box(0);
}
x_51 = lean_apply_2(x_3, x_28, x_49);
x_52 = l_Lean_mkNatLit(x_51);
if (lean_is_scalar(x_50)) {
 x_53 = lean_alloc_ctor(0, 1, 0);
} else {
 x_53 = x_50;
 lean_ctor_set_tag(x_53, 0);
}
lean_ctor_set(x_53, 0, x_52);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_48);
return x_54;
}
}
}
else
{
uint8_t x_55; 
lean_free_object(x_17);
lean_dec(x_28);
lean_dec(x_3);
x_55 = !lean_is_exclusive(x_30);
if (x_55 == 0)
{
return x_30;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_30, 0);
x_57 = lean_ctor_get(x_30, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_30);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_17, 0);
lean_inc(x_59);
lean_dec(x_17);
x_60 = l_Lean_Expr_appArg_x21(x_4);
x_61 = l_Lean_Meta_getNatValue_x3f(x_60, x_5, x_6, x_7, x_8, x_26);
lean_dec(x_60);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_59);
lean_dec(x_3);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_64 = x_61;
} else {
 lean_dec_ref(x_61);
 x_64 = lean_box(0);
}
x_65 = lean_box(0);
x_66 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_66, 0, x_65);
if (lean_is_scalar(x_64)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_64;
}
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_63);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_68 = lean_ctor_get(x_61, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_69 = x_61;
} else {
 lean_dec_ref(x_61);
 x_69 = lean_box(0);
}
x_70 = lean_ctor_get(x_62, 0);
lean_inc(x_70);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 x_71 = x_62;
} else {
 lean_dec_ref(x_62);
 x_71 = lean_box(0);
}
x_72 = lean_apply_2(x_3, x_59, x_70);
x_73 = l_Lean_mkNatLit(x_72);
if (lean_is_scalar(x_71)) {
 x_74 = lean_alloc_ctor(0, 1, 0);
} else {
 x_74 = x_71;
 lean_ctor_set_tag(x_74, 0);
}
lean_ctor_set(x_74, 0, x_73);
if (lean_is_scalar(x_69)) {
 x_75 = lean_alloc_ctor(0, 2, 0);
} else {
 x_75 = x_69;
}
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_68);
return x_75;
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_59);
lean_dec(x_3);
x_76 = lean_ctor_get(x_61, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_61, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_78 = x_61;
} else {
 lean_dec_ref(x_61);
 x_78 = lean_box(0);
}
if (lean_is_scalar(x_78)) {
 x_79 = lean_alloc_ctor(1, 2, 0);
} else {
 x_79 = x_78;
}
lean_ctor_set(x_79, 0, x_76);
lean_ctor_set(x_79, 1, x_77);
return x_79;
}
}
}
}
else
{
uint8_t x_80; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_80 = !lean_is_exclusive(x_16);
if (x_80 == 0)
{
return x_16;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_16, 0);
x_82 = lean_ctor_get(x_16, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_16);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBin(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = l_Lean_Expr_isAppOfArity(x_4, x_1, x_2);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_12);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = l_Lean_Expr_appFn_x21(x_4);
x_18 = l_Lean_Expr_appArg_x21(x_17);
lean_dec(x_17);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_19 = l_Lean_Meta_getNatValue_x3f(x_18, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_19, 0);
lean_dec(x_22);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_19, 0, x_24);
return x_19;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_19, 1);
lean_inc(x_25);
lean_dec(x_19);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_25);
return x_28;
}
}
else
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_19, 1);
lean_inc(x_29);
lean_dec(x_19);
x_30 = !lean_is_exclusive(x_20);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_20, 0);
x_32 = l_Lean_Expr_appArg_x21(x_4);
x_33 = l_Lean_Meta_getNatValue_x3f(x_32, x_8, x_9, x_10, x_11, x_29);
lean_dec(x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
if (lean_obj_tag(x_34) == 0)
{
uint8_t x_35; 
lean_dec(x_31);
lean_dec(x_3);
x_35 = !lean_is_exclusive(x_33);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_33, 0);
lean_dec(x_36);
x_37 = lean_box(0);
lean_ctor_set_tag(x_20, 2);
lean_ctor_set(x_20, 0, x_37);
lean_ctor_set(x_33, 0, x_20);
return x_33;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_33, 1);
lean_inc(x_38);
lean_dec(x_33);
x_39 = lean_box(0);
lean_ctor_set_tag(x_20, 2);
lean_ctor_set(x_20, 0, x_39);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_20);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
else
{
uint8_t x_41; 
lean_free_object(x_20);
x_41 = !lean_is_exclusive(x_33);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_33, 0);
lean_dec(x_42);
x_43 = !lean_is_exclusive(x_34);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_34, 0);
x_45 = lean_apply_2(x_3, x_31, x_44);
x_46 = l_Lean_mkNatLit(x_45);
lean_ctor_set_tag(x_34, 0);
lean_ctor_set(x_34, 0, x_46);
return x_33;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_47 = lean_ctor_get(x_34, 0);
lean_inc(x_47);
lean_dec(x_34);
x_48 = lean_apply_2(x_3, x_31, x_47);
x_49 = l_Lean_mkNatLit(x_48);
x_50 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_33, 0, x_50);
return x_33;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_51 = lean_ctor_get(x_33, 1);
lean_inc(x_51);
lean_dec(x_33);
x_52 = lean_ctor_get(x_34, 0);
lean_inc(x_52);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 x_53 = x_34;
} else {
 lean_dec_ref(x_34);
 x_53 = lean_box(0);
}
x_54 = lean_apply_2(x_3, x_31, x_52);
x_55 = l_Lean_mkNatLit(x_54);
if (lean_is_scalar(x_53)) {
 x_56 = lean_alloc_ctor(0, 1, 0);
} else {
 x_56 = x_53;
 lean_ctor_set_tag(x_56, 0);
}
lean_ctor_set(x_56, 0, x_55);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_51);
return x_57;
}
}
}
else
{
uint8_t x_58; 
lean_free_object(x_20);
lean_dec(x_31);
lean_dec(x_3);
x_58 = !lean_is_exclusive(x_33);
if (x_58 == 0)
{
return x_33;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_33, 0);
x_60 = lean_ctor_get(x_33, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_33);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_20, 0);
lean_inc(x_62);
lean_dec(x_20);
x_63 = l_Lean_Expr_appArg_x21(x_4);
x_64 = l_Lean_Meta_getNatValue_x3f(x_63, x_8, x_9, x_10, x_11, x_29);
lean_dec(x_63);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_62);
lean_dec(x_3);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_67 = x_64;
} else {
 lean_dec_ref(x_64);
 x_67 = lean_box(0);
}
x_68 = lean_box(0);
x_69 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_69, 0, x_68);
if (lean_is_scalar(x_67)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_67;
}
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_66);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_71 = lean_ctor_get(x_64, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_72 = x_64;
} else {
 lean_dec_ref(x_64);
 x_72 = lean_box(0);
}
x_73 = lean_ctor_get(x_65, 0);
lean_inc(x_73);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 x_74 = x_65;
} else {
 lean_dec_ref(x_65);
 x_74 = lean_box(0);
}
x_75 = lean_apply_2(x_3, x_62, x_73);
x_76 = l_Lean_mkNatLit(x_75);
if (lean_is_scalar(x_74)) {
 x_77 = lean_alloc_ctor(0, 1, 0);
} else {
 x_77 = x_74;
 lean_ctor_set_tag(x_77, 0);
}
lean_ctor_set(x_77, 0, x_76);
if (lean_is_scalar(x_72)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_72;
}
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_71);
return x_78;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_62);
lean_dec(x_3);
x_79 = lean_ctor_get(x_64, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_64, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_81 = x_64;
} else {
 lean_dec_ref(x_64);
 x_81 = lean_box(0);
}
if (lean_is_scalar(x_81)) {
 x_82 = lean_alloc_ctor(1, 2, 0);
} else {
 x_82 = x_81;
}
lean_ctor_set(x_82, 0, x_79);
lean_ctor_set(x_82, 1, x_80);
return x_82;
}
}
}
}
else
{
uint8_t x_83; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
x_83 = !lean_is_exclusive(x_19);
if (x_83 == 0)
{
return x_19;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_19, 0);
x_85 = lean_ctor_get(x_19, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_19);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBin___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Nat_reduceBin___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBin___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Nat_reduceBin(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBinPred___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = l_Lean_Expr_isAppOfArity(x_4, x_1, x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_9);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = l_Lean_Expr_appFn_x21(x_4);
x_15 = l_Lean_Expr_appArg_x21(x_14);
lean_dec(x_14);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_16 = l_Lean_Meta_getNatValue_x3f(x_15, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_16, 0);
lean_dec(x_19);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_16, 0, x_21);
return x_16;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_16, 1);
lean_inc(x_22);
lean_dec(x_16);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_22);
return x_25;
}
}
else
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_16, 1);
lean_inc(x_26);
lean_dec(x_16);
x_27 = !lean_is_exclusive(x_17);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_17, 0);
x_29 = l_Lean_Expr_appArg_x21(x_4);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_30 = l_Lean_Meta_getNatValue_x3f(x_29, x_5, x_6, x_7, x_8, x_26);
lean_dec(x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
lean_dec(x_28);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_32 = !lean_is_exclusive(x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_30, 0);
lean_dec(x_33);
x_34 = lean_box(0);
lean_ctor_set_tag(x_17, 2);
lean_ctor_set(x_17, 0, x_34);
lean_ctor_set(x_30, 0, x_17);
return x_30;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_30, 1);
lean_inc(x_35);
lean_dec(x_30);
x_36 = lean_box(0);
lean_ctor_set_tag(x_17, 2);
lean_ctor_set(x_17, 0, x_36);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_17);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; 
lean_free_object(x_17);
x_38 = lean_ctor_get(x_30, 1);
lean_inc(x_38);
lean_dec(x_30);
x_39 = lean_ctor_get(x_31, 0);
lean_inc(x_39);
lean_dec(x_31);
x_40 = lean_apply_2(x_3, x_28, x_39);
x_41 = lean_unbox(x_40);
lean_dec(x_40);
x_42 = l_Lean_Meta_Simp_evalPropStep___redArg(x_4, x_41, x_5, x_6, x_7, x_8, x_38);
return x_42;
}
}
else
{
uint8_t x_43; 
lean_free_object(x_17);
lean_dec(x_28);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_43 = !lean_is_exclusive(x_30);
if (x_43 == 0)
{
return x_30;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_30, 0);
x_45 = lean_ctor_get(x_30, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_30);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_17, 0);
lean_inc(x_47);
lean_dec(x_17);
x_48 = l_Lean_Expr_appArg_x21(x_4);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_49 = l_Lean_Meta_getNatValue_x3f(x_48, x_5, x_6, x_7, x_8, x_26);
lean_dec(x_48);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_47);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
x_53 = lean_box(0);
x_54 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_54, 0, x_53);
if (lean_is_scalar(x_52)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_52;
}
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_51);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; 
x_56 = lean_ctor_get(x_49, 1);
lean_inc(x_56);
lean_dec(x_49);
x_57 = lean_ctor_get(x_50, 0);
lean_inc(x_57);
lean_dec(x_50);
x_58 = lean_apply_2(x_3, x_47, x_57);
x_59 = lean_unbox(x_58);
lean_dec(x_58);
x_60 = l_Lean_Meta_Simp_evalPropStep___redArg(x_4, x_59, x_5, x_6, x_7, x_8, x_56);
return x_60;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_47);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_61 = lean_ctor_get(x_49, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_49, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_63 = x_49;
} else {
 lean_dec_ref(x_49);
 x_63 = lean_box(0);
}
if (lean_is_scalar(x_63)) {
 x_64 = lean_alloc_ctor(1, 2, 0);
} else {
 x_64 = x_63;
}
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set(x_64, 1, x_62);
return x_64;
}
}
}
}
else
{
uint8_t x_65; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_65 = !lean_is_exclusive(x_16);
if (x_65 == 0)
{
return x_16;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_16, 0);
x_67 = lean_ctor_get(x_16, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_16);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBinPred(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = l_Lean_Expr_isAppOfArity(x_4, x_1, x_2);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_12);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = l_Lean_Expr_appFn_x21(x_4);
x_18 = l_Lean_Expr_appArg_x21(x_17);
lean_dec(x_17);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_19 = l_Lean_Meta_getNatValue_x3f(x_18, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_19, 0);
lean_dec(x_22);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_19, 0, x_24);
return x_19;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_19, 1);
lean_inc(x_25);
lean_dec(x_19);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_25);
return x_28;
}
}
else
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_19, 1);
lean_inc(x_29);
lean_dec(x_19);
x_30 = !lean_is_exclusive(x_20);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_20, 0);
x_32 = l_Lean_Expr_appArg_x21(x_4);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_33 = l_Lean_Meta_getNatValue_x3f(x_32, x_8, x_9, x_10, x_11, x_29);
lean_dec(x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
if (lean_obj_tag(x_34) == 0)
{
uint8_t x_35; 
lean_dec(x_31);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_35 = !lean_is_exclusive(x_33);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_33, 0);
lean_dec(x_36);
x_37 = lean_box(0);
lean_ctor_set_tag(x_20, 2);
lean_ctor_set(x_20, 0, x_37);
lean_ctor_set(x_33, 0, x_20);
return x_33;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_33, 1);
lean_inc(x_38);
lean_dec(x_33);
x_39 = lean_box(0);
lean_ctor_set_tag(x_20, 2);
lean_ctor_set(x_20, 0, x_39);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_20);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; 
lean_free_object(x_20);
x_41 = lean_ctor_get(x_33, 1);
lean_inc(x_41);
lean_dec(x_33);
x_42 = lean_ctor_get(x_34, 0);
lean_inc(x_42);
lean_dec(x_34);
x_43 = lean_apply_2(x_3, x_31, x_42);
x_44 = lean_unbox(x_43);
lean_dec(x_43);
x_45 = l_Lean_Meta_Simp_evalPropStep___redArg(x_4, x_44, x_8, x_9, x_10, x_11, x_41);
return x_45;
}
}
else
{
uint8_t x_46; 
lean_free_object(x_20);
lean_dec(x_31);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_46 = !lean_is_exclusive(x_33);
if (x_46 == 0)
{
return x_33;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_33, 0);
x_48 = lean_ctor_get(x_33, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_33);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_20, 0);
lean_inc(x_50);
lean_dec(x_20);
x_51 = l_Lean_Expr_appArg_x21(x_4);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_52 = l_Lean_Meta_getNatValue_x3f(x_51, x_8, x_9, x_10, x_11, x_29);
lean_dec(x_51);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_50);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_55 = x_52;
} else {
 lean_dec_ref(x_52);
 x_55 = lean_box(0);
}
x_56 = lean_box(0);
x_57 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_57, 0, x_56);
if (lean_is_scalar(x_55)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_55;
}
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_54);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; 
x_59 = lean_ctor_get(x_52, 1);
lean_inc(x_59);
lean_dec(x_52);
x_60 = lean_ctor_get(x_53, 0);
lean_inc(x_60);
lean_dec(x_53);
x_61 = lean_apply_2(x_3, x_50, x_60);
x_62 = lean_unbox(x_61);
lean_dec(x_61);
x_63 = l_Lean_Meta_Simp_evalPropStep___redArg(x_4, x_62, x_8, x_9, x_10, x_11, x_59);
return x_63;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_50);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_64 = lean_ctor_get(x_52, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_52, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_66 = x_52;
} else {
 lean_dec_ref(x_52);
 x_66 = lean_box(0);
}
if (lean_is_scalar(x_66)) {
 x_67 = lean_alloc_ctor(1, 2, 0);
} else {
 x_67 = x_66;
}
lean_ctor_set(x_67, 0, x_64);
lean_ctor_set(x_67, 1, x_65);
return x_67;
}
}
}
}
else
{
uint8_t x_68; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_68 = !lean_is_exclusive(x_19);
if (x_68 == 0)
{
return x_19;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_19, 0);
x_70 = lean_ctor_get(x_19, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_19);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBinPred___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Nat_reduceBinPred___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBinPred___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Nat_reduceBinPred(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBoolPred___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = l_Lean_Expr_isAppOfArity(x_4, x_1, x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_9);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = l_Lean_Expr_appFn_x21(x_4);
x_15 = l_Lean_Expr_appArg_x21(x_14);
lean_dec(x_14);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_16 = l_Lean_Meta_getNatValue_x3f(x_15, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_16, 0);
lean_dec(x_19);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_16, 0, x_21);
return x_16;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_16, 1);
lean_inc(x_22);
lean_dec(x_16);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_22);
return x_25;
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_16);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_27 = lean_ctor_get(x_16, 1);
x_28 = lean_ctor_get(x_16, 0);
lean_dec(x_28);
x_29 = lean_ctor_get(x_17, 0);
lean_inc(x_29);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 x_30 = x_17;
} else {
 lean_dec_ref(x_17);
 x_30 = lean_box(0);
}
x_31 = l_Lean_Expr_appArg_x21(x_4);
x_32 = l_Lean_Meta_getNatValue_x3f(x_31, x_5, x_6, x_7, x_8, x_27);
lean_dec(x_31);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_35 = x_32;
} else {
 lean_dec_ref(x_32);
 x_35 = lean_box(0);
}
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_35);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_3);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_16, 1, x_34);
lean_ctor_set(x_16, 0, x_41);
return x_16;
}
else
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; 
lean_free_object(x_16);
x_42 = lean_ctor_get(x_33, 0);
lean_inc(x_42);
lean_dec(x_33);
x_43 = lean_apply_2(x_3, x_29, x_42);
x_44 = lean_unbox(x_43);
lean_dec(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_45 = lean_mk_string_unchecked("Bool", 4, 4);
x_46 = lean_mk_string_unchecked("false", 5, 5);
x_47 = l_Lean_Name_mkStr2(x_45, x_46);
x_48 = lean_box(0);
x_49 = l_Lean_Expr_const___override(x_47, x_48);
x_36 = x_49;
goto block_39;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_50 = lean_mk_string_unchecked("Bool", 4, 4);
x_51 = lean_mk_string_unchecked("true", 4, 4);
x_52 = l_Lean_Name_mkStr2(x_50, x_51);
x_53 = lean_box(0);
x_54 = l_Lean_Expr_const___override(x_52, x_53);
x_36 = x_54;
goto block_39;
}
}
block_39:
{
lean_object* x_37; lean_object* x_38; 
if (lean_is_scalar(x_30)) {
 x_37 = lean_alloc_ctor(0, 1, 0);
} else {
 x_37 = x_30;
 lean_ctor_set_tag(x_37, 0);
}
lean_ctor_set(x_37, 0, x_36);
if (lean_is_scalar(x_35)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_35;
}
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_34);
return x_38;
}
}
else
{
uint8_t x_55; 
lean_dec(x_30);
lean_dec(x_29);
lean_free_object(x_16);
lean_dec(x_3);
x_55 = !lean_is_exclusive(x_32);
if (x_55 == 0)
{
return x_32;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_32, 0);
x_57 = lean_ctor_get(x_32, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_32);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_59 = lean_ctor_get(x_16, 1);
lean_inc(x_59);
lean_dec(x_16);
x_60 = lean_ctor_get(x_17, 0);
lean_inc(x_60);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 x_61 = x_17;
} else {
 lean_dec_ref(x_17);
 x_61 = lean_box(0);
}
x_62 = l_Lean_Expr_appArg_x21(x_4);
x_63 = l_Lean_Meta_getNatValue_x3f(x_62, x_5, x_6, x_7, x_8, x_59);
lean_dec(x_62);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
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
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_66);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_3);
x_71 = lean_box(0);
x_72 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_72, 0, x_71);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_65);
return x_73;
}
else
{
lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_74 = lean_ctor_get(x_64, 0);
lean_inc(x_74);
lean_dec(x_64);
x_75 = lean_apply_2(x_3, x_60, x_74);
x_76 = lean_unbox(x_75);
lean_dec(x_75);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_77 = lean_mk_string_unchecked("Bool", 4, 4);
x_78 = lean_mk_string_unchecked("false", 5, 5);
x_79 = l_Lean_Name_mkStr2(x_77, x_78);
x_80 = lean_box(0);
x_81 = l_Lean_Expr_const___override(x_79, x_80);
x_67 = x_81;
goto block_70;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_82 = lean_mk_string_unchecked("Bool", 4, 4);
x_83 = lean_mk_string_unchecked("true", 4, 4);
x_84 = l_Lean_Name_mkStr2(x_82, x_83);
x_85 = lean_box(0);
x_86 = l_Lean_Expr_const___override(x_84, x_85);
x_67 = x_86;
goto block_70;
}
}
block_70:
{
lean_object* x_68; lean_object* x_69; 
if (lean_is_scalar(x_61)) {
 x_68 = lean_alloc_ctor(0, 1, 0);
} else {
 x_68 = x_61;
 lean_ctor_set_tag(x_68, 0);
}
lean_ctor_set(x_68, 0, x_67);
if (lean_is_scalar(x_66)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_66;
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_65);
return x_69;
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_3);
x_87 = lean_ctor_get(x_63, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_63, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_89 = x_63;
} else {
 lean_dec_ref(x_63);
 x_89 = lean_box(0);
}
if (lean_is_scalar(x_89)) {
 x_90 = lean_alloc_ctor(1, 2, 0);
} else {
 x_90 = x_89;
}
lean_ctor_set(x_90, 0, x_87);
lean_ctor_set(x_90, 1, x_88);
return x_90;
}
}
}
}
else
{
uint8_t x_91; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_91 = !lean_is_exclusive(x_16);
if (x_91 == 0)
{
return x_16;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_16, 0);
x_93 = lean_ctor_get(x_16, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_16);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBoolPred(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = l_Lean_Expr_isAppOfArity(x_4, x_1, x_2);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_12);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = l_Lean_Expr_appFn_x21(x_4);
x_18 = l_Lean_Expr_appArg_x21(x_17);
lean_dec(x_17);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_19 = l_Lean_Meta_getNatValue_x3f(x_18, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_19, 0);
lean_dec(x_22);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_19, 0, x_24);
return x_19;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_19, 1);
lean_inc(x_25);
lean_dec(x_19);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_25);
return x_28;
}
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_19);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_30 = lean_ctor_get(x_19, 1);
x_31 = lean_ctor_get(x_19, 0);
lean_dec(x_31);
x_32 = lean_ctor_get(x_20, 0);
lean_inc(x_32);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 x_33 = x_20;
} else {
 lean_dec_ref(x_20);
 x_33 = lean_box(0);
}
x_34 = l_Lean_Expr_appArg_x21(x_4);
x_35 = l_Lean_Meta_getNatValue_x3f(x_34, x_8, x_9, x_10, x_11, x_30);
lean_dec(x_34);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_38 = x_35;
} else {
 lean_dec_ref(x_35);
 x_38 = lean_box(0);
}
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_38);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_3);
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_19, 1, x_37);
lean_ctor_set(x_19, 0, x_44);
return x_19;
}
else
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; 
lean_free_object(x_19);
x_45 = lean_ctor_get(x_36, 0);
lean_inc(x_45);
lean_dec(x_36);
x_46 = lean_apply_2(x_3, x_32, x_45);
x_47 = lean_unbox(x_46);
lean_dec(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_48 = lean_mk_string_unchecked("Bool", 4, 4);
x_49 = lean_mk_string_unchecked("false", 5, 5);
x_50 = l_Lean_Name_mkStr2(x_48, x_49);
x_51 = lean_box(0);
x_52 = l_Lean_Expr_const___override(x_50, x_51);
x_39 = x_52;
goto block_42;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_53 = lean_mk_string_unchecked("Bool", 4, 4);
x_54 = lean_mk_string_unchecked("true", 4, 4);
x_55 = l_Lean_Name_mkStr2(x_53, x_54);
x_56 = lean_box(0);
x_57 = l_Lean_Expr_const___override(x_55, x_56);
x_39 = x_57;
goto block_42;
}
}
block_42:
{
lean_object* x_40; lean_object* x_41; 
if (lean_is_scalar(x_33)) {
 x_40 = lean_alloc_ctor(0, 1, 0);
} else {
 x_40 = x_33;
 lean_ctor_set_tag(x_40, 0);
}
lean_ctor_set(x_40, 0, x_39);
if (lean_is_scalar(x_38)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_38;
}
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_37);
return x_41;
}
}
else
{
uint8_t x_58; 
lean_dec(x_33);
lean_dec(x_32);
lean_free_object(x_19);
lean_dec(x_3);
x_58 = !lean_is_exclusive(x_35);
if (x_58 == 0)
{
return x_35;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_35, 0);
x_60 = lean_ctor_get(x_35, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_35);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_62 = lean_ctor_get(x_19, 1);
lean_inc(x_62);
lean_dec(x_19);
x_63 = lean_ctor_get(x_20, 0);
lean_inc(x_63);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 x_64 = x_20;
} else {
 lean_dec_ref(x_20);
 x_64 = lean_box(0);
}
x_65 = l_Lean_Expr_appArg_x21(x_4);
x_66 = l_Lean_Meta_getNatValue_x3f(x_65, x_8, x_9, x_10, x_11, x_62);
lean_dec(x_65);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
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
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_69);
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_3);
x_74 = lean_box(0);
x_75 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_75, 0, x_74);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_68);
return x_76;
}
else
{
lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_77 = lean_ctor_get(x_67, 0);
lean_inc(x_77);
lean_dec(x_67);
x_78 = lean_apply_2(x_3, x_63, x_77);
x_79 = lean_unbox(x_78);
lean_dec(x_78);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_80 = lean_mk_string_unchecked("Bool", 4, 4);
x_81 = lean_mk_string_unchecked("false", 5, 5);
x_82 = l_Lean_Name_mkStr2(x_80, x_81);
x_83 = lean_box(0);
x_84 = l_Lean_Expr_const___override(x_82, x_83);
x_70 = x_84;
goto block_73;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_85 = lean_mk_string_unchecked("Bool", 4, 4);
x_86 = lean_mk_string_unchecked("true", 4, 4);
x_87 = l_Lean_Name_mkStr2(x_85, x_86);
x_88 = lean_box(0);
x_89 = l_Lean_Expr_const___override(x_87, x_88);
x_70 = x_89;
goto block_73;
}
}
block_73:
{
lean_object* x_71; lean_object* x_72; 
if (lean_is_scalar(x_64)) {
 x_71 = lean_alloc_ctor(0, 1, 0);
} else {
 x_71 = x_64;
 lean_ctor_set_tag(x_71, 0);
}
lean_ctor_set(x_71, 0, x_70);
if (lean_is_scalar(x_69)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_69;
}
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_68);
return x_72;
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_3);
x_90 = lean_ctor_get(x_66, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_66, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_92 = x_66;
} else {
 lean_dec_ref(x_66);
 x_92 = lean_box(0);
}
if (lean_is_scalar(x_92)) {
 x_93 = lean_alloc_ctor(1, 2, 0);
} else {
 x_93 = x_92;
}
lean_ctor_set(x_93, 0, x_90);
lean_ctor_set(x_93, 1, x_91);
return x_93;
}
}
}
}
else
{
uint8_t x_94; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
x_94 = !lean_is_exclusive(x_19);
if (x_94 == 0)
{
return x_19;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_19, 0);
x_96 = lean_ctor_get(x_19, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_19);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBoolPred___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Nat_reduceBoolPred___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBoolPred___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Nat_reduceBoolPred(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceSucc___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_mk_string_unchecked("Nat", 3, 3);
x_8 = lean_mk_string_unchecked("succ", 4, 4);
x_9 = l_Lean_Name_mkStr2(x_7, x_8);
x_10 = lean_unsigned_to_nat(1u);
x_11 = l_Lean_Expr_isAppOfArity(x_1, x_9, x_10);
lean_dec(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_6);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = l_Lean_Expr_appArg_x21(x_1);
x_16 = l_Lean_Meta_getNatValue_x3f(x_15, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_16, 0);
lean_dec(x_19);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_16, 0, x_21);
return x_16;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_16, 1);
lean_inc(x_22);
lean_dec(x_16);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_22);
return x_25;
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_16);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_16, 0);
lean_dec(x_27);
x_28 = !lean_is_exclusive(x_17);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_17, 0);
x_30 = lean_nat_add(x_29, x_10);
lean_dec(x_29);
x_31 = l_Lean_mkNatLit(x_30);
lean_ctor_set_tag(x_17, 0);
lean_ctor_set(x_17, 0, x_31);
return x_16;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_17, 0);
lean_inc(x_32);
lean_dec(x_17);
x_33 = lean_nat_add(x_32, x_10);
lean_dec(x_32);
x_34 = l_Lean_mkNatLit(x_33);
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_16, 0, x_35);
return x_16;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_36 = lean_ctor_get(x_16, 1);
lean_inc(x_36);
lean_dec(x_16);
x_37 = lean_ctor_get(x_17, 0);
lean_inc(x_37);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 x_38 = x_17;
} else {
 lean_dec_ref(x_17);
 x_38 = lean_box(0);
}
x_39 = lean_nat_add(x_37, x_10);
lean_dec(x_37);
x_40 = l_Lean_mkNatLit(x_39);
if (lean_is_scalar(x_38)) {
 x_41 = lean_alloc_ctor(0, 1, 0);
} else {
 x_41 = x_38;
 lean_ctor_set_tag(x_41, 0);
}
lean_ctor_set(x_41, 0, x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_36);
return x_42;
}
}
}
else
{
uint8_t x_43; 
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
}
LEAN_EXPORT lean_object* l_Nat_reduceSucc(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Nat_reduceSucc___redArg(x_1, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceSucc___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Nat_reduceSucc___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceSucc___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Nat_reduceSucc(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_559_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_2 = lean_mk_string_unchecked("Nat", 3, 3);
x_3 = lean_mk_string_unchecked("reduceSucc", 10, 10);
lean_inc(x_2);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_mk_string_unchecked("succ", 4, 4);
x_6 = l_Lean_Name_mkStr2(x_2, x_5);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_box(3);
x_10 = lean_unsigned_to_nat(2u);
x_11 = lean_mk_empty_array_with_capacity(x_10);
x_12 = lean_array_push(x_11, x_8);
x_13 = lean_array_push(x_12, x_9);
x_14 = lean_alloc_closure((void*)(l_Nat_reduceSucc___boxed), 9, 0);
x_15 = l_Lean_Meta_Simp_registerBuiltinDSimproc(x_4, x_13, x_14, x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_561_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Nat", 3, 3);
x_3 = lean_mk_string_unchecked("reduceSucc", 10, 10);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Nat_reduceSucc___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_563_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Nat", 3, 3);
x_3 = lean_mk_string_unchecked("reduceSucc", 10, 10);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Nat_reduceSucc___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceAdd___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_mk_string_unchecked("HAdd", 4, 4);
x_8 = lean_mk_string_unchecked("hAdd", 4, 4);
x_9 = l_Lean_Name_mkStr2(x_7, x_8);
x_10 = lean_unsigned_to_nat(6u);
x_11 = l_Lean_Expr_isAppOfArity(x_1, x_9, x_10);
lean_dec(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_6);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = l_Lean_Expr_appFn_x21(x_1);
x_16 = l_Lean_Expr_appArg_x21(x_15);
lean_dec(x_15);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_17 = l_Lean_Meta_getNatValue_x3f(x_16, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_17, 0);
lean_dec(x_20);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_17, 0, x_22);
return x_17;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_dec(x_17);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_23);
return x_26;
}
}
else
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_17, 1);
lean_inc(x_27);
lean_dec(x_17);
x_28 = !lean_is_exclusive(x_18);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_18, 0);
x_30 = l_Lean_Expr_appArg_x21(x_1);
x_31 = l_Lean_Meta_getNatValue_x3f(x_30, x_2, x_3, x_4, x_5, x_27);
lean_dec(x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
lean_dec(x_29);
x_33 = !lean_is_exclusive(x_31);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_31, 0);
lean_dec(x_34);
x_35 = lean_box(0);
lean_ctor_set_tag(x_18, 2);
lean_ctor_set(x_18, 0, x_35);
lean_ctor_set(x_31, 0, x_18);
return x_31;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_31, 1);
lean_inc(x_36);
lean_dec(x_31);
x_37 = lean_box(0);
lean_ctor_set_tag(x_18, 2);
lean_ctor_set(x_18, 0, x_37);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_18);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
else
{
uint8_t x_39; 
lean_free_object(x_18);
x_39 = !lean_is_exclusive(x_31);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_31, 0);
lean_dec(x_40);
x_41 = !lean_is_exclusive(x_32);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_32, 0);
x_43 = lean_nat_add(x_29, x_42);
lean_dec(x_42);
lean_dec(x_29);
x_44 = l_Lean_mkNatLit(x_43);
lean_ctor_set_tag(x_32, 0);
lean_ctor_set(x_32, 0, x_44);
return x_31;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_32, 0);
lean_inc(x_45);
lean_dec(x_32);
x_46 = lean_nat_add(x_29, x_45);
lean_dec(x_45);
lean_dec(x_29);
x_47 = l_Lean_mkNatLit(x_46);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_31, 0, x_48);
return x_31;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_49 = lean_ctor_get(x_31, 1);
lean_inc(x_49);
lean_dec(x_31);
x_50 = lean_ctor_get(x_32, 0);
lean_inc(x_50);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 x_51 = x_32;
} else {
 lean_dec_ref(x_32);
 x_51 = lean_box(0);
}
x_52 = lean_nat_add(x_29, x_50);
lean_dec(x_50);
lean_dec(x_29);
x_53 = l_Lean_mkNatLit(x_52);
if (lean_is_scalar(x_51)) {
 x_54 = lean_alloc_ctor(0, 1, 0);
} else {
 x_54 = x_51;
 lean_ctor_set_tag(x_54, 0);
}
lean_ctor_set(x_54, 0, x_53);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_49);
return x_55;
}
}
}
else
{
uint8_t x_56; 
lean_free_object(x_18);
lean_dec(x_29);
x_56 = !lean_is_exclusive(x_31);
if (x_56 == 0)
{
return x_31;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_31, 0);
x_58 = lean_ctor_get(x_31, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_31);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_18, 0);
lean_inc(x_60);
lean_dec(x_18);
x_61 = l_Lean_Expr_appArg_x21(x_1);
x_62 = l_Lean_Meta_getNatValue_x3f(x_61, x_2, x_3, x_4, x_5, x_27);
lean_dec(x_61);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_60);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_65 = x_62;
} else {
 lean_dec_ref(x_62);
 x_65 = lean_box(0);
}
x_66 = lean_box(0);
x_67 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_67, 0, x_66);
if (lean_is_scalar(x_65)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_65;
}
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_64);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_69 = lean_ctor_get(x_62, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_70 = x_62;
} else {
 lean_dec_ref(x_62);
 x_70 = lean_box(0);
}
x_71 = lean_ctor_get(x_63, 0);
lean_inc(x_71);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 x_72 = x_63;
} else {
 lean_dec_ref(x_63);
 x_72 = lean_box(0);
}
x_73 = lean_nat_add(x_60, x_71);
lean_dec(x_71);
lean_dec(x_60);
x_74 = l_Lean_mkNatLit(x_73);
if (lean_is_scalar(x_72)) {
 x_75 = lean_alloc_ctor(0, 1, 0);
} else {
 x_75 = x_72;
 lean_ctor_set_tag(x_75, 0);
}
lean_ctor_set(x_75, 0, x_74);
if (lean_is_scalar(x_70)) {
 x_76 = lean_alloc_ctor(0, 2, 0);
} else {
 x_76 = x_70;
}
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_69);
return x_76;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_60);
x_77 = lean_ctor_get(x_62, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_62, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_79 = x_62;
} else {
 lean_dec_ref(x_62);
 x_79 = lean_box(0);
}
if (lean_is_scalar(x_79)) {
 x_80 = lean_alloc_ctor(1, 2, 0);
} else {
 x_80 = x_79;
}
lean_ctor_set(x_80, 0, x_77);
lean_ctor_set(x_80, 1, x_78);
return x_80;
}
}
}
}
else
{
uint8_t x_81; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_81 = !lean_is_exclusive(x_17);
if (x_81 == 0)
{
return x_17;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_17, 0);
x_83 = lean_ctor_get(x_17, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_17);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceAdd(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Nat_reduceAdd___redArg(x_1, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceAdd___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Nat_reduceAdd___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceAdd___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Nat_reduceAdd(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_597_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_2 = lean_mk_string_unchecked("Nat", 3, 3);
x_3 = lean_mk_string_unchecked("reduceAdd", 9, 9);
lean_inc(x_2);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_mk_string_unchecked("HAdd", 4, 4);
x_6 = lean_mk_string_unchecked("hAdd", 4, 4);
x_7 = l_Lean_Name_mkStr2(x_5, x_6);
x_8 = lean_unsigned_to_nat(6u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Lean_Name_mkStr1(x_2);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_box(3);
x_14 = lean_unsigned_to_nat(7u);
x_15 = lean_mk_empty_array_with_capacity(x_14);
x_16 = lean_array_push(x_15, x_9);
lean_inc(x_12);
x_17 = lean_array_push(x_16, x_12);
lean_inc(x_12);
x_18 = lean_array_push(x_17, x_12);
x_19 = lean_array_push(x_18, x_12);
x_20 = lean_array_push(x_19, x_13);
x_21 = lean_array_push(x_20, x_13);
x_22 = lean_array_push(x_21, x_13);
x_23 = lean_alloc_closure((void*)(l_Nat_reduceAdd___boxed), 9, 0);
x_24 = l_Lean_Meta_Simp_registerBuiltinDSimproc(x_4, x_22, x_23, x_1);
return x_24;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_599_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Nat", 3, 3);
x_3 = lean_mk_string_unchecked("reduceAdd", 9, 9);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Nat_reduceAdd___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_601_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Nat", 3, 3);
x_3 = lean_mk_string_unchecked("reduceAdd", 9, 9);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Nat_reduceAdd___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceMul___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_mk_string_unchecked("HMul", 4, 4);
x_8 = lean_mk_string_unchecked("hMul", 4, 4);
x_9 = l_Lean_Name_mkStr2(x_7, x_8);
x_10 = lean_unsigned_to_nat(6u);
x_11 = l_Lean_Expr_isAppOfArity(x_1, x_9, x_10);
lean_dec(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_6);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = l_Lean_Expr_appFn_x21(x_1);
x_16 = l_Lean_Expr_appArg_x21(x_15);
lean_dec(x_15);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_17 = l_Lean_Meta_getNatValue_x3f(x_16, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_17, 0);
lean_dec(x_20);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_17, 0, x_22);
return x_17;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_dec(x_17);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_23);
return x_26;
}
}
else
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_17, 1);
lean_inc(x_27);
lean_dec(x_17);
x_28 = !lean_is_exclusive(x_18);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_18, 0);
x_30 = l_Lean_Expr_appArg_x21(x_1);
x_31 = l_Lean_Meta_getNatValue_x3f(x_30, x_2, x_3, x_4, x_5, x_27);
lean_dec(x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
lean_dec(x_29);
x_33 = !lean_is_exclusive(x_31);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_31, 0);
lean_dec(x_34);
x_35 = lean_box(0);
lean_ctor_set_tag(x_18, 2);
lean_ctor_set(x_18, 0, x_35);
lean_ctor_set(x_31, 0, x_18);
return x_31;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_31, 1);
lean_inc(x_36);
lean_dec(x_31);
x_37 = lean_box(0);
lean_ctor_set_tag(x_18, 2);
lean_ctor_set(x_18, 0, x_37);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_18);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
else
{
uint8_t x_39; 
lean_free_object(x_18);
x_39 = !lean_is_exclusive(x_31);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_31, 0);
lean_dec(x_40);
x_41 = !lean_is_exclusive(x_32);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_32, 0);
x_43 = lean_nat_mul(x_29, x_42);
lean_dec(x_42);
lean_dec(x_29);
x_44 = l_Lean_mkNatLit(x_43);
lean_ctor_set_tag(x_32, 0);
lean_ctor_set(x_32, 0, x_44);
return x_31;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_32, 0);
lean_inc(x_45);
lean_dec(x_32);
x_46 = lean_nat_mul(x_29, x_45);
lean_dec(x_45);
lean_dec(x_29);
x_47 = l_Lean_mkNatLit(x_46);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_31, 0, x_48);
return x_31;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_49 = lean_ctor_get(x_31, 1);
lean_inc(x_49);
lean_dec(x_31);
x_50 = lean_ctor_get(x_32, 0);
lean_inc(x_50);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 x_51 = x_32;
} else {
 lean_dec_ref(x_32);
 x_51 = lean_box(0);
}
x_52 = lean_nat_mul(x_29, x_50);
lean_dec(x_50);
lean_dec(x_29);
x_53 = l_Lean_mkNatLit(x_52);
if (lean_is_scalar(x_51)) {
 x_54 = lean_alloc_ctor(0, 1, 0);
} else {
 x_54 = x_51;
 lean_ctor_set_tag(x_54, 0);
}
lean_ctor_set(x_54, 0, x_53);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_49);
return x_55;
}
}
}
else
{
uint8_t x_56; 
lean_free_object(x_18);
lean_dec(x_29);
x_56 = !lean_is_exclusive(x_31);
if (x_56 == 0)
{
return x_31;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_31, 0);
x_58 = lean_ctor_get(x_31, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_31);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_18, 0);
lean_inc(x_60);
lean_dec(x_18);
x_61 = l_Lean_Expr_appArg_x21(x_1);
x_62 = l_Lean_Meta_getNatValue_x3f(x_61, x_2, x_3, x_4, x_5, x_27);
lean_dec(x_61);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_60);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_65 = x_62;
} else {
 lean_dec_ref(x_62);
 x_65 = lean_box(0);
}
x_66 = lean_box(0);
x_67 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_67, 0, x_66);
if (lean_is_scalar(x_65)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_65;
}
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_64);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_69 = lean_ctor_get(x_62, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_70 = x_62;
} else {
 lean_dec_ref(x_62);
 x_70 = lean_box(0);
}
x_71 = lean_ctor_get(x_63, 0);
lean_inc(x_71);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 x_72 = x_63;
} else {
 lean_dec_ref(x_63);
 x_72 = lean_box(0);
}
x_73 = lean_nat_mul(x_60, x_71);
lean_dec(x_71);
lean_dec(x_60);
x_74 = l_Lean_mkNatLit(x_73);
if (lean_is_scalar(x_72)) {
 x_75 = lean_alloc_ctor(0, 1, 0);
} else {
 x_75 = x_72;
 lean_ctor_set_tag(x_75, 0);
}
lean_ctor_set(x_75, 0, x_74);
if (lean_is_scalar(x_70)) {
 x_76 = lean_alloc_ctor(0, 2, 0);
} else {
 x_76 = x_70;
}
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_69);
return x_76;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_60);
x_77 = lean_ctor_get(x_62, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_62, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_79 = x_62;
} else {
 lean_dec_ref(x_62);
 x_79 = lean_box(0);
}
if (lean_is_scalar(x_79)) {
 x_80 = lean_alloc_ctor(1, 2, 0);
} else {
 x_80 = x_79;
}
lean_ctor_set(x_80, 0, x_77);
lean_ctor_set(x_80, 1, x_78);
return x_80;
}
}
}
}
else
{
uint8_t x_81; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_81 = !lean_is_exclusive(x_17);
if (x_81 == 0)
{
return x_17;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_17, 0);
x_83 = lean_ctor_get(x_17, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_17);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceMul(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Nat_reduceMul___redArg(x_1, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceMul___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Nat_reduceMul___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceMul___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Nat_reduceMul(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceMul_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_635_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_2 = lean_mk_string_unchecked("Nat", 3, 3);
x_3 = lean_mk_string_unchecked("reduceMul", 9, 9);
lean_inc(x_2);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_mk_string_unchecked("HMul", 4, 4);
x_6 = lean_mk_string_unchecked("hMul", 4, 4);
x_7 = l_Lean_Name_mkStr2(x_5, x_6);
x_8 = lean_unsigned_to_nat(6u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Lean_Name_mkStr1(x_2);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_box(3);
x_14 = lean_unsigned_to_nat(7u);
x_15 = lean_mk_empty_array_with_capacity(x_14);
x_16 = lean_array_push(x_15, x_9);
lean_inc(x_12);
x_17 = lean_array_push(x_16, x_12);
lean_inc(x_12);
x_18 = lean_array_push(x_17, x_12);
x_19 = lean_array_push(x_18, x_12);
x_20 = lean_array_push(x_19, x_13);
x_21 = lean_array_push(x_20, x_13);
x_22 = lean_array_push(x_21, x_13);
x_23 = lean_alloc_closure((void*)(l_Nat_reduceMul___boxed), 9, 0);
x_24 = l_Lean_Meta_Simp_registerBuiltinDSimproc(x_4, x_22, x_23, x_1);
return x_24;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceMul_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_637_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Nat", 3, 3);
x_3 = lean_mk_string_unchecked("reduceMul", 9, 9);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Nat_reduceMul___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceMul_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_639_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Nat", 3, 3);
x_3 = lean_mk_string_unchecked("reduceMul", 9, 9);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Nat_reduceMul___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceSub___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_mk_string_unchecked("HSub", 4, 4);
x_8 = lean_mk_string_unchecked("hSub", 4, 4);
x_9 = l_Lean_Name_mkStr2(x_7, x_8);
x_10 = lean_unsigned_to_nat(6u);
x_11 = l_Lean_Expr_isAppOfArity(x_1, x_9, x_10);
lean_dec(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_6);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = l_Lean_Expr_appFn_x21(x_1);
x_16 = l_Lean_Expr_appArg_x21(x_15);
lean_dec(x_15);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_17 = l_Lean_Meta_getNatValue_x3f(x_16, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_17, 0);
lean_dec(x_20);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_17, 0, x_22);
return x_17;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_dec(x_17);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_23);
return x_26;
}
}
else
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_17, 1);
lean_inc(x_27);
lean_dec(x_17);
x_28 = !lean_is_exclusive(x_18);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_18, 0);
x_30 = l_Lean_Expr_appArg_x21(x_1);
x_31 = l_Lean_Meta_getNatValue_x3f(x_30, x_2, x_3, x_4, x_5, x_27);
lean_dec(x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
lean_dec(x_29);
x_33 = !lean_is_exclusive(x_31);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_31, 0);
lean_dec(x_34);
x_35 = lean_box(0);
lean_ctor_set_tag(x_18, 2);
lean_ctor_set(x_18, 0, x_35);
lean_ctor_set(x_31, 0, x_18);
return x_31;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_31, 1);
lean_inc(x_36);
lean_dec(x_31);
x_37 = lean_box(0);
lean_ctor_set_tag(x_18, 2);
lean_ctor_set(x_18, 0, x_37);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_18);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
else
{
uint8_t x_39; 
lean_free_object(x_18);
x_39 = !lean_is_exclusive(x_31);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_31, 0);
lean_dec(x_40);
x_41 = !lean_is_exclusive(x_32);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_32, 0);
x_43 = lean_nat_sub(x_29, x_42);
lean_dec(x_42);
lean_dec(x_29);
x_44 = l_Lean_mkNatLit(x_43);
lean_ctor_set_tag(x_32, 0);
lean_ctor_set(x_32, 0, x_44);
return x_31;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_32, 0);
lean_inc(x_45);
lean_dec(x_32);
x_46 = lean_nat_sub(x_29, x_45);
lean_dec(x_45);
lean_dec(x_29);
x_47 = l_Lean_mkNatLit(x_46);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_31, 0, x_48);
return x_31;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_49 = lean_ctor_get(x_31, 1);
lean_inc(x_49);
lean_dec(x_31);
x_50 = lean_ctor_get(x_32, 0);
lean_inc(x_50);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 x_51 = x_32;
} else {
 lean_dec_ref(x_32);
 x_51 = lean_box(0);
}
x_52 = lean_nat_sub(x_29, x_50);
lean_dec(x_50);
lean_dec(x_29);
x_53 = l_Lean_mkNatLit(x_52);
if (lean_is_scalar(x_51)) {
 x_54 = lean_alloc_ctor(0, 1, 0);
} else {
 x_54 = x_51;
 lean_ctor_set_tag(x_54, 0);
}
lean_ctor_set(x_54, 0, x_53);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_49);
return x_55;
}
}
}
else
{
uint8_t x_56; 
lean_free_object(x_18);
lean_dec(x_29);
x_56 = !lean_is_exclusive(x_31);
if (x_56 == 0)
{
return x_31;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_31, 0);
x_58 = lean_ctor_get(x_31, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_31);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_18, 0);
lean_inc(x_60);
lean_dec(x_18);
x_61 = l_Lean_Expr_appArg_x21(x_1);
x_62 = l_Lean_Meta_getNatValue_x3f(x_61, x_2, x_3, x_4, x_5, x_27);
lean_dec(x_61);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_60);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_65 = x_62;
} else {
 lean_dec_ref(x_62);
 x_65 = lean_box(0);
}
x_66 = lean_box(0);
x_67 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_67, 0, x_66);
if (lean_is_scalar(x_65)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_65;
}
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_64);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_69 = lean_ctor_get(x_62, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_70 = x_62;
} else {
 lean_dec_ref(x_62);
 x_70 = lean_box(0);
}
x_71 = lean_ctor_get(x_63, 0);
lean_inc(x_71);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 x_72 = x_63;
} else {
 lean_dec_ref(x_63);
 x_72 = lean_box(0);
}
x_73 = lean_nat_sub(x_60, x_71);
lean_dec(x_71);
lean_dec(x_60);
x_74 = l_Lean_mkNatLit(x_73);
if (lean_is_scalar(x_72)) {
 x_75 = lean_alloc_ctor(0, 1, 0);
} else {
 x_75 = x_72;
 lean_ctor_set_tag(x_75, 0);
}
lean_ctor_set(x_75, 0, x_74);
if (lean_is_scalar(x_70)) {
 x_76 = lean_alloc_ctor(0, 2, 0);
} else {
 x_76 = x_70;
}
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_69);
return x_76;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_60);
x_77 = lean_ctor_get(x_62, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_62, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_79 = x_62;
} else {
 lean_dec_ref(x_62);
 x_79 = lean_box(0);
}
if (lean_is_scalar(x_79)) {
 x_80 = lean_alloc_ctor(1, 2, 0);
} else {
 x_80 = x_79;
}
lean_ctor_set(x_80, 0, x_77);
lean_ctor_set(x_80, 1, x_78);
return x_80;
}
}
}
}
else
{
uint8_t x_81; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_81 = !lean_is_exclusive(x_17);
if (x_81 == 0)
{
return x_17;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_17, 0);
x_83 = lean_ctor_get(x_17, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_17);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceSub(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Nat_reduceSub___redArg(x_1, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceSub___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Nat_reduceSub___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceSub___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Nat_reduceSub(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceSub_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_673_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_2 = lean_mk_string_unchecked("Nat", 3, 3);
x_3 = lean_mk_string_unchecked("reduceSub", 9, 9);
lean_inc(x_2);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_mk_string_unchecked("HSub", 4, 4);
x_6 = lean_mk_string_unchecked("hSub", 4, 4);
x_7 = l_Lean_Name_mkStr2(x_5, x_6);
x_8 = lean_unsigned_to_nat(6u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Lean_Name_mkStr1(x_2);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_box(3);
x_14 = lean_unsigned_to_nat(7u);
x_15 = lean_mk_empty_array_with_capacity(x_14);
x_16 = lean_array_push(x_15, x_9);
lean_inc(x_12);
x_17 = lean_array_push(x_16, x_12);
lean_inc(x_12);
x_18 = lean_array_push(x_17, x_12);
x_19 = lean_array_push(x_18, x_12);
x_20 = lean_array_push(x_19, x_13);
x_21 = lean_array_push(x_20, x_13);
x_22 = lean_array_push(x_21, x_13);
x_23 = lean_alloc_closure((void*)(l_Nat_reduceSub___boxed), 9, 0);
x_24 = l_Lean_Meta_Simp_registerBuiltinDSimproc(x_4, x_22, x_23, x_1);
return x_24;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceSub_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_675_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Nat", 3, 3);
x_3 = lean_mk_string_unchecked("reduceSub", 9, 9);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Nat_reduceSub___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceSub_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_677_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Nat", 3, 3);
x_3 = lean_mk_string_unchecked("reduceSub", 9, 9);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Nat_reduceSub___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceDiv___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_mk_string_unchecked("HDiv", 4, 4);
x_8 = lean_mk_string_unchecked("hDiv", 4, 4);
x_9 = l_Lean_Name_mkStr2(x_7, x_8);
x_10 = lean_unsigned_to_nat(6u);
x_11 = l_Lean_Expr_isAppOfArity(x_1, x_9, x_10);
lean_dec(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_6);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = l_Lean_Expr_appFn_x21(x_1);
x_16 = l_Lean_Expr_appArg_x21(x_15);
lean_dec(x_15);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_17 = l_Lean_Meta_getNatValue_x3f(x_16, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_17, 0);
lean_dec(x_20);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_17, 0, x_22);
return x_17;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_dec(x_17);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_23);
return x_26;
}
}
else
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_17, 1);
lean_inc(x_27);
lean_dec(x_17);
x_28 = !lean_is_exclusive(x_18);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_18, 0);
x_30 = l_Lean_Expr_appArg_x21(x_1);
x_31 = l_Lean_Meta_getNatValue_x3f(x_30, x_2, x_3, x_4, x_5, x_27);
lean_dec(x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
lean_dec(x_29);
x_33 = !lean_is_exclusive(x_31);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_31, 0);
lean_dec(x_34);
x_35 = lean_box(0);
lean_ctor_set_tag(x_18, 2);
lean_ctor_set(x_18, 0, x_35);
lean_ctor_set(x_31, 0, x_18);
return x_31;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_31, 1);
lean_inc(x_36);
lean_dec(x_31);
x_37 = lean_box(0);
lean_ctor_set_tag(x_18, 2);
lean_ctor_set(x_18, 0, x_37);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_18);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
else
{
uint8_t x_39; 
lean_free_object(x_18);
x_39 = !lean_is_exclusive(x_31);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_31, 0);
lean_dec(x_40);
x_41 = !lean_is_exclusive(x_32);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_32, 0);
x_43 = lean_nat_div(x_29, x_42);
lean_dec(x_42);
lean_dec(x_29);
x_44 = l_Lean_mkNatLit(x_43);
lean_ctor_set_tag(x_32, 0);
lean_ctor_set(x_32, 0, x_44);
return x_31;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_32, 0);
lean_inc(x_45);
lean_dec(x_32);
x_46 = lean_nat_div(x_29, x_45);
lean_dec(x_45);
lean_dec(x_29);
x_47 = l_Lean_mkNatLit(x_46);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_31, 0, x_48);
return x_31;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_49 = lean_ctor_get(x_31, 1);
lean_inc(x_49);
lean_dec(x_31);
x_50 = lean_ctor_get(x_32, 0);
lean_inc(x_50);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 x_51 = x_32;
} else {
 lean_dec_ref(x_32);
 x_51 = lean_box(0);
}
x_52 = lean_nat_div(x_29, x_50);
lean_dec(x_50);
lean_dec(x_29);
x_53 = l_Lean_mkNatLit(x_52);
if (lean_is_scalar(x_51)) {
 x_54 = lean_alloc_ctor(0, 1, 0);
} else {
 x_54 = x_51;
 lean_ctor_set_tag(x_54, 0);
}
lean_ctor_set(x_54, 0, x_53);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_49);
return x_55;
}
}
}
else
{
uint8_t x_56; 
lean_free_object(x_18);
lean_dec(x_29);
x_56 = !lean_is_exclusive(x_31);
if (x_56 == 0)
{
return x_31;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_31, 0);
x_58 = lean_ctor_get(x_31, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_31);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_18, 0);
lean_inc(x_60);
lean_dec(x_18);
x_61 = l_Lean_Expr_appArg_x21(x_1);
x_62 = l_Lean_Meta_getNatValue_x3f(x_61, x_2, x_3, x_4, x_5, x_27);
lean_dec(x_61);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_60);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_65 = x_62;
} else {
 lean_dec_ref(x_62);
 x_65 = lean_box(0);
}
x_66 = lean_box(0);
x_67 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_67, 0, x_66);
if (lean_is_scalar(x_65)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_65;
}
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_64);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_69 = lean_ctor_get(x_62, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_70 = x_62;
} else {
 lean_dec_ref(x_62);
 x_70 = lean_box(0);
}
x_71 = lean_ctor_get(x_63, 0);
lean_inc(x_71);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 x_72 = x_63;
} else {
 lean_dec_ref(x_63);
 x_72 = lean_box(0);
}
x_73 = lean_nat_div(x_60, x_71);
lean_dec(x_71);
lean_dec(x_60);
x_74 = l_Lean_mkNatLit(x_73);
if (lean_is_scalar(x_72)) {
 x_75 = lean_alloc_ctor(0, 1, 0);
} else {
 x_75 = x_72;
 lean_ctor_set_tag(x_75, 0);
}
lean_ctor_set(x_75, 0, x_74);
if (lean_is_scalar(x_70)) {
 x_76 = lean_alloc_ctor(0, 2, 0);
} else {
 x_76 = x_70;
}
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_69);
return x_76;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_60);
x_77 = lean_ctor_get(x_62, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_62, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_79 = x_62;
} else {
 lean_dec_ref(x_62);
 x_79 = lean_box(0);
}
if (lean_is_scalar(x_79)) {
 x_80 = lean_alloc_ctor(1, 2, 0);
} else {
 x_80 = x_79;
}
lean_ctor_set(x_80, 0, x_77);
lean_ctor_set(x_80, 1, x_78);
return x_80;
}
}
}
}
else
{
uint8_t x_81; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_81 = !lean_is_exclusive(x_17);
if (x_81 == 0)
{
return x_17;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_17, 0);
x_83 = lean_ctor_get(x_17, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_17);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceDiv(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Nat_reduceDiv___redArg(x_1, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceDiv___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Nat_reduceDiv___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceDiv___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Nat_reduceDiv(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceDiv_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_711_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_2 = lean_mk_string_unchecked("Nat", 3, 3);
x_3 = lean_mk_string_unchecked("reduceDiv", 9, 9);
lean_inc(x_2);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_mk_string_unchecked("HDiv", 4, 4);
x_6 = lean_mk_string_unchecked("hDiv", 4, 4);
x_7 = l_Lean_Name_mkStr2(x_5, x_6);
x_8 = lean_unsigned_to_nat(6u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Lean_Name_mkStr1(x_2);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_box(3);
x_14 = lean_unsigned_to_nat(7u);
x_15 = lean_mk_empty_array_with_capacity(x_14);
x_16 = lean_array_push(x_15, x_9);
lean_inc(x_12);
x_17 = lean_array_push(x_16, x_12);
lean_inc(x_12);
x_18 = lean_array_push(x_17, x_12);
x_19 = lean_array_push(x_18, x_12);
x_20 = lean_array_push(x_19, x_13);
x_21 = lean_array_push(x_20, x_13);
x_22 = lean_array_push(x_21, x_13);
x_23 = lean_alloc_closure((void*)(l_Nat_reduceDiv___boxed), 9, 0);
x_24 = l_Lean_Meta_Simp_registerBuiltinDSimproc(x_4, x_22, x_23, x_1);
return x_24;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceDiv_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_713_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Nat", 3, 3);
x_3 = lean_mk_string_unchecked("reduceDiv", 9, 9);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Nat_reduceDiv___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceDiv_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_715_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Nat", 3, 3);
x_3 = lean_mk_string_unchecked("reduceDiv", 9, 9);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Nat_reduceDiv___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceMod___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_mk_string_unchecked("HMod", 4, 4);
x_8 = lean_mk_string_unchecked("hMod", 4, 4);
x_9 = l_Lean_Name_mkStr2(x_7, x_8);
x_10 = lean_unsigned_to_nat(6u);
x_11 = l_Lean_Expr_isAppOfArity(x_1, x_9, x_10);
lean_dec(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_6);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = l_Lean_Expr_appFn_x21(x_1);
x_16 = l_Lean_Expr_appArg_x21(x_15);
lean_dec(x_15);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_17 = l_Lean_Meta_getNatValue_x3f(x_16, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_17, 0);
lean_dec(x_20);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_17, 0, x_22);
return x_17;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_dec(x_17);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_23);
return x_26;
}
}
else
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_17, 1);
lean_inc(x_27);
lean_dec(x_17);
x_28 = !lean_is_exclusive(x_18);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_18, 0);
x_30 = l_Lean_Expr_appArg_x21(x_1);
x_31 = l_Lean_Meta_getNatValue_x3f(x_30, x_2, x_3, x_4, x_5, x_27);
lean_dec(x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
lean_dec(x_29);
x_33 = !lean_is_exclusive(x_31);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_31, 0);
lean_dec(x_34);
x_35 = lean_box(0);
lean_ctor_set_tag(x_18, 2);
lean_ctor_set(x_18, 0, x_35);
lean_ctor_set(x_31, 0, x_18);
return x_31;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_31, 1);
lean_inc(x_36);
lean_dec(x_31);
x_37 = lean_box(0);
lean_ctor_set_tag(x_18, 2);
lean_ctor_set(x_18, 0, x_37);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_18);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
else
{
uint8_t x_39; 
lean_free_object(x_18);
x_39 = !lean_is_exclusive(x_31);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_31, 0);
lean_dec(x_40);
x_41 = !lean_is_exclusive(x_32);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_32, 0);
x_43 = lean_nat_mod(x_29, x_42);
lean_dec(x_42);
lean_dec(x_29);
x_44 = l_Lean_mkNatLit(x_43);
lean_ctor_set_tag(x_32, 0);
lean_ctor_set(x_32, 0, x_44);
return x_31;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_32, 0);
lean_inc(x_45);
lean_dec(x_32);
x_46 = lean_nat_mod(x_29, x_45);
lean_dec(x_45);
lean_dec(x_29);
x_47 = l_Lean_mkNatLit(x_46);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_31, 0, x_48);
return x_31;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_49 = lean_ctor_get(x_31, 1);
lean_inc(x_49);
lean_dec(x_31);
x_50 = lean_ctor_get(x_32, 0);
lean_inc(x_50);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 x_51 = x_32;
} else {
 lean_dec_ref(x_32);
 x_51 = lean_box(0);
}
x_52 = lean_nat_mod(x_29, x_50);
lean_dec(x_50);
lean_dec(x_29);
x_53 = l_Lean_mkNatLit(x_52);
if (lean_is_scalar(x_51)) {
 x_54 = lean_alloc_ctor(0, 1, 0);
} else {
 x_54 = x_51;
 lean_ctor_set_tag(x_54, 0);
}
lean_ctor_set(x_54, 0, x_53);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_49);
return x_55;
}
}
}
else
{
uint8_t x_56; 
lean_free_object(x_18);
lean_dec(x_29);
x_56 = !lean_is_exclusive(x_31);
if (x_56 == 0)
{
return x_31;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_31, 0);
x_58 = lean_ctor_get(x_31, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_31);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_18, 0);
lean_inc(x_60);
lean_dec(x_18);
x_61 = l_Lean_Expr_appArg_x21(x_1);
x_62 = l_Lean_Meta_getNatValue_x3f(x_61, x_2, x_3, x_4, x_5, x_27);
lean_dec(x_61);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_60);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_65 = x_62;
} else {
 lean_dec_ref(x_62);
 x_65 = lean_box(0);
}
x_66 = lean_box(0);
x_67 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_67, 0, x_66);
if (lean_is_scalar(x_65)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_65;
}
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_64);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_69 = lean_ctor_get(x_62, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_70 = x_62;
} else {
 lean_dec_ref(x_62);
 x_70 = lean_box(0);
}
x_71 = lean_ctor_get(x_63, 0);
lean_inc(x_71);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 x_72 = x_63;
} else {
 lean_dec_ref(x_63);
 x_72 = lean_box(0);
}
x_73 = lean_nat_mod(x_60, x_71);
lean_dec(x_71);
lean_dec(x_60);
x_74 = l_Lean_mkNatLit(x_73);
if (lean_is_scalar(x_72)) {
 x_75 = lean_alloc_ctor(0, 1, 0);
} else {
 x_75 = x_72;
 lean_ctor_set_tag(x_75, 0);
}
lean_ctor_set(x_75, 0, x_74);
if (lean_is_scalar(x_70)) {
 x_76 = lean_alloc_ctor(0, 2, 0);
} else {
 x_76 = x_70;
}
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_69);
return x_76;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_60);
x_77 = lean_ctor_get(x_62, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_62, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_79 = x_62;
} else {
 lean_dec_ref(x_62);
 x_79 = lean_box(0);
}
if (lean_is_scalar(x_79)) {
 x_80 = lean_alloc_ctor(1, 2, 0);
} else {
 x_80 = x_79;
}
lean_ctor_set(x_80, 0, x_77);
lean_ctor_set(x_80, 1, x_78);
return x_80;
}
}
}
}
else
{
uint8_t x_81; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_81 = !lean_is_exclusive(x_17);
if (x_81 == 0)
{
return x_17;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_17, 0);
x_83 = lean_ctor_get(x_17, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_17);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceMod(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Nat_reduceMod___redArg(x_1, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceMod___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Nat_reduceMod___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceMod___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Nat_reduceMod(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceMod_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_749_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_2 = lean_mk_string_unchecked("Nat", 3, 3);
x_3 = lean_mk_string_unchecked("reduceMod", 9, 9);
lean_inc(x_2);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_mk_string_unchecked("HMod", 4, 4);
x_6 = lean_mk_string_unchecked("hMod", 4, 4);
x_7 = l_Lean_Name_mkStr2(x_5, x_6);
x_8 = lean_unsigned_to_nat(6u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Lean_Name_mkStr1(x_2);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_box(3);
x_14 = lean_unsigned_to_nat(7u);
x_15 = lean_mk_empty_array_with_capacity(x_14);
x_16 = lean_array_push(x_15, x_9);
lean_inc(x_12);
x_17 = lean_array_push(x_16, x_12);
lean_inc(x_12);
x_18 = lean_array_push(x_17, x_12);
x_19 = lean_array_push(x_18, x_12);
x_20 = lean_array_push(x_19, x_13);
x_21 = lean_array_push(x_20, x_13);
x_22 = lean_array_push(x_21, x_13);
x_23 = lean_alloc_closure((void*)(l_Nat_reduceMod___boxed), 9, 0);
x_24 = l_Lean_Meta_Simp_registerBuiltinDSimproc(x_4, x_22, x_23, x_1);
return x_24;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceMod_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_751_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Nat", 3, 3);
x_3 = lean_mk_string_unchecked("reduceMod", 9, 9);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Nat_reduceMod___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceMod_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_753_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Nat", 3, 3);
x_3 = lean_mk_string_unchecked("reduceMod", 9, 9);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Nat_reduceMod___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Nat_reducePow___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_12; uint8_t x_13; 
x_12 = l_Lean_Expr_cleanupAnnotations(x_1);
x_13 = l_Lean_Expr_isApp(x_12);
if (x_13 == 0)
{
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_7 = x_6;
goto block_11;
}
else
{
lean_object* x_14; uint8_t x_15; 
lean_inc(x_12);
x_14 = l_Lean_Expr_appFnCleanup___redArg(x_12);
x_15 = l_Lean_Expr_isApp(x_14);
if (x_15 == 0)
{
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_7 = x_6;
goto block_11;
}
else
{
lean_object* x_16; uint8_t x_17; 
lean_inc(x_14);
x_16 = l_Lean_Expr_appFnCleanup___redArg(x_14);
x_17 = l_Lean_Expr_isApp(x_16);
if (x_17 == 0)
{
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_7 = x_6;
goto block_11;
}
else
{
lean_object* x_18; uint8_t x_19; 
x_18 = l_Lean_Expr_appFnCleanup___redArg(x_16);
x_19 = l_Lean_Expr_isApp(x_18);
if (x_19 == 0)
{
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_7 = x_6;
goto block_11;
}
else
{
lean_object* x_20; uint8_t x_21; 
x_20 = l_Lean_Expr_appFnCleanup___redArg(x_18);
x_21 = l_Lean_Expr_isApp(x_20);
if (x_21 == 0)
{
lean_dec(x_20);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_7 = x_6;
goto block_11;
}
else
{
lean_object* x_22; uint8_t x_23; 
x_22 = l_Lean_Expr_appFnCleanup___redArg(x_20);
x_23 = l_Lean_Expr_isApp(x_22);
if (x_23 == 0)
{
lean_dec(x_22);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_7 = x_6;
goto block_11;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_24 = l_Lean_Expr_appFnCleanup___redArg(x_22);
x_25 = lean_mk_string_unchecked("HPow", 4, 4);
x_26 = lean_mk_string_unchecked("hPow", 4, 4);
x_27 = l_Lean_Name_mkStr2(x_25, x_26);
x_28 = l_Lean_Expr_isConstOf(x_24, x_27);
lean_dec(x_27);
lean_dec(x_24);
if (x_28 == 0)
{
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_7 = x_6;
goto block_11;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_14, 1);
lean_inc(x_29);
lean_dec(x_14);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_30 = l_Lean_Meta_getNatValue_x3f(x_29, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_32 = !lean_is_exclusive(x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_30, 0);
lean_dec(x_33);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_30, 0, x_35);
return x_30;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_30, 1);
lean_inc(x_36);
lean_dec(x_30);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_38, 0, x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_36);
return x_39;
}
}
else
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_30, 1);
lean_inc(x_40);
lean_dec(x_30);
x_41 = !lean_is_exclusive(x_31);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_31, 0);
x_43 = lean_ctor_get(x_12, 1);
lean_inc(x_43);
lean_dec(x_12);
lean_inc(x_5);
lean_inc(x_4);
x_44 = l_Lean_Meta_getNatValue_x3f(x_43, x_2, x_3, x_4, x_5, x_40);
lean_dec(x_43);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
if (lean_obj_tag(x_45) == 0)
{
uint8_t x_46; 
lean_dec(x_42);
lean_dec(x_5);
lean_dec(x_4);
x_46 = !lean_is_exclusive(x_44);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_44, 0);
lean_dec(x_47);
x_48 = lean_box(0);
lean_ctor_set_tag(x_31, 2);
lean_ctor_set(x_31, 0, x_48);
lean_ctor_set(x_44, 0, x_31);
return x_44;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_44, 1);
lean_inc(x_49);
lean_dec(x_44);
x_50 = lean_box(0);
lean_ctor_set_tag(x_31, 2);
lean_ctor_set(x_31, 0, x_50);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_31);
lean_ctor_set(x_51, 1, x_49);
return x_51;
}
}
else
{
lean_object* x_52; uint8_t x_53; 
lean_free_object(x_31);
x_52 = lean_ctor_get(x_44, 1);
lean_inc(x_52);
lean_dec(x_44);
x_53 = !lean_is_exclusive(x_45);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_54 = lean_ctor_get(x_45, 0);
lean_inc(x_54);
x_55 = l_Lean_checkExponent(x_54, x_4, x_5, x_52);
lean_dec(x_5);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_unbox(x_56);
lean_dec(x_56);
if (x_57 == 0)
{
uint8_t x_58; 
lean_dec(x_54);
lean_dec(x_42);
x_58 = !lean_is_exclusive(x_55);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_55, 0);
lean_dec(x_59);
x_60 = lean_box(0);
lean_ctor_set_tag(x_45, 2);
lean_ctor_set(x_45, 0, x_60);
lean_ctor_set(x_55, 0, x_45);
return x_55;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_55, 1);
lean_inc(x_61);
lean_dec(x_55);
x_62 = lean_box(0);
lean_ctor_set_tag(x_45, 2);
lean_ctor_set(x_45, 0, x_62);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_45);
lean_ctor_set(x_63, 1, x_61);
return x_63;
}
}
else
{
uint8_t x_64; 
x_64 = !lean_is_exclusive(x_55);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_55, 0);
lean_dec(x_65);
x_66 = lean_nat_pow(x_42, x_54);
lean_dec(x_54);
lean_dec(x_42);
x_67 = l_Lean_mkNatLit(x_66);
lean_ctor_set_tag(x_45, 0);
lean_ctor_set(x_45, 0, x_67);
lean_ctor_set(x_55, 0, x_45);
return x_55;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_68 = lean_ctor_get(x_55, 1);
lean_inc(x_68);
lean_dec(x_55);
x_69 = lean_nat_pow(x_42, x_54);
lean_dec(x_54);
lean_dec(x_42);
x_70 = l_Lean_mkNatLit(x_69);
lean_ctor_set_tag(x_45, 0);
lean_ctor_set(x_45, 0, x_70);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_45);
lean_ctor_set(x_71, 1, x_68);
return x_71;
}
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_72 = lean_ctor_get(x_45, 0);
lean_inc(x_72);
lean_dec(x_45);
lean_inc(x_72);
x_73 = l_Lean_checkExponent(x_72, x_4, x_5, x_52);
lean_dec(x_5);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_unbox(x_74);
lean_dec(x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_72);
lean_dec(x_42);
x_76 = lean_ctor_get(x_73, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_77 = x_73;
} else {
 lean_dec_ref(x_73);
 x_77 = lean_box(0);
}
x_78 = lean_box(0);
x_79 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_79, 0, x_78);
if (lean_is_scalar(x_77)) {
 x_80 = lean_alloc_ctor(0, 2, 0);
} else {
 x_80 = x_77;
}
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_76);
return x_80;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_81 = lean_ctor_get(x_73, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_82 = x_73;
} else {
 lean_dec_ref(x_73);
 x_82 = lean_box(0);
}
x_83 = lean_nat_pow(x_42, x_72);
lean_dec(x_72);
lean_dec(x_42);
x_84 = l_Lean_mkNatLit(x_83);
x_85 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_85, 0, x_84);
if (lean_is_scalar(x_82)) {
 x_86 = lean_alloc_ctor(0, 2, 0);
} else {
 x_86 = x_82;
}
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_81);
return x_86;
}
}
}
}
else
{
uint8_t x_87; 
lean_free_object(x_31);
lean_dec(x_42);
lean_dec(x_5);
lean_dec(x_4);
x_87 = !lean_is_exclusive(x_44);
if (x_87 == 0)
{
return x_44;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_44, 0);
x_89 = lean_ctor_get(x_44, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_44);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_31, 0);
lean_inc(x_91);
lean_dec(x_31);
x_92 = lean_ctor_get(x_12, 1);
lean_inc(x_92);
lean_dec(x_12);
lean_inc(x_5);
lean_inc(x_4);
x_93 = l_Lean_Meta_getNatValue_x3f(x_92, x_2, x_3, x_4, x_5, x_40);
lean_dec(x_92);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_91);
lean_dec(x_5);
lean_dec(x_4);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_96 = x_93;
} else {
 lean_dec_ref(x_93);
 x_96 = lean_box(0);
}
x_97 = lean_box(0);
x_98 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_98, 0, x_97);
if (lean_is_scalar(x_96)) {
 x_99 = lean_alloc_ctor(0, 2, 0);
} else {
 x_99 = x_96;
}
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_95);
return x_99;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; 
x_100 = lean_ctor_get(x_93, 1);
lean_inc(x_100);
lean_dec(x_93);
x_101 = lean_ctor_get(x_94, 0);
lean_inc(x_101);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 x_102 = x_94;
} else {
 lean_dec_ref(x_94);
 x_102 = lean_box(0);
}
lean_inc(x_101);
x_103 = l_Lean_checkExponent(x_101, x_4, x_5, x_100);
lean_dec(x_5);
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_unbox(x_104);
lean_dec(x_104);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_dec(x_101);
lean_dec(x_91);
x_106 = lean_ctor_get(x_103, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_107 = x_103;
} else {
 lean_dec_ref(x_103);
 x_107 = lean_box(0);
}
x_108 = lean_box(0);
if (lean_is_scalar(x_102)) {
 x_109 = lean_alloc_ctor(2, 1, 0);
} else {
 x_109 = x_102;
 lean_ctor_set_tag(x_109, 2);
}
lean_ctor_set(x_109, 0, x_108);
if (lean_is_scalar(x_107)) {
 x_110 = lean_alloc_ctor(0, 2, 0);
} else {
 x_110 = x_107;
}
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_106);
return x_110;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_111 = lean_ctor_get(x_103, 1);
lean_inc(x_111);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_112 = x_103;
} else {
 lean_dec_ref(x_103);
 x_112 = lean_box(0);
}
x_113 = lean_nat_pow(x_91, x_101);
lean_dec(x_101);
lean_dec(x_91);
x_114 = l_Lean_mkNatLit(x_113);
if (lean_is_scalar(x_102)) {
 x_115 = lean_alloc_ctor(0, 1, 0);
} else {
 x_115 = x_102;
 lean_ctor_set_tag(x_115, 0);
}
lean_ctor_set(x_115, 0, x_114);
if (lean_is_scalar(x_112)) {
 x_116 = lean_alloc_ctor(0, 2, 0);
} else {
 x_116 = x_112;
}
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_111);
return x_116;
}
}
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
lean_dec(x_91);
lean_dec(x_5);
lean_dec(x_4);
x_117 = lean_ctor_get(x_93, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_93, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_119 = x_93;
} else {
 lean_dec_ref(x_93);
 x_119 = lean_box(0);
}
if (lean_is_scalar(x_119)) {
 x_120 = lean_alloc_ctor(1, 2, 0);
} else {
 x_120 = x_119;
}
lean_ctor_set(x_120, 0, x_117);
lean_ctor_set(x_120, 1, x_118);
return x_120;
}
}
}
}
else
{
uint8_t x_121; 
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_121 = !lean_is_exclusive(x_30);
if (x_121 == 0)
{
return x_30;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_30, 0);
x_123 = lean_ctor_get(x_30, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_30);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
return x_124;
}
}
}
}
}
}
}
}
}
block_11:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Nat_reducePow(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Nat_reducePow___redArg(x_1, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Nat_reducePow___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Nat_reducePow___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Nat_reducePow___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Nat_reducePow(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reducePow_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1170_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_2 = lean_mk_string_unchecked("Nat", 3, 3);
x_3 = lean_mk_string_unchecked("reducePow", 9, 9);
lean_inc(x_2);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_mk_string_unchecked("HPow", 4, 4);
x_6 = lean_mk_string_unchecked("hPow", 4, 4);
x_7 = l_Lean_Name_mkStr2(x_5, x_6);
x_8 = lean_unsigned_to_nat(6u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Lean_Name_mkStr1(x_2);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_box(3);
x_14 = lean_unsigned_to_nat(7u);
x_15 = lean_mk_empty_array_with_capacity(x_14);
x_16 = lean_array_push(x_15, x_9);
lean_inc(x_12);
x_17 = lean_array_push(x_16, x_12);
x_18 = lean_array_push(x_17, x_13);
x_19 = lean_array_push(x_18, x_12);
x_20 = lean_array_push(x_19, x_13);
x_21 = lean_array_push(x_20, x_13);
x_22 = lean_array_push(x_21, x_13);
x_23 = lean_alloc_closure((void*)(l_Nat_reducePow___boxed), 9, 0);
x_24 = l_Lean_Meta_Simp_registerBuiltinDSimproc(x_4, x_22, x_23, x_1);
return x_24;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reducePow_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1172_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Nat", 3, 3);
x_3 = lean_mk_string_unchecked("reducePow", 9, 9);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Nat_reducePow___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reducePow_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1174_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Nat", 3, 3);
x_3 = lean_mk_string_unchecked("reducePow", 9, 9);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Nat_reducePow___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceAnd___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_mk_string_unchecked("HAnd", 4, 4);
x_8 = lean_mk_string_unchecked("hAnd", 4, 4);
x_9 = l_Lean_Name_mkStr2(x_7, x_8);
x_10 = lean_unsigned_to_nat(6u);
x_11 = l_Lean_Expr_isAppOfArity(x_1, x_9, x_10);
lean_dec(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_6);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = l_Lean_Expr_appFn_x21(x_1);
x_16 = l_Lean_Expr_appArg_x21(x_15);
lean_dec(x_15);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_17 = l_Lean_Meta_getNatValue_x3f(x_16, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_17, 0);
lean_dec(x_20);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_17, 0, x_22);
return x_17;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_dec(x_17);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_23);
return x_26;
}
}
else
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_17, 1);
lean_inc(x_27);
lean_dec(x_17);
x_28 = !lean_is_exclusive(x_18);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_18, 0);
x_30 = l_Lean_Expr_appArg_x21(x_1);
x_31 = l_Lean_Meta_getNatValue_x3f(x_30, x_2, x_3, x_4, x_5, x_27);
lean_dec(x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
lean_dec(x_29);
x_33 = !lean_is_exclusive(x_31);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_31, 0);
lean_dec(x_34);
x_35 = lean_box(0);
lean_ctor_set_tag(x_18, 2);
lean_ctor_set(x_18, 0, x_35);
lean_ctor_set(x_31, 0, x_18);
return x_31;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_31, 1);
lean_inc(x_36);
lean_dec(x_31);
x_37 = lean_box(0);
lean_ctor_set_tag(x_18, 2);
lean_ctor_set(x_18, 0, x_37);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_18);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
else
{
uint8_t x_39; 
lean_free_object(x_18);
x_39 = !lean_is_exclusive(x_31);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_31, 0);
lean_dec(x_40);
x_41 = !lean_is_exclusive(x_32);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_32, 0);
x_43 = lean_nat_land(x_29, x_42);
lean_dec(x_42);
lean_dec(x_29);
x_44 = l_Lean_mkNatLit(x_43);
lean_ctor_set_tag(x_32, 0);
lean_ctor_set(x_32, 0, x_44);
return x_31;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_32, 0);
lean_inc(x_45);
lean_dec(x_32);
x_46 = lean_nat_land(x_29, x_45);
lean_dec(x_45);
lean_dec(x_29);
x_47 = l_Lean_mkNatLit(x_46);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_31, 0, x_48);
return x_31;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_49 = lean_ctor_get(x_31, 1);
lean_inc(x_49);
lean_dec(x_31);
x_50 = lean_ctor_get(x_32, 0);
lean_inc(x_50);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 x_51 = x_32;
} else {
 lean_dec_ref(x_32);
 x_51 = lean_box(0);
}
x_52 = lean_nat_land(x_29, x_50);
lean_dec(x_50);
lean_dec(x_29);
x_53 = l_Lean_mkNatLit(x_52);
if (lean_is_scalar(x_51)) {
 x_54 = lean_alloc_ctor(0, 1, 0);
} else {
 x_54 = x_51;
 lean_ctor_set_tag(x_54, 0);
}
lean_ctor_set(x_54, 0, x_53);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_49);
return x_55;
}
}
}
else
{
uint8_t x_56; 
lean_free_object(x_18);
lean_dec(x_29);
x_56 = !lean_is_exclusive(x_31);
if (x_56 == 0)
{
return x_31;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_31, 0);
x_58 = lean_ctor_get(x_31, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_31);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_18, 0);
lean_inc(x_60);
lean_dec(x_18);
x_61 = l_Lean_Expr_appArg_x21(x_1);
x_62 = l_Lean_Meta_getNatValue_x3f(x_61, x_2, x_3, x_4, x_5, x_27);
lean_dec(x_61);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_60);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_65 = x_62;
} else {
 lean_dec_ref(x_62);
 x_65 = lean_box(0);
}
x_66 = lean_box(0);
x_67 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_67, 0, x_66);
if (lean_is_scalar(x_65)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_65;
}
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_64);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_69 = lean_ctor_get(x_62, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_70 = x_62;
} else {
 lean_dec_ref(x_62);
 x_70 = lean_box(0);
}
x_71 = lean_ctor_get(x_63, 0);
lean_inc(x_71);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 x_72 = x_63;
} else {
 lean_dec_ref(x_63);
 x_72 = lean_box(0);
}
x_73 = lean_nat_land(x_60, x_71);
lean_dec(x_71);
lean_dec(x_60);
x_74 = l_Lean_mkNatLit(x_73);
if (lean_is_scalar(x_72)) {
 x_75 = lean_alloc_ctor(0, 1, 0);
} else {
 x_75 = x_72;
 lean_ctor_set_tag(x_75, 0);
}
lean_ctor_set(x_75, 0, x_74);
if (lean_is_scalar(x_70)) {
 x_76 = lean_alloc_ctor(0, 2, 0);
} else {
 x_76 = x_70;
}
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_69);
return x_76;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_60);
x_77 = lean_ctor_get(x_62, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_62, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_79 = x_62;
} else {
 lean_dec_ref(x_62);
 x_79 = lean_box(0);
}
if (lean_is_scalar(x_79)) {
 x_80 = lean_alloc_ctor(1, 2, 0);
} else {
 x_80 = x_79;
}
lean_ctor_set(x_80, 0, x_77);
lean_ctor_set(x_80, 1, x_78);
return x_80;
}
}
}
}
else
{
uint8_t x_81; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_81 = !lean_is_exclusive(x_17);
if (x_81 == 0)
{
return x_17;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_17, 0);
x_83 = lean_ctor_get(x_17, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_17);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceAnd(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Nat_reduceAnd___redArg(x_1, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceAnd___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Nat_reduceAnd___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceAnd___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Nat_reduceAnd(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceAnd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1208_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_2 = lean_mk_string_unchecked("Nat", 3, 3);
x_3 = lean_mk_string_unchecked("reduceAnd", 9, 9);
lean_inc(x_2);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_mk_string_unchecked("HAnd", 4, 4);
x_6 = lean_mk_string_unchecked("hAnd", 4, 4);
x_7 = l_Lean_Name_mkStr2(x_5, x_6);
x_8 = lean_unsigned_to_nat(6u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Lean_Name_mkStr1(x_2);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_box(3);
x_14 = lean_unsigned_to_nat(7u);
x_15 = lean_mk_empty_array_with_capacity(x_14);
x_16 = lean_array_push(x_15, x_9);
lean_inc(x_12);
x_17 = lean_array_push(x_16, x_12);
lean_inc(x_12);
x_18 = lean_array_push(x_17, x_12);
x_19 = lean_array_push(x_18, x_12);
x_20 = lean_array_push(x_19, x_13);
x_21 = lean_array_push(x_20, x_13);
x_22 = lean_array_push(x_21, x_13);
x_23 = lean_alloc_closure((void*)(l_Nat_reduceAnd___boxed), 9, 0);
x_24 = l_Lean_Meta_Simp_registerBuiltinDSimproc(x_4, x_22, x_23, x_1);
return x_24;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceAnd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1210_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Nat", 3, 3);
x_3 = lean_mk_string_unchecked("reduceAnd", 9, 9);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Nat_reduceAnd___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceAnd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1212_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Nat", 3, 3);
x_3 = lean_mk_string_unchecked("reduceAnd", 9, 9);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Nat_reduceAnd___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceXor___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_mk_string_unchecked("HXor", 4, 4);
x_8 = lean_mk_string_unchecked("hXor", 4, 4);
x_9 = l_Lean_Name_mkStr2(x_7, x_8);
x_10 = lean_unsigned_to_nat(6u);
x_11 = l_Lean_Expr_isAppOfArity(x_1, x_9, x_10);
lean_dec(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_6);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = l_Lean_Expr_appFn_x21(x_1);
x_16 = l_Lean_Expr_appArg_x21(x_15);
lean_dec(x_15);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_17 = l_Lean_Meta_getNatValue_x3f(x_16, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_17, 0);
lean_dec(x_20);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_17, 0, x_22);
return x_17;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_dec(x_17);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_23);
return x_26;
}
}
else
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_17, 1);
lean_inc(x_27);
lean_dec(x_17);
x_28 = !lean_is_exclusive(x_18);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_18, 0);
x_30 = l_Lean_Expr_appArg_x21(x_1);
x_31 = l_Lean_Meta_getNatValue_x3f(x_30, x_2, x_3, x_4, x_5, x_27);
lean_dec(x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
lean_dec(x_29);
x_33 = !lean_is_exclusive(x_31);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_31, 0);
lean_dec(x_34);
x_35 = lean_box(0);
lean_ctor_set_tag(x_18, 2);
lean_ctor_set(x_18, 0, x_35);
lean_ctor_set(x_31, 0, x_18);
return x_31;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_31, 1);
lean_inc(x_36);
lean_dec(x_31);
x_37 = lean_box(0);
lean_ctor_set_tag(x_18, 2);
lean_ctor_set(x_18, 0, x_37);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_18);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
else
{
uint8_t x_39; 
lean_free_object(x_18);
x_39 = !lean_is_exclusive(x_31);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_31, 0);
lean_dec(x_40);
x_41 = !lean_is_exclusive(x_32);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_32, 0);
x_43 = lean_nat_lxor(x_29, x_42);
lean_dec(x_42);
lean_dec(x_29);
x_44 = l_Lean_mkNatLit(x_43);
lean_ctor_set_tag(x_32, 0);
lean_ctor_set(x_32, 0, x_44);
return x_31;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_32, 0);
lean_inc(x_45);
lean_dec(x_32);
x_46 = lean_nat_lxor(x_29, x_45);
lean_dec(x_45);
lean_dec(x_29);
x_47 = l_Lean_mkNatLit(x_46);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_31, 0, x_48);
return x_31;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_49 = lean_ctor_get(x_31, 1);
lean_inc(x_49);
lean_dec(x_31);
x_50 = lean_ctor_get(x_32, 0);
lean_inc(x_50);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 x_51 = x_32;
} else {
 lean_dec_ref(x_32);
 x_51 = lean_box(0);
}
x_52 = lean_nat_lxor(x_29, x_50);
lean_dec(x_50);
lean_dec(x_29);
x_53 = l_Lean_mkNatLit(x_52);
if (lean_is_scalar(x_51)) {
 x_54 = lean_alloc_ctor(0, 1, 0);
} else {
 x_54 = x_51;
 lean_ctor_set_tag(x_54, 0);
}
lean_ctor_set(x_54, 0, x_53);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_49);
return x_55;
}
}
}
else
{
uint8_t x_56; 
lean_free_object(x_18);
lean_dec(x_29);
x_56 = !lean_is_exclusive(x_31);
if (x_56 == 0)
{
return x_31;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_31, 0);
x_58 = lean_ctor_get(x_31, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_31);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_18, 0);
lean_inc(x_60);
lean_dec(x_18);
x_61 = l_Lean_Expr_appArg_x21(x_1);
x_62 = l_Lean_Meta_getNatValue_x3f(x_61, x_2, x_3, x_4, x_5, x_27);
lean_dec(x_61);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_60);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_65 = x_62;
} else {
 lean_dec_ref(x_62);
 x_65 = lean_box(0);
}
x_66 = lean_box(0);
x_67 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_67, 0, x_66);
if (lean_is_scalar(x_65)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_65;
}
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_64);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_69 = lean_ctor_get(x_62, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_70 = x_62;
} else {
 lean_dec_ref(x_62);
 x_70 = lean_box(0);
}
x_71 = lean_ctor_get(x_63, 0);
lean_inc(x_71);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 x_72 = x_63;
} else {
 lean_dec_ref(x_63);
 x_72 = lean_box(0);
}
x_73 = lean_nat_lxor(x_60, x_71);
lean_dec(x_71);
lean_dec(x_60);
x_74 = l_Lean_mkNatLit(x_73);
if (lean_is_scalar(x_72)) {
 x_75 = lean_alloc_ctor(0, 1, 0);
} else {
 x_75 = x_72;
 lean_ctor_set_tag(x_75, 0);
}
lean_ctor_set(x_75, 0, x_74);
if (lean_is_scalar(x_70)) {
 x_76 = lean_alloc_ctor(0, 2, 0);
} else {
 x_76 = x_70;
}
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_69);
return x_76;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_60);
x_77 = lean_ctor_get(x_62, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_62, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_79 = x_62;
} else {
 lean_dec_ref(x_62);
 x_79 = lean_box(0);
}
if (lean_is_scalar(x_79)) {
 x_80 = lean_alloc_ctor(1, 2, 0);
} else {
 x_80 = x_79;
}
lean_ctor_set(x_80, 0, x_77);
lean_ctor_set(x_80, 1, x_78);
return x_80;
}
}
}
}
else
{
uint8_t x_81; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_81 = !lean_is_exclusive(x_17);
if (x_81 == 0)
{
return x_17;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_17, 0);
x_83 = lean_ctor_get(x_17, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_17);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceXor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Nat_reduceXor___redArg(x_1, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceXor___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Nat_reduceXor___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceXor___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Nat_reduceXor(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceXor_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1246_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_2 = lean_mk_string_unchecked("Nat", 3, 3);
x_3 = lean_mk_string_unchecked("reduceXor", 9, 9);
lean_inc(x_2);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_mk_string_unchecked("HXor", 4, 4);
x_6 = lean_mk_string_unchecked("hXor", 4, 4);
x_7 = l_Lean_Name_mkStr2(x_5, x_6);
x_8 = lean_unsigned_to_nat(6u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Lean_Name_mkStr1(x_2);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_box(3);
x_14 = lean_unsigned_to_nat(7u);
x_15 = lean_mk_empty_array_with_capacity(x_14);
x_16 = lean_array_push(x_15, x_9);
lean_inc(x_12);
x_17 = lean_array_push(x_16, x_12);
lean_inc(x_12);
x_18 = lean_array_push(x_17, x_12);
x_19 = lean_array_push(x_18, x_12);
x_20 = lean_array_push(x_19, x_13);
x_21 = lean_array_push(x_20, x_13);
x_22 = lean_array_push(x_21, x_13);
x_23 = lean_alloc_closure((void*)(l_Nat_reduceXor___boxed), 9, 0);
x_24 = l_Lean_Meta_Simp_registerBuiltinDSimproc(x_4, x_22, x_23, x_1);
return x_24;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceXor_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1248_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Nat", 3, 3);
x_3 = lean_mk_string_unchecked("reduceXor", 9, 9);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Nat_reduceXor___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceXor_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1250_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Nat", 3, 3);
x_3 = lean_mk_string_unchecked("reduceXor", 9, 9);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Nat_reduceXor___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceOr___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_mk_string_unchecked("HOr", 3, 3);
x_8 = lean_mk_string_unchecked("hOr", 3, 3);
x_9 = l_Lean_Name_mkStr2(x_7, x_8);
x_10 = lean_unsigned_to_nat(6u);
x_11 = l_Lean_Expr_isAppOfArity(x_1, x_9, x_10);
lean_dec(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_6);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = l_Lean_Expr_appFn_x21(x_1);
x_16 = l_Lean_Expr_appArg_x21(x_15);
lean_dec(x_15);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_17 = l_Lean_Meta_getNatValue_x3f(x_16, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_17, 0);
lean_dec(x_20);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_17, 0, x_22);
return x_17;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_dec(x_17);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_23);
return x_26;
}
}
else
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_17, 1);
lean_inc(x_27);
lean_dec(x_17);
x_28 = !lean_is_exclusive(x_18);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_18, 0);
x_30 = l_Lean_Expr_appArg_x21(x_1);
x_31 = l_Lean_Meta_getNatValue_x3f(x_30, x_2, x_3, x_4, x_5, x_27);
lean_dec(x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
lean_dec(x_29);
x_33 = !lean_is_exclusive(x_31);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_31, 0);
lean_dec(x_34);
x_35 = lean_box(0);
lean_ctor_set_tag(x_18, 2);
lean_ctor_set(x_18, 0, x_35);
lean_ctor_set(x_31, 0, x_18);
return x_31;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_31, 1);
lean_inc(x_36);
lean_dec(x_31);
x_37 = lean_box(0);
lean_ctor_set_tag(x_18, 2);
lean_ctor_set(x_18, 0, x_37);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_18);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
else
{
uint8_t x_39; 
lean_free_object(x_18);
x_39 = !lean_is_exclusive(x_31);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_31, 0);
lean_dec(x_40);
x_41 = !lean_is_exclusive(x_32);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_32, 0);
x_43 = lean_nat_lor(x_29, x_42);
lean_dec(x_42);
lean_dec(x_29);
x_44 = l_Lean_mkNatLit(x_43);
lean_ctor_set_tag(x_32, 0);
lean_ctor_set(x_32, 0, x_44);
return x_31;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_32, 0);
lean_inc(x_45);
lean_dec(x_32);
x_46 = lean_nat_lor(x_29, x_45);
lean_dec(x_45);
lean_dec(x_29);
x_47 = l_Lean_mkNatLit(x_46);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_31, 0, x_48);
return x_31;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_49 = lean_ctor_get(x_31, 1);
lean_inc(x_49);
lean_dec(x_31);
x_50 = lean_ctor_get(x_32, 0);
lean_inc(x_50);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 x_51 = x_32;
} else {
 lean_dec_ref(x_32);
 x_51 = lean_box(0);
}
x_52 = lean_nat_lor(x_29, x_50);
lean_dec(x_50);
lean_dec(x_29);
x_53 = l_Lean_mkNatLit(x_52);
if (lean_is_scalar(x_51)) {
 x_54 = lean_alloc_ctor(0, 1, 0);
} else {
 x_54 = x_51;
 lean_ctor_set_tag(x_54, 0);
}
lean_ctor_set(x_54, 0, x_53);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_49);
return x_55;
}
}
}
else
{
uint8_t x_56; 
lean_free_object(x_18);
lean_dec(x_29);
x_56 = !lean_is_exclusive(x_31);
if (x_56 == 0)
{
return x_31;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_31, 0);
x_58 = lean_ctor_get(x_31, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_31);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_18, 0);
lean_inc(x_60);
lean_dec(x_18);
x_61 = l_Lean_Expr_appArg_x21(x_1);
x_62 = l_Lean_Meta_getNatValue_x3f(x_61, x_2, x_3, x_4, x_5, x_27);
lean_dec(x_61);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_60);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_65 = x_62;
} else {
 lean_dec_ref(x_62);
 x_65 = lean_box(0);
}
x_66 = lean_box(0);
x_67 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_67, 0, x_66);
if (lean_is_scalar(x_65)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_65;
}
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_64);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_69 = lean_ctor_get(x_62, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_70 = x_62;
} else {
 lean_dec_ref(x_62);
 x_70 = lean_box(0);
}
x_71 = lean_ctor_get(x_63, 0);
lean_inc(x_71);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 x_72 = x_63;
} else {
 lean_dec_ref(x_63);
 x_72 = lean_box(0);
}
x_73 = lean_nat_lor(x_60, x_71);
lean_dec(x_71);
lean_dec(x_60);
x_74 = l_Lean_mkNatLit(x_73);
if (lean_is_scalar(x_72)) {
 x_75 = lean_alloc_ctor(0, 1, 0);
} else {
 x_75 = x_72;
 lean_ctor_set_tag(x_75, 0);
}
lean_ctor_set(x_75, 0, x_74);
if (lean_is_scalar(x_70)) {
 x_76 = lean_alloc_ctor(0, 2, 0);
} else {
 x_76 = x_70;
}
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_69);
return x_76;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_60);
x_77 = lean_ctor_get(x_62, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_62, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_79 = x_62;
} else {
 lean_dec_ref(x_62);
 x_79 = lean_box(0);
}
if (lean_is_scalar(x_79)) {
 x_80 = lean_alloc_ctor(1, 2, 0);
} else {
 x_80 = x_79;
}
lean_ctor_set(x_80, 0, x_77);
lean_ctor_set(x_80, 1, x_78);
return x_80;
}
}
}
}
else
{
uint8_t x_81; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_81 = !lean_is_exclusive(x_17);
if (x_81 == 0)
{
return x_17;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_17, 0);
x_83 = lean_ctor_get(x_17, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_17);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceOr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Nat_reduceOr___redArg(x_1, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceOr___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Nat_reduceOr___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceOr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Nat_reduceOr(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceOr_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1284_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_2 = lean_mk_string_unchecked("Nat", 3, 3);
x_3 = lean_mk_string_unchecked("reduceOr", 8, 8);
lean_inc(x_2);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_mk_string_unchecked("HOr", 3, 3);
x_6 = lean_mk_string_unchecked("hOr", 3, 3);
x_7 = l_Lean_Name_mkStr2(x_5, x_6);
x_8 = lean_unsigned_to_nat(6u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Lean_Name_mkStr1(x_2);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_box(3);
x_14 = lean_unsigned_to_nat(7u);
x_15 = lean_mk_empty_array_with_capacity(x_14);
x_16 = lean_array_push(x_15, x_9);
lean_inc(x_12);
x_17 = lean_array_push(x_16, x_12);
lean_inc(x_12);
x_18 = lean_array_push(x_17, x_12);
x_19 = lean_array_push(x_18, x_12);
x_20 = lean_array_push(x_19, x_13);
x_21 = lean_array_push(x_20, x_13);
x_22 = lean_array_push(x_21, x_13);
x_23 = lean_alloc_closure((void*)(l_Nat_reduceOr___boxed), 9, 0);
x_24 = l_Lean_Meta_Simp_registerBuiltinDSimproc(x_4, x_22, x_23, x_1);
return x_24;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceOr_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1286_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Nat", 3, 3);
x_3 = lean_mk_string_unchecked("reduceOr", 8, 8);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Nat_reduceOr___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceOr_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1288_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Nat", 3, 3);
x_3 = lean_mk_string_unchecked("reduceOr", 8, 8);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Nat_reduceOr___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceShiftLeft___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_mk_string_unchecked("HShiftLeft", 10, 10);
x_8 = lean_mk_string_unchecked("hShiftLeft", 10, 10);
x_9 = l_Lean_Name_mkStr2(x_7, x_8);
x_10 = lean_unsigned_to_nat(6u);
x_11 = l_Lean_Expr_isAppOfArity(x_1, x_9, x_10);
lean_dec(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_6);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = l_Lean_Expr_appFn_x21(x_1);
x_16 = l_Lean_Expr_appArg_x21(x_15);
lean_dec(x_15);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_17 = l_Lean_Meta_getNatValue_x3f(x_16, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_17, 0);
lean_dec(x_20);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_17, 0, x_22);
return x_17;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_dec(x_17);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_23);
return x_26;
}
}
else
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_17, 1);
lean_inc(x_27);
lean_dec(x_17);
x_28 = !lean_is_exclusive(x_18);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_18, 0);
x_30 = l_Lean_Expr_appArg_x21(x_1);
x_31 = l_Lean_Meta_getNatValue_x3f(x_30, x_2, x_3, x_4, x_5, x_27);
lean_dec(x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
lean_dec(x_29);
x_33 = !lean_is_exclusive(x_31);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_31, 0);
lean_dec(x_34);
x_35 = lean_box(0);
lean_ctor_set_tag(x_18, 2);
lean_ctor_set(x_18, 0, x_35);
lean_ctor_set(x_31, 0, x_18);
return x_31;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_31, 1);
lean_inc(x_36);
lean_dec(x_31);
x_37 = lean_box(0);
lean_ctor_set_tag(x_18, 2);
lean_ctor_set(x_18, 0, x_37);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_18);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
else
{
uint8_t x_39; 
lean_free_object(x_18);
x_39 = !lean_is_exclusive(x_31);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_31, 0);
lean_dec(x_40);
x_41 = !lean_is_exclusive(x_32);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_32, 0);
x_43 = lean_nat_shiftl(x_29, x_42);
lean_dec(x_42);
lean_dec(x_29);
x_44 = l_Lean_mkNatLit(x_43);
lean_ctor_set_tag(x_32, 0);
lean_ctor_set(x_32, 0, x_44);
return x_31;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_32, 0);
lean_inc(x_45);
lean_dec(x_32);
x_46 = lean_nat_shiftl(x_29, x_45);
lean_dec(x_45);
lean_dec(x_29);
x_47 = l_Lean_mkNatLit(x_46);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_31, 0, x_48);
return x_31;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_49 = lean_ctor_get(x_31, 1);
lean_inc(x_49);
lean_dec(x_31);
x_50 = lean_ctor_get(x_32, 0);
lean_inc(x_50);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 x_51 = x_32;
} else {
 lean_dec_ref(x_32);
 x_51 = lean_box(0);
}
x_52 = lean_nat_shiftl(x_29, x_50);
lean_dec(x_50);
lean_dec(x_29);
x_53 = l_Lean_mkNatLit(x_52);
if (lean_is_scalar(x_51)) {
 x_54 = lean_alloc_ctor(0, 1, 0);
} else {
 x_54 = x_51;
 lean_ctor_set_tag(x_54, 0);
}
lean_ctor_set(x_54, 0, x_53);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_49);
return x_55;
}
}
}
else
{
uint8_t x_56; 
lean_free_object(x_18);
lean_dec(x_29);
x_56 = !lean_is_exclusive(x_31);
if (x_56 == 0)
{
return x_31;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_31, 0);
x_58 = lean_ctor_get(x_31, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_31);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_18, 0);
lean_inc(x_60);
lean_dec(x_18);
x_61 = l_Lean_Expr_appArg_x21(x_1);
x_62 = l_Lean_Meta_getNatValue_x3f(x_61, x_2, x_3, x_4, x_5, x_27);
lean_dec(x_61);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_60);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_65 = x_62;
} else {
 lean_dec_ref(x_62);
 x_65 = lean_box(0);
}
x_66 = lean_box(0);
x_67 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_67, 0, x_66);
if (lean_is_scalar(x_65)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_65;
}
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_64);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_69 = lean_ctor_get(x_62, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_70 = x_62;
} else {
 lean_dec_ref(x_62);
 x_70 = lean_box(0);
}
x_71 = lean_ctor_get(x_63, 0);
lean_inc(x_71);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 x_72 = x_63;
} else {
 lean_dec_ref(x_63);
 x_72 = lean_box(0);
}
x_73 = lean_nat_shiftl(x_60, x_71);
lean_dec(x_71);
lean_dec(x_60);
x_74 = l_Lean_mkNatLit(x_73);
if (lean_is_scalar(x_72)) {
 x_75 = lean_alloc_ctor(0, 1, 0);
} else {
 x_75 = x_72;
 lean_ctor_set_tag(x_75, 0);
}
lean_ctor_set(x_75, 0, x_74);
if (lean_is_scalar(x_70)) {
 x_76 = lean_alloc_ctor(0, 2, 0);
} else {
 x_76 = x_70;
}
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_69);
return x_76;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_60);
x_77 = lean_ctor_get(x_62, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_62, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_79 = x_62;
} else {
 lean_dec_ref(x_62);
 x_79 = lean_box(0);
}
if (lean_is_scalar(x_79)) {
 x_80 = lean_alloc_ctor(1, 2, 0);
} else {
 x_80 = x_79;
}
lean_ctor_set(x_80, 0, x_77);
lean_ctor_set(x_80, 1, x_78);
return x_80;
}
}
}
}
else
{
uint8_t x_81; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_81 = !lean_is_exclusive(x_17);
if (x_81 == 0)
{
return x_17;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_17, 0);
x_83 = lean_ctor_get(x_17, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_17);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceShiftLeft(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Nat_reduceShiftLeft___redArg(x_1, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceShiftLeft___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Nat_reduceShiftLeft___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceShiftLeft___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Nat_reduceShiftLeft(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceShiftLeft_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1322_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_2 = lean_mk_string_unchecked("Nat", 3, 3);
x_3 = lean_mk_string_unchecked("reduceShiftLeft", 15, 15);
lean_inc(x_2);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_mk_string_unchecked("HShiftLeft", 10, 10);
x_6 = lean_mk_string_unchecked("hShiftLeft", 10, 10);
x_7 = l_Lean_Name_mkStr2(x_5, x_6);
x_8 = lean_unsigned_to_nat(6u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_box(3);
x_11 = l_Lean_Name_mkStr1(x_2);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_unsigned_to_nat(7u);
x_15 = lean_mk_empty_array_with_capacity(x_14);
x_16 = lean_array_push(x_15, x_9);
x_17 = lean_array_push(x_16, x_10);
x_18 = lean_array_push(x_17, x_10);
x_19 = lean_array_push(x_18, x_13);
x_20 = lean_array_push(x_19, x_10);
x_21 = lean_array_push(x_20, x_10);
x_22 = lean_array_push(x_21, x_10);
x_23 = lean_alloc_closure((void*)(l_Nat_reduceShiftLeft___boxed), 9, 0);
x_24 = l_Lean_Meta_Simp_registerBuiltinDSimproc(x_4, x_22, x_23, x_1);
return x_24;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceShiftLeft_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1324_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Nat", 3, 3);
x_3 = lean_mk_string_unchecked("reduceShiftLeft", 15, 15);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Nat_reduceShiftLeft___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceShiftLeft_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1326_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Nat", 3, 3);
x_3 = lean_mk_string_unchecked("reduceShiftLeft", 15, 15);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Nat_reduceShiftLeft___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceShiftRight___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_mk_string_unchecked("HShiftRight", 11, 11);
x_8 = lean_mk_string_unchecked("hShiftRight", 11, 11);
x_9 = l_Lean_Name_mkStr2(x_7, x_8);
x_10 = lean_unsigned_to_nat(6u);
x_11 = l_Lean_Expr_isAppOfArity(x_1, x_9, x_10);
lean_dec(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_6);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = l_Lean_Expr_appFn_x21(x_1);
x_16 = l_Lean_Expr_appArg_x21(x_15);
lean_dec(x_15);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_17 = l_Lean_Meta_getNatValue_x3f(x_16, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_17, 0);
lean_dec(x_20);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_17, 0, x_22);
return x_17;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_dec(x_17);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_23);
return x_26;
}
}
else
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_17, 1);
lean_inc(x_27);
lean_dec(x_17);
x_28 = !lean_is_exclusive(x_18);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_18, 0);
x_30 = l_Lean_Expr_appArg_x21(x_1);
x_31 = l_Lean_Meta_getNatValue_x3f(x_30, x_2, x_3, x_4, x_5, x_27);
lean_dec(x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
lean_dec(x_29);
x_33 = !lean_is_exclusive(x_31);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_31, 0);
lean_dec(x_34);
x_35 = lean_box(0);
lean_ctor_set_tag(x_18, 2);
lean_ctor_set(x_18, 0, x_35);
lean_ctor_set(x_31, 0, x_18);
return x_31;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_31, 1);
lean_inc(x_36);
lean_dec(x_31);
x_37 = lean_box(0);
lean_ctor_set_tag(x_18, 2);
lean_ctor_set(x_18, 0, x_37);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_18);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
else
{
uint8_t x_39; 
lean_free_object(x_18);
x_39 = !lean_is_exclusive(x_31);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_31, 0);
lean_dec(x_40);
x_41 = !lean_is_exclusive(x_32);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_32, 0);
x_43 = lean_nat_shiftr(x_29, x_42);
lean_dec(x_42);
lean_dec(x_29);
x_44 = l_Lean_mkNatLit(x_43);
lean_ctor_set_tag(x_32, 0);
lean_ctor_set(x_32, 0, x_44);
return x_31;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_32, 0);
lean_inc(x_45);
lean_dec(x_32);
x_46 = lean_nat_shiftr(x_29, x_45);
lean_dec(x_45);
lean_dec(x_29);
x_47 = l_Lean_mkNatLit(x_46);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_31, 0, x_48);
return x_31;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_49 = lean_ctor_get(x_31, 1);
lean_inc(x_49);
lean_dec(x_31);
x_50 = lean_ctor_get(x_32, 0);
lean_inc(x_50);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 x_51 = x_32;
} else {
 lean_dec_ref(x_32);
 x_51 = lean_box(0);
}
x_52 = lean_nat_shiftr(x_29, x_50);
lean_dec(x_50);
lean_dec(x_29);
x_53 = l_Lean_mkNatLit(x_52);
if (lean_is_scalar(x_51)) {
 x_54 = lean_alloc_ctor(0, 1, 0);
} else {
 x_54 = x_51;
 lean_ctor_set_tag(x_54, 0);
}
lean_ctor_set(x_54, 0, x_53);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_49);
return x_55;
}
}
}
else
{
uint8_t x_56; 
lean_free_object(x_18);
lean_dec(x_29);
x_56 = !lean_is_exclusive(x_31);
if (x_56 == 0)
{
return x_31;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_31, 0);
x_58 = lean_ctor_get(x_31, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_31);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_18, 0);
lean_inc(x_60);
lean_dec(x_18);
x_61 = l_Lean_Expr_appArg_x21(x_1);
x_62 = l_Lean_Meta_getNatValue_x3f(x_61, x_2, x_3, x_4, x_5, x_27);
lean_dec(x_61);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_60);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_65 = x_62;
} else {
 lean_dec_ref(x_62);
 x_65 = lean_box(0);
}
x_66 = lean_box(0);
x_67 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_67, 0, x_66);
if (lean_is_scalar(x_65)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_65;
}
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_64);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_69 = lean_ctor_get(x_62, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_70 = x_62;
} else {
 lean_dec_ref(x_62);
 x_70 = lean_box(0);
}
x_71 = lean_ctor_get(x_63, 0);
lean_inc(x_71);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 x_72 = x_63;
} else {
 lean_dec_ref(x_63);
 x_72 = lean_box(0);
}
x_73 = lean_nat_shiftr(x_60, x_71);
lean_dec(x_71);
lean_dec(x_60);
x_74 = l_Lean_mkNatLit(x_73);
if (lean_is_scalar(x_72)) {
 x_75 = lean_alloc_ctor(0, 1, 0);
} else {
 x_75 = x_72;
 lean_ctor_set_tag(x_75, 0);
}
lean_ctor_set(x_75, 0, x_74);
if (lean_is_scalar(x_70)) {
 x_76 = lean_alloc_ctor(0, 2, 0);
} else {
 x_76 = x_70;
}
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_69);
return x_76;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_60);
x_77 = lean_ctor_get(x_62, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_62, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_79 = x_62;
} else {
 lean_dec_ref(x_62);
 x_79 = lean_box(0);
}
if (lean_is_scalar(x_79)) {
 x_80 = lean_alloc_ctor(1, 2, 0);
} else {
 x_80 = x_79;
}
lean_ctor_set(x_80, 0, x_77);
lean_ctor_set(x_80, 1, x_78);
return x_80;
}
}
}
}
else
{
uint8_t x_81; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_81 = !lean_is_exclusive(x_17);
if (x_81 == 0)
{
return x_17;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_17, 0);
x_83 = lean_ctor_get(x_17, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_17);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceShiftRight(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Nat_reduceShiftRight___redArg(x_1, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceShiftRight___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Nat_reduceShiftRight___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceShiftRight___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Nat_reduceShiftRight(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceShiftRight_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1360_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_2 = lean_mk_string_unchecked("Nat", 3, 3);
x_3 = lean_mk_string_unchecked("reduceShiftRight", 16, 16);
lean_inc(x_2);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_mk_string_unchecked("HShiftRight", 11, 11);
x_6 = lean_mk_string_unchecked("hShiftRight", 11, 11);
x_7 = l_Lean_Name_mkStr2(x_5, x_6);
x_8 = lean_unsigned_to_nat(6u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_box(3);
x_11 = l_Lean_Name_mkStr1(x_2);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_unsigned_to_nat(7u);
x_15 = lean_mk_empty_array_with_capacity(x_14);
x_16 = lean_array_push(x_15, x_9);
x_17 = lean_array_push(x_16, x_10);
x_18 = lean_array_push(x_17, x_10);
x_19 = lean_array_push(x_18, x_13);
x_20 = lean_array_push(x_19, x_10);
x_21 = lean_array_push(x_20, x_10);
x_22 = lean_array_push(x_21, x_10);
x_23 = lean_alloc_closure((void*)(l_Nat_reduceShiftRight___boxed), 9, 0);
x_24 = l_Lean_Meta_Simp_registerBuiltinDSimproc(x_4, x_22, x_23, x_1);
return x_24;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceShiftRight_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1362_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Nat", 3, 3);
x_3 = lean_mk_string_unchecked("reduceShiftRight", 16, 16);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Nat_reduceShiftRight___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceShiftRight_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1364_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Nat", 3, 3);
x_3 = lean_mk_string_unchecked("reduceShiftRight", 16, 16);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Nat_reduceShiftRight___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceGcd___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_mk_string_unchecked("Nat", 3, 3);
x_8 = lean_mk_string_unchecked("gcd", 3, 3);
x_9 = l_Lean_Name_mkStr2(x_7, x_8);
x_10 = lean_unsigned_to_nat(2u);
x_11 = l_Lean_Expr_isAppOfArity(x_1, x_9, x_10);
lean_dec(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_6);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = l_Lean_Expr_appFn_x21(x_1);
x_16 = l_Lean_Expr_appArg_x21(x_15);
lean_dec(x_15);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_17 = l_Lean_Meta_getNatValue_x3f(x_16, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_17, 0);
lean_dec(x_20);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_17, 0, x_22);
return x_17;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_dec(x_17);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_23);
return x_26;
}
}
else
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_17, 1);
lean_inc(x_27);
lean_dec(x_17);
x_28 = !lean_is_exclusive(x_18);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_18, 0);
x_30 = l_Lean_Expr_appArg_x21(x_1);
x_31 = l_Lean_Meta_getNatValue_x3f(x_30, x_2, x_3, x_4, x_5, x_27);
lean_dec(x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
lean_dec(x_29);
x_33 = !lean_is_exclusive(x_31);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_31, 0);
lean_dec(x_34);
x_35 = lean_box(0);
lean_ctor_set_tag(x_18, 2);
lean_ctor_set(x_18, 0, x_35);
lean_ctor_set(x_31, 0, x_18);
return x_31;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_31, 1);
lean_inc(x_36);
lean_dec(x_31);
x_37 = lean_box(0);
lean_ctor_set_tag(x_18, 2);
lean_ctor_set(x_18, 0, x_37);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_18);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
else
{
uint8_t x_39; 
lean_free_object(x_18);
x_39 = !lean_is_exclusive(x_31);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_31, 0);
lean_dec(x_40);
x_41 = !lean_is_exclusive(x_32);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_32, 0);
x_43 = lean_nat_gcd(x_29, x_42);
lean_dec(x_42);
lean_dec(x_29);
x_44 = l_Lean_mkNatLit(x_43);
lean_ctor_set_tag(x_32, 0);
lean_ctor_set(x_32, 0, x_44);
return x_31;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_32, 0);
lean_inc(x_45);
lean_dec(x_32);
x_46 = lean_nat_gcd(x_29, x_45);
lean_dec(x_45);
lean_dec(x_29);
x_47 = l_Lean_mkNatLit(x_46);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_31, 0, x_48);
return x_31;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_49 = lean_ctor_get(x_31, 1);
lean_inc(x_49);
lean_dec(x_31);
x_50 = lean_ctor_get(x_32, 0);
lean_inc(x_50);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 x_51 = x_32;
} else {
 lean_dec_ref(x_32);
 x_51 = lean_box(0);
}
x_52 = lean_nat_gcd(x_29, x_50);
lean_dec(x_50);
lean_dec(x_29);
x_53 = l_Lean_mkNatLit(x_52);
if (lean_is_scalar(x_51)) {
 x_54 = lean_alloc_ctor(0, 1, 0);
} else {
 x_54 = x_51;
 lean_ctor_set_tag(x_54, 0);
}
lean_ctor_set(x_54, 0, x_53);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_49);
return x_55;
}
}
}
else
{
uint8_t x_56; 
lean_free_object(x_18);
lean_dec(x_29);
x_56 = !lean_is_exclusive(x_31);
if (x_56 == 0)
{
return x_31;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_31, 0);
x_58 = lean_ctor_get(x_31, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_31);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_18, 0);
lean_inc(x_60);
lean_dec(x_18);
x_61 = l_Lean_Expr_appArg_x21(x_1);
x_62 = l_Lean_Meta_getNatValue_x3f(x_61, x_2, x_3, x_4, x_5, x_27);
lean_dec(x_61);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_60);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_65 = x_62;
} else {
 lean_dec_ref(x_62);
 x_65 = lean_box(0);
}
x_66 = lean_box(0);
x_67 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_67, 0, x_66);
if (lean_is_scalar(x_65)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_65;
}
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_64);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_69 = lean_ctor_get(x_62, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_70 = x_62;
} else {
 lean_dec_ref(x_62);
 x_70 = lean_box(0);
}
x_71 = lean_ctor_get(x_63, 0);
lean_inc(x_71);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 x_72 = x_63;
} else {
 lean_dec_ref(x_63);
 x_72 = lean_box(0);
}
x_73 = lean_nat_gcd(x_60, x_71);
lean_dec(x_71);
lean_dec(x_60);
x_74 = l_Lean_mkNatLit(x_73);
if (lean_is_scalar(x_72)) {
 x_75 = lean_alloc_ctor(0, 1, 0);
} else {
 x_75 = x_72;
 lean_ctor_set_tag(x_75, 0);
}
lean_ctor_set(x_75, 0, x_74);
if (lean_is_scalar(x_70)) {
 x_76 = lean_alloc_ctor(0, 2, 0);
} else {
 x_76 = x_70;
}
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_69);
return x_76;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_60);
x_77 = lean_ctor_get(x_62, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_62, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_79 = x_62;
} else {
 lean_dec_ref(x_62);
 x_79 = lean_box(0);
}
if (lean_is_scalar(x_79)) {
 x_80 = lean_alloc_ctor(1, 2, 0);
} else {
 x_80 = x_79;
}
lean_ctor_set(x_80, 0, x_77);
lean_ctor_set(x_80, 1, x_78);
return x_80;
}
}
}
}
else
{
uint8_t x_81; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_81 = !lean_is_exclusive(x_17);
if (x_81 == 0)
{
return x_17;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_17, 0);
x_83 = lean_ctor_get(x_17, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_17);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceGcd(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Nat_reduceGcd___redArg(x_1, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceGcd___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Nat_reduceGcd___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceGcd___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Nat_reduceGcd(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceGcd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1382_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_2 = lean_mk_string_unchecked("Nat", 3, 3);
x_3 = lean_mk_string_unchecked("reduceGcd", 9, 9);
lean_inc(x_2);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_mk_string_unchecked("gcd", 3, 3);
x_6 = l_Lean_Name_mkStr2(x_2, x_5);
x_7 = lean_unsigned_to_nat(2u);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_box(3);
x_10 = lean_unsigned_to_nat(3u);
x_11 = lean_mk_empty_array_with_capacity(x_10);
x_12 = lean_array_push(x_11, x_8);
x_13 = lean_array_push(x_12, x_9);
x_14 = lean_array_push(x_13, x_9);
x_15 = lean_alloc_closure((void*)(l_Nat_reduceGcd___boxed), 9, 0);
x_16 = l_Lean_Meta_Simp_registerBuiltinDSimproc(x_4, x_14, x_15, x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceGcd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1384_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Nat", 3, 3);
x_3 = lean_mk_string_unchecked("reduceGcd", 9, 9);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Nat_reduceGcd___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceGcd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1386_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Nat", 3, 3);
x_3 = lean_mk_string_unchecked("reduceGcd", 9, 9);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Nat_reduceGcd___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceLT___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_mk_string_unchecked("LT", 2, 2);
x_8 = lean_mk_string_unchecked("lt", 2, 2);
x_9 = l_Lean_Name_mkStr2(x_7, x_8);
x_10 = lean_unsigned_to_nat(4u);
x_11 = l_Lean_Expr_isAppOfArity(x_1, x_9, x_10);
lean_dec(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_6);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = l_Lean_Expr_appFn_x21(x_1);
x_16 = l_Lean_Expr_appArg_x21(x_15);
lean_dec(x_15);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_17 = l_Lean_Meta_getNatValue_x3f(x_16, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_17, 0);
lean_dec(x_20);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_17, 0, x_22);
return x_17;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_dec(x_17);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_23);
return x_26;
}
}
else
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_17, 1);
lean_inc(x_27);
lean_dec(x_17);
x_28 = !lean_is_exclusive(x_18);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_18, 0);
x_30 = l_Lean_Expr_appArg_x21(x_1);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_31 = l_Lean_Meta_getNatValue_x3f(x_30, x_2, x_3, x_4, x_5, x_27);
lean_dec(x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
lean_dec(x_29);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_31);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_31, 0);
lean_dec(x_34);
x_35 = lean_box(0);
lean_ctor_set_tag(x_18, 2);
lean_ctor_set(x_18, 0, x_35);
lean_ctor_set(x_31, 0, x_18);
return x_31;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_31, 1);
lean_inc(x_36);
lean_dec(x_31);
x_37 = lean_box(0);
lean_ctor_set_tag(x_18, 2);
lean_ctor_set(x_18, 0, x_37);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_18);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; 
lean_free_object(x_18);
x_39 = lean_ctor_get(x_31, 1);
lean_inc(x_39);
lean_dec(x_31);
x_40 = lean_ctor_get(x_32, 0);
lean_inc(x_40);
lean_dec(x_32);
x_41 = lean_nat_dec_lt(x_29, x_40);
lean_dec(x_40);
lean_dec(x_29);
x_42 = l_Lean_Meta_Simp_evalPropStep___redArg(x_1, x_41, x_2, x_3, x_4, x_5, x_39);
return x_42;
}
}
else
{
uint8_t x_43; 
lean_free_object(x_18);
lean_dec(x_29);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_31);
if (x_43 == 0)
{
return x_31;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_31, 0);
x_45 = lean_ctor_get(x_31, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_31);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_18, 0);
lean_inc(x_47);
lean_dec(x_18);
x_48 = l_Lean_Expr_appArg_x21(x_1);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_49 = l_Lean_Meta_getNatValue_x3f(x_48, x_2, x_3, x_4, x_5, x_27);
lean_dec(x_48);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_47);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
x_53 = lean_box(0);
x_54 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_54, 0, x_53);
if (lean_is_scalar(x_52)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_52;
}
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_51);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; 
x_56 = lean_ctor_get(x_49, 1);
lean_inc(x_56);
lean_dec(x_49);
x_57 = lean_ctor_get(x_50, 0);
lean_inc(x_57);
lean_dec(x_50);
x_58 = lean_nat_dec_lt(x_47, x_57);
lean_dec(x_57);
lean_dec(x_47);
x_59 = l_Lean_Meta_Simp_evalPropStep___redArg(x_1, x_58, x_2, x_3, x_4, x_5, x_56);
return x_59;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_47);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_60 = lean_ctor_get(x_49, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_49, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_62 = x_49;
} else {
 lean_dec_ref(x_49);
 x_62 = lean_box(0);
}
if (lean_is_scalar(x_62)) {
 x_63 = lean_alloc_ctor(1, 2, 0);
} else {
 x_63 = x_62;
}
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_61);
return x_63;
}
}
}
}
else
{
uint8_t x_64; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_64 = !lean_is_exclusive(x_17);
if (x_64 == 0)
{
return x_17;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_17, 0);
x_66 = lean_ctor_get(x_17, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_17);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceLT(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Nat_reduceLT___redArg(x_1, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceLT___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Nat_reduceLT(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceLT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1421_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_2 = lean_mk_string_unchecked("Nat", 3, 3);
x_3 = lean_mk_string_unchecked("reduceLT", 8, 8);
lean_inc(x_2);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_mk_string_unchecked("LT", 2, 2);
x_6 = lean_mk_string_unchecked("lt", 2, 2);
x_7 = l_Lean_Name_mkStr2(x_5, x_6);
x_8 = lean_unsigned_to_nat(4u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Lean_Name_mkStr1(x_2);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_box(3);
x_14 = lean_unsigned_to_nat(5u);
x_15 = lean_mk_empty_array_with_capacity(x_14);
x_16 = lean_array_push(x_15, x_9);
x_17 = lean_array_push(x_16, x_12);
x_18 = lean_array_push(x_17, x_13);
x_19 = lean_array_push(x_18, x_13);
x_20 = lean_array_push(x_19, x_13);
x_21 = lean_alloc_closure((void*)(l_Nat_reduceLT___boxed), 9, 0);
x_22 = l_Lean_Meta_Simp_registerBuiltinSimproc(x_4, x_20, x_21, x_1);
return x_22;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceLT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1423_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Nat", 3, 3);
x_3 = lean_mk_string_unchecked("reduceLT", 8, 8);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Nat_reduceLT___boxed), 9, 0);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceLT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1425_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Nat", 3, 3);
x_3 = lean_mk_string_unchecked("reduceLT", 8, 8);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Nat_reduceLT___boxed), 9, 0);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceGT___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_mk_string_unchecked("GT", 2, 2);
x_8 = lean_mk_string_unchecked("gt", 2, 2);
x_9 = l_Lean_Name_mkStr2(x_7, x_8);
x_10 = lean_unsigned_to_nat(4u);
x_11 = l_Lean_Expr_isAppOfArity(x_1, x_9, x_10);
lean_dec(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_6);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = l_Lean_Expr_appFn_x21(x_1);
x_16 = l_Lean_Expr_appArg_x21(x_15);
lean_dec(x_15);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_17 = l_Lean_Meta_getNatValue_x3f(x_16, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_17, 0);
lean_dec(x_20);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_17, 0, x_22);
return x_17;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_dec(x_17);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_23);
return x_26;
}
}
else
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_17, 1);
lean_inc(x_27);
lean_dec(x_17);
x_28 = !lean_is_exclusive(x_18);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_18, 0);
x_30 = l_Lean_Expr_appArg_x21(x_1);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_31 = l_Lean_Meta_getNatValue_x3f(x_30, x_2, x_3, x_4, x_5, x_27);
lean_dec(x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
lean_dec(x_29);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_31);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_31, 0);
lean_dec(x_34);
x_35 = lean_box(0);
lean_ctor_set_tag(x_18, 2);
lean_ctor_set(x_18, 0, x_35);
lean_ctor_set(x_31, 0, x_18);
return x_31;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_31, 1);
lean_inc(x_36);
lean_dec(x_31);
x_37 = lean_box(0);
lean_ctor_set_tag(x_18, 2);
lean_ctor_set(x_18, 0, x_37);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_18);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; 
lean_free_object(x_18);
x_39 = lean_ctor_get(x_31, 1);
lean_inc(x_39);
lean_dec(x_31);
x_40 = lean_ctor_get(x_32, 0);
lean_inc(x_40);
lean_dec(x_32);
x_41 = lean_nat_dec_lt(x_40, x_29);
lean_dec(x_29);
lean_dec(x_40);
x_42 = l_Lean_Meta_Simp_evalPropStep___redArg(x_1, x_41, x_2, x_3, x_4, x_5, x_39);
return x_42;
}
}
else
{
uint8_t x_43; 
lean_free_object(x_18);
lean_dec(x_29);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_31);
if (x_43 == 0)
{
return x_31;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_31, 0);
x_45 = lean_ctor_get(x_31, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_31);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_18, 0);
lean_inc(x_47);
lean_dec(x_18);
x_48 = l_Lean_Expr_appArg_x21(x_1);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_49 = l_Lean_Meta_getNatValue_x3f(x_48, x_2, x_3, x_4, x_5, x_27);
lean_dec(x_48);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_47);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
x_53 = lean_box(0);
x_54 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_54, 0, x_53);
if (lean_is_scalar(x_52)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_52;
}
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_51);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; 
x_56 = lean_ctor_get(x_49, 1);
lean_inc(x_56);
lean_dec(x_49);
x_57 = lean_ctor_get(x_50, 0);
lean_inc(x_57);
lean_dec(x_50);
x_58 = lean_nat_dec_lt(x_57, x_47);
lean_dec(x_47);
lean_dec(x_57);
x_59 = l_Lean_Meta_Simp_evalPropStep___redArg(x_1, x_58, x_2, x_3, x_4, x_5, x_56);
return x_59;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_47);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_60 = lean_ctor_get(x_49, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_49, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_62 = x_49;
} else {
 lean_dec_ref(x_49);
 x_62 = lean_box(0);
}
if (lean_is_scalar(x_62)) {
 x_63 = lean_alloc_ctor(1, 2, 0);
} else {
 x_63 = x_62;
}
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_61);
return x_63;
}
}
}
}
else
{
uint8_t x_64; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_64 = !lean_is_exclusive(x_17);
if (x_64 == 0)
{
return x_17;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_17, 0);
x_66 = lean_ctor_get(x_17, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_17);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceGT(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Nat_reduceGT___redArg(x_1, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceGT___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Nat_reduceGT(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceGT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1460_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_2 = lean_mk_string_unchecked("Nat", 3, 3);
x_3 = lean_mk_string_unchecked("reduceGT", 8, 8);
lean_inc(x_2);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_mk_string_unchecked("LT", 2, 2);
x_6 = lean_mk_string_unchecked("lt", 2, 2);
x_7 = l_Lean_Name_mkStr2(x_5, x_6);
x_8 = lean_unsigned_to_nat(4u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Lean_Name_mkStr1(x_2);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_box(3);
x_14 = lean_unsigned_to_nat(5u);
x_15 = lean_mk_empty_array_with_capacity(x_14);
x_16 = lean_array_push(x_15, x_9);
x_17 = lean_array_push(x_16, x_12);
x_18 = lean_array_push(x_17, x_13);
x_19 = lean_array_push(x_18, x_13);
x_20 = lean_array_push(x_19, x_13);
x_21 = lean_alloc_closure((void*)(l_Nat_reduceGT___boxed), 9, 0);
x_22 = l_Lean_Meta_Simp_registerBuiltinSimproc(x_4, x_20, x_21, x_1);
return x_22;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceGT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1462_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Nat", 3, 3);
x_3 = lean_mk_string_unchecked("reduceGT", 8, 8);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Nat_reduceGT___boxed), 9, 0);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceGT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1464_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Nat", 3, 3);
x_3 = lean_mk_string_unchecked("reduceGT", 8, 8);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Nat_reduceGT___boxed), 9, 0);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBEq___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_mk_string_unchecked("BEq", 3, 3);
x_8 = lean_mk_string_unchecked("beq", 3, 3);
x_9 = l_Lean_Name_mkStr2(x_7, x_8);
x_10 = lean_unsigned_to_nat(4u);
x_11 = l_Lean_Expr_isAppOfArity(x_1, x_9, x_10);
lean_dec(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_6);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = l_Lean_Expr_appFn_x21(x_1);
x_16 = l_Lean_Expr_appArg_x21(x_15);
lean_dec(x_15);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_17 = l_Lean_Meta_getNatValue_x3f(x_16, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_17, 0);
lean_dec(x_20);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_17, 0, x_22);
return x_17;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_dec(x_17);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_23);
return x_26;
}
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_17);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_28 = lean_ctor_get(x_17, 1);
x_29 = lean_ctor_get(x_17, 0);
lean_dec(x_29);
x_30 = lean_ctor_get(x_18, 0);
lean_inc(x_30);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 x_31 = x_18;
} else {
 lean_dec_ref(x_18);
 x_31 = lean_box(0);
}
x_32 = l_Lean_Expr_appArg_x21(x_1);
x_33 = l_Lean_Meta_getNatValue_x3f(x_32, x_2, x_3, x_4, x_5, x_28);
lean_dec(x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_36 = x_33;
} else {
 lean_dec_ref(x_33);
 x_36 = lean_box(0);
}
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_36);
lean_dec(x_31);
lean_dec(x_30);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_17, 1, x_35);
lean_ctor_set(x_17, 0, x_42);
return x_17;
}
else
{
lean_object* x_43; uint8_t x_44; 
lean_free_object(x_17);
x_43 = lean_ctor_get(x_34, 0);
lean_inc(x_43);
lean_dec(x_34);
x_44 = lean_nat_dec_eq(x_30, x_43);
lean_dec(x_43);
lean_dec(x_30);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_45 = lean_mk_string_unchecked("Bool", 4, 4);
x_46 = lean_mk_string_unchecked("false", 5, 5);
x_47 = l_Lean_Name_mkStr2(x_45, x_46);
x_48 = lean_box(0);
x_49 = l_Lean_Expr_const___override(x_47, x_48);
x_37 = x_49;
goto block_40;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_50 = lean_mk_string_unchecked("Bool", 4, 4);
x_51 = lean_mk_string_unchecked("true", 4, 4);
x_52 = l_Lean_Name_mkStr2(x_50, x_51);
x_53 = lean_box(0);
x_54 = l_Lean_Expr_const___override(x_52, x_53);
x_37 = x_54;
goto block_40;
}
}
block_40:
{
lean_object* x_38; lean_object* x_39; 
if (lean_is_scalar(x_31)) {
 x_38 = lean_alloc_ctor(0, 1, 0);
} else {
 x_38 = x_31;
 lean_ctor_set_tag(x_38, 0);
}
lean_ctor_set(x_38, 0, x_37);
if (lean_is_scalar(x_36)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_36;
}
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_35);
return x_39;
}
}
else
{
uint8_t x_55; 
lean_dec(x_31);
lean_dec(x_30);
lean_free_object(x_17);
x_55 = !lean_is_exclusive(x_33);
if (x_55 == 0)
{
return x_33;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_33, 0);
x_57 = lean_ctor_get(x_33, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_33);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_59 = lean_ctor_get(x_17, 1);
lean_inc(x_59);
lean_dec(x_17);
x_60 = lean_ctor_get(x_18, 0);
lean_inc(x_60);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 x_61 = x_18;
} else {
 lean_dec_ref(x_18);
 x_61 = lean_box(0);
}
x_62 = l_Lean_Expr_appArg_x21(x_1);
x_63 = l_Lean_Meta_getNatValue_x3f(x_62, x_2, x_3, x_4, x_5, x_59);
lean_dec(x_62);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
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
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_66);
lean_dec(x_61);
lean_dec(x_60);
x_71 = lean_box(0);
x_72 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_72, 0, x_71);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_65);
return x_73;
}
else
{
lean_object* x_74; uint8_t x_75; 
x_74 = lean_ctor_get(x_64, 0);
lean_inc(x_74);
lean_dec(x_64);
x_75 = lean_nat_dec_eq(x_60, x_74);
lean_dec(x_74);
lean_dec(x_60);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_76 = lean_mk_string_unchecked("Bool", 4, 4);
x_77 = lean_mk_string_unchecked("false", 5, 5);
x_78 = l_Lean_Name_mkStr2(x_76, x_77);
x_79 = lean_box(0);
x_80 = l_Lean_Expr_const___override(x_78, x_79);
x_67 = x_80;
goto block_70;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_81 = lean_mk_string_unchecked("Bool", 4, 4);
x_82 = lean_mk_string_unchecked("true", 4, 4);
x_83 = l_Lean_Name_mkStr2(x_81, x_82);
x_84 = lean_box(0);
x_85 = l_Lean_Expr_const___override(x_83, x_84);
x_67 = x_85;
goto block_70;
}
}
block_70:
{
lean_object* x_68; lean_object* x_69; 
if (lean_is_scalar(x_61)) {
 x_68 = lean_alloc_ctor(0, 1, 0);
} else {
 x_68 = x_61;
 lean_ctor_set_tag(x_68, 0);
}
lean_ctor_set(x_68, 0, x_67);
if (lean_is_scalar(x_66)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_66;
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_65);
return x_69;
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_61);
lean_dec(x_60);
x_86 = lean_ctor_get(x_63, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_63, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_88 = x_63;
} else {
 lean_dec_ref(x_63);
 x_88 = lean_box(0);
}
if (lean_is_scalar(x_88)) {
 x_89 = lean_alloc_ctor(1, 2, 0);
} else {
 x_89 = x_88;
}
lean_ctor_set(x_89, 0, x_86);
lean_ctor_set(x_89, 1, x_87);
return x_89;
}
}
}
}
else
{
uint8_t x_90; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_90 = !lean_is_exclusive(x_17);
if (x_90 == 0)
{
return x_17;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_17, 0);
x_92 = lean_ctor_get(x_17, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_17);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Nat_reduceBEq___redArg(x_1, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBEq___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Nat_reduceBEq___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBEq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Nat_reduceBEq(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceBEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1499_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_2 = lean_mk_string_unchecked("Nat", 3, 3);
x_3 = lean_mk_string_unchecked("reduceBEq", 9, 9);
lean_inc(x_2);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_mk_string_unchecked("BEq", 3, 3);
x_6 = lean_mk_string_unchecked("beq", 3, 3);
x_7 = l_Lean_Name_mkStr2(x_5, x_6);
x_8 = lean_unsigned_to_nat(4u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Lean_Name_mkStr1(x_2);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_box(3);
x_14 = lean_unsigned_to_nat(5u);
x_15 = lean_mk_empty_array_with_capacity(x_14);
x_16 = lean_array_push(x_15, x_9);
x_17 = lean_array_push(x_16, x_12);
x_18 = lean_array_push(x_17, x_13);
x_19 = lean_array_push(x_18, x_13);
x_20 = lean_array_push(x_19, x_13);
x_21 = lean_alloc_closure((void*)(l_Nat_reduceBEq___boxed), 9, 0);
x_22 = l_Lean_Meta_Simp_registerBuiltinDSimproc(x_4, x_20, x_21, x_1);
return x_22;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceBEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1501_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Nat", 3, 3);
x_3 = lean_mk_string_unchecked("reduceBEq", 9, 9);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Nat_reduceBEq___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceBEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1503_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Nat", 3, 3);
x_3 = lean_mk_string_unchecked("reduceBEq", 9, 9);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Nat_reduceBEq___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBNe___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_mk_string_unchecked("bne", 3, 3);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_unsigned_to_nat(4u);
x_10 = l_Lean_Expr_isAppOfArity(x_1, x_8, x_9);
lean_dec(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_6);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = l_Lean_Expr_appFn_x21(x_1);
x_15 = l_Lean_Expr_appArg_x21(x_14);
lean_dec(x_14);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_16 = l_Lean_Meta_getNatValue_x3f(x_15, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_16, 0);
lean_dec(x_19);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_16, 0, x_21);
return x_16;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_16, 1);
lean_inc(x_22);
lean_dec(x_16);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_22);
return x_25;
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_16);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_27 = lean_ctor_get(x_16, 1);
x_28 = lean_ctor_get(x_16, 0);
lean_dec(x_28);
x_29 = lean_ctor_get(x_17, 0);
lean_inc(x_29);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 x_30 = x_17;
} else {
 lean_dec_ref(x_17);
 x_30 = lean_box(0);
}
x_31 = l_Lean_Expr_appArg_x21(x_1);
x_32 = l_Lean_Meta_getNatValue_x3f(x_31, x_2, x_3, x_4, x_5, x_27);
lean_dec(x_31);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_35 = x_32;
} else {
 lean_dec_ref(x_32);
 x_35 = lean_box(0);
}
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_35);
lean_dec(x_30);
lean_dec(x_29);
x_46 = lean_box(0);
x_47 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_16, 1, x_34);
lean_ctor_set(x_16, 0, x_47);
return x_16;
}
else
{
lean_object* x_48; uint8_t x_49; 
lean_free_object(x_16);
x_48 = lean_ctor_get(x_33, 0);
lean_inc(x_48);
lean_dec(x_33);
x_49 = lean_nat_dec_eq(x_29, x_48);
lean_dec(x_48);
lean_dec(x_29);
if (x_49 == 0)
{
if (x_10 == 0)
{
goto block_45;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_50 = lean_mk_string_unchecked("Bool", 4, 4);
x_51 = lean_mk_string_unchecked("true", 4, 4);
x_52 = l_Lean_Name_mkStr2(x_50, x_51);
x_53 = lean_box(0);
x_54 = l_Lean_Expr_const___override(x_52, x_53);
x_36 = x_54;
goto block_39;
}
}
else
{
goto block_45;
}
}
block_39:
{
lean_object* x_37; lean_object* x_38; 
if (lean_is_scalar(x_30)) {
 x_37 = lean_alloc_ctor(0, 1, 0);
} else {
 x_37 = x_30;
 lean_ctor_set_tag(x_37, 0);
}
lean_ctor_set(x_37, 0, x_36);
if (lean_is_scalar(x_35)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_35;
}
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_34);
return x_38;
}
block_45:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_40 = lean_mk_string_unchecked("Bool", 4, 4);
x_41 = lean_mk_string_unchecked("false", 5, 5);
x_42 = l_Lean_Name_mkStr2(x_40, x_41);
x_43 = lean_box(0);
x_44 = l_Lean_Expr_const___override(x_42, x_43);
x_36 = x_44;
goto block_39;
}
}
else
{
uint8_t x_55; 
lean_dec(x_30);
lean_dec(x_29);
lean_free_object(x_16);
x_55 = !lean_is_exclusive(x_32);
if (x_55 == 0)
{
return x_32;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_32, 0);
x_57 = lean_ctor_get(x_32, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_32);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_59 = lean_ctor_get(x_16, 1);
lean_inc(x_59);
lean_dec(x_16);
x_60 = lean_ctor_get(x_17, 0);
lean_inc(x_60);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 x_61 = x_17;
} else {
 lean_dec_ref(x_17);
 x_61 = lean_box(0);
}
x_62 = l_Lean_Expr_appArg_x21(x_1);
x_63 = l_Lean_Meta_getNatValue_x3f(x_62, x_2, x_3, x_4, x_5, x_59);
lean_dec(x_62);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
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
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_66);
lean_dec(x_61);
lean_dec(x_60);
x_77 = lean_box(0);
x_78 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_78, 0, x_77);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_65);
return x_79;
}
else
{
lean_object* x_80; uint8_t x_81; 
x_80 = lean_ctor_get(x_64, 0);
lean_inc(x_80);
lean_dec(x_64);
x_81 = lean_nat_dec_eq(x_60, x_80);
lean_dec(x_80);
lean_dec(x_60);
if (x_81 == 0)
{
if (x_10 == 0)
{
goto block_76;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_82 = lean_mk_string_unchecked("Bool", 4, 4);
x_83 = lean_mk_string_unchecked("true", 4, 4);
x_84 = l_Lean_Name_mkStr2(x_82, x_83);
x_85 = lean_box(0);
x_86 = l_Lean_Expr_const___override(x_84, x_85);
x_67 = x_86;
goto block_70;
}
}
else
{
goto block_76;
}
}
block_70:
{
lean_object* x_68; lean_object* x_69; 
if (lean_is_scalar(x_61)) {
 x_68 = lean_alloc_ctor(0, 1, 0);
} else {
 x_68 = x_61;
 lean_ctor_set_tag(x_68, 0);
}
lean_ctor_set(x_68, 0, x_67);
if (lean_is_scalar(x_66)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_66;
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_65);
return x_69;
}
block_76:
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_71 = lean_mk_string_unchecked("Bool", 4, 4);
x_72 = lean_mk_string_unchecked("false", 5, 5);
x_73 = l_Lean_Name_mkStr2(x_71, x_72);
x_74 = lean_box(0);
x_75 = l_Lean_Expr_const___override(x_73, x_74);
x_67 = x_75;
goto block_70;
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_61);
lean_dec(x_60);
x_87 = lean_ctor_get(x_63, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_63, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_89 = x_63;
} else {
 lean_dec_ref(x_63);
 x_89 = lean_box(0);
}
if (lean_is_scalar(x_89)) {
 x_90 = lean_alloc_ctor(1, 2, 0);
} else {
 x_90 = x_89;
}
lean_ctor_set(x_90, 0, x_87);
lean_ctor_set(x_90, 1, x_88);
return x_90;
}
}
}
}
else
{
uint8_t x_91; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_91 = !lean_is_exclusive(x_16);
if (x_91 == 0)
{
return x_16;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_16, 0);
x_93 = lean_ctor_get(x_16, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_16);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBNe(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Nat_reduceBNe___redArg(x_1, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBNe___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Nat_reduceBNe___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBNe___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Nat_reduceBNe(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceBNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1537_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_2 = lean_mk_string_unchecked("Nat", 3, 3);
x_3 = lean_mk_string_unchecked("reduceBNe", 9, 9);
lean_inc(x_2);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_mk_string_unchecked("bne", 3, 3);
x_6 = l_Lean_Name_mkStr1(x_5);
x_7 = lean_unsigned_to_nat(4u);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
x_9 = l_Lean_Name_mkStr1(x_2);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_box(3);
x_13 = lean_unsigned_to_nat(5u);
x_14 = lean_mk_empty_array_with_capacity(x_13);
x_15 = lean_array_push(x_14, x_8);
x_16 = lean_array_push(x_15, x_11);
x_17 = lean_array_push(x_16, x_12);
x_18 = lean_array_push(x_17, x_12);
x_19 = lean_array_push(x_18, x_12);
x_20 = lean_alloc_closure((void*)(l_Nat_reduceBNe___boxed), 9, 0);
x_21 = l_Lean_Meta_Simp_registerBuiltinDSimproc(x_4, x_19, x_20, x_1);
return x_21;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceBNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1539_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Nat", 3, 3);
x_3 = lean_mk_string_unchecked("reduceBNe", 9, 9);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Nat_reduceBNe___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceBNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1541_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Nat", 3, 3);
x_3 = lean_mk_string_unchecked("reduceBNe", 9, 9);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Nat_reduceBNe___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Nat_isValue___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_12; uint8_t x_13; 
lean_inc(x_1);
x_4 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_1, x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_7 = x_4;
} else {
 lean_dec_ref(x_4);
 x_7 = lean_box(0);
}
x_12 = l_Lean_Expr_cleanupAnnotations(x_5);
x_13 = l_Lean_Expr_isApp(x_12);
if (x_13 == 0)
{
lean_dec(x_12);
lean_dec(x_1);
goto block_11;
}
else
{
lean_object* x_14; uint8_t x_15; 
x_14 = l_Lean_Expr_appFnCleanup___redArg(x_12);
x_15 = l_Lean_Expr_isApp(x_14);
if (x_15 == 0)
{
lean_dec(x_14);
lean_dec(x_1);
goto block_11;
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = l_Lean_Expr_appFnCleanup___redArg(x_14);
x_17 = l_Lean_Expr_isApp(x_16);
if (x_17 == 0)
{
lean_dec(x_16);
lean_dec(x_1);
goto block_11;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_18 = l_Lean_Expr_appFnCleanup___redArg(x_16);
x_19 = lean_mk_string_unchecked("OfNat", 5, 5);
x_20 = lean_mk_string_unchecked("ofNat", 5, 5);
x_21 = l_Lean_Name_mkStr2(x_19, x_20);
x_22 = l_Lean_Expr_isConstOf(x_18, x_21);
lean_dec(x_21);
lean_dec(x_18);
if (x_22 == 0)
{
lean_dec(x_1);
goto block_11;
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_7);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_1);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_6);
return x_24;
}
}
}
}
block_11:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_9, 0, x_8);
if (lean_is_scalar(x_7)) {
 x_10 = lean_alloc_ctor(0, 2, 0);
} else {
 x_10 = x_7;
}
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_6);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Nat_isValue(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Nat_isValue___redArg(x_1, x_6, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Nat_isValue___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Nat_isValue___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Nat_isValue___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Nat_isValue(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_isValue_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1713_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_2 = lean_mk_string_unchecked("Nat", 3, 3);
x_3 = lean_mk_string_unchecked("isValue", 7, 7);
lean_inc(x_2);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_mk_string_unchecked("OfNat", 5, 5);
x_6 = lean_mk_string_unchecked("ofNat", 5, 5);
x_7 = l_Lean_Name_mkStr2(x_5, x_6);
x_8 = lean_unsigned_to_nat(3u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Lean_Name_mkStr1(x_2);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_box(3);
x_14 = lean_unsigned_to_nat(4u);
x_15 = lean_mk_empty_array_with_capacity(x_14);
x_16 = lean_array_push(x_15, x_9);
x_17 = lean_array_push(x_16, x_12);
x_18 = lean_array_push(x_17, x_13);
x_19 = lean_array_push(x_18, x_13);
x_20 = lean_alloc_closure((void*)(l_Nat_isValue___boxed), 9, 0);
x_21 = l_Lean_Meta_Simp_registerBuiltinDSimproc(x_4, x_19, x_20, x_1);
return x_21;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_isValue_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1715_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Nat", 3, 3);
x_3 = lean_mk_string_unchecked("isValue", 7, 7);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Nat_isValue___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_asOffset___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_mk_string_unchecked("HAdd", 4, 4);
x_8 = lean_mk_string_unchecked("hAdd", 4, 4);
x_9 = l_Lean_Name_mkStr2(x_7, x_8);
x_10 = lean_unsigned_to_nat(6u);
x_11 = l_Lean_Expr_isAppOfArity(x_1, x_9, x_10);
lean_dec(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_mk_string_unchecked("Add", 3, 3);
x_13 = lean_mk_string_unchecked("add", 3, 3);
lean_inc(x_13);
x_14 = l_Lean_Name_mkStr2(x_12, x_13);
x_15 = lean_unsigned_to_nat(4u);
x_16 = l_Lean_Expr_isAppOfArity(x_1, x_14, x_15);
lean_dec(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_mk_string_unchecked("Nat", 3, 3);
lean_inc(x_17);
x_18 = l_Lean_Name_mkStr2(x_17, x_13);
x_19 = lean_unsigned_to_nat(2u);
x_20 = l_Lean_Expr_isAppOfArity(x_1, x_18, x_19);
lean_dec(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_21 = lean_mk_string_unchecked("succ", 4, 4);
x_22 = l_Lean_Name_mkStr2(x_17, x_21);
x_23 = lean_unsigned_to_nat(1u);
x_24 = l_Lean_Expr_isAppOfArity(x_1, x_22, x_23);
lean_dec(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_6);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = l_Lean_Expr_appArg_x21(x_1);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_23);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_6);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_17);
x_31 = l_Lean_Expr_appArg_x21(x_1);
x_32 = l_Lean_Meta_getNatValue_x3f(x_31, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_31);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_32);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_32, 0);
lean_dec(x_35);
x_36 = lean_box(0);
lean_ctor_set(x_32, 0, x_36);
return x_32;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_32, 1);
lean_inc(x_37);
lean_dec(x_32);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
else
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_32);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_32, 0);
lean_dec(x_41);
x_42 = !lean_is_exclusive(x_33);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_33, 0);
x_44 = l_Lean_Expr_appFn_x21(x_1);
x_45 = l_Lean_Expr_appArg_x21(x_44);
lean_dec(x_44);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_43);
lean_ctor_set(x_33, 0, x_46);
return x_32;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_47 = lean_ctor_get(x_33, 0);
lean_inc(x_47);
lean_dec(x_33);
x_48 = l_Lean_Expr_appFn_x21(x_1);
x_49 = l_Lean_Expr_appArg_x21(x_48);
lean_dec(x_48);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_47);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_32, 0, x_51);
return x_32;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_52 = lean_ctor_get(x_32, 1);
lean_inc(x_52);
lean_dec(x_32);
x_53 = lean_ctor_get(x_33, 0);
lean_inc(x_53);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 x_54 = x_33;
} else {
 lean_dec_ref(x_33);
 x_54 = lean_box(0);
}
x_55 = l_Lean_Expr_appFn_x21(x_1);
x_56 = l_Lean_Expr_appArg_x21(x_55);
lean_dec(x_55);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_53);
if (lean_is_scalar(x_54)) {
 x_58 = lean_alloc_ctor(1, 1, 0);
} else {
 x_58 = x_54;
}
lean_ctor_set(x_58, 0, x_57);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_52);
return x_59;
}
}
}
else
{
uint8_t x_60; 
x_60 = !lean_is_exclusive(x_32);
if (x_60 == 0)
{
return x_32;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_32, 0);
x_62 = lean_ctor_get(x_32, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_32);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_13);
x_64 = l_Lean_Expr_appFn_x21(x_1);
x_65 = l_Lean_Expr_appFn_x21(x_64);
x_66 = l_Lean_Expr_appArg_x21(x_65);
lean_dec(x_65);
x_67 = l_Lean_Nat_mkInstAdd;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_68 = l_Lean_Meta_matchesInstance(x_66, x_67, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; uint8_t x_70; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_unbox(x_69);
lean_dec(x_69);
if (x_70 == 0)
{
uint8_t x_71; 
lean_dec(x_64);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_71 = !lean_is_exclusive(x_68);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_68, 0);
lean_dec(x_72);
x_73 = lean_box(0);
lean_ctor_set(x_68, 0, x_73);
return x_68;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_68, 1);
lean_inc(x_74);
lean_dec(x_68);
x_75 = lean_box(0);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_74);
return x_76;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_68, 1);
lean_inc(x_77);
lean_dec(x_68);
x_78 = l_Lean_Expr_appArg_x21(x_1);
x_79 = l_Lean_Meta_getNatValue_x3f(x_78, x_2, x_3, x_4, x_5, x_77);
lean_dec(x_2);
lean_dec(x_78);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
if (lean_obj_tag(x_80) == 0)
{
uint8_t x_81; 
lean_dec(x_64);
x_81 = !lean_is_exclusive(x_79);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_79, 0);
lean_dec(x_82);
x_83 = lean_box(0);
lean_ctor_set(x_79, 0, x_83);
return x_79;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_79, 1);
lean_inc(x_84);
lean_dec(x_79);
x_85 = lean_box(0);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_84);
return x_86;
}
}
else
{
uint8_t x_87; 
x_87 = !lean_is_exclusive(x_79);
if (x_87 == 0)
{
lean_object* x_88; uint8_t x_89; 
x_88 = lean_ctor_get(x_79, 0);
lean_dec(x_88);
x_89 = !lean_is_exclusive(x_80);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_80, 0);
x_91 = l_Lean_Expr_appArg_x21(x_64);
lean_dec(x_64);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_90);
lean_ctor_set(x_80, 0, x_92);
return x_79;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_93 = lean_ctor_get(x_80, 0);
lean_inc(x_93);
lean_dec(x_80);
x_94 = l_Lean_Expr_appArg_x21(x_64);
lean_dec(x_64);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_93);
x_96 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_79, 0, x_96);
return x_79;
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_97 = lean_ctor_get(x_79, 1);
lean_inc(x_97);
lean_dec(x_79);
x_98 = lean_ctor_get(x_80, 0);
lean_inc(x_98);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 x_99 = x_80;
} else {
 lean_dec_ref(x_80);
 x_99 = lean_box(0);
}
x_100 = l_Lean_Expr_appArg_x21(x_64);
lean_dec(x_64);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_98);
if (lean_is_scalar(x_99)) {
 x_102 = lean_alloc_ctor(1, 1, 0);
} else {
 x_102 = x_99;
}
lean_ctor_set(x_102, 0, x_101);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_97);
return x_103;
}
}
}
else
{
uint8_t x_104; 
lean_dec(x_64);
x_104 = !lean_is_exclusive(x_79);
if (x_104 == 0)
{
return x_79;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_79, 0);
x_106 = lean_ctor_get(x_79, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_79);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
}
}
}
else
{
uint8_t x_108; 
lean_dec(x_64);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_108 = !lean_is_exclusive(x_68);
if (x_108 == 0)
{
return x_68;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_68, 0);
x_110 = lean_ctor_get(x_68, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_68);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_112 = l_Lean_Expr_appFn_x21(x_1);
x_113 = l_Lean_Expr_appFn_x21(x_112);
x_114 = l_Lean_Expr_appArg_x21(x_113);
lean_dec(x_113);
x_115 = l_Lean_Nat_mkInstHAdd;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_116 = l_Lean_Meta_matchesInstance(x_114, x_115, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; uint8_t x_118; 
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_unbox(x_117);
lean_dec(x_117);
if (x_118 == 0)
{
uint8_t x_119; 
lean_dec(x_112);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_119 = !lean_is_exclusive(x_116);
if (x_119 == 0)
{
lean_object* x_120; lean_object* x_121; 
x_120 = lean_ctor_get(x_116, 0);
lean_dec(x_120);
x_121 = lean_box(0);
lean_ctor_set(x_116, 0, x_121);
return x_116;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_116, 1);
lean_inc(x_122);
lean_dec(x_116);
x_123 = lean_box(0);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_122);
return x_124;
}
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_116, 1);
lean_inc(x_125);
lean_dec(x_116);
x_126 = l_Lean_Expr_appArg_x21(x_1);
x_127 = l_Lean_Meta_getNatValue_x3f(x_126, x_2, x_3, x_4, x_5, x_125);
lean_dec(x_2);
lean_dec(x_126);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; 
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
if (lean_obj_tag(x_128) == 0)
{
uint8_t x_129; 
lean_dec(x_112);
x_129 = !lean_is_exclusive(x_127);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; 
x_130 = lean_ctor_get(x_127, 0);
lean_dec(x_130);
x_131 = lean_box(0);
lean_ctor_set(x_127, 0, x_131);
return x_127;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_132 = lean_ctor_get(x_127, 1);
lean_inc(x_132);
lean_dec(x_127);
x_133 = lean_box(0);
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_132);
return x_134;
}
}
else
{
uint8_t x_135; 
x_135 = !lean_is_exclusive(x_127);
if (x_135 == 0)
{
lean_object* x_136; uint8_t x_137; 
x_136 = lean_ctor_get(x_127, 0);
lean_dec(x_136);
x_137 = !lean_is_exclusive(x_128);
if (x_137 == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_138 = lean_ctor_get(x_128, 0);
x_139 = l_Lean_Expr_appArg_x21(x_112);
lean_dec(x_112);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_138);
lean_ctor_set(x_128, 0, x_140);
return x_127;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_141 = lean_ctor_get(x_128, 0);
lean_inc(x_141);
lean_dec(x_128);
x_142 = l_Lean_Expr_appArg_x21(x_112);
lean_dec(x_112);
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_141);
x_144 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_127, 0, x_144);
return x_127;
}
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_145 = lean_ctor_get(x_127, 1);
lean_inc(x_145);
lean_dec(x_127);
x_146 = lean_ctor_get(x_128, 0);
lean_inc(x_146);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 x_147 = x_128;
} else {
 lean_dec_ref(x_128);
 x_147 = lean_box(0);
}
x_148 = l_Lean_Expr_appArg_x21(x_112);
lean_dec(x_112);
x_149 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_146);
if (lean_is_scalar(x_147)) {
 x_150 = lean_alloc_ctor(1, 1, 0);
} else {
 x_150 = x_147;
}
lean_ctor_set(x_150, 0, x_149);
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set(x_151, 1, x_145);
return x_151;
}
}
}
else
{
uint8_t x_152; 
lean_dec(x_112);
x_152 = !lean_is_exclusive(x_127);
if (x_152 == 0)
{
return x_127;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = lean_ctor_get(x_127, 0);
x_154 = lean_ctor_get(x_127, 1);
lean_inc(x_154);
lean_inc(x_153);
lean_dec(x_127);
x_155 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set(x_155, 1, x_154);
return x_155;
}
}
}
}
else
{
uint8_t x_156; 
lean_dec(x_112);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_156 = !lean_is_exclusive(x_116);
if (x_156 == 0)
{
return x_116;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_157 = lean_ctor_get(x_116, 0);
x_158 = lean_ctor_get(x_116, 1);
lean_inc(x_158);
lean_inc(x_157);
lean_dec(x_116);
x_159 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_159, 0, x_157);
lean_ctor_set(x_159, 1, x_158);
return x_159;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_asOffset(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_asOffset___redArg(x_1, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_asOffset___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_asOffset___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_asOffset___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_asOffset(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExprAux___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_Expr_consumeMData(x_1);
lean_dec(x_1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_9 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_asOffset___redArg(x_8, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_eq(x_2, x_12);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_9);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_9, 1);
lean_dec(x_15);
x_16 = lean_ctor_get(x_9, 0);
lean_dec(x_16);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_8);
lean_ctor_set(x_17, 1, x_2);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_9, 0, x_18);
return x_9;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_9);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_8);
lean_ctor_set(x_19, 1, x_2);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_11);
return x_21;
}
}
else
{
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_2);
return x_9;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_8);
x_22 = lean_ctor_get(x_10, 0);
lean_inc(x_22);
lean_dec(x_10);
x_23 = lean_ctor_get(x_9, 1);
lean_inc(x_23);
lean_dec(x_9);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_nat_add(x_2, x_25);
lean_dec(x_25);
lean_dec(x_2);
x_1 = x_24;
x_2 = x_26;
x_7 = x_23;
goto _start;
}
}
else
{
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExprAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExprAux___redArg(x_1, x_2, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExprAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExprAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExpr_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_8 = l_Lean_Meta_getNatValue_x3f(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExprAux___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 0);
lean_dec(x_14);
x_15 = lean_box(0);
lean_ctor_set(x_11, 0, x_15);
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_12);
if (x_19 == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_11);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_12, 0);
x_22 = lean_ctor_get(x_11, 0);
lean_dec(x_22);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
lean_inc(x_24);
x_25 = l_Lean_mkNatLit(x_24);
x_26 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set(x_26, 2, x_24);
lean_ctor_set(x_12, 0, x_26);
return x_11;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_27 = lean_ctor_get(x_12, 0);
x_28 = lean_ctor_get(x_11, 1);
lean_inc(x_28);
lean_dec(x_11);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
lean_inc(x_30);
x_31 = l_Lean_mkNatLit(x_30);
x_32 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set(x_32, 2, x_30);
lean_ctor_set(x_12, 0, x_32);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_12);
lean_ctor_set(x_33, 1, x_28);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_34 = lean_ctor_get(x_12, 0);
lean_inc(x_34);
lean_dec(x_12);
x_35 = lean_ctor_get(x_11, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_36 = x_11;
} else {
 lean_dec_ref(x_11);
 x_36 = lean_box(0);
}
x_37 = lean_ctor_get(x_34, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_34, 1);
lean_inc(x_38);
lean_dec(x_34);
lean_inc(x_38);
x_39 = l_Lean_mkNatLit(x_38);
x_40 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_39);
lean_ctor_set(x_40, 2, x_38);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
if (lean_is_scalar(x_36)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_36;
}
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_35);
return x_42;
}
}
}
else
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_11);
if (x_43 == 0)
{
return x_11;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_11, 0);
x_45 = lean_ctor_get(x_11, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_11);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_8);
if (x_47 == 0)
{
lean_object* x_48; uint8_t x_49; 
x_48 = lean_ctor_get(x_8, 0);
lean_dec(x_48);
x_49 = !lean_is_exclusive(x_9);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_9, 0);
x_51 = lean_nat_add(x_50, x_2);
lean_dec(x_2);
lean_dec(x_50);
x_52 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_9, 0, x_52);
return x_8;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_9, 0);
lean_inc(x_53);
lean_dec(x_9);
x_54 = lean_nat_add(x_53, x_2);
lean_dec(x_2);
lean_dec(x_53);
x_55 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_55, 0, x_54);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_8, 0, x_56);
return x_8;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_57 = lean_ctor_get(x_8, 1);
lean_inc(x_57);
lean_dec(x_8);
x_58 = lean_ctor_get(x_9, 0);
lean_inc(x_58);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 x_59 = x_9;
} else {
 lean_dec_ref(x_9);
 x_59 = lean_box(0);
}
x_60 = lean_nat_add(x_58, x_2);
lean_dec(x_2);
lean_dec(x_58);
x_61 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_61, 0, x_60);
if (lean_is_scalar(x_59)) {
 x_62 = lean_alloc_ctor(1, 1, 0);
} else {
 x_62 = x_59;
}
lean_ctor_set(x_62, 0, x_61);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_57);
return x_63;
}
}
}
else
{
uint8_t x_64; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_64 = !lean_is_exclusive(x_8);
if (x_64 == 0)
{
return x_8;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_8, 0);
x_66 = lean_ctor_get(x_8, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_8);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExpr_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExpr_x3f___redArg(x_1, x_2, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExpr_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExpr_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_3 = lean_box(0);
x_4 = lean_mk_string_unchecked("Nat", 3, 3);
x_5 = l_Lean_Name_mkStr1(x_4);
x_6 = lean_box(0);
x_7 = l_Lean_Expr_const___override(x_5, x_6);
x_8 = lean_mk_string_unchecked("instHAdd", 8, 8);
x_9 = l_Lean_Name_mkStr1(x_8);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_6);
lean_inc(x_10);
x_11 = l_Lean_Expr_const___override(x_9, x_10);
x_12 = lean_mk_string_unchecked("instAddNat", 10, 10);
x_13 = l_Lean_Name_mkStr1(x_12);
x_14 = l_Lean_Expr_const___override(x_13, x_6);
x_15 = lean_unsigned_to_nat(2u);
x_16 = lean_mk_empty_array_with_capacity(x_15);
lean_inc(x_7);
x_17 = lean_array_push(x_16, x_7);
x_18 = lean_array_push(x_17, x_14);
x_19 = l_Lean_mkAppN(x_11, x_18);
lean_dec(x_18);
x_20 = lean_mk_string_unchecked("HAdd", 4, 4);
x_21 = lean_mk_string_unchecked("hAdd", 4, 4);
x_22 = l_Lean_Name_mkStr2(x_20, x_21);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_3);
lean_ctor_set(x_23, 1, x_10);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_3);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_Expr_const___override(x_22, x_24);
x_26 = lean_unsigned_to_nat(6u);
x_27 = lean_mk_empty_array_with_capacity(x_26);
lean_inc(x_7);
x_28 = lean_array_push(x_27, x_7);
lean_inc(x_7);
x_29 = lean_array_push(x_28, x_7);
x_30 = lean_array_push(x_29, x_7);
x_31 = lean_array_push(x_30, x_19);
x_32 = lean_array_push(x_31, x_1);
x_33 = lean_array_push(x_32, x_2);
x_34 = l_Lean_mkAppN(x_25, x_33);
lean_dec(x_33);
return x_34;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_3 = lean_box(0);
x_4 = lean_mk_string_unchecked("Nat", 3, 3);
x_5 = l_Lean_Name_mkStr1(x_4);
x_6 = lean_box(0);
x_7 = l_Lean_Expr_const___override(x_5, x_6);
x_8 = lean_mk_string_unchecked("instSubNat", 10, 10);
x_9 = l_Lean_Name_mkStr1(x_8);
x_10 = l_Lean_Expr_const___override(x_9, x_6);
x_11 = lean_mk_string_unchecked("instHSub", 8, 8);
x_12 = l_Lean_Name_mkStr1(x_11);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_3);
lean_ctor_set(x_13, 1, x_6);
lean_inc(x_13);
x_14 = l_Lean_Expr_const___override(x_12, x_13);
x_15 = lean_unsigned_to_nat(2u);
x_16 = lean_mk_empty_array_with_capacity(x_15);
lean_inc(x_7);
x_17 = lean_array_push(x_16, x_7);
x_18 = lean_array_push(x_17, x_10);
x_19 = l_Lean_mkAppN(x_14, x_18);
lean_dec(x_18);
x_20 = lean_mk_string_unchecked("HSub", 4, 4);
x_21 = lean_mk_string_unchecked("hSub", 4, 4);
x_22 = l_Lean_Name_mkStr2(x_20, x_21);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_3);
lean_ctor_set(x_23, 1, x_13);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_3);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_Expr_const___override(x_22, x_24);
x_26 = lean_unsigned_to_nat(6u);
x_27 = lean_mk_empty_array_with_capacity(x_26);
lean_inc(x_7);
x_28 = lean_array_push(x_27, x_7);
lean_inc(x_7);
x_29 = lean_array_push(x_28, x_7);
x_30 = lean_array_push(x_29, x_7);
x_31 = lean_array_push(x_30, x_19);
x_32 = lean_array_push(x_31, x_1);
x_33 = lean_array_push(x_32, x_2);
x_34 = l_Lean_mkAppN(x_25, x_33);
lean_dec(x_33);
return x_34;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_3 = lean_mk_string_unchecked("Eq", 2, 2);
x_4 = l_Lean_Name_mkStr1(x_3);
x_5 = l_Lean_levelOne;
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
x_8 = l_Lean_Expr_const___override(x_4, x_7);
x_9 = lean_mk_string_unchecked("Nat", 3, 3);
x_10 = l_Lean_Name_mkStr1(x_9);
x_11 = l_Lean_Expr_const___override(x_10, x_6);
x_12 = lean_unsigned_to_nat(3u);
x_13 = lean_mk_empty_array_with_capacity(x_12);
x_14 = lean_array_push(x_13, x_11);
x_15 = lean_array_push(x_14, x_1);
x_16 = lean_array_push(x_15, x_2);
x_17 = l_Lean_mkAppN(x_8, x_16);
lean_dec(x_16);
return x_17;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_1 = lean_mk_string_unchecked("instBEqOfDecidableEq", 20, 20);
x_2 = l_Lean_Name_mkStr1(x_1);
x_3 = lean_box(0);
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
x_6 = l_Lean_Expr_const___override(x_2, x_5);
x_7 = lean_mk_string_unchecked("Nat", 3, 3);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = l_Lean_Expr_const___override(x_8, x_4);
x_10 = lean_mk_string_unchecked("instDecidableEqNat", 18, 18);
x_11 = l_Lean_Name_mkStr1(x_10);
x_12 = l_Lean_Expr_const___override(x_11, x_4);
x_13 = lean_unsigned_to_nat(2u);
x_14 = lean_mk_empty_array_with_capacity(x_13);
x_15 = lean_array_push(x_14, x_9);
x_16 = lean_array_push(x_15, x_12);
x_17 = l_Lean_mkAppN(x_6, x_16);
lean_dec(x_16);
return x_17;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNat(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_3 = lean_mk_string_unchecked("BEq", 3, 3);
x_4 = lean_mk_string_unchecked("beq", 3, 3);
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
x_13 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance;
x_14 = lean_unsigned_to_nat(4u);
x_15 = lean_mk_empty_array_with_capacity(x_14);
x_16 = lean_array_push(x_15, x_12);
x_17 = lean_array_push(x_16, x_13);
x_18 = lean_array_push(x_17, x_1);
x_19 = lean_array_push(x_18, x_2);
x_20 = l_Lean_mkAppN(x_9, x_19);
lean_dec(x_19);
return x_20;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBneNat(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_3 = lean_mk_string_unchecked("bne", 3, 3);
x_4 = l_Lean_Name_mkStr1(x_3);
x_5 = lean_box(0);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
x_8 = l_Lean_Expr_const___override(x_4, x_7);
x_9 = lean_mk_string_unchecked("Nat", 3, 3);
x_10 = l_Lean_Name_mkStr1(x_9);
x_11 = l_Lean_Expr_const___override(x_10, x_6);
x_12 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance;
x_13 = lean_unsigned_to_nat(4u);
x_14 = lean_mk_empty_array_with_capacity(x_13);
x_15 = lean_array_push(x_14, x_11);
x_16 = lean_array_push(x_15, x_12);
x_17 = lean_array_push(x_16, x_1);
x_18 = lean_array_push(x_17, x_2);
x_19 = l_Lean_mkAppN(x_8, x_18);
lean_dec(x_18);
return x_19;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_3 = lean_mk_string_unchecked("LE", 2, 2);
x_4 = lean_mk_string_unchecked("le", 2, 2);
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
x_13 = lean_mk_string_unchecked("instLENat", 9, 9);
x_14 = l_Lean_Name_mkStr1(x_13);
x_15 = l_Lean_Expr_const___override(x_14, x_7);
x_16 = lean_unsigned_to_nat(4u);
x_17 = lean_mk_empty_array_with_capacity(x_16);
x_18 = lean_array_push(x_17, x_12);
x_19 = lean_array_push(x_18, x_15);
x_20 = lean_array_push(x_19, x_1);
x_21 = lean_array_push(x_20, x_2);
x_22 = l_Lean_mkAppN(x_9, x_21);
lean_dec(x_21);
return x_22;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkGENat(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_3 = lean_mk_string_unchecked("LT", 2, 2);
x_4 = lean_mk_string_unchecked("lt", 2, 2);
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
x_13 = lean_mk_string_unchecked("instLTNat", 9, 9);
x_14 = l_Lean_Name_mkStr1(x_13);
x_15 = l_Lean_Expr_const___override(x_14, x_7);
x_16 = lean_unsigned_to_nat(4u);
x_17 = lean_mk_empty_array_with_capacity(x_16);
x_18 = lean_array_push(x_17, x_12);
x_19 = lean_array_push(x_18, x_15);
x_20 = lean_array_push(x_19, x_1);
x_21 = lean_array_push(x_20, x_2);
x_22 = l_Lean_mkAppN(x_9, x_21);
lean_dec(x_21);
return x_22;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkGTNat(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_7 = l_Lean_Meta_mkDecide(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_mk_string_unchecked("Bool", 4, 4);
x_11 = lean_mk_string_unchecked("true", 4, 4);
x_12 = l_Lean_Name_mkStr2(x_10, x_11);
x_13 = lean_box(0);
x_14 = l_Lean_Expr_const___override(x_12, x_13);
x_15 = l_Lean_Meta_mkEqRefl(x_14, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_mk_string_unchecked("of_decide_eq_true", 17, 17);
x_19 = l_Lean_Name_mkStr1(x_18);
x_20 = l_Lean_Expr_const___override(x_19, x_13);
x_21 = l_Lean_Expr_appArg_x21(x_8);
lean_dec(x_8);
x_22 = lean_unsigned_to_nat(3u);
x_23 = lean_mk_empty_array_with_capacity(x_22);
x_24 = lean_array_push(x_23, x_1);
x_25 = lean_array_push(x_24, x_21);
x_26 = lean_array_push(x_25, x_17);
x_27 = l_Lean_mkAppN(x_20, x_26);
lean_dec(x_26);
lean_ctor_set(x_15, 0, x_27);
return x_15;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_28 = lean_ctor_get(x_15, 0);
x_29 = lean_ctor_get(x_15, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_15);
x_30 = lean_mk_string_unchecked("of_decide_eq_true", 17, 17);
x_31 = l_Lean_Name_mkStr1(x_30);
x_32 = l_Lean_Expr_const___override(x_31, x_13);
x_33 = l_Lean_Expr_appArg_x21(x_8);
lean_dec(x_8);
x_34 = lean_unsigned_to_nat(3u);
x_35 = lean_mk_empty_array_with_capacity(x_34);
x_36 = lean_array_push(x_35, x_1);
x_37 = lean_array_push(x_36, x_33);
x_38 = lean_array_push(x_37, x_28);
x_39 = l_Lean_mkAppN(x_32, x_38);
lean_dec(x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_29);
return x_40;
}
}
else
{
lean_dec(x_8);
lean_dec(x_1);
return x_15;
}
}
else
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Nat_applySimprocConst___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_st_ref_get(x_4, x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_box(1);
x_11 = lean_unbox(x_10);
lean_inc(x_2);
x_12 = l_Lean_Environment_contains(x_9, x_2, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_2);
lean_dec(x_1);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_6, 0, x_14);
return x_6;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_box(0);
x_16 = l_Lean_Expr_const___override(x_2, x_15);
x_17 = l_Lean_mkAppN(x_16, x_3);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set_uint8(x_19, sizeof(void*)*2, x_12);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_6, 0, x_20);
return x_6;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_26; 
x_21 = lean_ctor_get(x_6, 0);
x_22 = lean_ctor_get(x_6, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_6);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_box(1);
x_25 = lean_unbox(x_24);
lean_inc(x_2);
x_26 = l_Lean_Environment_contains(x_23, x_2, x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_2);
lean_dec(x_1);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_22);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_30 = lean_box(0);
x_31 = l_Lean_Expr_const___override(x_2, x_30);
x_32 = l_Lean_mkAppN(x_31, x_3);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_34, 0, x_1);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set_uint8(x_34, sizeof(void*)*2, x_26);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_22);
return x_36;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_applySimprocConst(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Nat_applySimprocConst___redArg(x_1, x_2, x_3, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Nat_applySimprocConst___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Nat_applySimprocConst___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Nat_applySimprocConst___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Nat_applySimprocConst(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Nat_applyEqLemma___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_st_ref_get(x_4, x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_box(1);
x_11 = lean_unbox(x_10);
lean_inc(x_2);
x_12 = l_Lean_Environment_contains(x_9, x_2, x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_2);
lean_dec(x_1);
x_13 = lean_box(0);
lean_ctor_set(x_6, 0, x_13);
return x_6;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_box(0);
x_15 = l_Lean_Expr_const___override(x_2, x_14);
x_16 = l_Lean_mkAppN(x_15, x_3);
x_17 = lean_apply_1(x_1, x_16);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_6, 0, x_18);
return x_6;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_24; 
x_19 = lean_ctor_get(x_6, 0);
x_20 = lean_ctor_get(x_6, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_6);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_box(1);
x_23 = lean_unbox(x_22);
lean_inc(x_2);
x_24 = l_Lean_Environment_contains(x_21, x_2, x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_2);
lean_dec(x_1);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_20);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_27 = lean_box(0);
x_28 = l_Lean_Expr_const___override(x_2, x_27);
x_29 = l_Lean_mkAppN(x_28, x_3);
x_30 = lean_apply_1(x_1, x_29);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_20);
return x_32;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_applyEqLemma(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Nat_applyEqLemma___redArg(x_1, x_2, x_3, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Nat_applyEqLemma___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Nat_applyEqLemma___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Nat_applyEqLemma___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Nat_applyEqLemma(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceNatEqExpr___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceNatEqExpr___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_nat_sub(x_1, x_2);
x_6 = l_Lean_mkNatLit(x_5);
x_7 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_6);
lean_ctor_set(x_7, 2, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceNatEqExpr___redArg___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceNatEqExpr___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceNatEqExpr___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_unsigned_to_nat(0u);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_9 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExpr_x3f___redArg(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_9, 0);
lean_dec(x_12);
x_13 = lean_box(0);
lean_ctor_set(x_9, 0, x_13);
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_dec(x_9);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_9, 1);
lean_inc(x_17);
lean_dec(x_9);
x_18 = lean_ctor_get(x_10, 0);
lean_inc(x_18);
lean_dec(x_10);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_19 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExpr_x3f___redArg(x_2, x_8, x_3, x_4, x_5, x_6, x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
lean_dec(x_18);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 0);
lean_dec(x_22);
x_23 = lean_box(0);
lean_ctor_set(x_19, 0, x_23);
return x_19;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_dec(x_19);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
else
{
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_27; 
lean_dec(x_2);
x_27 = !lean_is_exclusive(x_20);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_20, 0);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_19);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_19, 0);
lean_dec(x_30);
x_31 = lean_ctor_get(x_18, 0);
lean_inc(x_31);
lean_dec(x_18);
x_32 = lean_ctor_get(x_28, 0);
lean_inc(x_32);
lean_dec(x_28);
x_33 = lean_nat_dec_eq(x_31, x_32);
lean_dec(x_32);
lean_dec(x_31);
x_34 = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(x_34, 0, x_33);
lean_ctor_set(x_20, 0, x_34);
return x_19;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; 
x_35 = lean_ctor_get(x_19, 1);
lean_inc(x_35);
lean_dec(x_19);
x_36 = lean_ctor_get(x_18, 0);
lean_inc(x_36);
lean_dec(x_18);
x_37 = lean_ctor_get(x_28, 0);
lean_inc(x_37);
lean_dec(x_28);
x_38 = lean_nat_dec_eq(x_36, x_37);
lean_dec(x_37);
lean_dec(x_36);
x_39 = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(x_39, 0, x_38);
lean_ctor_set(x_20, 0, x_39);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_20);
lean_ctor_set(x_40, 1, x_35);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
lean_free_object(x_20);
x_41 = lean_ctor_get(x_19, 1);
lean_inc(x_41);
lean_dec(x_19);
x_42 = lean_ctor_get(x_18, 0);
lean_inc(x_42);
lean_dec(x_18);
x_43 = lean_ctor_get(x_28, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_28, 1);
lean_inc(x_44);
x_45 = lean_ctor_get(x_28, 2);
lean_inc(x_45);
lean_dec(x_28);
x_46 = lean_nat_dec_le(x_45, x_42);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_45);
lean_dec(x_42);
lean_inc(x_44);
lean_inc(x_1);
x_47 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat(x_1, x_44);
lean_inc(x_6);
x_48 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(x_47, x_3, x_4, x_5, x_6, x_41);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_alloc_closure((void*)(l_Nat_reduceNatEqExpr___redArg___lam__0), 1, 0);
x_52 = lean_mk_string_unchecked("Nat", 3, 3);
x_53 = lean_mk_string_unchecked("Simproc", 7, 7);
x_54 = lean_mk_string_unchecked("eq_add_gt", 9, 9);
x_55 = l_Lean_Name_mkStr3(x_52, x_53, x_54);
x_56 = lean_unsigned_to_nat(4u);
x_57 = lean_mk_empty_array_with_capacity(x_56);
x_58 = lean_array_push(x_57, x_1);
x_59 = lean_array_push(x_58, x_43);
x_60 = lean_array_push(x_59, x_44);
x_61 = lean_array_push(x_60, x_49);
x_62 = l_Nat_applyEqLemma___redArg(x_51, x_55, x_61, x_6, x_50);
lean_dec(x_6);
lean_dec(x_61);
return x_62;
}
else
{
uint8_t x_63; 
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_6);
lean_dec(x_1);
x_63 = !lean_is_exclusive(x_48);
if (x_63 == 0)
{
return x_48;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_48, 0);
x_65 = lean_ctor_get(x_48, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_48);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
else
{
lean_object* x_67; lean_object* x_68; 
lean_inc(x_1);
lean_inc(x_44);
x_67 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(x_44, x_1);
lean_inc(x_6);
x_68 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(x_67, x_3, x_4, x_5, x_6, x_41);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
lean_inc(x_43);
x_71 = lean_alloc_closure((void*)(l_Nat_reduceNatEqExpr___redArg___lam__1___boxed), 4, 3);
lean_closure_set(x_71, 0, x_42);
lean_closure_set(x_71, 1, x_45);
lean_closure_set(x_71, 2, x_43);
x_72 = lean_mk_string_unchecked("Nat", 3, 3);
x_73 = lean_mk_string_unchecked("Simproc", 7, 7);
x_74 = lean_mk_string_unchecked("eq_add_le", 9, 9);
x_75 = l_Lean_Name_mkStr3(x_72, x_73, x_74);
x_76 = lean_unsigned_to_nat(4u);
x_77 = lean_mk_empty_array_with_capacity(x_76);
x_78 = lean_array_push(x_77, x_1);
x_79 = lean_array_push(x_78, x_43);
x_80 = lean_array_push(x_79, x_44);
x_81 = lean_array_push(x_80, x_69);
x_82 = l_Nat_applyEqLemma___redArg(x_71, x_75, x_81, x_6, x_70);
lean_dec(x_6);
lean_dec(x_81);
return x_82;
}
else
{
uint8_t x_83; 
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_6);
lean_dec(x_1);
x_83 = !lean_is_exclusive(x_68);
if (x_83 == 0)
{
return x_68;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_68, 0);
x_85 = lean_ctor_get(x_68, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_68);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
}
}
else
{
lean_object* x_87; 
x_87 = lean_ctor_get(x_20, 0);
lean_inc(x_87);
lean_dec(x_20);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_88 = lean_ctor_get(x_19, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_89 = x_19;
} else {
 lean_dec_ref(x_19);
 x_89 = lean_box(0);
}
x_90 = lean_ctor_get(x_18, 0);
lean_inc(x_90);
lean_dec(x_18);
x_91 = lean_ctor_get(x_87, 0);
lean_inc(x_91);
lean_dec(x_87);
x_92 = lean_nat_dec_eq(x_90, x_91);
lean_dec(x_91);
lean_dec(x_90);
x_93 = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(x_93, 0, x_92);
x_94 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_94, 0, x_93);
if (lean_is_scalar(x_89)) {
 x_95 = lean_alloc_ctor(0, 2, 0);
} else {
 x_95 = x_89;
}
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_88);
return x_95;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_96 = lean_ctor_get(x_19, 1);
lean_inc(x_96);
lean_dec(x_19);
x_97 = lean_ctor_get(x_18, 0);
lean_inc(x_97);
lean_dec(x_18);
x_98 = lean_ctor_get(x_87, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_87, 1);
lean_inc(x_99);
x_100 = lean_ctor_get(x_87, 2);
lean_inc(x_100);
lean_dec(x_87);
x_101 = lean_nat_dec_le(x_100, x_97);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; 
lean_dec(x_100);
lean_dec(x_97);
lean_inc(x_99);
lean_inc(x_1);
x_102 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat(x_1, x_99);
lean_inc(x_6);
x_103 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(x_102, x_3, x_4, x_5, x_6, x_96);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
x_106 = lean_alloc_closure((void*)(l_Nat_reduceNatEqExpr___redArg___lam__0), 1, 0);
x_107 = lean_mk_string_unchecked("Nat", 3, 3);
x_108 = lean_mk_string_unchecked("Simproc", 7, 7);
x_109 = lean_mk_string_unchecked("eq_add_gt", 9, 9);
x_110 = l_Lean_Name_mkStr3(x_107, x_108, x_109);
x_111 = lean_unsigned_to_nat(4u);
x_112 = lean_mk_empty_array_with_capacity(x_111);
x_113 = lean_array_push(x_112, x_1);
x_114 = lean_array_push(x_113, x_98);
x_115 = lean_array_push(x_114, x_99);
x_116 = lean_array_push(x_115, x_104);
x_117 = l_Nat_applyEqLemma___redArg(x_106, x_110, x_116, x_6, x_105);
lean_dec(x_6);
lean_dec(x_116);
return x_117;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_6);
lean_dec(x_1);
x_118 = lean_ctor_get(x_103, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_103, 1);
lean_inc(x_119);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_120 = x_103;
} else {
 lean_dec_ref(x_103);
 x_120 = lean_box(0);
}
if (lean_is_scalar(x_120)) {
 x_121 = lean_alloc_ctor(1, 2, 0);
} else {
 x_121 = x_120;
}
lean_ctor_set(x_121, 0, x_118);
lean_ctor_set(x_121, 1, x_119);
return x_121;
}
}
else
{
lean_object* x_122; lean_object* x_123; 
lean_inc(x_1);
lean_inc(x_99);
x_122 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(x_99, x_1);
lean_inc(x_6);
x_123 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(x_122, x_3, x_4, x_5, x_6, x_96);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
lean_dec(x_123);
lean_inc(x_98);
x_126 = lean_alloc_closure((void*)(l_Nat_reduceNatEqExpr___redArg___lam__1___boxed), 4, 3);
lean_closure_set(x_126, 0, x_97);
lean_closure_set(x_126, 1, x_100);
lean_closure_set(x_126, 2, x_98);
x_127 = lean_mk_string_unchecked("Nat", 3, 3);
x_128 = lean_mk_string_unchecked("Simproc", 7, 7);
x_129 = lean_mk_string_unchecked("eq_add_le", 9, 9);
x_130 = l_Lean_Name_mkStr3(x_127, x_128, x_129);
x_131 = lean_unsigned_to_nat(4u);
x_132 = lean_mk_empty_array_with_capacity(x_131);
x_133 = lean_array_push(x_132, x_1);
x_134 = lean_array_push(x_133, x_98);
x_135 = lean_array_push(x_134, x_99);
x_136 = lean_array_push(x_135, x_124);
x_137 = l_Nat_applyEqLemma___redArg(x_126, x_130, x_136, x_6, x_125);
lean_dec(x_6);
lean_dec(x_136);
return x_137;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_6);
lean_dec(x_1);
x_138 = lean_ctor_get(x_123, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_123, 1);
lean_inc(x_139);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 x_140 = x_123;
} else {
 lean_dec_ref(x_123);
 x_140 = lean_box(0);
}
if (lean_is_scalar(x_140)) {
 x_141 = lean_alloc_ctor(1, 2, 0);
} else {
 x_141 = x_140;
}
lean_ctor_set(x_141, 0, x_138);
lean_ctor_set(x_141, 1, x_139);
return x_141;
}
}
}
}
}
else
{
lean_object* x_142; 
lean_dec(x_1);
x_142 = lean_ctor_get(x_20, 0);
lean_inc(x_142);
lean_dec(x_20);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; 
x_143 = lean_ctor_get(x_19, 1);
lean_inc(x_143);
lean_dec(x_19);
x_144 = lean_ctor_get(x_18, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_18, 1);
lean_inc(x_145);
x_146 = lean_ctor_get(x_18, 2);
lean_inc(x_146);
lean_dec(x_18);
x_147 = lean_ctor_get(x_142, 0);
lean_inc(x_147);
lean_dec(x_142);
x_148 = lean_nat_dec_le(x_146, x_147);
if (x_148 == 0)
{
lean_object* x_149; lean_object* x_150; 
lean_dec(x_147);
lean_dec(x_146);
lean_inc(x_145);
lean_inc(x_2);
x_149 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat(x_2, x_145);
lean_inc(x_6);
x_150 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(x_149, x_3, x_4, x_5, x_6, x_143);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_150, 1);
lean_inc(x_152);
lean_dec(x_150);
x_153 = lean_alloc_closure((void*)(l_Nat_reduceNatEqExpr___redArg___lam__0), 1, 0);
x_154 = lean_mk_string_unchecked("Nat", 3, 3);
x_155 = lean_mk_string_unchecked("Simproc", 7, 7);
x_156 = lean_mk_string_unchecked("add_eq_gt", 9, 9);
x_157 = l_Lean_Name_mkStr3(x_154, x_155, x_156);
x_158 = lean_unsigned_to_nat(4u);
x_159 = lean_mk_empty_array_with_capacity(x_158);
x_160 = lean_array_push(x_159, x_144);
x_161 = lean_array_push(x_160, x_145);
x_162 = lean_array_push(x_161, x_2);
x_163 = lean_array_push(x_162, x_151);
x_164 = l_Nat_applyEqLemma___redArg(x_153, x_157, x_163, x_6, x_152);
lean_dec(x_6);
lean_dec(x_163);
return x_164;
}
else
{
uint8_t x_165; 
lean_dec(x_145);
lean_dec(x_144);
lean_dec(x_6);
lean_dec(x_2);
x_165 = !lean_is_exclusive(x_150);
if (x_165 == 0)
{
return x_150;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = lean_ctor_get(x_150, 0);
x_167 = lean_ctor_get(x_150, 1);
lean_inc(x_167);
lean_inc(x_166);
lean_dec(x_150);
x_168 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_168, 0, x_166);
lean_ctor_set(x_168, 1, x_167);
return x_168;
}
}
}
else
{
lean_object* x_169; lean_object* x_170; 
lean_inc(x_2);
lean_inc(x_145);
x_169 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(x_145, x_2);
lean_inc(x_6);
x_170 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(x_169, x_3, x_4, x_5, x_6, x_143);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_170, 1);
lean_inc(x_172);
lean_dec(x_170);
lean_inc(x_144);
x_173 = lean_alloc_closure((void*)(l_Nat_reduceNatEqExpr___redArg___lam__1___boxed), 4, 3);
lean_closure_set(x_173, 0, x_147);
lean_closure_set(x_173, 1, x_146);
lean_closure_set(x_173, 2, x_144);
x_174 = lean_mk_string_unchecked("Nat", 3, 3);
x_175 = lean_mk_string_unchecked("Simproc", 7, 7);
x_176 = lean_mk_string_unchecked("add_eq_le", 9, 9);
x_177 = l_Lean_Name_mkStr3(x_174, x_175, x_176);
x_178 = lean_unsigned_to_nat(4u);
x_179 = lean_mk_empty_array_with_capacity(x_178);
x_180 = lean_array_push(x_179, x_144);
x_181 = lean_array_push(x_180, x_145);
x_182 = lean_array_push(x_181, x_2);
x_183 = lean_array_push(x_182, x_171);
x_184 = l_Nat_applyEqLemma___redArg(x_173, x_177, x_183, x_6, x_172);
lean_dec(x_6);
lean_dec(x_183);
return x_184;
}
else
{
uint8_t x_185; 
lean_dec(x_147);
lean_dec(x_146);
lean_dec(x_145);
lean_dec(x_144);
lean_dec(x_6);
lean_dec(x_2);
x_185 = !lean_is_exclusive(x_170);
if (x_185 == 0)
{
return x_170;
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_186 = lean_ctor_get(x_170, 0);
x_187 = lean_ctor_get(x_170, 1);
lean_inc(x_187);
lean_inc(x_186);
lean_dec(x_170);
x_188 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_188, 0, x_186);
lean_ctor_set(x_188, 1, x_187);
return x_188;
}
}
}
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; uint8_t x_219; 
lean_dec(x_2);
x_189 = lean_ctor_get(x_19, 1);
lean_inc(x_189);
lean_dec(x_19);
x_190 = lean_ctor_get(x_18, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_18, 1);
lean_inc(x_191);
x_192 = lean_ctor_get(x_18, 2);
lean_inc(x_192);
lean_dec(x_18);
x_193 = lean_ctor_get(x_142, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_142, 1);
lean_inc(x_194);
x_195 = lean_ctor_get(x_142, 2);
lean_inc(x_195);
lean_dec(x_142);
x_219 = lean_nat_dec_le(x_192, x_195);
if (x_219 == 0)
{
lean_object* x_220; lean_object* x_221; 
lean_inc(x_191);
lean_inc(x_194);
x_220 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(x_194, x_191);
lean_inc(x_6);
x_221 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(x_220, x_3, x_4, x_5, x_6, x_189);
if (lean_obj_tag(x_221) == 0)
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_222 = lean_ctor_get(x_221, 0);
lean_inc(x_222);
x_223 = lean_ctor_get(x_221, 1);
lean_inc(x_223);
lean_dec(x_221);
x_224 = lean_nat_sub(x_192, x_195);
lean_dec(x_195);
lean_dec(x_192);
x_225 = l_Lean_mkNatLit(x_224);
lean_inc(x_190);
x_226 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat(x_190, x_225);
lean_inc(x_193);
x_227 = lean_alloc_closure((void*)(l_Nat_reduceNatEqExpr___redArg___lam__4), 3, 2);
lean_closure_set(x_227, 0, x_226);
lean_closure_set(x_227, 1, x_193);
x_228 = lean_mk_string_unchecked("Nat", 3, 3);
x_229 = lean_mk_string_unchecked("Simproc", 7, 7);
x_230 = lean_mk_string_unchecked("add_eq_add_ge", 13, 13);
x_231 = l_Lean_Name_mkStr3(x_228, x_229, x_230);
x_232 = lean_unsigned_to_nat(5u);
x_233 = lean_mk_empty_array_with_capacity(x_232);
x_234 = lean_array_push(x_233, x_190);
x_235 = lean_array_push(x_234, x_193);
x_236 = lean_array_push(x_235, x_191);
x_237 = lean_array_push(x_236, x_194);
x_238 = lean_array_push(x_237, x_222);
x_239 = l_Nat_applyEqLemma___redArg(x_227, x_231, x_238, x_6, x_223);
lean_dec(x_6);
lean_dec(x_238);
return x_239;
}
else
{
uint8_t x_240; 
lean_dec(x_195);
lean_dec(x_194);
lean_dec(x_193);
lean_dec(x_192);
lean_dec(x_191);
lean_dec(x_190);
lean_dec(x_6);
x_240 = !lean_is_exclusive(x_221);
if (x_240 == 0)
{
return x_221;
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; 
x_241 = lean_ctor_get(x_221, 0);
x_242 = lean_ctor_get(x_221, 1);
lean_inc(x_242);
lean_inc(x_241);
lean_dec(x_221);
x_243 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_243, 0, x_241);
lean_ctor_set(x_243, 1, x_242);
return x_243;
}
}
}
else
{
uint8_t x_244; 
x_244 = lean_nat_dec_eq(x_192, x_195);
if (x_244 == 0)
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; 
x_245 = lean_nat_sub(x_195, x_192);
lean_dec(x_192);
lean_dec(x_195);
x_246 = l_Lean_mkNatLit(x_245);
lean_inc(x_193);
x_247 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat(x_193, x_246);
x_196 = x_247;
goto block_218;
}
else
{
lean_dec(x_195);
lean_dec(x_192);
lean_inc(x_193);
x_196 = x_193;
goto block_218;
}
}
block_218:
{
lean_object* x_197; lean_object* x_198; 
lean_inc(x_194);
lean_inc(x_191);
x_197 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(x_191, x_194);
lean_inc(x_6);
x_198 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(x_197, x_3, x_4, x_5, x_6, x_189);
if (lean_obj_tag(x_198) == 0)
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_199 = lean_ctor_get(x_198, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_198, 1);
lean_inc(x_200);
lean_dec(x_198);
lean_inc(x_190);
x_201 = lean_alloc_closure((void*)(l_Nat_reduceNatEqExpr___redArg___lam__2), 3, 2);
lean_closure_set(x_201, 0, x_190);
lean_closure_set(x_201, 1, x_196);
x_202 = lean_mk_string_unchecked("Nat", 3, 3);
x_203 = lean_mk_string_unchecked("Simproc", 7, 7);
x_204 = lean_mk_string_unchecked("add_eq_add_le", 13, 13);
x_205 = l_Lean_Name_mkStr3(x_202, x_203, x_204);
x_206 = lean_unsigned_to_nat(5u);
x_207 = lean_mk_empty_array_with_capacity(x_206);
x_208 = lean_array_push(x_207, x_190);
x_209 = lean_array_push(x_208, x_193);
x_210 = lean_array_push(x_209, x_191);
x_211 = lean_array_push(x_210, x_194);
x_212 = lean_array_push(x_211, x_199);
x_213 = l_Nat_applyEqLemma___redArg(x_201, x_205, x_212, x_6, x_200);
lean_dec(x_6);
lean_dec(x_212);
return x_213;
}
else
{
uint8_t x_214; 
lean_dec(x_196);
lean_dec(x_194);
lean_dec(x_193);
lean_dec(x_191);
lean_dec(x_190);
lean_dec(x_6);
x_214 = !lean_is_exclusive(x_198);
if (x_214 == 0)
{
return x_198;
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_215 = lean_ctor_get(x_198, 0);
x_216 = lean_ctor_get(x_198, 1);
lean_inc(x_216);
lean_inc(x_215);
lean_dec(x_198);
x_217 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_217, 0, x_215);
lean_ctor_set(x_217, 1, x_216);
return x_217;
}
}
}
}
}
}
}
else
{
uint8_t x_248; 
lean_dec(x_18);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_248 = !lean_is_exclusive(x_19);
if (x_248 == 0)
{
return x_19;
}
else
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; 
x_249 = lean_ctor_get(x_19, 0);
x_250 = lean_ctor_get(x_19, 1);
lean_inc(x_250);
lean_inc(x_249);
lean_dec(x_19);
x_251 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_251, 0, x_249);
lean_ctor_set(x_251, 1, x_250);
return x_251;
}
}
}
}
else
{
uint8_t x_252; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_252 = !lean_is_exclusive(x_9);
if (x_252 == 0)
{
return x_9;
}
else
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; 
x_253 = lean_ctor_get(x_9, 0);
x_254 = lean_ctor_get(x_9, 1);
lean_inc(x_254);
lean_inc(x_253);
lean_dec(x_9);
x_255 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_255, 0, x_253);
lean_ctor_set(x_255, 1, x_254);
return x_255;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceNatEqExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Nat_reduceNatEqExpr___redArg(x_1, x_2, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceNatEqExpr___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Nat_reduceNatEqExpr___redArg___lam__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceNatEqExpr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Nat_reduceNatEqExpr(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceEqDiff___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_6);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = l_Lean_Expr_appFn_x21(x_1);
x_15 = l_Lean_Expr_appArg_x21(x_14);
lean_dec(x_14);
x_16 = l_Lean_Expr_appArg_x21(x_1);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_17 = l_Nat_reduceNatEqExpr___redArg(x_15, x_16, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_17, 0);
lean_dec(x_20);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_17, 0, x_22);
return x_17;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_dec(x_17);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_23);
return x_26;
}
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_18);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_18, 0);
switch (lean_obj_tag(x_28)) {
case 0:
{
uint8_t x_29; 
x_29 = lean_ctor_get_uint8(x_28, 0);
lean_dec(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_17, 1);
lean_inc(x_30);
lean_dec(x_17);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_31 = l_Lean_Meta_mkDecide(x_1, x_2, x_3, x_4, x_5, x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_mk_string_unchecked("Bool", 4, 4);
x_35 = lean_mk_string_unchecked("false", 5, 5);
x_36 = l_Lean_Name_mkStr2(x_34, x_35);
x_37 = lean_box(0);
x_38 = l_Lean_Expr_const___override(x_36, x_37);
x_39 = l_Lean_Meta_mkEqRefl(x_38, x_2, x_3, x_4, x_5, x_33);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_41 = lean_ctor_get(x_39, 0);
x_42 = lean_mk_string_unchecked("eq_false_of_decide", 18, 18);
x_43 = l_Lean_Name_mkStr1(x_42);
x_44 = l_Lean_Expr_const___override(x_43, x_37);
x_45 = l_Lean_Expr_appArg_x21(x_32);
lean_dec(x_32);
x_46 = lean_mk_empty_array_with_capacity(x_9);
x_47 = lean_array_push(x_46, x_1);
x_48 = lean_array_push(x_47, x_45);
x_49 = lean_array_push(x_48, x_41);
x_50 = l_Lean_mkAppN(x_44, x_49);
lean_dec(x_49);
x_51 = lean_mk_string_unchecked("False", 5, 5);
x_52 = l_Lean_Name_mkStr1(x_51);
x_53 = l_Lean_Expr_const___override(x_52, x_37);
lean_ctor_set(x_18, 0, x_50);
x_54 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_18);
lean_ctor_set_uint8(x_54, sizeof(void*)*2, x_10);
x_55 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_39, 0, x_55);
return x_39;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_56 = lean_ctor_get(x_39, 0);
x_57 = lean_ctor_get(x_39, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_39);
x_58 = lean_mk_string_unchecked("eq_false_of_decide", 18, 18);
x_59 = l_Lean_Name_mkStr1(x_58);
x_60 = l_Lean_Expr_const___override(x_59, x_37);
x_61 = l_Lean_Expr_appArg_x21(x_32);
lean_dec(x_32);
x_62 = lean_mk_empty_array_with_capacity(x_9);
x_63 = lean_array_push(x_62, x_1);
x_64 = lean_array_push(x_63, x_61);
x_65 = lean_array_push(x_64, x_56);
x_66 = l_Lean_mkAppN(x_60, x_65);
lean_dec(x_65);
x_67 = lean_mk_string_unchecked("False", 5, 5);
x_68 = l_Lean_Name_mkStr1(x_67);
x_69 = l_Lean_Expr_const___override(x_68, x_37);
lean_ctor_set(x_18, 0, x_66);
x_70 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_18);
lean_ctor_set_uint8(x_70, sizeof(void*)*2, x_10);
x_71 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_71, 0, x_70);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_57);
return x_72;
}
}
else
{
uint8_t x_73; 
lean_dec(x_32);
lean_free_object(x_18);
lean_dec(x_1);
x_73 = !lean_is_exclusive(x_39);
if (x_73 == 0)
{
return x_39;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_39, 0);
x_75 = lean_ctor_get(x_39, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_39);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
else
{
uint8_t x_77; 
lean_free_object(x_18);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_77 = !lean_is_exclusive(x_31);
if (x_77 == 0)
{
return x_31;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_31, 0);
x_79 = lean_ctor_get(x_31, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_31);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
else
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_17, 1);
lean_inc(x_81);
lean_dec(x_17);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_82 = l_Lean_Meta_mkDecide(x_1, x_2, x_3, x_4, x_5, x_81);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_85 = lean_mk_string_unchecked("Bool", 4, 4);
x_86 = lean_mk_string_unchecked("true", 4, 4);
x_87 = l_Lean_Name_mkStr2(x_85, x_86);
x_88 = lean_box(0);
x_89 = l_Lean_Expr_const___override(x_87, x_88);
x_90 = l_Lean_Meta_mkEqRefl(x_89, x_2, x_3, x_4, x_5, x_84);
if (lean_obj_tag(x_90) == 0)
{
uint8_t x_91; 
x_91 = !lean_is_exclusive(x_90);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_92 = lean_ctor_get(x_90, 0);
x_93 = lean_mk_string_unchecked("eq_true_of_decide", 17, 17);
x_94 = l_Lean_Name_mkStr1(x_93);
x_95 = l_Lean_Expr_const___override(x_94, x_88);
x_96 = l_Lean_Expr_appArg_x21(x_83);
lean_dec(x_83);
x_97 = lean_mk_empty_array_with_capacity(x_9);
x_98 = lean_array_push(x_97, x_1);
x_99 = lean_array_push(x_98, x_96);
x_100 = lean_array_push(x_99, x_92);
x_101 = l_Lean_mkAppN(x_95, x_100);
lean_dec(x_100);
x_102 = lean_mk_string_unchecked("True", 4, 4);
x_103 = l_Lean_Name_mkStr1(x_102);
x_104 = l_Lean_Expr_const___override(x_103, x_88);
lean_ctor_set(x_18, 0, x_101);
x_105 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_18);
lean_ctor_set_uint8(x_105, sizeof(void*)*2, x_29);
x_106 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_90, 0, x_106);
return x_90;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_107 = lean_ctor_get(x_90, 0);
x_108 = lean_ctor_get(x_90, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_90);
x_109 = lean_mk_string_unchecked("eq_true_of_decide", 17, 17);
x_110 = l_Lean_Name_mkStr1(x_109);
x_111 = l_Lean_Expr_const___override(x_110, x_88);
x_112 = l_Lean_Expr_appArg_x21(x_83);
lean_dec(x_83);
x_113 = lean_mk_empty_array_with_capacity(x_9);
x_114 = lean_array_push(x_113, x_1);
x_115 = lean_array_push(x_114, x_112);
x_116 = lean_array_push(x_115, x_107);
x_117 = l_Lean_mkAppN(x_111, x_116);
lean_dec(x_116);
x_118 = lean_mk_string_unchecked("True", 4, 4);
x_119 = l_Lean_Name_mkStr1(x_118);
x_120 = l_Lean_Expr_const___override(x_119, x_88);
lean_ctor_set(x_18, 0, x_117);
x_121 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_18);
lean_ctor_set_uint8(x_121, sizeof(void*)*2, x_29);
x_122 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_122, 0, x_121);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_108);
return x_123;
}
}
else
{
uint8_t x_124; 
lean_dec(x_83);
lean_free_object(x_18);
lean_dec(x_1);
x_124 = !lean_is_exclusive(x_90);
if (x_124 == 0)
{
return x_90;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_90, 0);
x_126 = lean_ctor_get(x_90, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_90);
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
lean_free_object(x_18);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_128 = !lean_is_exclusive(x_82);
if (x_128 == 0)
{
return x_82;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_82, 0);
x_130 = lean_ctor_get(x_82, 1);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_82);
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
return x_131;
}
}
}
}
case 1:
{
uint8_t x_132; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_132 = !lean_is_exclusive(x_17);
if (x_132 == 0)
{
lean_object* x_133; uint8_t x_134; 
x_133 = lean_ctor_get(x_17, 0);
lean_dec(x_133);
x_134 = !lean_is_exclusive(x_28);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_135 = lean_ctor_get(x_28, 0);
x_136 = lean_mk_string_unchecked("False", 5, 5);
x_137 = l_Lean_Name_mkStr1(x_136);
x_138 = lean_box(0);
x_139 = l_Lean_Expr_const___override(x_137, x_138);
lean_ctor_set(x_18, 0, x_135);
x_140 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_18);
lean_ctor_set_uint8(x_140, sizeof(void*)*2, x_10);
lean_ctor_set_tag(x_28, 0);
lean_ctor_set(x_28, 0, x_140);
lean_ctor_set(x_17, 0, x_28);
return x_17;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_141 = lean_ctor_get(x_28, 0);
lean_inc(x_141);
lean_dec(x_28);
x_142 = lean_mk_string_unchecked("False", 5, 5);
x_143 = l_Lean_Name_mkStr1(x_142);
x_144 = lean_box(0);
x_145 = l_Lean_Expr_const___override(x_143, x_144);
lean_ctor_set(x_18, 0, x_141);
x_146 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_18);
lean_ctor_set_uint8(x_146, sizeof(void*)*2, x_10);
x_147 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_17, 0, x_147);
return x_17;
}
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_148 = lean_ctor_get(x_17, 1);
lean_inc(x_148);
lean_dec(x_17);
x_149 = lean_ctor_get(x_28, 0);
lean_inc(x_149);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 x_150 = x_28;
} else {
 lean_dec_ref(x_28);
 x_150 = lean_box(0);
}
x_151 = lean_mk_string_unchecked("False", 5, 5);
x_152 = l_Lean_Name_mkStr1(x_151);
x_153 = lean_box(0);
x_154 = l_Lean_Expr_const___override(x_152, x_153);
lean_ctor_set(x_18, 0, x_149);
x_155 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_155, 1, x_18);
lean_ctor_set_uint8(x_155, sizeof(void*)*2, x_10);
if (lean_is_scalar(x_150)) {
 x_156 = lean_alloc_ctor(0, 1, 0);
} else {
 x_156 = x_150;
 lean_ctor_set_tag(x_156, 0);
}
lean_ctor_set(x_156, 0, x_155);
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_148);
return x_157;
}
}
default: 
{
uint8_t x_158; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_158 = !lean_is_exclusive(x_17);
if (x_158 == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_159 = lean_ctor_get(x_17, 0);
lean_dec(x_159);
x_160 = lean_ctor_get(x_28, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_28, 1);
lean_inc(x_161);
x_162 = lean_ctor_get(x_28, 2);
lean_inc(x_162);
lean_dec(x_28);
x_163 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat(x_160, x_161);
lean_ctor_set(x_18, 0, x_162);
x_164 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_164, 1, x_18);
lean_ctor_set_uint8(x_164, sizeof(void*)*2, x_10);
x_165 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_165, 0, x_164);
lean_ctor_set(x_17, 0, x_165);
return x_17;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_166 = lean_ctor_get(x_17, 1);
lean_inc(x_166);
lean_dec(x_17);
x_167 = lean_ctor_get(x_28, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_28, 1);
lean_inc(x_168);
x_169 = lean_ctor_get(x_28, 2);
lean_inc(x_169);
lean_dec(x_28);
x_170 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat(x_167, x_168);
lean_ctor_set(x_18, 0, x_169);
x_171 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_18);
lean_ctor_set_uint8(x_171, sizeof(void*)*2, x_10);
x_172 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_172, 0, x_171);
x_173 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_173, 0, x_172);
lean_ctor_set(x_173, 1, x_166);
return x_173;
}
}
}
}
else
{
lean_object* x_174; 
x_174 = lean_ctor_get(x_18, 0);
lean_inc(x_174);
lean_dec(x_18);
switch (lean_obj_tag(x_174)) {
case 0:
{
uint8_t x_175; 
x_175 = lean_ctor_get_uint8(x_174, 0);
lean_dec(x_174);
if (x_175 == 0)
{
lean_object* x_176; lean_object* x_177; 
x_176 = lean_ctor_get(x_17, 1);
lean_inc(x_176);
lean_dec(x_17);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_177 = l_Lean_Meta_mkDecide(x_1, x_2, x_3, x_4, x_5, x_176);
if (lean_obj_tag(x_177) == 0)
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_177, 1);
lean_inc(x_179);
lean_dec(x_177);
x_180 = lean_mk_string_unchecked("Bool", 4, 4);
x_181 = lean_mk_string_unchecked("false", 5, 5);
x_182 = l_Lean_Name_mkStr2(x_180, x_181);
x_183 = lean_box(0);
x_184 = l_Lean_Expr_const___override(x_182, x_183);
x_185 = l_Lean_Meta_mkEqRefl(x_184, x_2, x_3, x_4, x_5, x_179);
if (lean_obj_tag(x_185) == 0)
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_185, 1);
lean_inc(x_187);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 lean_ctor_release(x_185, 1);
 x_188 = x_185;
} else {
 lean_dec_ref(x_185);
 x_188 = lean_box(0);
}
x_189 = lean_mk_string_unchecked("eq_false_of_decide", 18, 18);
x_190 = l_Lean_Name_mkStr1(x_189);
x_191 = l_Lean_Expr_const___override(x_190, x_183);
x_192 = l_Lean_Expr_appArg_x21(x_178);
lean_dec(x_178);
x_193 = lean_mk_empty_array_with_capacity(x_9);
x_194 = lean_array_push(x_193, x_1);
x_195 = lean_array_push(x_194, x_192);
x_196 = lean_array_push(x_195, x_186);
x_197 = l_Lean_mkAppN(x_191, x_196);
lean_dec(x_196);
x_198 = lean_mk_string_unchecked("False", 5, 5);
x_199 = l_Lean_Name_mkStr1(x_198);
x_200 = l_Lean_Expr_const___override(x_199, x_183);
x_201 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_201, 0, x_197);
x_202 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_202, 0, x_200);
lean_ctor_set(x_202, 1, x_201);
lean_ctor_set_uint8(x_202, sizeof(void*)*2, x_10);
x_203 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_203, 0, x_202);
if (lean_is_scalar(x_188)) {
 x_204 = lean_alloc_ctor(0, 2, 0);
} else {
 x_204 = x_188;
}
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set(x_204, 1, x_187);
return x_204;
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
lean_dec(x_178);
lean_dec(x_1);
x_205 = lean_ctor_get(x_185, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_185, 1);
lean_inc(x_206);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 lean_ctor_release(x_185, 1);
 x_207 = x_185;
} else {
 lean_dec_ref(x_185);
 x_207 = lean_box(0);
}
if (lean_is_scalar(x_207)) {
 x_208 = lean_alloc_ctor(1, 2, 0);
} else {
 x_208 = x_207;
}
lean_ctor_set(x_208, 0, x_205);
lean_ctor_set(x_208, 1, x_206);
return x_208;
}
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_209 = lean_ctor_get(x_177, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_177, 1);
lean_inc(x_210);
if (lean_is_exclusive(x_177)) {
 lean_ctor_release(x_177, 0);
 lean_ctor_release(x_177, 1);
 x_211 = x_177;
} else {
 lean_dec_ref(x_177);
 x_211 = lean_box(0);
}
if (lean_is_scalar(x_211)) {
 x_212 = lean_alloc_ctor(1, 2, 0);
} else {
 x_212 = x_211;
}
lean_ctor_set(x_212, 0, x_209);
lean_ctor_set(x_212, 1, x_210);
return x_212;
}
}
else
{
lean_object* x_213; lean_object* x_214; 
x_213 = lean_ctor_get(x_17, 1);
lean_inc(x_213);
lean_dec(x_17);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_214 = l_Lean_Meta_mkDecide(x_1, x_2, x_3, x_4, x_5, x_213);
if (lean_obj_tag(x_214) == 0)
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_215 = lean_ctor_get(x_214, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_214, 1);
lean_inc(x_216);
lean_dec(x_214);
x_217 = lean_mk_string_unchecked("Bool", 4, 4);
x_218 = lean_mk_string_unchecked("true", 4, 4);
x_219 = l_Lean_Name_mkStr2(x_217, x_218);
x_220 = lean_box(0);
x_221 = l_Lean_Expr_const___override(x_219, x_220);
x_222 = l_Lean_Meta_mkEqRefl(x_221, x_2, x_3, x_4, x_5, x_216);
if (lean_obj_tag(x_222) == 0)
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_223 = lean_ctor_get(x_222, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_222, 1);
lean_inc(x_224);
if (lean_is_exclusive(x_222)) {
 lean_ctor_release(x_222, 0);
 lean_ctor_release(x_222, 1);
 x_225 = x_222;
} else {
 lean_dec_ref(x_222);
 x_225 = lean_box(0);
}
x_226 = lean_mk_string_unchecked("eq_true_of_decide", 17, 17);
x_227 = l_Lean_Name_mkStr1(x_226);
x_228 = l_Lean_Expr_const___override(x_227, x_220);
x_229 = l_Lean_Expr_appArg_x21(x_215);
lean_dec(x_215);
x_230 = lean_mk_empty_array_with_capacity(x_9);
x_231 = lean_array_push(x_230, x_1);
x_232 = lean_array_push(x_231, x_229);
x_233 = lean_array_push(x_232, x_223);
x_234 = l_Lean_mkAppN(x_228, x_233);
lean_dec(x_233);
x_235 = lean_mk_string_unchecked("True", 4, 4);
x_236 = l_Lean_Name_mkStr1(x_235);
x_237 = l_Lean_Expr_const___override(x_236, x_220);
x_238 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_238, 0, x_234);
x_239 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_239, 0, x_237);
lean_ctor_set(x_239, 1, x_238);
lean_ctor_set_uint8(x_239, sizeof(void*)*2, x_175);
x_240 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_240, 0, x_239);
if (lean_is_scalar(x_225)) {
 x_241 = lean_alloc_ctor(0, 2, 0);
} else {
 x_241 = x_225;
}
lean_ctor_set(x_241, 0, x_240);
lean_ctor_set(x_241, 1, x_224);
return x_241;
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
lean_dec(x_215);
lean_dec(x_1);
x_242 = lean_ctor_get(x_222, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_222, 1);
lean_inc(x_243);
if (lean_is_exclusive(x_222)) {
 lean_ctor_release(x_222, 0);
 lean_ctor_release(x_222, 1);
 x_244 = x_222;
} else {
 lean_dec_ref(x_222);
 x_244 = lean_box(0);
}
if (lean_is_scalar(x_244)) {
 x_245 = lean_alloc_ctor(1, 2, 0);
} else {
 x_245 = x_244;
}
lean_ctor_set(x_245, 0, x_242);
lean_ctor_set(x_245, 1, x_243);
return x_245;
}
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_246 = lean_ctor_get(x_214, 0);
lean_inc(x_246);
x_247 = lean_ctor_get(x_214, 1);
lean_inc(x_247);
if (lean_is_exclusive(x_214)) {
 lean_ctor_release(x_214, 0);
 lean_ctor_release(x_214, 1);
 x_248 = x_214;
} else {
 lean_dec_ref(x_214);
 x_248 = lean_box(0);
}
if (lean_is_scalar(x_248)) {
 x_249 = lean_alloc_ctor(1, 2, 0);
} else {
 x_249 = x_248;
}
lean_ctor_set(x_249, 0, x_246);
lean_ctor_set(x_249, 1, x_247);
return x_249;
}
}
}
case 1:
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_250 = lean_ctor_get(x_17, 1);
lean_inc(x_250);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 x_251 = x_17;
} else {
 lean_dec_ref(x_17);
 x_251 = lean_box(0);
}
x_252 = lean_ctor_get(x_174, 0);
lean_inc(x_252);
if (lean_is_exclusive(x_174)) {
 lean_ctor_release(x_174, 0);
 x_253 = x_174;
} else {
 lean_dec_ref(x_174);
 x_253 = lean_box(0);
}
x_254 = lean_mk_string_unchecked("False", 5, 5);
x_255 = l_Lean_Name_mkStr1(x_254);
x_256 = lean_box(0);
x_257 = l_Lean_Expr_const___override(x_255, x_256);
x_258 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_258, 0, x_252);
x_259 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_259, 0, x_257);
lean_ctor_set(x_259, 1, x_258);
lean_ctor_set_uint8(x_259, sizeof(void*)*2, x_10);
if (lean_is_scalar(x_253)) {
 x_260 = lean_alloc_ctor(0, 1, 0);
} else {
 x_260 = x_253;
 lean_ctor_set_tag(x_260, 0);
}
lean_ctor_set(x_260, 0, x_259);
if (lean_is_scalar(x_251)) {
 x_261 = lean_alloc_ctor(0, 2, 0);
} else {
 x_261 = x_251;
}
lean_ctor_set(x_261, 0, x_260);
lean_ctor_set(x_261, 1, x_250);
return x_261;
}
default: 
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_262 = lean_ctor_get(x_17, 1);
lean_inc(x_262);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 x_263 = x_17;
} else {
 lean_dec_ref(x_17);
 x_263 = lean_box(0);
}
x_264 = lean_ctor_get(x_174, 0);
lean_inc(x_264);
x_265 = lean_ctor_get(x_174, 1);
lean_inc(x_265);
x_266 = lean_ctor_get(x_174, 2);
lean_inc(x_266);
lean_dec(x_174);
x_267 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat(x_264, x_265);
x_268 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_268, 0, x_266);
x_269 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_269, 0, x_267);
lean_ctor_set(x_269, 1, x_268);
lean_ctor_set_uint8(x_269, sizeof(void*)*2, x_10);
x_270 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_270, 0, x_269);
if (lean_is_scalar(x_263)) {
 x_271 = lean_alloc_ctor(0, 2, 0);
} else {
 x_271 = x_263;
}
lean_ctor_set(x_271, 0, x_270);
lean_ctor_set(x_271, 1, x_262);
return x_271;
}
}
}
}
}
else
{
uint8_t x_272; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_272 = !lean_is_exclusive(x_17);
if (x_272 == 0)
{
return x_17;
}
else
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; 
x_273 = lean_ctor_get(x_17, 0);
x_274 = lean_ctor_get(x_17, 1);
lean_inc(x_274);
lean_inc(x_273);
lean_dec(x_17);
x_275 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_275, 0, x_273);
lean_ctor_set(x_275, 1, x_274);
return x_275;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceEqDiff(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Nat_reduceEqDiff___redArg(x_1, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceEqDiff___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Nat_reduceEqDiff(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceEqDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_3864_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("Nat", 3, 3);
x_3 = lean_mk_string_unchecked("reduceEqDiff", 12, 12);
lean_inc(x_2);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_mk_string_unchecked("Eq", 2, 2);
x_6 = l_Lean_Name_mkStr1(x_5);
x_7 = lean_unsigned_to_nat(3u);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
x_9 = l_Lean_Name_mkStr1(x_2);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_box(3);
x_13 = lean_unsigned_to_nat(4u);
x_14 = lean_mk_empty_array_with_capacity(x_13);
x_15 = lean_array_push(x_14, x_8);
x_16 = lean_array_push(x_15, x_11);
x_17 = lean_array_push(x_16, x_12);
x_18 = lean_array_push(x_17, x_12);
x_19 = lean_alloc_closure((void*)(l_Nat_reduceEqDiff___boxed), 9, 0);
x_20 = l_Lean_Meta_Simp_registerBuiltinSimproc(x_4, x_18, x_19, x_1);
return x_20;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceEqDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_3866_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Nat", 3, 3);
x_3 = lean_mk_string_unchecked("reduceEqDiff", 12, 12);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Nat_reduceEqDiff___boxed), 9, 0);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceEqDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_3868_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Nat", 3, 3);
x_3 = lean_mk_string_unchecked("reduceEqDiff", 12, 12);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Nat_reduceEqDiff___boxed), 9, 0);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBeqDiff___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_mk_string_unchecked("BEq", 3, 3);
x_8 = lean_mk_string_unchecked("beq", 3, 3);
x_9 = l_Lean_Name_mkStr2(x_7, x_8);
x_10 = lean_unsigned_to_nat(4u);
x_11 = l_Lean_Expr_isAppOfArity(x_1, x_9, x_10);
lean_dec(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_6);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = l_Lean_Expr_appFn_x21(x_1);
x_16 = l_Lean_Expr_appArg_x21(x_15);
lean_dec(x_15);
x_17 = l_Lean_Expr_appArg_x21(x_1);
lean_inc(x_17);
lean_inc(x_16);
x_18 = l_Nat_reduceNatEqExpr___redArg(x_16, x_17, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_21 = x_18;
} else {
 lean_dec_ref(x_18);
 x_21 = lean_box(0);
}
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_21);
lean_dec(x_17);
lean_dec(x_16);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_20);
return x_30;
}
else
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_19);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_19, 0);
switch (lean_obj_tag(x_32)) {
case 0:
{
uint8_t x_33; 
lean_free_object(x_19);
lean_dec(x_17);
lean_dec(x_16);
x_33 = lean_ctor_get_uint8(x_32, 0);
lean_dec(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_34 = lean_mk_string_unchecked("Bool", 4, 4);
x_35 = lean_mk_string_unchecked("false", 5, 5);
x_36 = l_Lean_Name_mkStr2(x_34, x_35);
x_37 = lean_box(0);
x_38 = l_Lean_Expr_const___override(x_36, x_37);
x_22 = x_38;
goto block_27;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_mk_string_unchecked("Bool", 4, 4);
x_40 = lean_mk_string_unchecked("true", 4, 4);
x_41 = l_Lean_Name_mkStr2(x_39, x_40);
x_42 = lean_box(0);
x_43 = l_Lean_Expr_const___override(x_41, x_42);
x_22 = x_43;
goto block_27;
}
}
case 1:
{
uint8_t x_44; 
lean_dec(x_21);
x_44 = !lean_is_exclusive(x_32);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_45 = lean_ctor_get(x_32, 0);
x_46 = lean_mk_string_unchecked("Nat", 3, 3);
x_47 = lean_mk_string_unchecked("Simproc", 7, 7);
x_48 = lean_mk_string_unchecked("beqFalseOfEqFalse", 17, 17);
x_49 = l_Lean_Name_mkStr3(x_46, x_47, x_48);
x_50 = lean_box(0);
x_51 = l_Lean_Expr_const___override(x_49, x_50);
x_52 = lean_unsigned_to_nat(3u);
x_53 = lean_mk_empty_array_with_capacity(x_52);
x_54 = lean_array_push(x_53, x_16);
x_55 = lean_array_push(x_54, x_17);
x_56 = lean_array_push(x_55, x_45);
x_57 = l_Lean_mkAppN(x_51, x_56);
lean_dec(x_56);
x_58 = lean_mk_string_unchecked("Bool", 4, 4);
x_59 = lean_mk_string_unchecked("false", 5, 5);
x_60 = l_Lean_Name_mkStr2(x_58, x_59);
x_61 = l_Lean_Expr_const___override(x_60, x_50);
lean_ctor_set(x_19, 0, x_57);
x_62 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_19);
lean_ctor_set_uint8(x_62, sizeof(void*)*2, x_11);
lean_ctor_set_tag(x_32, 0);
lean_ctor_set(x_32, 0, x_62);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_32);
lean_ctor_set(x_63, 1, x_20);
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_64 = lean_ctor_get(x_32, 0);
lean_inc(x_64);
lean_dec(x_32);
x_65 = lean_mk_string_unchecked("Nat", 3, 3);
x_66 = lean_mk_string_unchecked("Simproc", 7, 7);
x_67 = lean_mk_string_unchecked("beqFalseOfEqFalse", 17, 17);
x_68 = l_Lean_Name_mkStr3(x_65, x_66, x_67);
x_69 = lean_box(0);
x_70 = l_Lean_Expr_const___override(x_68, x_69);
x_71 = lean_unsigned_to_nat(3u);
x_72 = lean_mk_empty_array_with_capacity(x_71);
x_73 = lean_array_push(x_72, x_16);
x_74 = lean_array_push(x_73, x_17);
x_75 = lean_array_push(x_74, x_64);
x_76 = l_Lean_mkAppN(x_70, x_75);
lean_dec(x_75);
x_77 = lean_mk_string_unchecked("Bool", 4, 4);
x_78 = lean_mk_string_unchecked("false", 5, 5);
x_79 = l_Lean_Name_mkStr2(x_77, x_78);
x_80 = l_Lean_Expr_const___override(x_79, x_69);
lean_ctor_set(x_19, 0, x_76);
x_81 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_19);
lean_ctor_set_uint8(x_81, sizeof(void*)*2, x_11);
x_82 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_82, 0, x_81);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_20);
return x_83;
}
}
default: 
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_dec(x_21);
x_84 = lean_ctor_get(x_32, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_32, 1);
lean_inc(x_85);
x_86 = lean_ctor_get(x_32, 2);
lean_inc(x_86);
lean_dec(x_32);
x_87 = lean_mk_string_unchecked("Nat", 3, 3);
x_88 = lean_mk_string_unchecked("Simproc", 7, 7);
x_89 = lean_mk_string_unchecked("beqEqOfEqEq", 11, 11);
x_90 = l_Lean_Name_mkStr3(x_87, x_88, x_89);
x_91 = lean_box(0);
x_92 = l_Lean_Expr_const___override(x_90, x_91);
x_93 = lean_unsigned_to_nat(5u);
x_94 = lean_mk_empty_array_with_capacity(x_93);
x_95 = lean_array_push(x_94, x_16);
x_96 = lean_array_push(x_95, x_17);
lean_inc(x_84);
x_97 = lean_array_push(x_96, x_84);
lean_inc(x_85);
x_98 = lean_array_push(x_97, x_85);
x_99 = lean_array_push(x_98, x_86);
x_100 = l_Lean_mkAppN(x_92, x_99);
lean_dec(x_99);
x_101 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNat(x_84, x_85);
lean_ctor_set(x_19, 0, x_100);
x_102 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_19);
lean_ctor_set_uint8(x_102, sizeof(void*)*2, x_11);
x_103 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_103, 0, x_102);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_20);
return x_104;
}
}
}
else
{
lean_object* x_105; 
x_105 = lean_ctor_get(x_19, 0);
lean_inc(x_105);
lean_dec(x_19);
switch (lean_obj_tag(x_105)) {
case 0:
{
uint8_t x_106; 
lean_dec(x_17);
lean_dec(x_16);
x_106 = lean_ctor_get_uint8(x_105, 0);
lean_dec(x_105);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_107 = lean_mk_string_unchecked("Bool", 4, 4);
x_108 = lean_mk_string_unchecked("false", 5, 5);
x_109 = l_Lean_Name_mkStr2(x_107, x_108);
x_110 = lean_box(0);
x_111 = l_Lean_Expr_const___override(x_109, x_110);
x_22 = x_111;
goto block_27;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_112 = lean_mk_string_unchecked("Bool", 4, 4);
x_113 = lean_mk_string_unchecked("true", 4, 4);
x_114 = l_Lean_Name_mkStr2(x_112, x_113);
x_115 = lean_box(0);
x_116 = l_Lean_Expr_const___override(x_114, x_115);
x_22 = x_116;
goto block_27;
}
}
case 1:
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
lean_dec(x_21);
x_117 = lean_ctor_get(x_105, 0);
lean_inc(x_117);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 x_118 = x_105;
} else {
 lean_dec_ref(x_105);
 x_118 = lean_box(0);
}
x_119 = lean_mk_string_unchecked("Nat", 3, 3);
x_120 = lean_mk_string_unchecked("Simproc", 7, 7);
x_121 = lean_mk_string_unchecked("beqFalseOfEqFalse", 17, 17);
x_122 = l_Lean_Name_mkStr3(x_119, x_120, x_121);
x_123 = lean_box(0);
x_124 = l_Lean_Expr_const___override(x_122, x_123);
x_125 = lean_unsigned_to_nat(3u);
x_126 = lean_mk_empty_array_with_capacity(x_125);
x_127 = lean_array_push(x_126, x_16);
x_128 = lean_array_push(x_127, x_17);
x_129 = lean_array_push(x_128, x_117);
x_130 = l_Lean_mkAppN(x_124, x_129);
lean_dec(x_129);
x_131 = lean_mk_string_unchecked("Bool", 4, 4);
x_132 = lean_mk_string_unchecked("false", 5, 5);
x_133 = l_Lean_Name_mkStr2(x_131, x_132);
x_134 = l_Lean_Expr_const___override(x_133, x_123);
x_135 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_135, 0, x_130);
x_136 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_135);
lean_ctor_set_uint8(x_136, sizeof(void*)*2, x_11);
if (lean_is_scalar(x_118)) {
 x_137 = lean_alloc_ctor(0, 1, 0);
} else {
 x_137 = x_118;
 lean_ctor_set_tag(x_137, 0);
}
lean_ctor_set(x_137, 0, x_136);
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_20);
return x_138;
}
default: 
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_21);
x_139 = lean_ctor_get(x_105, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_105, 1);
lean_inc(x_140);
x_141 = lean_ctor_get(x_105, 2);
lean_inc(x_141);
lean_dec(x_105);
x_142 = lean_mk_string_unchecked("Nat", 3, 3);
x_143 = lean_mk_string_unchecked("Simproc", 7, 7);
x_144 = lean_mk_string_unchecked("beqEqOfEqEq", 11, 11);
x_145 = l_Lean_Name_mkStr3(x_142, x_143, x_144);
x_146 = lean_box(0);
x_147 = l_Lean_Expr_const___override(x_145, x_146);
x_148 = lean_unsigned_to_nat(5u);
x_149 = lean_mk_empty_array_with_capacity(x_148);
x_150 = lean_array_push(x_149, x_16);
x_151 = lean_array_push(x_150, x_17);
lean_inc(x_139);
x_152 = lean_array_push(x_151, x_139);
lean_inc(x_140);
x_153 = lean_array_push(x_152, x_140);
x_154 = lean_array_push(x_153, x_141);
x_155 = l_Lean_mkAppN(x_147, x_154);
lean_dec(x_154);
x_156 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNat(x_139, x_140);
x_157 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_157, 0, x_155);
x_158 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_158, 0, x_156);
lean_ctor_set(x_158, 1, x_157);
lean_ctor_set_uint8(x_158, sizeof(void*)*2, x_11);
x_159 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_159, 0, x_158);
x_160 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_20);
return x_160;
}
}
}
}
block_27:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set_uint8(x_24, sizeof(void*)*2, x_11);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
if (lean_is_scalar(x_21)) {
 x_26 = lean_alloc_ctor(0, 2, 0);
} else {
 x_26 = x_21;
}
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_20);
return x_26;
}
}
else
{
uint8_t x_161; 
lean_dec(x_17);
lean_dec(x_16);
x_161 = !lean_is_exclusive(x_18);
if (x_161 == 0)
{
return x_18;
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_162 = lean_ctor_get(x_18, 0);
x_163 = lean_ctor_get(x_18, 1);
lean_inc(x_163);
lean_inc(x_162);
lean_dec(x_18);
x_164 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_164, 0, x_162);
lean_ctor_set(x_164, 1, x_163);
return x_164;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBeqDiff(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Nat_reduceBeqDiff___redArg(x_1, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBeqDiff___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Nat_reduceBeqDiff___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBeqDiff___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Nat_reduceBeqDiff(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceBeqDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4101_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_2 = lean_mk_string_unchecked("Nat", 3, 3);
x_3 = lean_mk_string_unchecked("reduceBeqDiff", 13, 13);
lean_inc(x_2);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_mk_string_unchecked("BEq", 3, 3);
x_6 = lean_mk_string_unchecked("beq", 3, 3);
x_7 = l_Lean_Name_mkStr2(x_5, x_6);
x_8 = lean_unsigned_to_nat(4u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Lean_Name_mkStr1(x_2);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_box(3);
x_14 = lean_unsigned_to_nat(5u);
x_15 = lean_mk_empty_array_with_capacity(x_14);
x_16 = lean_array_push(x_15, x_9);
x_17 = lean_array_push(x_16, x_12);
x_18 = lean_array_push(x_17, x_13);
x_19 = lean_array_push(x_18, x_13);
x_20 = lean_array_push(x_19, x_13);
x_21 = lean_alloc_closure((void*)(l_Nat_reduceBeqDiff___boxed), 9, 0);
x_22 = l_Lean_Meta_Simp_registerBuiltinSimproc(x_4, x_20, x_21, x_1);
return x_22;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceBeqDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4103_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Nat", 3, 3);
x_3 = lean_mk_string_unchecked("reduceBeqDiff", 13, 13);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Nat_reduceBeqDiff___boxed), 9, 0);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceBeqDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4105_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Nat", 3, 3);
x_3 = lean_mk_string_unchecked("reduceBeqDiff", 13, 13);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Nat_reduceBeqDiff___boxed), 9, 0);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBneDiff___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_mk_string_unchecked("bne", 3, 3);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_unsigned_to_nat(4u);
x_10 = l_Lean_Expr_isAppOfArity(x_1, x_8, x_9);
lean_dec(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_6);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = l_Lean_Expr_appFn_x21(x_1);
x_15 = l_Lean_Expr_appArg_x21(x_14);
lean_dec(x_14);
x_16 = l_Lean_Expr_appArg_x21(x_1);
lean_inc(x_16);
lean_inc(x_15);
x_17 = l_Nat_reduceNatEqExpr___redArg(x_15, x_16, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 x_20 = x_17;
} else {
 lean_dec_ref(x_17);
 x_20 = lean_box(0);
}
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_20);
lean_dec(x_16);
lean_dec(x_15);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_19);
return x_35;
}
else
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_18);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_18, 0);
switch (lean_obj_tag(x_37)) {
case 0:
{
uint8_t x_38; 
lean_free_object(x_18);
lean_dec(x_16);
lean_dec(x_15);
x_38 = lean_ctor_get_uint8(x_37, 0);
lean_dec(x_37);
if (x_38 == 0)
{
if (x_10 == 0)
{
goto block_32;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_mk_string_unchecked("Bool", 4, 4);
x_40 = lean_mk_string_unchecked("true", 4, 4);
x_41 = l_Lean_Name_mkStr2(x_39, x_40);
x_42 = lean_box(0);
x_43 = l_Lean_Expr_const___override(x_41, x_42);
x_21 = x_43;
goto block_26;
}
}
else
{
goto block_32;
}
}
case 1:
{
uint8_t x_44; 
lean_dec(x_20);
x_44 = !lean_is_exclusive(x_37);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_45 = lean_ctor_get(x_37, 0);
x_46 = lean_mk_string_unchecked("Nat", 3, 3);
x_47 = lean_mk_string_unchecked("Simproc", 7, 7);
x_48 = lean_mk_string_unchecked("bneTrueOfEqFalse", 16, 16);
x_49 = l_Lean_Name_mkStr3(x_46, x_47, x_48);
x_50 = lean_box(0);
x_51 = l_Lean_Expr_const___override(x_49, x_50);
x_52 = lean_unsigned_to_nat(3u);
x_53 = lean_mk_empty_array_with_capacity(x_52);
x_54 = lean_array_push(x_53, x_15);
x_55 = lean_array_push(x_54, x_16);
x_56 = lean_array_push(x_55, x_45);
x_57 = l_Lean_mkAppN(x_51, x_56);
lean_dec(x_56);
x_58 = lean_mk_string_unchecked("Bool", 4, 4);
x_59 = lean_mk_string_unchecked("true", 4, 4);
x_60 = l_Lean_Name_mkStr2(x_58, x_59);
x_61 = l_Lean_Expr_const___override(x_60, x_50);
lean_ctor_set(x_18, 0, x_57);
x_62 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_18);
lean_ctor_set_uint8(x_62, sizeof(void*)*2, x_10);
lean_ctor_set_tag(x_37, 0);
lean_ctor_set(x_37, 0, x_62);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_37);
lean_ctor_set(x_63, 1, x_19);
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_64 = lean_ctor_get(x_37, 0);
lean_inc(x_64);
lean_dec(x_37);
x_65 = lean_mk_string_unchecked("Nat", 3, 3);
x_66 = lean_mk_string_unchecked("Simproc", 7, 7);
x_67 = lean_mk_string_unchecked("bneTrueOfEqFalse", 16, 16);
x_68 = l_Lean_Name_mkStr3(x_65, x_66, x_67);
x_69 = lean_box(0);
x_70 = l_Lean_Expr_const___override(x_68, x_69);
x_71 = lean_unsigned_to_nat(3u);
x_72 = lean_mk_empty_array_with_capacity(x_71);
x_73 = lean_array_push(x_72, x_15);
x_74 = lean_array_push(x_73, x_16);
x_75 = lean_array_push(x_74, x_64);
x_76 = l_Lean_mkAppN(x_70, x_75);
lean_dec(x_75);
x_77 = lean_mk_string_unchecked("Bool", 4, 4);
x_78 = lean_mk_string_unchecked("true", 4, 4);
x_79 = l_Lean_Name_mkStr2(x_77, x_78);
x_80 = l_Lean_Expr_const___override(x_79, x_69);
lean_ctor_set(x_18, 0, x_76);
x_81 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_18);
lean_ctor_set_uint8(x_81, sizeof(void*)*2, x_10);
x_82 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_82, 0, x_81);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_19);
return x_83;
}
}
default: 
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_dec(x_20);
x_84 = lean_ctor_get(x_37, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_37, 1);
lean_inc(x_85);
x_86 = lean_ctor_get(x_37, 2);
lean_inc(x_86);
lean_dec(x_37);
x_87 = lean_mk_string_unchecked("Nat", 3, 3);
x_88 = lean_mk_string_unchecked("Simproc", 7, 7);
x_89 = lean_mk_string_unchecked("bneEqOfEqEq", 11, 11);
x_90 = l_Lean_Name_mkStr3(x_87, x_88, x_89);
x_91 = lean_box(0);
x_92 = l_Lean_Expr_const___override(x_90, x_91);
x_93 = lean_unsigned_to_nat(5u);
x_94 = lean_mk_empty_array_with_capacity(x_93);
x_95 = lean_array_push(x_94, x_15);
x_96 = lean_array_push(x_95, x_16);
lean_inc(x_84);
x_97 = lean_array_push(x_96, x_84);
lean_inc(x_85);
x_98 = lean_array_push(x_97, x_85);
x_99 = lean_array_push(x_98, x_86);
x_100 = l_Lean_mkAppN(x_92, x_99);
lean_dec(x_99);
x_101 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBneNat(x_84, x_85);
lean_ctor_set(x_18, 0, x_100);
x_102 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_18);
lean_ctor_set_uint8(x_102, sizeof(void*)*2, x_10);
x_103 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_103, 0, x_102);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_19);
return x_104;
}
}
}
else
{
lean_object* x_105; 
x_105 = lean_ctor_get(x_18, 0);
lean_inc(x_105);
lean_dec(x_18);
switch (lean_obj_tag(x_105)) {
case 0:
{
uint8_t x_106; 
lean_dec(x_16);
lean_dec(x_15);
x_106 = lean_ctor_get_uint8(x_105, 0);
lean_dec(x_105);
if (x_106 == 0)
{
if (x_10 == 0)
{
goto block_32;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_107 = lean_mk_string_unchecked("Bool", 4, 4);
x_108 = lean_mk_string_unchecked("true", 4, 4);
x_109 = l_Lean_Name_mkStr2(x_107, x_108);
x_110 = lean_box(0);
x_111 = l_Lean_Expr_const___override(x_109, x_110);
x_21 = x_111;
goto block_26;
}
}
else
{
goto block_32;
}
}
case 1:
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
lean_dec(x_20);
x_112 = lean_ctor_get(x_105, 0);
lean_inc(x_112);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 x_113 = x_105;
} else {
 lean_dec_ref(x_105);
 x_113 = lean_box(0);
}
x_114 = lean_mk_string_unchecked("Nat", 3, 3);
x_115 = lean_mk_string_unchecked("Simproc", 7, 7);
x_116 = lean_mk_string_unchecked("bneTrueOfEqFalse", 16, 16);
x_117 = l_Lean_Name_mkStr3(x_114, x_115, x_116);
x_118 = lean_box(0);
x_119 = l_Lean_Expr_const___override(x_117, x_118);
x_120 = lean_unsigned_to_nat(3u);
x_121 = lean_mk_empty_array_with_capacity(x_120);
x_122 = lean_array_push(x_121, x_15);
x_123 = lean_array_push(x_122, x_16);
x_124 = lean_array_push(x_123, x_112);
x_125 = l_Lean_mkAppN(x_119, x_124);
lean_dec(x_124);
x_126 = lean_mk_string_unchecked("Bool", 4, 4);
x_127 = lean_mk_string_unchecked("true", 4, 4);
x_128 = l_Lean_Name_mkStr2(x_126, x_127);
x_129 = l_Lean_Expr_const___override(x_128, x_118);
x_130 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_130, 0, x_125);
x_131 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
lean_ctor_set_uint8(x_131, sizeof(void*)*2, x_10);
if (lean_is_scalar(x_113)) {
 x_132 = lean_alloc_ctor(0, 1, 0);
} else {
 x_132 = x_113;
 lean_ctor_set_tag(x_132, 0);
}
lean_ctor_set(x_132, 0, x_131);
x_133 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_19);
return x_133;
}
default: 
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
lean_dec(x_20);
x_134 = lean_ctor_get(x_105, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_105, 1);
lean_inc(x_135);
x_136 = lean_ctor_get(x_105, 2);
lean_inc(x_136);
lean_dec(x_105);
x_137 = lean_mk_string_unchecked("Nat", 3, 3);
x_138 = lean_mk_string_unchecked("Simproc", 7, 7);
x_139 = lean_mk_string_unchecked("bneEqOfEqEq", 11, 11);
x_140 = l_Lean_Name_mkStr3(x_137, x_138, x_139);
x_141 = lean_box(0);
x_142 = l_Lean_Expr_const___override(x_140, x_141);
x_143 = lean_unsigned_to_nat(5u);
x_144 = lean_mk_empty_array_with_capacity(x_143);
x_145 = lean_array_push(x_144, x_15);
x_146 = lean_array_push(x_145, x_16);
lean_inc(x_134);
x_147 = lean_array_push(x_146, x_134);
lean_inc(x_135);
x_148 = lean_array_push(x_147, x_135);
x_149 = lean_array_push(x_148, x_136);
x_150 = l_Lean_mkAppN(x_142, x_149);
lean_dec(x_149);
x_151 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBneNat(x_134, x_135);
x_152 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_152, 0, x_150);
x_153 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_153, 0, x_151);
lean_ctor_set(x_153, 1, x_152);
lean_ctor_set_uint8(x_153, sizeof(void*)*2, x_10);
x_154 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_154, 0, x_153);
x_155 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_155, 1, x_19);
return x_155;
}
}
}
}
block_26:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set_uint8(x_23, sizeof(void*)*2, x_10);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_23);
if (lean_is_scalar(x_20)) {
 x_25 = lean_alloc_ctor(0, 2, 0);
} else {
 x_25 = x_20;
}
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_19);
return x_25;
}
block_32:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_mk_string_unchecked("Bool", 4, 4);
x_28 = lean_mk_string_unchecked("false", 5, 5);
x_29 = l_Lean_Name_mkStr2(x_27, x_28);
x_30 = lean_box(0);
x_31 = l_Lean_Expr_const___override(x_29, x_30);
x_21 = x_31;
goto block_26;
}
}
else
{
uint8_t x_156; 
lean_dec(x_16);
lean_dec(x_15);
x_156 = !lean_is_exclusive(x_17);
if (x_156 == 0)
{
return x_17;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_157 = lean_ctor_get(x_17, 0);
x_158 = lean_ctor_get(x_17, 1);
lean_inc(x_158);
lean_inc(x_157);
lean_dec(x_17);
x_159 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_159, 0, x_157);
lean_ctor_set(x_159, 1, x_158);
return x_159;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBneDiff(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Nat_reduceBneDiff___redArg(x_1, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBneDiff___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Nat_reduceBneDiff___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBneDiff___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Nat_reduceBneDiff(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceBneDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4342_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_2 = lean_mk_string_unchecked("Nat", 3, 3);
x_3 = lean_mk_string_unchecked("reduceBneDiff", 13, 13);
lean_inc(x_2);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_mk_string_unchecked("bne", 3, 3);
x_6 = l_Lean_Name_mkStr1(x_5);
x_7 = lean_unsigned_to_nat(4u);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
x_9 = l_Lean_Name_mkStr1(x_2);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_box(3);
x_13 = lean_unsigned_to_nat(5u);
x_14 = lean_mk_empty_array_with_capacity(x_13);
x_15 = lean_array_push(x_14, x_8);
x_16 = lean_array_push(x_15, x_11);
x_17 = lean_array_push(x_16, x_12);
x_18 = lean_array_push(x_17, x_12);
x_19 = lean_array_push(x_18, x_12);
x_20 = lean_alloc_closure((void*)(l_Nat_reduceBneDiff___boxed), 9, 0);
x_21 = l_Lean_Meta_Simp_registerBuiltinSimproc(x_4, x_19, x_20, x_1);
return x_21;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceBneDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4344_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Nat", 3, 3);
x_3 = lean_mk_string_unchecked("reduceBneDiff", 13, 13);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Nat_reduceBneDiff___boxed), 9, 0);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceBneDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4346_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Nat", 3, 3);
x_3 = lean_mk_string_unchecked("reduceBneDiff", 13, 13);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Nat_reduceBneDiff___boxed), 9, 0);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceLTLE___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_38; 
x_38 = l_Lean_Expr_isAppOfArity(x_4, x_1, x_2);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_40, 0, x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_9);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = l_Lean_Expr_appFn_x21(x_4);
x_43 = l_Lean_Expr_appArg_x21(x_42);
lean_dec(x_42);
x_44 = l_Lean_Expr_appArg_x21(x_4);
if (x_3 == 0)
{
lean_object* x_380; 
x_380 = lean_unsigned_to_nat(0u);
x_45 = x_380;
goto block_379;
}
else
{
lean_object* x_381; 
x_381 = lean_unsigned_to_nat(1u);
x_45 = x_381;
goto block_379;
}
block_379:
{
lean_object* x_46; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_43);
x_46 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExpr_x3f___redArg(x_43, x_45, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; 
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_48 = !lean_is_exclusive(x_46);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_46, 0);
lean_dec(x_49);
x_50 = lean_box(0);
x_51 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_46, 0, x_51);
return x_46;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_46, 1);
lean_inc(x_52);
lean_dec(x_46);
x_53 = lean_box(0);
x_54 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_52);
return x_55;
}
}
else
{
lean_object* x_56; uint8_t x_57; 
x_56 = lean_ctor_get(x_46, 1);
lean_inc(x_56);
lean_dec(x_46);
x_57 = !lean_is_exclusive(x_47);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_47, 0);
x_59 = lean_unsigned_to_nat(0u);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_44);
x_60 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExpr_x3f___redArg(x_44, x_59, x_5, x_6, x_7, x_8, x_56);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
if (lean_obj_tag(x_61) == 0)
{
uint8_t x_62; 
lean_dec(x_58);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_62 = !lean_is_exclusive(x_60);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_60, 0);
lean_dec(x_63);
x_64 = lean_box(0);
lean_ctor_set_tag(x_47, 2);
lean_ctor_set(x_47, 0, x_64);
lean_ctor_set(x_60, 0, x_47);
return x_60;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_60, 1);
lean_inc(x_65);
lean_dec(x_60);
x_66 = lean_box(0);
lean_ctor_set_tag(x_47, 2);
lean_ctor_set(x_47, 0, x_66);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_47);
lean_ctor_set(x_67, 1, x_65);
return x_67;
}
}
else
{
lean_free_object(x_47);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_68; 
lean_dec(x_44);
x_68 = lean_ctor_get(x_61, 0);
lean_inc(x_68);
lean_dec(x_61);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; lean_object* x_73; 
lean_dec(x_43);
x_69 = lean_ctor_get(x_60, 1);
lean_inc(x_69);
lean_dec(x_60);
x_70 = lean_ctor_get(x_58, 0);
lean_inc(x_70);
lean_dec(x_58);
x_71 = lean_ctor_get(x_68, 0);
lean_inc(x_71);
lean_dec(x_68);
x_72 = lean_nat_dec_le(x_70, x_71);
lean_dec(x_71);
lean_dec(x_70);
x_73 = l_Lean_Meta_Simp_evalPropStep___redArg(x_4, x_72, x_5, x_6, x_7, x_8, x_69);
return x_73;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
lean_dec(x_4);
x_74 = lean_ctor_get(x_60, 1);
lean_inc(x_74);
lean_dec(x_60);
x_75 = lean_ctor_get(x_58, 0);
lean_inc(x_75);
lean_dec(x_58);
x_76 = lean_ctor_get(x_68, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_68, 1);
lean_inc(x_77);
x_78 = lean_ctor_get(x_68, 2);
lean_inc(x_78);
lean_dec(x_68);
x_79 = lean_nat_dec_le(x_75, x_78);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; 
lean_inc(x_43);
lean_inc(x_77);
x_80 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(x_77, x_43);
lean_inc(x_8);
x_81 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(x_80, x_5, x_6, x_7, x_8, x_74);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_84 = lean_nat_sub(x_75, x_78);
lean_dec(x_78);
lean_dec(x_75);
x_85 = l_Lean_mkNatLit(x_84);
lean_inc(x_76);
x_86 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(x_85, x_76);
x_87 = lean_mk_string_unchecked("Nat", 3, 3);
x_88 = lean_mk_string_unchecked("Simproc", 7, 7);
x_89 = lean_mk_string_unchecked("le_add_ge", 9, 9);
x_90 = l_Lean_Name_mkStr3(x_87, x_88, x_89);
x_91 = lean_unsigned_to_nat(4u);
x_92 = lean_mk_empty_array_with_capacity(x_91);
x_93 = lean_array_push(x_92, x_43);
x_94 = lean_array_push(x_93, x_76);
x_95 = lean_array_push(x_94, x_77);
x_96 = lean_array_push(x_95, x_82);
x_97 = l_Nat_applySimprocConst___redArg(x_86, x_90, x_96, x_8, x_83);
lean_dec(x_8);
lean_dec(x_96);
return x_97;
}
else
{
uint8_t x_98; 
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_43);
lean_dec(x_8);
x_98 = !lean_is_exclusive(x_81);
if (x_98 == 0)
{
return x_81;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_81, 0);
x_100 = lean_ctor_get(x_81, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_81);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
}
else
{
lean_object* x_102; lean_object* x_103; 
lean_dec(x_78);
lean_dec(x_75);
lean_inc(x_77);
lean_inc(x_43);
x_102 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(x_43, x_77);
lean_inc(x_8);
x_103 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(x_102, x_5, x_6, x_7, x_8, x_74);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
x_106 = lean_mk_string_unchecked("True", 4, 4);
x_107 = l_Lean_Name_mkStr1(x_106);
x_108 = lean_box(0);
x_109 = l_Lean_Expr_const___override(x_107, x_108);
x_110 = lean_mk_string_unchecked("Nat", 3, 3);
x_111 = lean_mk_string_unchecked("Simproc", 7, 7);
x_112 = lean_mk_string_unchecked("le_add_le", 9, 9);
x_113 = l_Lean_Name_mkStr3(x_110, x_111, x_112);
x_114 = lean_unsigned_to_nat(4u);
x_115 = lean_mk_empty_array_with_capacity(x_114);
x_116 = lean_array_push(x_115, x_43);
x_117 = lean_array_push(x_116, x_76);
x_118 = lean_array_push(x_117, x_77);
x_119 = lean_array_push(x_118, x_104);
x_120 = l_Nat_applySimprocConst___redArg(x_109, x_113, x_119, x_8, x_105);
lean_dec(x_8);
lean_dec(x_119);
return x_120;
}
else
{
uint8_t x_121; 
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_43);
lean_dec(x_8);
x_121 = !lean_is_exclusive(x_103);
if (x_121 == 0)
{
return x_103;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_103, 0);
x_123 = lean_ctor_get(x_103, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_103);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
return x_124;
}
}
}
}
}
else
{
lean_object* x_125; 
lean_dec(x_43);
lean_dec(x_4);
x_125 = lean_ctor_get(x_61, 0);
lean_inc(x_125);
lean_dec(x_61);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; uint8_t x_131; 
x_126 = lean_ctor_get(x_60, 1);
lean_inc(x_126);
lean_dec(x_60);
x_127 = lean_ctor_get(x_58, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_58, 1);
lean_inc(x_128);
x_129 = lean_ctor_get(x_58, 2);
lean_inc(x_129);
lean_dec(x_58);
x_130 = lean_ctor_get(x_125, 0);
lean_inc(x_130);
lean_dec(x_125);
x_131 = lean_nat_dec_le(x_129, x_130);
if (x_131 == 0)
{
lean_object* x_132; lean_object* x_133; 
lean_dec(x_130);
lean_dec(x_129);
lean_inc(x_128);
lean_inc(x_44);
x_132 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat(x_44, x_128);
lean_inc(x_8);
x_133 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(x_132, x_5, x_6, x_7, x_8, x_126);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
lean_dec(x_133);
x_136 = lean_mk_string_unchecked("False", 5, 5);
x_137 = l_Lean_Name_mkStr1(x_136);
x_138 = lean_box(0);
x_139 = l_Lean_Expr_const___override(x_137, x_138);
x_140 = lean_mk_string_unchecked("Nat", 3, 3);
x_141 = lean_mk_string_unchecked("Simproc", 7, 7);
x_142 = lean_mk_string_unchecked("add_le_gt", 9, 9);
x_143 = l_Lean_Name_mkStr3(x_140, x_141, x_142);
x_144 = lean_unsigned_to_nat(4u);
x_145 = lean_mk_empty_array_with_capacity(x_144);
x_146 = lean_array_push(x_145, x_127);
x_147 = lean_array_push(x_146, x_128);
x_148 = lean_array_push(x_147, x_44);
x_149 = lean_array_push(x_148, x_134);
x_150 = l_Nat_applySimprocConst___redArg(x_139, x_143, x_149, x_8, x_135);
lean_dec(x_8);
lean_dec(x_149);
return x_150;
}
else
{
uint8_t x_151; 
lean_dec(x_128);
lean_dec(x_127);
lean_dec(x_44);
lean_dec(x_8);
x_151 = !lean_is_exclusive(x_133);
if (x_151 == 0)
{
return x_133;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_152 = lean_ctor_get(x_133, 0);
x_153 = lean_ctor_get(x_133, 1);
lean_inc(x_153);
lean_inc(x_152);
lean_dec(x_133);
x_154 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_154, 0, x_152);
lean_ctor_set(x_154, 1, x_153);
return x_154;
}
}
}
else
{
lean_object* x_155; lean_object* x_156; 
lean_inc(x_44);
lean_inc(x_128);
x_155 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(x_128, x_44);
lean_inc(x_8);
x_156 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(x_155, x_5, x_6, x_7, x_8, x_126);
if (lean_obj_tag(x_156) == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_156, 1);
lean_inc(x_158);
lean_dec(x_156);
x_159 = lean_nat_sub(x_130, x_129);
lean_dec(x_129);
lean_dec(x_130);
x_160 = l_Lean_mkNatLit(x_159);
lean_inc(x_127);
x_161 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(x_127, x_160);
x_162 = lean_mk_string_unchecked("Nat", 3, 3);
x_163 = lean_mk_string_unchecked("Simproc", 7, 7);
x_164 = lean_mk_string_unchecked("add_le_le", 9, 9);
x_165 = l_Lean_Name_mkStr3(x_162, x_163, x_164);
x_166 = lean_unsigned_to_nat(4u);
x_167 = lean_mk_empty_array_with_capacity(x_166);
x_168 = lean_array_push(x_167, x_127);
x_169 = lean_array_push(x_168, x_128);
x_170 = lean_array_push(x_169, x_44);
x_171 = lean_array_push(x_170, x_157);
x_172 = l_Nat_applySimprocConst___redArg(x_161, x_165, x_171, x_8, x_158);
lean_dec(x_8);
lean_dec(x_171);
return x_172;
}
else
{
uint8_t x_173; 
lean_dec(x_130);
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_127);
lean_dec(x_44);
lean_dec(x_8);
x_173 = !lean_is_exclusive(x_156);
if (x_173 == 0)
{
return x_156;
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_174 = lean_ctor_get(x_156, 0);
x_175 = lean_ctor_get(x_156, 1);
lean_inc(x_175);
lean_inc(x_174);
lean_dec(x_156);
x_176 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_176, 0, x_174);
lean_ctor_set(x_176, 1, x_175);
return x_176;
}
}
}
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; uint8_t x_184; 
lean_dec(x_44);
x_177 = lean_ctor_get(x_60, 1);
lean_inc(x_177);
lean_dec(x_60);
x_178 = lean_ctor_get(x_58, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_58, 1);
lean_inc(x_179);
x_180 = lean_ctor_get(x_58, 2);
lean_inc(x_180);
lean_dec(x_58);
x_181 = lean_ctor_get(x_125, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_125, 1);
lean_inc(x_182);
x_183 = lean_ctor_get(x_125, 2);
lean_inc(x_183);
lean_dec(x_125);
x_184 = lean_nat_dec_le(x_180, x_183);
if (x_184 == 0)
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_185 = lean_nat_sub(x_180, x_183);
lean_dec(x_183);
lean_dec(x_180);
lean_inc(x_179);
lean_inc(x_182);
x_186 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(x_182, x_179);
lean_inc(x_8);
x_187 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(x_186, x_5, x_6, x_7, x_8, x_177);
if (lean_obj_tag(x_187) == 0)
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_187, 1);
lean_inc(x_189);
lean_dec(x_187);
x_190 = l_Lean_mkNatLit(x_185);
lean_inc(x_178);
x_191 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat(x_178, x_190);
lean_inc(x_181);
x_192 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(x_191, x_181);
x_193 = lean_mk_string_unchecked("Nat", 3, 3);
x_194 = lean_mk_string_unchecked("Simproc", 7, 7);
x_195 = lean_mk_string_unchecked("add_le_add_ge", 13, 13);
x_196 = l_Lean_Name_mkStr3(x_193, x_194, x_195);
x_197 = lean_unsigned_to_nat(5u);
x_198 = lean_mk_empty_array_with_capacity(x_197);
x_199 = lean_array_push(x_198, x_178);
x_200 = lean_array_push(x_199, x_181);
x_201 = lean_array_push(x_200, x_179);
x_202 = lean_array_push(x_201, x_182);
x_203 = lean_array_push(x_202, x_188);
x_204 = l_Nat_applySimprocConst___redArg(x_192, x_196, x_203, x_8, x_189);
lean_dec(x_8);
lean_dec(x_203);
return x_204;
}
else
{
uint8_t x_205; 
lean_dec(x_185);
lean_dec(x_182);
lean_dec(x_181);
lean_dec(x_179);
lean_dec(x_178);
lean_dec(x_8);
x_205 = !lean_is_exclusive(x_187);
if (x_205 == 0)
{
return x_187;
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_206 = lean_ctor_get(x_187, 0);
x_207 = lean_ctor_get(x_187, 1);
lean_inc(x_207);
lean_inc(x_206);
lean_dec(x_187);
x_208 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_208, 0, x_206);
lean_ctor_set(x_208, 1, x_207);
return x_208;
}
}
}
else
{
uint8_t x_209; 
x_209 = lean_nat_dec_eq(x_180, x_183);
if (x_209 == 0)
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_210 = lean_nat_sub(x_183, x_180);
lean_dec(x_180);
lean_dec(x_183);
x_211 = l_Lean_mkNatLit(x_210);
lean_inc(x_181);
x_212 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat(x_181, x_211);
x_10 = x_181;
x_11 = x_179;
x_12 = x_178;
x_13 = x_177;
x_14 = x_182;
x_15 = x_212;
goto block_37;
}
else
{
lean_dec(x_183);
lean_dec(x_180);
lean_inc(x_181);
x_10 = x_181;
x_11 = x_179;
x_12 = x_178;
x_13 = x_177;
x_14 = x_182;
x_15 = x_181;
goto block_37;
}
}
}
}
}
}
else
{
uint8_t x_213; 
lean_free_object(x_47);
lean_dec(x_58);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_213 = !lean_is_exclusive(x_60);
if (x_213 == 0)
{
return x_60;
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_214 = lean_ctor_get(x_60, 0);
x_215 = lean_ctor_get(x_60, 1);
lean_inc(x_215);
lean_inc(x_214);
lean_dec(x_60);
x_216 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_216, 0, x_214);
lean_ctor_set(x_216, 1, x_215);
return x_216;
}
}
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_217 = lean_ctor_get(x_47, 0);
lean_inc(x_217);
lean_dec(x_47);
x_218 = lean_unsigned_to_nat(0u);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_44);
x_219 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExpr_x3f___redArg(x_44, x_218, x_5, x_6, x_7, x_8, x_56);
if (lean_obj_tag(x_219) == 0)
{
lean_object* x_220; 
x_220 = lean_ctor_get(x_219, 0);
lean_inc(x_220);
if (lean_obj_tag(x_220) == 0)
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; 
lean_dec(x_217);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_221 = lean_ctor_get(x_219, 1);
lean_inc(x_221);
if (lean_is_exclusive(x_219)) {
 lean_ctor_release(x_219, 0);
 lean_ctor_release(x_219, 1);
 x_222 = x_219;
} else {
 lean_dec_ref(x_219);
 x_222 = lean_box(0);
}
x_223 = lean_box(0);
x_224 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_224, 0, x_223);
if (lean_is_scalar(x_222)) {
 x_225 = lean_alloc_ctor(0, 2, 0);
} else {
 x_225 = x_222;
}
lean_ctor_set(x_225, 0, x_224);
lean_ctor_set(x_225, 1, x_221);
return x_225;
}
else
{
if (lean_obj_tag(x_217) == 0)
{
lean_object* x_226; 
lean_dec(x_44);
x_226 = lean_ctor_get(x_220, 0);
lean_inc(x_226);
lean_dec(x_220);
if (lean_obj_tag(x_226) == 0)
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; uint8_t x_230; lean_object* x_231; 
lean_dec(x_43);
x_227 = lean_ctor_get(x_219, 1);
lean_inc(x_227);
lean_dec(x_219);
x_228 = lean_ctor_get(x_217, 0);
lean_inc(x_228);
lean_dec(x_217);
x_229 = lean_ctor_get(x_226, 0);
lean_inc(x_229);
lean_dec(x_226);
x_230 = lean_nat_dec_le(x_228, x_229);
lean_dec(x_229);
lean_dec(x_228);
x_231 = l_Lean_Meta_Simp_evalPropStep___redArg(x_4, x_230, x_5, x_6, x_7, x_8, x_227);
return x_231;
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; uint8_t x_237; 
lean_dec(x_4);
x_232 = lean_ctor_get(x_219, 1);
lean_inc(x_232);
lean_dec(x_219);
x_233 = lean_ctor_get(x_217, 0);
lean_inc(x_233);
lean_dec(x_217);
x_234 = lean_ctor_get(x_226, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_226, 1);
lean_inc(x_235);
x_236 = lean_ctor_get(x_226, 2);
lean_inc(x_236);
lean_dec(x_226);
x_237 = lean_nat_dec_le(x_233, x_236);
if (x_237 == 0)
{
lean_object* x_238; lean_object* x_239; 
lean_inc(x_43);
lean_inc(x_235);
x_238 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(x_235, x_43);
lean_inc(x_8);
x_239 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(x_238, x_5, x_6, x_7, x_8, x_232);
if (lean_obj_tag(x_239) == 0)
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; 
x_240 = lean_ctor_get(x_239, 0);
lean_inc(x_240);
x_241 = lean_ctor_get(x_239, 1);
lean_inc(x_241);
lean_dec(x_239);
x_242 = lean_nat_sub(x_233, x_236);
lean_dec(x_236);
lean_dec(x_233);
x_243 = l_Lean_mkNatLit(x_242);
lean_inc(x_234);
x_244 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(x_243, x_234);
x_245 = lean_mk_string_unchecked("Nat", 3, 3);
x_246 = lean_mk_string_unchecked("Simproc", 7, 7);
x_247 = lean_mk_string_unchecked("le_add_ge", 9, 9);
x_248 = l_Lean_Name_mkStr3(x_245, x_246, x_247);
x_249 = lean_unsigned_to_nat(4u);
x_250 = lean_mk_empty_array_with_capacity(x_249);
x_251 = lean_array_push(x_250, x_43);
x_252 = lean_array_push(x_251, x_234);
x_253 = lean_array_push(x_252, x_235);
x_254 = lean_array_push(x_253, x_240);
x_255 = l_Nat_applySimprocConst___redArg(x_244, x_248, x_254, x_8, x_241);
lean_dec(x_8);
lean_dec(x_254);
return x_255;
}
else
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; 
lean_dec(x_236);
lean_dec(x_235);
lean_dec(x_234);
lean_dec(x_233);
lean_dec(x_43);
lean_dec(x_8);
x_256 = lean_ctor_get(x_239, 0);
lean_inc(x_256);
x_257 = lean_ctor_get(x_239, 1);
lean_inc(x_257);
if (lean_is_exclusive(x_239)) {
 lean_ctor_release(x_239, 0);
 lean_ctor_release(x_239, 1);
 x_258 = x_239;
} else {
 lean_dec_ref(x_239);
 x_258 = lean_box(0);
}
if (lean_is_scalar(x_258)) {
 x_259 = lean_alloc_ctor(1, 2, 0);
} else {
 x_259 = x_258;
}
lean_ctor_set(x_259, 0, x_256);
lean_ctor_set(x_259, 1, x_257);
return x_259;
}
}
else
{
lean_object* x_260; lean_object* x_261; 
lean_dec(x_236);
lean_dec(x_233);
lean_inc(x_235);
lean_inc(x_43);
x_260 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(x_43, x_235);
lean_inc(x_8);
x_261 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(x_260, x_5, x_6, x_7, x_8, x_232);
if (lean_obj_tag(x_261) == 0)
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_262 = lean_ctor_get(x_261, 0);
lean_inc(x_262);
x_263 = lean_ctor_get(x_261, 1);
lean_inc(x_263);
lean_dec(x_261);
x_264 = lean_mk_string_unchecked("True", 4, 4);
x_265 = l_Lean_Name_mkStr1(x_264);
x_266 = lean_box(0);
x_267 = l_Lean_Expr_const___override(x_265, x_266);
x_268 = lean_mk_string_unchecked("Nat", 3, 3);
x_269 = lean_mk_string_unchecked("Simproc", 7, 7);
x_270 = lean_mk_string_unchecked("le_add_le", 9, 9);
x_271 = l_Lean_Name_mkStr3(x_268, x_269, x_270);
x_272 = lean_unsigned_to_nat(4u);
x_273 = lean_mk_empty_array_with_capacity(x_272);
x_274 = lean_array_push(x_273, x_43);
x_275 = lean_array_push(x_274, x_234);
x_276 = lean_array_push(x_275, x_235);
x_277 = lean_array_push(x_276, x_262);
x_278 = l_Nat_applySimprocConst___redArg(x_267, x_271, x_277, x_8, x_263);
lean_dec(x_8);
lean_dec(x_277);
return x_278;
}
else
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; 
lean_dec(x_235);
lean_dec(x_234);
lean_dec(x_43);
lean_dec(x_8);
x_279 = lean_ctor_get(x_261, 0);
lean_inc(x_279);
x_280 = lean_ctor_get(x_261, 1);
lean_inc(x_280);
if (lean_is_exclusive(x_261)) {
 lean_ctor_release(x_261, 0);
 lean_ctor_release(x_261, 1);
 x_281 = x_261;
} else {
 lean_dec_ref(x_261);
 x_281 = lean_box(0);
}
if (lean_is_scalar(x_281)) {
 x_282 = lean_alloc_ctor(1, 2, 0);
} else {
 x_282 = x_281;
}
lean_ctor_set(x_282, 0, x_279);
lean_ctor_set(x_282, 1, x_280);
return x_282;
}
}
}
}
else
{
lean_object* x_283; 
lean_dec(x_43);
lean_dec(x_4);
x_283 = lean_ctor_get(x_220, 0);
lean_inc(x_283);
lean_dec(x_220);
if (lean_obj_tag(x_283) == 0)
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; uint8_t x_289; 
x_284 = lean_ctor_get(x_219, 1);
lean_inc(x_284);
lean_dec(x_219);
x_285 = lean_ctor_get(x_217, 0);
lean_inc(x_285);
x_286 = lean_ctor_get(x_217, 1);
lean_inc(x_286);
x_287 = lean_ctor_get(x_217, 2);
lean_inc(x_287);
lean_dec(x_217);
x_288 = lean_ctor_get(x_283, 0);
lean_inc(x_288);
lean_dec(x_283);
x_289 = lean_nat_dec_le(x_287, x_288);
if (x_289 == 0)
{
lean_object* x_290; lean_object* x_291; 
lean_dec(x_288);
lean_dec(x_287);
lean_inc(x_286);
lean_inc(x_44);
x_290 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat(x_44, x_286);
lean_inc(x_8);
x_291 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(x_290, x_5, x_6, x_7, x_8, x_284);
if (lean_obj_tag(x_291) == 0)
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; 
x_292 = lean_ctor_get(x_291, 0);
lean_inc(x_292);
x_293 = lean_ctor_get(x_291, 1);
lean_inc(x_293);
lean_dec(x_291);
x_294 = lean_mk_string_unchecked("False", 5, 5);
x_295 = l_Lean_Name_mkStr1(x_294);
x_296 = lean_box(0);
x_297 = l_Lean_Expr_const___override(x_295, x_296);
x_298 = lean_mk_string_unchecked("Nat", 3, 3);
x_299 = lean_mk_string_unchecked("Simproc", 7, 7);
x_300 = lean_mk_string_unchecked("add_le_gt", 9, 9);
x_301 = l_Lean_Name_mkStr3(x_298, x_299, x_300);
x_302 = lean_unsigned_to_nat(4u);
x_303 = lean_mk_empty_array_with_capacity(x_302);
x_304 = lean_array_push(x_303, x_285);
x_305 = lean_array_push(x_304, x_286);
x_306 = lean_array_push(x_305, x_44);
x_307 = lean_array_push(x_306, x_292);
x_308 = l_Nat_applySimprocConst___redArg(x_297, x_301, x_307, x_8, x_293);
lean_dec(x_8);
lean_dec(x_307);
return x_308;
}
else
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; 
lean_dec(x_286);
lean_dec(x_285);
lean_dec(x_44);
lean_dec(x_8);
x_309 = lean_ctor_get(x_291, 0);
lean_inc(x_309);
x_310 = lean_ctor_get(x_291, 1);
lean_inc(x_310);
if (lean_is_exclusive(x_291)) {
 lean_ctor_release(x_291, 0);
 lean_ctor_release(x_291, 1);
 x_311 = x_291;
} else {
 lean_dec_ref(x_291);
 x_311 = lean_box(0);
}
if (lean_is_scalar(x_311)) {
 x_312 = lean_alloc_ctor(1, 2, 0);
} else {
 x_312 = x_311;
}
lean_ctor_set(x_312, 0, x_309);
lean_ctor_set(x_312, 1, x_310);
return x_312;
}
}
else
{
lean_object* x_313; lean_object* x_314; 
lean_inc(x_44);
lean_inc(x_286);
x_313 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(x_286, x_44);
lean_inc(x_8);
x_314 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(x_313, x_5, x_6, x_7, x_8, x_284);
if (lean_obj_tag(x_314) == 0)
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; 
x_315 = lean_ctor_get(x_314, 0);
lean_inc(x_315);
x_316 = lean_ctor_get(x_314, 1);
lean_inc(x_316);
lean_dec(x_314);
x_317 = lean_nat_sub(x_288, x_287);
lean_dec(x_287);
lean_dec(x_288);
x_318 = l_Lean_mkNatLit(x_317);
lean_inc(x_285);
x_319 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(x_285, x_318);
x_320 = lean_mk_string_unchecked("Nat", 3, 3);
x_321 = lean_mk_string_unchecked("Simproc", 7, 7);
x_322 = lean_mk_string_unchecked("add_le_le", 9, 9);
x_323 = l_Lean_Name_mkStr3(x_320, x_321, x_322);
x_324 = lean_unsigned_to_nat(4u);
x_325 = lean_mk_empty_array_with_capacity(x_324);
x_326 = lean_array_push(x_325, x_285);
x_327 = lean_array_push(x_326, x_286);
x_328 = lean_array_push(x_327, x_44);
x_329 = lean_array_push(x_328, x_315);
x_330 = l_Nat_applySimprocConst___redArg(x_319, x_323, x_329, x_8, x_316);
lean_dec(x_8);
lean_dec(x_329);
return x_330;
}
else
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; 
lean_dec(x_288);
lean_dec(x_287);
lean_dec(x_286);
lean_dec(x_285);
lean_dec(x_44);
lean_dec(x_8);
x_331 = lean_ctor_get(x_314, 0);
lean_inc(x_331);
x_332 = lean_ctor_get(x_314, 1);
lean_inc(x_332);
if (lean_is_exclusive(x_314)) {
 lean_ctor_release(x_314, 0);
 lean_ctor_release(x_314, 1);
 x_333 = x_314;
} else {
 lean_dec_ref(x_314);
 x_333 = lean_box(0);
}
if (lean_is_scalar(x_333)) {
 x_334 = lean_alloc_ctor(1, 2, 0);
} else {
 x_334 = x_333;
}
lean_ctor_set(x_334, 0, x_331);
lean_ctor_set(x_334, 1, x_332);
return x_334;
}
}
}
else
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; uint8_t x_342; 
lean_dec(x_44);
x_335 = lean_ctor_get(x_219, 1);
lean_inc(x_335);
lean_dec(x_219);
x_336 = lean_ctor_get(x_217, 0);
lean_inc(x_336);
x_337 = lean_ctor_get(x_217, 1);
lean_inc(x_337);
x_338 = lean_ctor_get(x_217, 2);
lean_inc(x_338);
lean_dec(x_217);
x_339 = lean_ctor_get(x_283, 0);
lean_inc(x_339);
x_340 = lean_ctor_get(x_283, 1);
lean_inc(x_340);
x_341 = lean_ctor_get(x_283, 2);
lean_inc(x_341);
lean_dec(x_283);
x_342 = lean_nat_dec_le(x_338, x_341);
if (x_342 == 0)
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; 
x_343 = lean_nat_sub(x_338, x_341);
lean_dec(x_341);
lean_dec(x_338);
lean_inc(x_337);
lean_inc(x_340);
x_344 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(x_340, x_337);
lean_inc(x_8);
x_345 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(x_344, x_5, x_6, x_7, x_8, x_335);
if (lean_obj_tag(x_345) == 0)
{
lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; 
x_346 = lean_ctor_get(x_345, 0);
lean_inc(x_346);
x_347 = lean_ctor_get(x_345, 1);
lean_inc(x_347);
lean_dec(x_345);
x_348 = l_Lean_mkNatLit(x_343);
lean_inc(x_336);
x_349 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat(x_336, x_348);
lean_inc(x_339);
x_350 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(x_349, x_339);
x_351 = lean_mk_string_unchecked("Nat", 3, 3);
x_352 = lean_mk_string_unchecked("Simproc", 7, 7);
x_353 = lean_mk_string_unchecked("add_le_add_ge", 13, 13);
x_354 = l_Lean_Name_mkStr3(x_351, x_352, x_353);
x_355 = lean_unsigned_to_nat(5u);
x_356 = lean_mk_empty_array_with_capacity(x_355);
x_357 = lean_array_push(x_356, x_336);
x_358 = lean_array_push(x_357, x_339);
x_359 = lean_array_push(x_358, x_337);
x_360 = lean_array_push(x_359, x_340);
x_361 = lean_array_push(x_360, x_346);
x_362 = l_Nat_applySimprocConst___redArg(x_350, x_354, x_361, x_8, x_347);
lean_dec(x_8);
lean_dec(x_361);
return x_362;
}
else
{
lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; 
lean_dec(x_343);
lean_dec(x_340);
lean_dec(x_339);
lean_dec(x_337);
lean_dec(x_336);
lean_dec(x_8);
x_363 = lean_ctor_get(x_345, 0);
lean_inc(x_363);
x_364 = lean_ctor_get(x_345, 1);
lean_inc(x_364);
if (lean_is_exclusive(x_345)) {
 lean_ctor_release(x_345, 0);
 lean_ctor_release(x_345, 1);
 x_365 = x_345;
} else {
 lean_dec_ref(x_345);
 x_365 = lean_box(0);
}
if (lean_is_scalar(x_365)) {
 x_366 = lean_alloc_ctor(1, 2, 0);
} else {
 x_366 = x_365;
}
lean_ctor_set(x_366, 0, x_363);
lean_ctor_set(x_366, 1, x_364);
return x_366;
}
}
else
{
uint8_t x_367; 
x_367 = lean_nat_dec_eq(x_338, x_341);
if (x_367 == 0)
{
lean_object* x_368; lean_object* x_369; lean_object* x_370; 
x_368 = lean_nat_sub(x_341, x_338);
lean_dec(x_338);
lean_dec(x_341);
x_369 = l_Lean_mkNatLit(x_368);
lean_inc(x_339);
x_370 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat(x_339, x_369);
x_10 = x_339;
x_11 = x_337;
x_12 = x_336;
x_13 = x_335;
x_14 = x_340;
x_15 = x_370;
goto block_37;
}
else
{
lean_dec(x_341);
lean_dec(x_338);
lean_inc(x_339);
x_10 = x_339;
x_11 = x_337;
x_12 = x_336;
x_13 = x_335;
x_14 = x_340;
x_15 = x_339;
goto block_37;
}
}
}
}
}
}
else
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; 
lean_dec(x_217);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_371 = lean_ctor_get(x_219, 0);
lean_inc(x_371);
x_372 = lean_ctor_get(x_219, 1);
lean_inc(x_372);
if (lean_is_exclusive(x_219)) {
 lean_ctor_release(x_219, 0);
 lean_ctor_release(x_219, 1);
 x_373 = x_219;
} else {
 lean_dec_ref(x_219);
 x_373 = lean_box(0);
}
if (lean_is_scalar(x_373)) {
 x_374 = lean_alloc_ctor(1, 2, 0);
} else {
 x_374 = x_373;
}
lean_ctor_set(x_374, 0, x_371);
lean_ctor_set(x_374, 1, x_372);
return x_374;
}
}
}
}
else
{
uint8_t x_375; 
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_375 = !lean_is_exclusive(x_46);
if (x_375 == 0)
{
return x_46;
}
else
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; 
x_376 = lean_ctor_get(x_46, 0);
x_377 = lean_ctor_get(x_46, 1);
lean_inc(x_377);
lean_inc(x_376);
lean_dec(x_46);
x_378 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_378, 0, x_376);
lean_ctor_set(x_378, 1, x_377);
return x_378;
}
}
}
}
block_37:
{
lean_object* x_16; lean_object* x_17; 
lean_inc(x_14);
lean_inc(x_11);
x_16 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(x_11, x_14);
lean_inc(x_8);
x_17 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(x_16, x_5, x_6, x_7, x_8, x_13);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_12);
x_20 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(x_12, x_15);
x_21 = lean_mk_string_unchecked("Nat", 3, 3);
x_22 = lean_mk_string_unchecked("Simproc", 7, 7);
x_23 = lean_mk_string_unchecked("add_le_add_le", 13, 13);
x_24 = l_Lean_Name_mkStr3(x_21, x_22, x_23);
x_25 = lean_unsigned_to_nat(5u);
x_26 = lean_mk_empty_array_with_capacity(x_25);
x_27 = lean_array_push(x_26, x_12);
x_28 = lean_array_push(x_27, x_10);
x_29 = lean_array_push(x_28, x_11);
x_30 = lean_array_push(x_29, x_14);
x_31 = lean_array_push(x_30, x_18);
x_32 = l_Nat_applySimprocConst___redArg(x_20, x_24, x_31, x_8, x_19);
lean_dec(x_8);
lean_dec(x_31);
return x_32;
}
else
{
uint8_t x_33; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
x_33 = !lean_is_exclusive(x_17);
if (x_33 == 0)
{
return x_17;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_17, 0);
x_35 = lean_ctor_get(x_17, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_17);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceLTLE(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Nat_reduceLTLE___redArg(x_1, x_2, x_3, x_4, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceLTLE___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = l_Nat_reduceLTLE___redArg(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceLTLE___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_3);
lean_dec(x_3);
x_14 = l_Nat_reduceLTLE(x_1, x_2, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceLeDiff___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_7 = lean_mk_string_unchecked("LE", 2, 2);
x_8 = lean_mk_string_unchecked("le", 2, 2);
x_9 = l_Lean_Name_mkStr2(x_7, x_8);
x_10 = lean_unsigned_to_nat(4u);
x_11 = lean_box(0);
x_12 = lean_unbox(x_11);
x_13 = l_Nat_reduceLTLE___redArg(x_9, x_10, x_12, x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceLeDiff(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Nat_reduceLeDiff___redArg(x_1, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceLeDiff___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Nat_reduceLeDiff(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceLeDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4970_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_2 = lean_mk_string_unchecked("Nat", 3, 3);
x_3 = lean_mk_string_unchecked("reduceLeDiff", 12, 12);
lean_inc(x_2);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_mk_string_unchecked("LE", 2, 2);
x_6 = lean_mk_string_unchecked("le", 2, 2);
x_7 = l_Lean_Name_mkStr2(x_5, x_6);
x_8 = lean_unsigned_to_nat(4u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Lean_Name_mkStr1(x_2);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_box(3);
x_14 = lean_unsigned_to_nat(5u);
x_15 = lean_mk_empty_array_with_capacity(x_14);
x_16 = lean_array_push(x_15, x_9);
x_17 = lean_array_push(x_16, x_12);
x_18 = lean_array_push(x_17, x_13);
x_19 = lean_array_push(x_18, x_13);
x_20 = lean_array_push(x_19, x_13);
x_21 = lean_alloc_closure((void*)(l_Nat_reduceLeDiff___boxed), 9, 0);
x_22 = l_Lean_Meta_Simp_registerBuiltinSimproc(x_4, x_20, x_21, x_1);
return x_22;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceLeDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4972_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Nat", 3, 3);
x_3 = lean_mk_string_unchecked("reduceLeDiff", 12, 12);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Nat_reduceLeDiff___boxed), 9, 0);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceLeDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4974_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Nat", 3, 3);
x_3 = lean_mk_string_unchecked("reduceLeDiff", 12, 12);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Nat_reduceLeDiff___boxed), 9, 0);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceSubDiff___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_mk_string_unchecked("HSub", 4, 4);
x_8 = lean_mk_string_unchecked("hSub", 4, 4);
x_9 = l_Lean_Name_mkStr2(x_7, x_8);
x_10 = lean_unsigned_to_nat(6u);
x_11 = l_Lean_Expr_isAppOfArity(x_1, x_9, x_10);
lean_dec(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_6);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = l_Lean_Expr_appFn_x21(x_1);
x_16 = l_Lean_Expr_appArg_x21(x_15);
lean_dec(x_15);
x_17 = lean_unsigned_to_nat(0u);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_16);
x_18 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExpr_x3f___redArg(x_16, x_17, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_18, 0);
lean_dec(x_21);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_18, 0, x_23);
return x_18;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_18, 1);
lean_inc(x_24);
lean_dec(x_18);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_24);
return x_27;
}
}
else
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_18, 1);
lean_inc(x_28);
lean_dec(x_18);
x_29 = !lean_is_exclusive(x_19);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_19, 0);
x_31 = l_Lean_Expr_appArg_x21(x_1);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_31);
x_32 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExpr_x3f___redArg(x_31, x_17, x_2, x_3, x_4, x_5, x_28);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_34 = !lean_is_exclusive(x_32);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_32, 0);
lean_dec(x_35);
x_36 = lean_box(0);
lean_ctor_set_tag(x_19, 2);
lean_ctor_set(x_19, 0, x_36);
lean_ctor_set(x_32, 0, x_19);
return x_32;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_32, 1);
lean_inc(x_37);
lean_dec(x_32);
x_38 = lean_box(0);
lean_ctor_set_tag(x_19, 2);
lean_ctor_set(x_19, 0, x_38);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_19);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
else
{
lean_free_object(x_19);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_40; 
lean_dec(x_31);
x_40 = !lean_is_exclusive(x_33);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_33, 0);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; 
lean_dec(x_16);
x_42 = lean_ctor_get(x_32, 1);
lean_inc(x_42);
lean_dec(x_32);
x_43 = lean_ctor_get(x_30, 0);
lean_inc(x_43);
lean_dec(x_30);
x_44 = !lean_is_exclusive(x_41);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_41, 0);
x_46 = lean_nat_sub(x_43, x_45);
lean_dec(x_45);
lean_dec(x_43);
x_47 = l_Lean_mkNatLit(x_46);
lean_inc(x_47);
x_48 = l_Lean_Meta_mkEqRefl(x_47, x_2, x_3, x_4, x_5, x_42);
if (lean_obj_tag(x_48) == 0)
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_48, 0);
lean_ctor_set(x_33, 0, x_50);
x_51 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_51, 0, x_47);
lean_ctor_set(x_51, 1, x_33);
lean_ctor_set_uint8(x_51, sizeof(void*)*2, x_11);
lean_ctor_set(x_41, 0, x_51);
lean_ctor_set(x_48, 0, x_41);
return x_48;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_48, 0);
x_53 = lean_ctor_get(x_48, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_48);
lean_ctor_set(x_33, 0, x_52);
x_54 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_54, 0, x_47);
lean_ctor_set(x_54, 1, x_33);
lean_ctor_set_uint8(x_54, sizeof(void*)*2, x_11);
lean_ctor_set(x_41, 0, x_54);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_41);
lean_ctor_set(x_55, 1, x_53);
return x_55;
}
}
else
{
uint8_t x_56; 
lean_dec(x_47);
lean_free_object(x_41);
lean_free_object(x_33);
x_56 = !lean_is_exclusive(x_48);
if (x_56 == 0)
{
return x_48;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_48, 0);
x_58 = lean_ctor_get(x_48, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_48);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_60 = lean_ctor_get(x_41, 0);
lean_inc(x_60);
lean_dec(x_41);
x_61 = lean_nat_sub(x_43, x_60);
lean_dec(x_60);
lean_dec(x_43);
x_62 = l_Lean_mkNatLit(x_61);
lean_inc(x_62);
x_63 = l_Lean_Meta_mkEqRefl(x_62, x_2, x_3, x_4, x_5, x_42);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
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
lean_ctor_set(x_33, 0, x_64);
x_67 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_67, 0, x_62);
lean_ctor_set(x_67, 1, x_33);
lean_ctor_set_uint8(x_67, sizeof(void*)*2, x_11);
x_68 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_68, 0, x_67);
if (lean_is_scalar(x_66)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_66;
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_65);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_62);
lean_free_object(x_33);
x_70 = lean_ctor_get(x_63, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_63, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_72 = x_63;
} else {
 lean_dec_ref(x_63);
 x_72 = lean_box(0);
}
if (lean_is_scalar(x_72)) {
 x_73 = lean_alloc_ctor(1, 2, 0);
} else {
 x_73 = x_72;
}
lean_ctor_set(x_73, 0, x_70);
lean_ctor_set(x_73, 1, x_71);
return x_73;
}
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_free_object(x_33);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_74 = lean_ctor_get(x_32, 1);
lean_inc(x_74);
lean_dec(x_32);
x_75 = lean_ctor_get(x_30, 0);
lean_inc(x_75);
lean_dec(x_30);
x_76 = lean_ctor_get(x_41, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_41, 1);
lean_inc(x_77);
x_78 = lean_ctor_get(x_41, 2);
lean_inc(x_78);
lean_dec(x_41);
x_79 = lean_nat_sub(x_75, x_78);
lean_dec(x_78);
lean_dec(x_75);
x_80 = l_Lean_mkNatLit(x_79);
lean_inc(x_76);
x_81 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat(x_80, x_76);
x_82 = lean_mk_string_unchecked("Nat", 3, 3);
x_83 = lean_mk_string_unchecked("Simproc", 7, 7);
x_84 = lean_mk_string_unchecked("sub_add_eq_comm", 15, 15);
x_85 = l_Lean_Name_mkStr3(x_82, x_83, x_84);
x_86 = lean_unsigned_to_nat(3u);
x_87 = lean_mk_empty_array_with_capacity(x_86);
x_88 = lean_array_push(x_87, x_16);
x_89 = lean_array_push(x_88, x_76);
x_90 = lean_array_push(x_89, x_77);
x_91 = l_Nat_applySimprocConst___redArg(x_81, x_85, x_90, x_5, x_74);
lean_dec(x_5);
lean_dec(x_90);
return x_91;
}
}
else
{
lean_object* x_92; 
x_92 = lean_ctor_get(x_33, 0);
lean_inc(x_92);
lean_dec(x_33);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_16);
x_93 = lean_ctor_get(x_32, 1);
lean_inc(x_93);
lean_dec(x_32);
x_94 = lean_ctor_get(x_30, 0);
lean_inc(x_94);
lean_dec(x_30);
x_95 = lean_ctor_get(x_92, 0);
lean_inc(x_95);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 x_96 = x_92;
} else {
 lean_dec_ref(x_92);
 x_96 = lean_box(0);
}
x_97 = lean_nat_sub(x_94, x_95);
lean_dec(x_95);
lean_dec(x_94);
x_98 = l_Lean_mkNatLit(x_97);
lean_inc(x_98);
x_99 = l_Lean_Meta_mkEqRefl(x_98, x_2, x_3, x_4, x_5, x_93);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_102 = x_99;
} else {
 lean_dec_ref(x_99);
 x_102 = lean_box(0);
}
x_103 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_103, 0, x_100);
x_104 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_104, 0, x_98);
lean_ctor_set(x_104, 1, x_103);
lean_ctor_set_uint8(x_104, sizeof(void*)*2, x_11);
if (lean_is_scalar(x_96)) {
 x_105 = lean_alloc_ctor(0, 1, 0);
} else {
 x_105 = x_96;
}
lean_ctor_set(x_105, 0, x_104);
if (lean_is_scalar(x_102)) {
 x_106 = lean_alloc_ctor(0, 2, 0);
} else {
 x_106 = x_102;
}
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_101);
return x_106;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_dec(x_98);
lean_dec(x_96);
x_107 = lean_ctor_get(x_99, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_99, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_109 = x_99;
} else {
 lean_dec_ref(x_99);
 x_109 = lean_box(0);
}
if (lean_is_scalar(x_109)) {
 x_110 = lean_alloc_ctor(1, 2, 0);
} else {
 x_110 = x_109;
}
lean_ctor_set(x_110, 0, x_107);
lean_ctor_set(x_110, 1, x_108);
return x_110;
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_111 = lean_ctor_get(x_32, 1);
lean_inc(x_111);
lean_dec(x_32);
x_112 = lean_ctor_get(x_30, 0);
lean_inc(x_112);
lean_dec(x_30);
x_113 = lean_ctor_get(x_92, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_92, 1);
lean_inc(x_114);
x_115 = lean_ctor_get(x_92, 2);
lean_inc(x_115);
lean_dec(x_92);
x_116 = lean_nat_sub(x_112, x_115);
lean_dec(x_115);
lean_dec(x_112);
x_117 = l_Lean_mkNatLit(x_116);
lean_inc(x_113);
x_118 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat(x_117, x_113);
x_119 = lean_mk_string_unchecked("Nat", 3, 3);
x_120 = lean_mk_string_unchecked("Simproc", 7, 7);
x_121 = lean_mk_string_unchecked("sub_add_eq_comm", 15, 15);
x_122 = l_Lean_Name_mkStr3(x_119, x_120, x_121);
x_123 = lean_unsigned_to_nat(3u);
x_124 = lean_mk_empty_array_with_capacity(x_123);
x_125 = lean_array_push(x_124, x_16);
x_126 = lean_array_push(x_125, x_113);
x_127 = lean_array_push(x_126, x_114);
x_128 = l_Nat_applySimprocConst___redArg(x_118, x_122, x_127, x_5, x_111);
lean_dec(x_5);
lean_dec(x_127);
return x_128;
}
}
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
lean_dec(x_16);
x_129 = lean_ctor_get(x_32, 1);
lean_inc(x_129);
lean_dec(x_32);
x_130 = lean_ctor_get(x_33, 0);
lean_inc(x_130);
lean_dec(x_33);
x_131 = lean_ctor_get(x_30, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_30, 1);
lean_inc(x_132);
x_133 = lean_ctor_get(x_30, 2);
lean_inc(x_133);
lean_dec(x_30);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_155; uint8_t x_156; 
x_155 = lean_ctor_get(x_130, 0);
lean_inc(x_155);
lean_dec(x_130);
x_156 = lean_nat_dec_le(x_133, x_155);
if (x_156 == 0)
{
lean_object* x_157; lean_object* x_158; 
lean_inc(x_132);
lean_inc(x_31);
x_157 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(x_31, x_132);
lean_inc(x_5);
x_158 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(x_157, x_2, x_3, x_4, x_5, x_129);
if (lean_obj_tag(x_158) == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_158, 1);
lean_inc(x_160);
lean_dec(x_158);
x_161 = lean_nat_sub(x_133, x_155);
lean_dec(x_155);
lean_dec(x_133);
x_162 = l_Lean_mkNatLit(x_161);
lean_inc(x_131);
x_163 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat(x_131, x_162);
x_164 = lean_mk_string_unchecked("Nat", 3, 3);
x_165 = lean_mk_string_unchecked("add_sub_assoc", 13, 13);
x_166 = l_Lean_Name_mkStr2(x_164, x_165);
x_167 = lean_unsigned_to_nat(4u);
x_168 = lean_mk_empty_array_with_capacity(x_167);
x_169 = lean_array_push(x_168, x_132);
x_170 = lean_array_push(x_169, x_31);
x_171 = lean_array_push(x_170, x_159);
x_172 = lean_array_push(x_171, x_131);
x_173 = l_Nat_applySimprocConst___redArg(x_163, x_166, x_172, x_5, x_160);
lean_dec(x_5);
lean_dec(x_172);
return x_173;
}
else
{
uint8_t x_174; 
lean_dec(x_155);
lean_dec(x_133);
lean_dec(x_132);
lean_dec(x_131);
lean_dec(x_31);
lean_dec(x_5);
x_174 = !lean_is_exclusive(x_158);
if (x_174 == 0)
{
return x_158;
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_175 = lean_ctor_get(x_158, 0);
x_176 = lean_ctor_get(x_158, 1);
lean_inc(x_176);
lean_inc(x_175);
lean_dec(x_158);
x_177 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_177, 0, x_175);
lean_ctor_set(x_177, 1, x_176);
return x_177;
}
}
}
else
{
uint8_t x_178; 
x_178 = lean_nat_dec_eq(x_133, x_155);
if (x_178 == 0)
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_179 = lean_nat_sub(x_155, x_133);
lean_dec(x_133);
lean_dec(x_155);
x_180 = l_Lean_mkNatLit(x_179);
lean_inc(x_131);
x_181 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat(x_131, x_180);
x_134 = x_181;
goto block_154;
}
else
{
lean_dec(x_155);
lean_dec(x_133);
lean_inc(x_131);
x_134 = x_131;
goto block_154;
}
}
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; uint8_t x_208; 
lean_dec(x_31);
x_182 = lean_ctor_get(x_130, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_130, 1);
lean_inc(x_183);
x_184 = lean_ctor_get(x_130, 2);
lean_inc(x_184);
lean_dec(x_130);
x_208 = lean_nat_dec_le(x_133, x_184);
if (x_208 == 0)
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_209 = lean_nat_sub(x_133, x_184);
lean_dec(x_184);
lean_dec(x_133);
lean_inc(x_132);
lean_inc(x_183);
x_210 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(x_183, x_132);
lean_inc(x_5);
x_211 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(x_210, x_2, x_3, x_4, x_5, x_129);
if (lean_obj_tag(x_211) == 0)
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_212 = lean_ctor_get(x_211, 0);
lean_inc(x_212);
x_213 = lean_ctor_get(x_211, 1);
lean_inc(x_213);
lean_dec(x_211);
x_214 = l_Lean_mkNatLit(x_209);
lean_inc(x_131);
x_215 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat(x_131, x_214);
lean_inc(x_182);
x_216 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat(x_215, x_182);
x_217 = lean_mk_string_unchecked("Nat", 3, 3);
x_218 = lean_mk_string_unchecked("Simproc", 7, 7);
x_219 = lean_mk_string_unchecked("add_sub_add_ge", 14, 14);
x_220 = l_Lean_Name_mkStr3(x_217, x_218, x_219);
x_221 = lean_unsigned_to_nat(5u);
x_222 = lean_mk_empty_array_with_capacity(x_221);
x_223 = lean_array_push(x_222, x_131);
x_224 = lean_array_push(x_223, x_182);
x_225 = lean_array_push(x_224, x_132);
x_226 = lean_array_push(x_225, x_183);
x_227 = lean_array_push(x_226, x_212);
x_228 = l_Nat_applySimprocConst___redArg(x_216, x_220, x_227, x_5, x_213);
lean_dec(x_5);
lean_dec(x_227);
return x_228;
}
else
{
uint8_t x_229; 
lean_dec(x_209);
lean_dec(x_183);
lean_dec(x_182);
lean_dec(x_132);
lean_dec(x_131);
lean_dec(x_5);
x_229 = !lean_is_exclusive(x_211);
if (x_229 == 0)
{
return x_211;
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_230 = lean_ctor_get(x_211, 0);
x_231 = lean_ctor_get(x_211, 1);
lean_inc(x_231);
lean_inc(x_230);
lean_dec(x_211);
x_232 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_232, 0, x_230);
lean_ctor_set(x_232, 1, x_231);
return x_232;
}
}
}
else
{
uint8_t x_233; 
x_233 = lean_nat_dec_eq(x_133, x_184);
if (x_233 == 0)
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_234 = lean_nat_sub(x_184, x_133);
lean_dec(x_133);
lean_dec(x_184);
x_235 = l_Lean_mkNatLit(x_234);
lean_inc(x_182);
x_236 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat(x_182, x_235);
x_185 = x_236;
goto block_207;
}
else
{
lean_dec(x_184);
lean_dec(x_133);
lean_inc(x_182);
x_185 = x_182;
goto block_207;
}
}
block_207:
{
lean_object* x_186; lean_object* x_187; 
lean_inc(x_183);
lean_inc(x_132);
x_186 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(x_132, x_183);
lean_inc(x_5);
x_187 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(x_186, x_2, x_3, x_4, x_5, x_129);
if (lean_obj_tag(x_187) == 0)
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_187, 1);
lean_inc(x_189);
lean_dec(x_187);
lean_inc(x_131);
x_190 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat(x_131, x_185);
x_191 = lean_mk_string_unchecked("Nat", 3, 3);
x_192 = lean_mk_string_unchecked("Simproc", 7, 7);
x_193 = lean_mk_string_unchecked("add_sub_add_le", 14, 14);
x_194 = l_Lean_Name_mkStr3(x_191, x_192, x_193);
x_195 = lean_unsigned_to_nat(5u);
x_196 = lean_mk_empty_array_with_capacity(x_195);
x_197 = lean_array_push(x_196, x_131);
x_198 = lean_array_push(x_197, x_182);
x_199 = lean_array_push(x_198, x_132);
x_200 = lean_array_push(x_199, x_183);
x_201 = lean_array_push(x_200, x_188);
x_202 = l_Nat_applySimprocConst___redArg(x_190, x_194, x_201, x_5, x_189);
lean_dec(x_5);
lean_dec(x_201);
return x_202;
}
else
{
uint8_t x_203; 
lean_dec(x_185);
lean_dec(x_183);
lean_dec(x_182);
lean_dec(x_132);
lean_dec(x_131);
lean_dec(x_5);
x_203 = !lean_is_exclusive(x_187);
if (x_203 == 0)
{
return x_187;
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_204 = lean_ctor_get(x_187, 0);
x_205 = lean_ctor_get(x_187, 1);
lean_inc(x_205);
lean_inc(x_204);
lean_dec(x_187);
x_206 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_206, 0, x_204);
lean_ctor_set(x_206, 1, x_205);
return x_206;
}
}
}
}
block_154:
{
lean_object* x_135; lean_object* x_136; 
lean_inc(x_31);
lean_inc(x_132);
x_135 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(x_132, x_31);
lean_inc(x_5);
x_136 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(x_135, x_2, x_3, x_4, x_5, x_129);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_136, 1);
lean_inc(x_138);
lean_dec(x_136);
x_139 = lean_mk_string_unchecked("Nat", 3, 3);
x_140 = lean_mk_string_unchecked("Simproc", 7, 7);
x_141 = lean_mk_string_unchecked("add_sub_le", 10, 10);
x_142 = l_Lean_Name_mkStr3(x_139, x_140, x_141);
x_143 = lean_unsigned_to_nat(4u);
x_144 = lean_mk_empty_array_with_capacity(x_143);
x_145 = lean_array_push(x_144, x_131);
x_146 = lean_array_push(x_145, x_132);
x_147 = lean_array_push(x_146, x_31);
x_148 = lean_array_push(x_147, x_137);
x_149 = l_Nat_applySimprocConst___redArg(x_134, x_142, x_148, x_5, x_138);
lean_dec(x_5);
lean_dec(x_148);
return x_149;
}
else
{
uint8_t x_150; 
lean_dec(x_134);
lean_dec(x_132);
lean_dec(x_131);
lean_dec(x_31);
lean_dec(x_5);
x_150 = !lean_is_exclusive(x_136);
if (x_150 == 0)
{
return x_136;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_151 = lean_ctor_get(x_136, 0);
x_152 = lean_ctor_get(x_136, 1);
lean_inc(x_152);
lean_inc(x_151);
lean_dec(x_136);
x_153 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_153, 0, x_151);
lean_ctor_set(x_153, 1, x_152);
return x_153;
}
}
}
}
}
}
else
{
uint8_t x_237; 
lean_dec(x_31);
lean_free_object(x_19);
lean_dec(x_30);
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_237 = !lean_is_exclusive(x_32);
if (x_237 == 0)
{
return x_32;
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; 
x_238 = lean_ctor_get(x_32, 0);
x_239 = lean_ctor_get(x_32, 1);
lean_inc(x_239);
lean_inc(x_238);
lean_dec(x_32);
x_240 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_240, 0, x_238);
lean_ctor_set(x_240, 1, x_239);
return x_240;
}
}
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; 
x_241 = lean_ctor_get(x_19, 0);
lean_inc(x_241);
lean_dec(x_19);
x_242 = l_Lean_Expr_appArg_x21(x_1);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_242);
x_243 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExpr_x3f___redArg(x_242, x_17, x_2, x_3, x_4, x_5, x_28);
if (lean_obj_tag(x_243) == 0)
{
lean_object* x_244; 
x_244 = lean_ctor_get(x_243, 0);
lean_inc(x_244);
if (lean_obj_tag(x_244) == 0)
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
lean_dec(x_242);
lean_dec(x_241);
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_245 = lean_ctor_get(x_243, 1);
lean_inc(x_245);
if (lean_is_exclusive(x_243)) {
 lean_ctor_release(x_243, 0);
 lean_ctor_release(x_243, 1);
 x_246 = x_243;
} else {
 lean_dec_ref(x_243);
 x_246 = lean_box(0);
}
x_247 = lean_box(0);
x_248 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_248, 0, x_247);
if (lean_is_scalar(x_246)) {
 x_249 = lean_alloc_ctor(0, 2, 0);
} else {
 x_249 = x_246;
}
lean_ctor_set(x_249, 0, x_248);
lean_ctor_set(x_249, 1, x_245);
return x_249;
}
else
{
if (lean_obj_tag(x_241) == 0)
{
lean_object* x_250; lean_object* x_251; 
lean_dec(x_242);
x_250 = lean_ctor_get(x_244, 0);
lean_inc(x_250);
if (lean_is_exclusive(x_244)) {
 lean_ctor_release(x_244, 0);
 x_251 = x_244;
} else {
 lean_dec_ref(x_244);
 x_251 = lean_box(0);
}
if (lean_obj_tag(x_250) == 0)
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; 
lean_dec(x_16);
x_252 = lean_ctor_get(x_243, 1);
lean_inc(x_252);
lean_dec(x_243);
x_253 = lean_ctor_get(x_241, 0);
lean_inc(x_253);
lean_dec(x_241);
x_254 = lean_ctor_get(x_250, 0);
lean_inc(x_254);
if (lean_is_exclusive(x_250)) {
 lean_ctor_release(x_250, 0);
 x_255 = x_250;
} else {
 lean_dec_ref(x_250);
 x_255 = lean_box(0);
}
x_256 = lean_nat_sub(x_253, x_254);
lean_dec(x_254);
lean_dec(x_253);
x_257 = l_Lean_mkNatLit(x_256);
lean_inc(x_257);
x_258 = l_Lean_Meta_mkEqRefl(x_257, x_2, x_3, x_4, x_5, x_252);
if (lean_obj_tag(x_258) == 0)
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; 
x_259 = lean_ctor_get(x_258, 0);
lean_inc(x_259);
x_260 = lean_ctor_get(x_258, 1);
lean_inc(x_260);
if (lean_is_exclusive(x_258)) {
 lean_ctor_release(x_258, 0);
 lean_ctor_release(x_258, 1);
 x_261 = x_258;
} else {
 lean_dec_ref(x_258);
 x_261 = lean_box(0);
}
if (lean_is_scalar(x_251)) {
 x_262 = lean_alloc_ctor(1, 1, 0);
} else {
 x_262 = x_251;
}
lean_ctor_set(x_262, 0, x_259);
x_263 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_263, 0, x_257);
lean_ctor_set(x_263, 1, x_262);
lean_ctor_set_uint8(x_263, sizeof(void*)*2, x_11);
if (lean_is_scalar(x_255)) {
 x_264 = lean_alloc_ctor(0, 1, 0);
} else {
 x_264 = x_255;
}
lean_ctor_set(x_264, 0, x_263);
if (lean_is_scalar(x_261)) {
 x_265 = lean_alloc_ctor(0, 2, 0);
} else {
 x_265 = x_261;
}
lean_ctor_set(x_265, 0, x_264);
lean_ctor_set(x_265, 1, x_260);
return x_265;
}
else
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; 
lean_dec(x_257);
lean_dec(x_255);
lean_dec(x_251);
x_266 = lean_ctor_get(x_258, 0);
lean_inc(x_266);
x_267 = lean_ctor_get(x_258, 1);
lean_inc(x_267);
if (lean_is_exclusive(x_258)) {
 lean_ctor_release(x_258, 0);
 lean_ctor_release(x_258, 1);
 x_268 = x_258;
} else {
 lean_dec_ref(x_258);
 x_268 = lean_box(0);
}
if (lean_is_scalar(x_268)) {
 x_269 = lean_alloc_ctor(1, 2, 0);
} else {
 x_269 = x_268;
}
lean_ctor_set(x_269, 0, x_266);
lean_ctor_set(x_269, 1, x_267);
return x_269;
}
}
else
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; 
lean_dec(x_251);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_270 = lean_ctor_get(x_243, 1);
lean_inc(x_270);
lean_dec(x_243);
x_271 = lean_ctor_get(x_241, 0);
lean_inc(x_271);
lean_dec(x_241);
x_272 = lean_ctor_get(x_250, 0);
lean_inc(x_272);
x_273 = lean_ctor_get(x_250, 1);
lean_inc(x_273);
x_274 = lean_ctor_get(x_250, 2);
lean_inc(x_274);
lean_dec(x_250);
x_275 = lean_nat_sub(x_271, x_274);
lean_dec(x_274);
lean_dec(x_271);
x_276 = l_Lean_mkNatLit(x_275);
lean_inc(x_272);
x_277 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat(x_276, x_272);
x_278 = lean_mk_string_unchecked("Nat", 3, 3);
x_279 = lean_mk_string_unchecked("Simproc", 7, 7);
x_280 = lean_mk_string_unchecked("sub_add_eq_comm", 15, 15);
x_281 = l_Lean_Name_mkStr3(x_278, x_279, x_280);
x_282 = lean_unsigned_to_nat(3u);
x_283 = lean_mk_empty_array_with_capacity(x_282);
x_284 = lean_array_push(x_283, x_16);
x_285 = lean_array_push(x_284, x_272);
x_286 = lean_array_push(x_285, x_273);
x_287 = l_Nat_applySimprocConst___redArg(x_277, x_281, x_286, x_5, x_270);
lean_dec(x_5);
lean_dec(x_286);
return x_287;
}
}
else
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; 
lean_dec(x_16);
x_288 = lean_ctor_get(x_243, 1);
lean_inc(x_288);
lean_dec(x_243);
x_289 = lean_ctor_get(x_244, 0);
lean_inc(x_289);
lean_dec(x_244);
x_290 = lean_ctor_get(x_241, 0);
lean_inc(x_290);
x_291 = lean_ctor_get(x_241, 1);
lean_inc(x_291);
x_292 = lean_ctor_get(x_241, 2);
lean_inc(x_292);
lean_dec(x_241);
if (lean_obj_tag(x_289) == 0)
{
lean_object* x_314; uint8_t x_315; 
x_314 = lean_ctor_get(x_289, 0);
lean_inc(x_314);
lean_dec(x_289);
x_315 = lean_nat_dec_le(x_292, x_314);
if (x_315 == 0)
{
lean_object* x_316; lean_object* x_317; 
lean_inc(x_291);
lean_inc(x_242);
x_316 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(x_242, x_291);
lean_inc(x_5);
x_317 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(x_316, x_2, x_3, x_4, x_5, x_288);
if (lean_obj_tag(x_317) == 0)
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; 
x_318 = lean_ctor_get(x_317, 0);
lean_inc(x_318);
x_319 = lean_ctor_get(x_317, 1);
lean_inc(x_319);
lean_dec(x_317);
x_320 = lean_nat_sub(x_292, x_314);
lean_dec(x_314);
lean_dec(x_292);
x_321 = l_Lean_mkNatLit(x_320);
lean_inc(x_290);
x_322 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat(x_290, x_321);
x_323 = lean_mk_string_unchecked("Nat", 3, 3);
x_324 = lean_mk_string_unchecked("add_sub_assoc", 13, 13);
x_325 = l_Lean_Name_mkStr2(x_323, x_324);
x_326 = lean_unsigned_to_nat(4u);
x_327 = lean_mk_empty_array_with_capacity(x_326);
x_328 = lean_array_push(x_327, x_291);
x_329 = lean_array_push(x_328, x_242);
x_330 = lean_array_push(x_329, x_318);
x_331 = lean_array_push(x_330, x_290);
x_332 = l_Nat_applySimprocConst___redArg(x_322, x_325, x_331, x_5, x_319);
lean_dec(x_5);
lean_dec(x_331);
return x_332;
}
else
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; 
lean_dec(x_314);
lean_dec(x_292);
lean_dec(x_291);
lean_dec(x_290);
lean_dec(x_242);
lean_dec(x_5);
x_333 = lean_ctor_get(x_317, 0);
lean_inc(x_333);
x_334 = lean_ctor_get(x_317, 1);
lean_inc(x_334);
if (lean_is_exclusive(x_317)) {
 lean_ctor_release(x_317, 0);
 lean_ctor_release(x_317, 1);
 x_335 = x_317;
} else {
 lean_dec_ref(x_317);
 x_335 = lean_box(0);
}
if (lean_is_scalar(x_335)) {
 x_336 = lean_alloc_ctor(1, 2, 0);
} else {
 x_336 = x_335;
}
lean_ctor_set(x_336, 0, x_333);
lean_ctor_set(x_336, 1, x_334);
return x_336;
}
}
else
{
uint8_t x_337; 
x_337 = lean_nat_dec_eq(x_292, x_314);
if (x_337 == 0)
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; 
x_338 = lean_nat_sub(x_314, x_292);
lean_dec(x_292);
lean_dec(x_314);
x_339 = l_Lean_mkNatLit(x_338);
lean_inc(x_290);
x_340 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat(x_290, x_339);
x_293 = x_340;
goto block_313;
}
else
{
lean_dec(x_314);
lean_dec(x_292);
lean_inc(x_290);
x_293 = x_290;
goto block_313;
}
}
}
else
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; uint8_t x_367; 
lean_dec(x_242);
x_341 = lean_ctor_get(x_289, 0);
lean_inc(x_341);
x_342 = lean_ctor_get(x_289, 1);
lean_inc(x_342);
x_343 = lean_ctor_get(x_289, 2);
lean_inc(x_343);
lean_dec(x_289);
x_367 = lean_nat_dec_le(x_292, x_343);
if (x_367 == 0)
{
lean_object* x_368; lean_object* x_369; lean_object* x_370; 
x_368 = lean_nat_sub(x_292, x_343);
lean_dec(x_343);
lean_dec(x_292);
lean_inc(x_291);
lean_inc(x_342);
x_369 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(x_342, x_291);
lean_inc(x_5);
x_370 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(x_369, x_2, x_3, x_4, x_5, x_288);
if (lean_obj_tag(x_370) == 0)
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; 
x_371 = lean_ctor_get(x_370, 0);
lean_inc(x_371);
x_372 = lean_ctor_get(x_370, 1);
lean_inc(x_372);
lean_dec(x_370);
x_373 = l_Lean_mkNatLit(x_368);
lean_inc(x_290);
x_374 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat(x_290, x_373);
lean_inc(x_341);
x_375 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat(x_374, x_341);
x_376 = lean_mk_string_unchecked("Nat", 3, 3);
x_377 = lean_mk_string_unchecked("Simproc", 7, 7);
x_378 = lean_mk_string_unchecked("add_sub_add_ge", 14, 14);
x_379 = l_Lean_Name_mkStr3(x_376, x_377, x_378);
x_380 = lean_unsigned_to_nat(5u);
x_381 = lean_mk_empty_array_with_capacity(x_380);
x_382 = lean_array_push(x_381, x_290);
x_383 = lean_array_push(x_382, x_341);
x_384 = lean_array_push(x_383, x_291);
x_385 = lean_array_push(x_384, x_342);
x_386 = lean_array_push(x_385, x_371);
x_387 = l_Nat_applySimprocConst___redArg(x_375, x_379, x_386, x_5, x_372);
lean_dec(x_5);
lean_dec(x_386);
return x_387;
}
else
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; 
lean_dec(x_368);
lean_dec(x_342);
lean_dec(x_341);
lean_dec(x_291);
lean_dec(x_290);
lean_dec(x_5);
x_388 = lean_ctor_get(x_370, 0);
lean_inc(x_388);
x_389 = lean_ctor_get(x_370, 1);
lean_inc(x_389);
if (lean_is_exclusive(x_370)) {
 lean_ctor_release(x_370, 0);
 lean_ctor_release(x_370, 1);
 x_390 = x_370;
} else {
 lean_dec_ref(x_370);
 x_390 = lean_box(0);
}
if (lean_is_scalar(x_390)) {
 x_391 = lean_alloc_ctor(1, 2, 0);
} else {
 x_391 = x_390;
}
lean_ctor_set(x_391, 0, x_388);
lean_ctor_set(x_391, 1, x_389);
return x_391;
}
}
else
{
uint8_t x_392; 
x_392 = lean_nat_dec_eq(x_292, x_343);
if (x_392 == 0)
{
lean_object* x_393; lean_object* x_394; lean_object* x_395; 
x_393 = lean_nat_sub(x_343, x_292);
lean_dec(x_292);
lean_dec(x_343);
x_394 = l_Lean_mkNatLit(x_393);
lean_inc(x_341);
x_395 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat(x_341, x_394);
x_344 = x_395;
goto block_366;
}
else
{
lean_dec(x_343);
lean_dec(x_292);
lean_inc(x_341);
x_344 = x_341;
goto block_366;
}
}
block_366:
{
lean_object* x_345; lean_object* x_346; 
lean_inc(x_342);
lean_inc(x_291);
x_345 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(x_291, x_342);
lean_inc(x_5);
x_346 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(x_345, x_2, x_3, x_4, x_5, x_288);
if (lean_obj_tag(x_346) == 0)
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; 
x_347 = lean_ctor_get(x_346, 0);
lean_inc(x_347);
x_348 = lean_ctor_get(x_346, 1);
lean_inc(x_348);
lean_dec(x_346);
lean_inc(x_290);
x_349 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat(x_290, x_344);
x_350 = lean_mk_string_unchecked("Nat", 3, 3);
x_351 = lean_mk_string_unchecked("Simproc", 7, 7);
x_352 = lean_mk_string_unchecked("add_sub_add_le", 14, 14);
x_353 = l_Lean_Name_mkStr3(x_350, x_351, x_352);
x_354 = lean_unsigned_to_nat(5u);
x_355 = lean_mk_empty_array_with_capacity(x_354);
x_356 = lean_array_push(x_355, x_290);
x_357 = lean_array_push(x_356, x_341);
x_358 = lean_array_push(x_357, x_291);
x_359 = lean_array_push(x_358, x_342);
x_360 = lean_array_push(x_359, x_347);
x_361 = l_Nat_applySimprocConst___redArg(x_349, x_353, x_360, x_5, x_348);
lean_dec(x_5);
lean_dec(x_360);
return x_361;
}
else
{
lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; 
lean_dec(x_344);
lean_dec(x_342);
lean_dec(x_341);
lean_dec(x_291);
lean_dec(x_290);
lean_dec(x_5);
x_362 = lean_ctor_get(x_346, 0);
lean_inc(x_362);
x_363 = lean_ctor_get(x_346, 1);
lean_inc(x_363);
if (lean_is_exclusive(x_346)) {
 lean_ctor_release(x_346, 0);
 lean_ctor_release(x_346, 1);
 x_364 = x_346;
} else {
 lean_dec_ref(x_346);
 x_364 = lean_box(0);
}
if (lean_is_scalar(x_364)) {
 x_365 = lean_alloc_ctor(1, 2, 0);
} else {
 x_365 = x_364;
}
lean_ctor_set(x_365, 0, x_362);
lean_ctor_set(x_365, 1, x_363);
return x_365;
}
}
}
block_313:
{
lean_object* x_294; lean_object* x_295; 
lean_inc(x_242);
lean_inc(x_291);
x_294 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(x_291, x_242);
lean_inc(x_5);
x_295 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(x_294, x_2, x_3, x_4, x_5, x_288);
if (lean_obj_tag(x_295) == 0)
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; 
x_296 = lean_ctor_get(x_295, 0);
lean_inc(x_296);
x_297 = lean_ctor_get(x_295, 1);
lean_inc(x_297);
lean_dec(x_295);
x_298 = lean_mk_string_unchecked("Nat", 3, 3);
x_299 = lean_mk_string_unchecked("Simproc", 7, 7);
x_300 = lean_mk_string_unchecked("add_sub_le", 10, 10);
x_301 = l_Lean_Name_mkStr3(x_298, x_299, x_300);
x_302 = lean_unsigned_to_nat(4u);
x_303 = lean_mk_empty_array_with_capacity(x_302);
x_304 = lean_array_push(x_303, x_290);
x_305 = lean_array_push(x_304, x_291);
x_306 = lean_array_push(x_305, x_242);
x_307 = lean_array_push(x_306, x_296);
x_308 = l_Nat_applySimprocConst___redArg(x_293, x_301, x_307, x_5, x_297);
lean_dec(x_5);
lean_dec(x_307);
return x_308;
}
else
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; 
lean_dec(x_293);
lean_dec(x_291);
lean_dec(x_290);
lean_dec(x_242);
lean_dec(x_5);
x_309 = lean_ctor_get(x_295, 0);
lean_inc(x_309);
x_310 = lean_ctor_get(x_295, 1);
lean_inc(x_310);
if (lean_is_exclusive(x_295)) {
 lean_ctor_release(x_295, 0);
 lean_ctor_release(x_295, 1);
 x_311 = x_295;
} else {
 lean_dec_ref(x_295);
 x_311 = lean_box(0);
}
if (lean_is_scalar(x_311)) {
 x_312 = lean_alloc_ctor(1, 2, 0);
} else {
 x_312 = x_311;
}
lean_ctor_set(x_312, 0, x_309);
lean_ctor_set(x_312, 1, x_310);
return x_312;
}
}
}
}
}
else
{
lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; 
lean_dec(x_242);
lean_dec(x_241);
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_396 = lean_ctor_get(x_243, 0);
lean_inc(x_396);
x_397 = lean_ctor_get(x_243, 1);
lean_inc(x_397);
if (lean_is_exclusive(x_243)) {
 lean_ctor_release(x_243, 0);
 lean_ctor_release(x_243, 1);
 x_398 = x_243;
} else {
 lean_dec_ref(x_243);
 x_398 = lean_box(0);
}
if (lean_is_scalar(x_398)) {
 x_399 = lean_alloc_ctor(1, 2, 0);
} else {
 x_399 = x_398;
}
lean_ctor_set(x_399, 0, x_396);
lean_ctor_set(x_399, 1, x_397);
return x_399;
}
}
}
}
else
{
uint8_t x_400; 
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_400 = !lean_is_exclusive(x_18);
if (x_400 == 0)
{
return x_18;
}
else
{
lean_object* x_401; lean_object* x_402; lean_object* x_403; 
x_401 = lean_ctor_get(x_18, 0);
x_402 = lean_ctor_get(x_18, 1);
lean_inc(x_402);
lean_inc(x_401);
lean_dec(x_18);
x_403 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_403, 0, x_401);
lean_ctor_set(x_403, 1, x_402);
return x_403;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceSubDiff(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Nat_reduceSubDiff___redArg(x_1, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceSubDiff___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Nat_reduceSubDiff___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceSubDiff___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Nat_reduceSubDiff(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceSubDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_5560_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_2 = lean_mk_string_unchecked("Nat", 3, 3);
x_3 = lean_mk_string_unchecked("reduceSubDiff", 13, 13);
lean_inc(x_2);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_mk_string_unchecked("HSub", 4, 4);
x_6 = lean_mk_string_unchecked("hSub", 4, 4);
x_7 = l_Lean_Name_mkStr2(x_5, x_6);
x_8 = lean_unsigned_to_nat(6u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Lean_Name_mkStr1(x_2);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_box(3);
x_14 = lean_unsigned_to_nat(7u);
x_15 = lean_mk_empty_array_with_capacity(x_14);
x_16 = lean_array_push(x_15, x_9);
lean_inc(x_12);
x_17 = lean_array_push(x_16, x_12);
lean_inc(x_12);
x_18 = lean_array_push(x_17, x_12);
x_19 = lean_array_push(x_18, x_12);
x_20 = lean_array_push(x_19, x_13);
x_21 = lean_array_push(x_20, x_13);
x_22 = lean_array_push(x_21, x_13);
x_23 = lean_alloc_closure((void*)(l_Nat_reduceSubDiff___boxed), 9, 0);
x_24 = l_Lean_Meta_Simp_registerBuiltinSimproc(x_4, x_22, x_23, x_1);
return x_24;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceSubDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_5562_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Nat", 3, 3);
x_3 = lean_mk_string_unchecked("reduceSubDiff", 13, 13);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Nat_reduceSubDiff___boxed), 9, 0);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceSubDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_5564_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Nat", 3, 3);
x_3 = lean_mk_string_unchecked("reduceSubDiff", 13, 13);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Nat_reduceSubDiff___boxed), 9, 0);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceDvd___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_15; uint8_t x_16; 
x_7 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_1, x_3, x_6);
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
x_15 = l_Lean_Expr_cleanupAnnotations(x_8);
x_16 = l_Lean_Expr_isApp(x_15);
if (x_16 == 0)
{
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
goto block_14;
}
else
{
lean_object* x_17; uint8_t x_18; 
lean_inc(x_15);
x_17 = l_Lean_Expr_appFnCleanup___redArg(x_15);
x_18 = l_Lean_Expr_isApp(x_17);
if (x_18 == 0)
{
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
goto block_14;
}
else
{
lean_object* x_19; uint8_t x_20; 
lean_inc(x_17);
x_19 = l_Lean_Expr_appFnCleanup___redArg(x_17);
x_20 = l_Lean_Expr_isApp(x_19);
if (x_20 == 0)
{
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
goto block_14;
}
else
{
lean_object* x_21; uint8_t x_22; 
lean_inc(x_19);
x_21 = l_Lean_Expr_appFnCleanup___redArg(x_19);
x_22 = l_Lean_Expr_isApp(x_21);
if (x_22 == 0)
{
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
goto block_14;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_23 = l_Lean_Expr_appFnCleanup___redArg(x_21);
x_24 = lean_mk_string_unchecked("Dvd", 3, 3);
x_25 = lean_mk_string_unchecked("dvd", 3, 3);
x_26 = l_Lean_Name_mkStr2(x_24, x_25);
x_27 = l_Lean_Expr_isConstOf(x_23, x_26);
lean_dec(x_26);
lean_dec(x_23);
if (x_27 == 0)
{
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
goto block_14;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_10);
x_28 = lean_ctor_get(x_19, 1);
lean_inc(x_28);
lean_dec(x_19);
x_29 = lean_mk_string_unchecked("Nat", 3, 3);
x_30 = lean_mk_string_unchecked("instDvd", 7, 7);
lean_inc(x_29);
x_31 = l_Lean_Name_mkStr2(x_29, x_30);
x_32 = lean_box(0);
x_33 = l_Lean_Expr_const___override(x_31, x_32);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_34 = l_Lean_Meta_matchesInstance(x_28, x_33, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_unbox(x_35);
if (x_36 == 0)
{
uint8_t x_37; 
lean_dec(x_35);
lean_dec(x_29);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_37 = !lean_is_exclusive(x_34);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_34, 0);
lean_dec(x_38);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_34, 0, x_40);
return x_34;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_34, 1);
lean_inc(x_41);
lean_dec(x_34);
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_41);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_34, 1);
lean_inc(x_45);
lean_dec(x_34);
x_46 = lean_ctor_get(x_17, 1);
lean_inc(x_46);
lean_dec(x_17);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_47 = l_Lean_Meta_getNatValue_x3f(x_46, x_2, x_3, x_4, x_5, x_45);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
if (lean_obj_tag(x_48) == 0)
{
uint8_t x_49; 
lean_dec(x_46);
lean_dec(x_35);
lean_dec(x_29);
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_49 = !lean_is_exclusive(x_47);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_47, 0);
lean_dec(x_50);
x_51 = lean_box(0);
x_52 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_47, 0, x_52);
return x_47;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_47, 1);
lean_inc(x_53);
lean_dec(x_47);
x_54 = lean_box(0);
x_55 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_55, 0, x_54);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_53);
return x_56;
}
}
else
{
lean_object* x_57; uint8_t x_58; 
x_57 = lean_ctor_get(x_47, 1);
lean_inc(x_57);
lean_dec(x_47);
x_58 = !lean_is_exclusive(x_48);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_48, 0);
x_60 = lean_ctor_get(x_15, 1);
lean_inc(x_60);
lean_dec(x_15);
x_61 = l_Lean_Meta_getNatValue_x3f(x_60, x_2, x_3, x_4, x_5, x_57);
lean_dec(x_2);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
if (lean_obj_tag(x_62) == 0)
{
uint8_t x_63; 
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_46);
lean_dec(x_35);
lean_dec(x_29);
x_63 = !lean_is_exclusive(x_61);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_61, 0);
lean_dec(x_64);
x_65 = lean_box(0);
lean_ctor_set_tag(x_48, 2);
lean_ctor_set(x_48, 0, x_65);
lean_ctor_set(x_61, 0, x_48);
return x_61;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_61, 1);
lean_inc(x_66);
lean_dec(x_61);
x_67 = lean_box(0);
lean_ctor_set_tag(x_48, 2);
lean_ctor_set(x_48, 0, x_67);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_48);
lean_ctor_set(x_68, 1, x_66);
return x_68;
}
}
else
{
uint8_t x_69; 
x_69 = !lean_is_exclusive(x_61);
if (x_69 == 0)
{
lean_object* x_70; uint8_t x_71; 
x_70 = lean_ctor_get(x_61, 0);
lean_dec(x_70);
x_71 = !lean_is_exclusive(x_62);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_72 = lean_ctor_get(x_62, 0);
x_73 = lean_nat_mod(x_72, x_59);
lean_dec(x_59);
lean_dec(x_72);
x_74 = lean_unsigned_to_nat(0u);
x_75 = lean_nat_dec_eq(x_73, x_74);
lean_dec(x_73);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_76 = lean_mk_string_unchecked("False", 5, 5);
x_77 = l_Lean_Name_mkStr1(x_76);
x_78 = l_Lean_Expr_const___override(x_77, x_32);
x_79 = lean_mk_string_unchecked("dvd_eq_false_of_mod_ne_zero", 27, 27);
x_80 = l_Lean_Name_mkStr2(x_29, x_79);
x_81 = l_Lean_Expr_const___override(x_80, x_32);
x_82 = l_Lean_reflBoolTrue;
x_83 = l_Lean_mkApp3(x_81, x_46, x_60, x_82);
lean_ctor_set(x_62, 0, x_83);
x_84 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_84, 0, x_78);
lean_ctor_set(x_84, 1, x_62);
x_85 = lean_unbox(x_35);
lean_dec(x_35);
lean_ctor_set_uint8(x_84, sizeof(void*)*2, x_85);
lean_ctor_set_tag(x_48, 0);
lean_ctor_set(x_48, 0, x_84);
lean_ctor_set(x_61, 0, x_48);
return x_61;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_86 = lean_mk_string_unchecked("True", 4, 4);
x_87 = l_Lean_Name_mkStr1(x_86);
x_88 = l_Lean_Expr_const___override(x_87, x_32);
x_89 = lean_mk_string_unchecked("dvd_eq_true_of_mod_eq_zero", 26, 26);
x_90 = l_Lean_Name_mkStr2(x_29, x_89);
x_91 = l_Lean_Expr_const___override(x_90, x_32);
x_92 = l_Lean_reflBoolTrue;
x_93 = l_Lean_mkApp3(x_91, x_46, x_60, x_92);
lean_ctor_set(x_62, 0, x_93);
x_94 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_94, 0, x_88);
lean_ctor_set(x_94, 1, x_62);
x_95 = lean_unbox(x_35);
lean_dec(x_35);
lean_ctor_set_uint8(x_94, sizeof(void*)*2, x_95);
lean_ctor_set_tag(x_48, 0);
lean_ctor_set(x_48, 0, x_94);
lean_ctor_set(x_61, 0, x_48);
return x_61;
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; 
x_96 = lean_ctor_get(x_62, 0);
lean_inc(x_96);
lean_dec(x_62);
x_97 = lean_nat_mod(x_96, x_59);
lean_dec(x_59);
lean_dec(x_96);
x_98 = lean_unsigned_to_nat(0u);
x_99 = lean_nat_dec_eq(x_97, x_98);
lean_dec(x_97);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; 
x_100 = lean_mk_string_unchecked("False", 5, 5);
x_101 = l_Lean_Name_mkStr1(x_100);
x_102 = l_Lean_Expr_const___override(x_101, x_32);
x_103 = lean_mk_string_unchecked("dvd_eq_false_of_mod_ne_zero", 27, 27);
x_104 = l_Lean_Name_mkStr2(x_29, x_103);
x_105 = l_Lean_Expr_const___override(x_104, x_32);
x_106 = l_Lean_reflBoolTrue;
x_107 = l_Lean_mkApp3(x_105, x_46, x_60, x_106);
x_108 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_108, 0, x_107);
x_109 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_109, 0, x_102);
lean_ctor_set(x_109, 1, x_108);
x_110 = lean_unbox(x_35);
lean_dec(x_35);
lean_ctor_set_uint8(x_109, sizeof(void*)*2, x_110);
lean_ctor_set_tag(x_48, 0);
lean_ctor_set(x_48, 0, x_109);
lean_ctor_set(x_61, 0, x_48);
return x_61;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; 
x_111 = lean_mk_string_unchecked("True", 4, 4);
x_112 = l_Lean_Name_mkStr1(x_111);
x_113 = l_Lean_Expr_const___override(x_112, x_32);
x_114 = lean_mk_string_unchecked("dvd_eq_true_of_mod_eq_zero", 26, 26);
x_115 = l_Lean_Name_mkStr2(x_29, x_114);
x_116 = l_Lean_Expr_const___override(x_115, x_32);
x_117 = l_Lean_reflBoolTrue;
x_118 = l_Lean_mkApp3(x_116, x_46, x_60, x_117);
x_119 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_119, 0, x_118);
x_120 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_120, 0, x_113);
lean_ctor_set(x_120, 1, x_119);
x_121 = lean_unbox(x_35);
lean_dec(x_35);
lean_ctor_set_uint8(x_120, sizeof(void*)*2, x_121);
lean_ctor_set_tag(x_48, 0);
lean_ctor_set(x_48, 0, x_120);
lean_ctor_set(x_61, 0, x_48);
return x_61;
}
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; 
x_122 = lean_ctor_get(x_61, 1);
lean_inc(x_122);
lean_dec(x_61);
x_123 = lean_ctor_get(x_62, 0);
lean_inc(x_123);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 x_124 = x_62;
} else {
 lean_dec_ref(x_62);
 x_124 = lean_box(0);
}
x_125 = lean_nat_mod(x_123, x_59);
lean_dec(x_59);
lean_dec(x_123);
x_126 = lean_unsigned_to_nat(0u);
x_127 = lean_nat_dec_eq(x_125, x_126);
lean_dec(x_125);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; lean_object* x_139; 
x_128 = lean_mk_string_unchecked("False", 5, 5);
x_129 = l_Lean_Name_mkStr1(x_128);
x_130 = l_Lean_Expr_const___override(x_129, x_32);
x_131 = lean_mk_string_unchecked("dvd_eq_false_of_mod_ne_zero", 27, 27);
x_132 = l_Lean_Name_mkStr2(x_29, x_131);
x_133 = l_Lean_Expr_const___override(x_132, x_32);
x_134 = l_Lean_reflBoolTrue;
x_135 = l_Lean_mkApp3(x_133, x_46, x_60, x_134);
if (lean_is_scalar(x_124)) {
 x_136 = lean_alloc_ctor(1, 1, 0);
} else {
 x_136 = x_124;
}
lean_ctor_set(x_136, 0, x_135);
x_137 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_137, 0, x_130);
lean_ctor_set(x_137, 1, x_136);
x_138 = lean_unbox(x_35);
lean_dec(x_35);
lean_ctor_set_uint8(x_137, sizeof(void*)*2, x_138);
lean_ctor_set_tag(x_48, 0);
lean_ctor_set(x_48, 0, x_137);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_48);
lean_ctor_set(x_139, 1, x_122);
return x_139;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; lean_object* x_151; 
x_140 = lean_mk_string_unchecked("True", 4, 4);
x_141 = l_Lean_Name_mkStr1(x_140);
x_142 = l_Lean_Expr_const___override(x_141, x_32);
x_143 = lean_mk_string_unchecked("dvd_eq_true_of_mod_eq_zero", 26, 26);
x_144 = l_Lean_Name_mkStr2(x_29, x_143);
x_145 = l_Lean_Expr_const___override(x_144, x_32);
x_146 = l_Lean_reflBoolTrue;
x_147 = l_Lean_mkApp3(x_145, x_46, x_60, x_146);
if (lean_is_scalar(x_124)) {
 x_148 = lean_alloc_ctor(1, 1, 0);
} else {
 x_148 = x_124;
}
lean_ctor_set(x_148, 0, x_147);
x_149 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_149, 0, x_142);
lean_ctor_set(x_149, 1, x_148);
x_150 = lean_unbox(x_35);
lean_dec(x_35);
lean_ctor_set_uint8(x_149, sizeof(void*)*2, x_150);
lean_ctor_set_tag(x_48, 0);
lean_ctor_set(x_48, 0, x_149);
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_48);
lean_ctor_set(x_151, 1, x_122);
return x_151;
}
}
}
}
else
{
uint8_t x_152; 
lean_dec(x_60);
lean_free_object(x_48);
lean_dec(x_59);
lean_dec(x_46);
lean_dec(x_35);
lean_dec(x_29);
x_152 = !lean_is_exclusive(x_61);
if (x_152 == 0)
{
return x_61;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = lean_ctor_get(x_61, 0);
x_154 = lean_ctor_get(x_61, 1);
lean_inc(x_154);
lean_inc(x_153);
lean_dec(x_61);
x_155 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set(x_155, 1, x_154);
return x_155;
}
}
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_156 = lean_ctor_get(x_48, 0);
lean_inc(x_156);
lean_dec(x_48);
x_157 = lean_ctor_get(x_15, 1);
lean_inc(x_157);
lean_dec(x_15);
x_158 = l_Lean_Meta_getNatValue_x3f(x_157, x_2, x_3, x_4, x_5, x_57);
lean_dec(x_2);
if (lean_obj_tag(x_158) == 0)
{
lean_object* x_159; 
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
if (lean_obj_tag(x_159) == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
lean_dec(x_157);
lean_dec(x_156);
lean_dec(x_46);
lean_dec(x_35);
lean_dec(x_29);
x_160 = lean_ctor_get(x_158, 1);
lean_inc(x_160);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 x_161 = x_158;
} else {
 lean_dec_ref(x_158);
 x_161 = lean_box(0);
}
x_162 = lean_box(0);
x_163 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_163, 0, x_162);
if (lean_is_scalar(x_161)) {
 x_164 = lean_alloc_ctor(0, 2, 0);
} else {
 x_164 = x_161;
}
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_164, 1, x_160);
return x_164;
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; uint8_t x_171; 
x_165 = lean_ctor_get(x_158, 1);
lean_inc(x_165);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 x_166 = x_158;
} else {
 lean_dec_ref(x_158);
 x_166 = lean_box(0);
}
x_167 = lean_ctor_get(x_159, 0);
lean_inc(x_167);
if (lean_is_exclusive(x_159)) {
 lean_ctor_release(x_159, 0);
 x_168 = x_159;
} else {
 lean_dec_ref(x_159);
 x_168 = lean_box(0);
}
x_169 = lean_nat_mod(x_167, x_156);
lean_dec(x_156);
lean_dec(x_167);
x_170 = lean_unsigned_to_nat(0u);
x_171 = lean_nat_dec_eq(x_169, x_170);
lean_dec(x_169);
if (x_171 == 0)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; uint8_t x_182; lean_object* x_183; lean_object* x_184; 
x_172 = lean_mk_string_unchecked("False", 5, 5);
x_173 = l_Lean_Name_mkStr1(x_172);
x_174 = l_Lean_Expr_const___override(x_173, x_32);
x_175 = lean_mk_string_unchecked("dvd_eq_false_of_mod_ne_zero", 27, 27);
x_176 = l_Lean_Name_mkStr2(x_29, x_175);
x_177 = l_Lean_Expr_const___override(x_176, x_32);
x_178 = l_Lean_reflBoolTrue;
x_179 = l_Lean_mkApp3(x_177, x_46, x_157, x_178);
if (lean_is_scalar(x_168)) {
 x_180 = lean_alloc_ctor(1, 1, 0);
} else {
 x_180 = x_168;
}
lean_ctor_set(x_180, 0, x_179);
x_181 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_181, 0, x_174);
lean_ctor_set(x_181, 1, x_180);
x_182 = lean_unbox(x_35);
lean_dec(x_35);
lean_ctor_set_uint8(x_181, sizeof(void*)*2, x_182);
x_183 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_183, 0, x_181);
if (lean_is_scalar(x_166)) {
 x_184 = lean_alloc_ctor(0, 2, 0);
} else {
 x_184 = x_166;
}
lean_ctor_set(x_184, 0, x_183);
lean_ctor_set(x_184, 1, x_165);
return x_184;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; uint8_t x_195; lean_object* x_196; lean_object* x_197; 
x_185 = lean_mk_string_unchecked("True", 4, 4);
x_186 = l_Lean_Name_mkStr1(x_185);
x_187 = l_Lean_Expr_const___override(x_186, x_32);
x_188 = lean_mk_string_unchecked("dvd_eq_true_of_mod_eq_zero", 26, 26);
x_189 = l_Lean_Name_mkStr2(x_29, x_188);
x_190 = l_Lean_Expr_const___override(x_189, x_32);
x_191 = l_Lean_reflBoolTrue;
x_192 = l_Lean_mkApp3(x_190, x_46, x_157, x_191);
if (lean_is_scalar(x_168)) {
 x_193 = lean_alloc_ctor(1, 1, 0);
} else {
 x_193 = x_168;
}
lean_ctor_set(x_193, 0, x_192);
x_194 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_194, 0, x_187);
lean_ctor_set(x_194, 1, x_193);
x_195 = lean_unbox(x_35);
lean_dec(x_35);
lean_ctor_set_uint8(x_194, sizeof(void*)*2, x_195);
x_196 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_196, 0, x_194);
if (lean_is_scalar(x_166)) {
 x_197 = lean_alloc_ctor(0, 2, 0);
} else {
 x_197 = x_166;
}
lean_ctor_set(x_197, 0, x_196);
lean_ctor_set(x_197, 1, x_165);
return x_197;
}
}
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
lean_dec(x_157);
lean_dec(x_156);
lean_dec(x_46);
lean_dec(x_35);
lean_dec(x_29);
x_198 = lean_ctor_get(x_158, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_158, 1);
lean_inc(x_199);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 x_200 = x_158;
} else {
 lean_dec_ref(x_158);
 x_200 = lean_box(0);
}
if (lean_is_scalar(x_200)) {
 x_201 = lean_alloc_ctor(1, 2, 0);
} else {
 x_201 = x_200;
}
lean_ctor_set(x_201, 0, x_198);
lean_ctor_set(x_201, 1, x_199);
return x_201;
}
}
}
}
else
{
uint8_t x_202; 
lean_dec(x_46);
lean_dec(x_35);
lean_dec(x_29);
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_202 = !lean_is_exclusive(x_47);
if (x_202 == 0)
{
return x_47;
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_203 = lean_ctor_get(x_47, 0);
x_204 = lean_ctor_get(x_47, 1);
lean_inc(x_204);
lean_inc(x_203);
lean_dec(x_47);
x_205 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_205, 0, x_203);
lean_ctor_set(x_205, 1, x_204);
return x_205;
}
}
}
}
else
{
uint8_t x_206; 
lean_dec(x_29);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_206 = !lean_is_exclusive(x_34);
if (x_206 == 0)
{
return x_34;
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_207 = lean_ctor_get(x_34, 0);
x_208 = lean_ctor_get(x_34, 1);
lean_inc(x_208);
lean_inc(x_207);
lean_dec(x_34);
x_209 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_209, 0, x_207);
lean_ctor_set(x_209, 1, x_208);
return x_209;
}
}
}
}
}
}
}
block_14:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_12, 0, x_11);
if (lean_is_scalar(x_10)) {
 x_13 = lean_alloc_ctor(0, 2, 0);
} else {
 x_13 = x_10;
}
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_9);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceDvd(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Nat_reduceDvd___redArg(x_1, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceDvd___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Nat_reduceDvd(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceDvd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_5971_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_2 = lean_mk_string_unchecked("Nat", 3, 3);
x_3 = lean_mk_string_unchecked("reduceDvd", 9, 9);
lean_inc(x_2);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_mk_string_unchecked("Dvd", 3, 3);
x_6 = lean_mk_string_unchecked("dvd", 3, 3);
x_7 = l_Lean_Name_mkStr2(x_5, x_6);
x_8 = lean_unsigned_to_nat(4u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Lean_Name_mkStr1(x_2);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_box(3);
x_14 = lean_unsigned_to_nat(5u);
x_15 = lean_mk_empty_array_with_capacity(x_14);
x_16 = lean_array_push(x_15, x_9);
x_17 = lean_array_push(x_16, x_12);
x_18 = lean_array_push(x_17, x_13);
x_19 = lean_array_push(x_18, x_13);
x_20 = lean_array_push(x_19, x_13);
x_21 = lean_alloc_closure((void*)(l_Nat_reduceDvd___boxed), 9, 0);
x_22 = l_Lean_Meta_Simp_registerBuiltinSimproc(x_4, x_20, x_21, x_1);
return x_22;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceDvd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_5973_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Nat", 3, 3);
x_3 = lean_mk_string_unchecked("reduceDvd", 9, 9);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Nat_reduceDvd___boxed), 9, 0);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceDvd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_5975_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Nat", 3, 3);
x_3 = lean_mk_string_unchecked("reduceDvd", 9, 9);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Nat_reduceDvd___boxed), 9, 0);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
lean_object* initialize_Init_Simproc(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Nat_Simproc(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_SafeExponentiation(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_LitValues(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Offset(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Simp_Simproc(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Util(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Simproc(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Simproc(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_SafeExponentiation(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_LitValues(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Offset(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Simproc(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Util(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
if (builtin) {res = l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_559_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_561_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_563_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_597_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_599_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_601_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceMul_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_635_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceMul_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_637_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceMul_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_639_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceSub_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_673_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceSub_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_675_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceSub_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_677_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceDiv_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_711_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceDiv_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_713_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceDiv_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_715_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceMod_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_749_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceMod_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_751_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceMod_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_753_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reducePow_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1170_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reducePow_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1172_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reducePow_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1174_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceAnd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1208_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceAnd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1210_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceAnd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1212_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceXor_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1246_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceXor_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1248_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceXor_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1250_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceOr_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1284_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceOr_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1286_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceOr_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1288_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceShiftLeft_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1322_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceShiftLeft_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1324_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceShiftLeft_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1326_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceShiftRight_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1360_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceShiftRight_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1362_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceShiftRight_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1364_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceGcd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1382_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceGcd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1384_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceGcd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1386_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceLT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1421_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceLT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1423_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceLT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1425_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceGT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1460_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceGT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1462_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceGT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1464_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceBEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1499_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceBEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1501_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceBEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1503_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceBNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1537_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceBNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1539_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceBNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1541_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_isValue_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1713_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_isValue_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1715_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance = _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance);
if (builtin) {res = l___regBuiltin_Nat_reduceEqDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_3864_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceEqDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_3866_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceEqDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_3868_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceBeqDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4101_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceBeqDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4103_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceBeqDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4105_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceBneDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4342_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceBneDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4344_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceBneDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4346_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceLeDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4970_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceLeDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4972_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceLeDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4974_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceSubDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_5560_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceSubDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_5562_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceSubDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_5564_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceDvd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_5971_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceDvd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_5973_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceDvd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_5975_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
