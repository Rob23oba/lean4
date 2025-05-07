// Lean compiler output
// Module: Lean.Meta.Tactic.Simp.BuiltinSimprocs.Int
// Imports: Lean.ToExpr Lean.Meta.LitValues Lean.Meta.Tactic.Simp.BuiltinSimprocs.Nat
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
LEAN_EXPORT lean_object* l_Int_reduceBoolPred___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceMod___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceBNe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceTMod_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1322_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCastCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_evalPropStep___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceNatCast_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_int_mod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_2069_(lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceToNat___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceBinIntNatOp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceSub___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceGE(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceNegSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_2451_(lean_object*);
lean_object* l_Lean_Meta_getNatValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceGT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1955_(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceLE_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1914_(lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceAdd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_isPosValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Int_reducePow_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1838_(lean_object*);
LEAN_EXPORT lean_object* l_Int_isPosValue___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceBdiv___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceToNat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceGE___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceNatCast___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceDiv_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1236_(lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceLE___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceAbs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_2033_(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceDiv___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceFMod___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceToNat_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_2284_(lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceFDiv___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceLT___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceNatCast_x27_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_3501_(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceBmod_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1404_(lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceNatCore___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceNatCore___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceTMod(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_2029_(lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCastCore___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceGE___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceNeg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceNatCast_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_3320_(lean_object*);
LEAN_EXPORT lean_object* l_Int_fromExpr_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceTMod_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1320_(lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceNegSucc___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceBNe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceBEq___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceTMod_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1318_(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceMul_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1164_(lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceToNat___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceBoolPred___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceNeg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceFDiv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Int_reducePow_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1836_(lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceDiv_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1240_(lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceUnary___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceAbs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceAdd___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceGE_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1990_(lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceBmod___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_checkExponent(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceSub___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceMul_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1160_(lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Int_isPosValue_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1088_(lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceUnary___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceMul___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceNegSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_2453_(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceNatCast_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_3316_(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceNatCast_x27_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_3503_(lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceBEq___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceFMod___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_fdiv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceNatCast_x27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceFMod_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1362_(lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceLE(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceToNat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceSub_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1198_(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1124_(lean_object*);
lean_object* l_Lean_Meta_getIntValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceBmod___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceTMod___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceLT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1877_(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceNatCast_x27_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_3505_(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceBNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_2144_(lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceGT___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_pow(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceNatCast_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_3318_(lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceNatCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceNeg___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceFMod_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1364_(lean_object*);
LEAN_EXPORT lean_object* l_Int_reducePow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_fmod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceLE_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1912_(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_2031_(lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceNegSucc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceMul(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceBinIntNatOp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceNegSucc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceUnary___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceMul___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceBoolPred___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceBdiv_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1385_(lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceTDiv___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceDvd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_3020_(lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceBEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceNe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceMod___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceGE_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1994_(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceGE_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1992_(lean_object*);
LEAN_EXPORT lean_object* l_Int_reducePow___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceBmod_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1406_(lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceNatCast_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceFDiv_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1342_(lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceBin___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceTDiv_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1300_(lean_object*);
LEAN_EXPORT lean_object* l_Int_fromExpr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_int_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceNeg_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_910_(lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceMul___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceFMod___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceFMod_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1366_(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceDiv_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1238_(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_2071_(lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceNatCast(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceOfNat___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_bmod___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceDvd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_3024_(lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceMod(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceLT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceNegSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_2449_(lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceUnary(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceNeg_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_912_(lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceNegSucc___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceFDiv___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceNatCast___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1126_(lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceTDiv_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1296_(lean_object*);
LEAN_EXPORT lean_object* l_Int_reducePow___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCastCore___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceBEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_2106_(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceTDiv_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1298_(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceMod_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1278_(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Int_reducePow_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1834_(lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceBin(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceTDiv___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceBEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_2108_(lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceBNe___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceLE___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceBmod(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceOfNat___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_registerBuiltinSimproc(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceAdd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceSub___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceBinPred___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceTMod___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceTDiv___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceFDiv_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1344_(lean_object*);
lean_object* l_Lean_Meta_Simp_registerBuiltinDSimproc(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_matchesInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceMul_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1162_(lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceBin___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceOfNat_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_2611_(lean_object*);
LEAN_EXPORT lean_object* l_Int_fromExpr_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceOfNat_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_2613_(lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceAbs___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceBEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_2110_(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceBdiv_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1383_(lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceBdiv___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceLT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1873_(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceGT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1953_(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceBdiv_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1387_(lean_object*);
lean_object* l_Int_toNat(lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceBmod___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_isPosValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceAdd___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceBinIntNatOp___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceLT___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceLE_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1916_(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceMod_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1276_(lean_object*);
uint8_t l_instDecidableNot___redArg(uint8_t);
LEAN_EXPORT lean_object* l_Int_reduceOfNat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceDvd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_reflBoolTrue;
LEAN_EXPORT lean_object* l_Int_reduceEq___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceNe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceSub(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceFDiv___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceBin___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceDvd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_addSimprocBuiltinAttr(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_isPosValue___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceAbs___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceAbs_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_2266_(lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceBdiv___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reducePow___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceNatCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceBinPred(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceGT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceSub_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1202_(lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceBinPred___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instToExprInt_mkNat(lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceTDiv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceBEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceBNe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_2067_(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceGT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1951_(lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceDvd___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceDvd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_3022_(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceSub_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1200_(lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceDiv___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceFMod(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceBinIntNatOp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceMod_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1274_(lean_object*);
lean_object* lean_int_neg(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceBmod_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1408_(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceAbs_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_2264_(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Int_isPosValue_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1086_(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceToNat_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_2286_(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceNeg_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_914_(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1122_(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceLT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1875_(lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceDiv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceDiv___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceBdiv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceOfNat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceBNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_2148_(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceToNat_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_2288_(lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceNatCast_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceNeg___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceNatCast___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceBoolPred(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceTMod___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceFDiv_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1340_(lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceNe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceBNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_2146_(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceOfNat_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_2609_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCastCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceGT___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceMod___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceBinPred___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_fromExpr_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_bdiv___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceAbs_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_2268_(lean_object*);
LEAN_EXPORT lean_object* l_Int_fromExpr_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_getIntValue_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Int_fromExpr_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_getIntValue_x3f(x_1, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Int_fromExpr_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Int_fromExpr_x3f___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Int_fromExpr_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Int_fromExpr_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Int_reduceUnary___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_15 = l_Lean_Meta_getIntValue_x3f(x_14, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_18 = x_15;
} else {
 lean_dec_ref(x_15);
 x_18 = lean_box(0);
}
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_18);
lean_dec(x_3);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_17);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_26 = lean_ctor_get(x_16, 0);
lean_inc(x_26);
lean_dec(x_16);
x_27 = lean_apply_1(x_3, x_26);
x_28 = lean_unsigned_to_nat(0u);
x_29 = lean_nat_to_int(x_28);
x_30 = lean_int_dec_le(x_29, x_27);
lean_dec(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_31 = lean_mk_string_unchecked("Neg", 3, 3);
x_32 = lean_mk_string_unchecked("neg", 3, 3);
x_33 = l_Lean_Name_mkStr2(x_31, x_32);
x_34 = l_Lean_Level_ofNat(x_28);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_Lean_Expr_const___override(x_33, x_36);
x_38 = lean_mk_string_unchecked("Int", 3, 3);
lean_inc(x_38);
x_39 = l_Lean_Name_mkStr1(x_38);
x_40 = l_Lean_Expr_const___override(x_39, x_35);
x_41 = lean_mk_string_unchecked("instNegInt", 10, 10);
x_42 = l_Lean_Name_mkStr2(x_38, x_41);
x_43 = l_Lean_Expr_const___override(x_42, x_35);
x_44 = lean_int_neg(x_27);
lean_dec(x_27);
x_45 = l_Int_toNat(x_44);
lean_dec(x_44);
x_46 = l_Lean_instToExprInt_mkNat(x_45);
x_47 = l_Lean_mkApp3(x_37, x_40, x_43, x_46);
x_19 = x_47;
goto block_22;
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = l_Int_toNat(x_27);
lean_dec(x_27);
x_49 = l_Lean_instToExprInt_mkNat(x_48);
x_19 = x_49;
goto block_22;
}
}
block_22:
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
if (lean_is_scalar(x_18)) {
 x_21 = lean_alloc_ctor(0, 2, 0);
} else {
 x_21 = x_18;
}
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_17);
return x_21;
}
}
else
{
uint8_t x_50; 
lean_dec(x_3);
x_50 = !lean_is_exclusive(x_15);
if (x_50 == 0)
{
return x_15;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_15, 0);
x_52 = lean_ctor_get(x_15, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_15);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_reduceUnary(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
x_18 = l_Lean_Meta_getIntValue_x3f(x_17, x_8, x_9, x_10, x_11, x_12);
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
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_21);
lean_dec(x_3);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_20);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_29 = lean_ctor_get(x_19, 0);
lean_inc(x_29);
lean_dec(x_19);
x_30 = lean_apply_1(x_3, x_29);
x_31 = lean_unsigned_to_nat(0u);
x_32 = lean_nat_to_int(x_31);
x_33 = lean_int_dec_le(x_32, x_30);
lean_dec(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_34 = lean_mk_string_unchecked("Neg", 3, 3);
x_35 = lean_mk_string_unchecked("neg", 3, 3);
x_36 = l_Lean_Name_mkStr2(x_34, x_35);
x_37 = l_Lean_Level_ofNat(x_31);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Lean_Expr_const___override(x_36, x_39);
x_41 = lean_mk_string_unchecked("Int", 3, 3);
lean_inc(x_41);
x_42 = l_Lean_Name_mkStr1(x_41);
x_43 = l_Lean_Expr_const___override(x_42, x_38);
x_44 = lean_mk_string_unchecked("instNegInt", 10, 10);
x_45 = l_Lean_Name_mkStr2(x_41, x_44);
x_46 = l_Lean_Expr_const___override(x_45, x_38);
x_47 = lean_int_neg(x_30);
lean_dec(x_30);
x_48 = l_Int_toNat(x_47);
lean_dec(x_47);
x_49 = l_Lean_instToExprInt_mkNat(x_48);
x_50 = l_Lean_mkApp3(x_40, x_43, x_46, x_49);
x_22 = x_50;
goto block_25;
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = l_Int_toNat(x_30);
lean_dec(x_30);
x_52 = l_Lean_instToExprInt_mkNat(x_51);
x_22 = x_52;
goto block_25;
}
}
block_25:
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_22);
if (lean_is_scalar(x_21)) {
 x_24 = lean_alloc_ctor(0, 2, 0);
} else {
 x_24 = x_21;
}
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_20);
return x_24;
}
}
else
{
uint8_t x_53; 
lean_dec(x_3);
x_53 = !lean_is_exclusive(x_18);
if (x_53 == 0)
{
return x_18;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_18, 0);
x_55 = lean_ctor_get(x_18, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_18);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_reduceUnary___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Int_reduceUnary___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Int_reduceUnary___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Int_reduceUnary(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Int_reduceBin___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_16 = l_Lean_Meta_getIntValue_x3f(x_15, x_5, x_6, x_7, x_8, x_9);
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
x_32 = l_Lean_Meta_getIntValue_x3f(x_31, x_5, x_6, x_7, x_8, x_27);
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
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
lean_free_object(x_16);
x_42 = lean_ctor_get(x_33, 0);
lean_inc(x_42);
lean_dec(x_33);
x_43 = lean_apply_2(x_3, x_29, x_42);
x_44 = lean_unsigned_to_nat(0u);
x_45 = lean_nat_to_int(x_44);
x_46 = lean_int_dec_le(x_45, x_43);
lean_dec(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_47 = lean_mk_string_unchecked("Neg", 3, 3);
x_48 = lean_mk_string_unchecked("neg", 3, 3);
x_49 = l_Lean_Name_mkStr2(x_47, x_48);
x_50 = l_Lean_Level_ofNat(x_44);
x_51 = lean_box(0);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = l_Lean_Expr_const___override(x_49, x_52);
x_54 = lean_mk_string_unchecked("Int", 3, 3);
lean_inc(x_54);
x_55 = l_Lean_Name_mkStr1(x_54);
x_56 = l_Lean_Expr_const___override(x_55, x_51);
x_57 = lean_mk_string_unchecked("instNegInt", 10, 10);
x_58 = l_Lean_Name_mkStr2(x_54, x_57);
x_59 = l_Lean_Expr_const___override(x_58, x_51);
x_60 = lean_int_neg(x_43);
lean_dec(x_43);
x_61 = l_Int_toNat(x_60);
lean_dec(x_60);
x_62 = l_Lean_instToExprInt_mkNat(x_61);
x_63 = l_Lean_mkApp3(x_53, x_56, x_59, x_62);
x_36 = x_63;
goto block_39;
}
else
{
lean_object* x_64; lean_object* x_65; 
x_64 = l_Int_toNat(x_43);
lean_dec(x_43);
x_65 = l_Lean_instToExprInt_mkNat(x_64);
x_36 = x_65;
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
uint8_t x_66; 
lean_dec(x_30);
lean_dec(x_29);
lean_free_object(x_16);
lean_dec(x_3);
x_66 = !lean_is_exclusive(x_32);
if (x_66 == 0)
{
return x_32;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_32, 0);
x_68 = lean_ctor_get(x_32, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_32);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_70 = lean_ctor_get(x_16, 1);
lean_inc(x_70);
lean_dec(x_16);
x_71 = lean_ctor_get(x_17, 0);
lean_inc(x_71);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 x_72 = x_17;
} else {
 lean_dec_ref(x_17);
 x_72 = lean_box(0);
}
x_73 = l_Lean_Expr_appArg_x21(x_4);
x_74 = l_Lean_Meta_getIntValue_x3f(x_73, x_5, x_6, x_7, x_8, x_70);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_77 = x_74;
} else {
 lean_dec_ref(x_74);
 x_77 = lean_box(0);
}
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_77);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_3);
x_82 = lean_box(0);
x_83 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_83, 0, x_82);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_76);
return x_84;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_85 = lean_ctor_get(x_75, 0);
lean_inc(x_85);
lean_dec(x_75);
x_86 = lean_apply_2(x_3, x_71, x_85);
x_87 = lean_unsigned_to_nat(0u);
x_88 = lean_nat_to_int(x_87);
x_89 = lean_int_dec_le(x_88, x_86);
lean_dec(x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_90 = lean_mk_string_unchecked("Neg", 3, 3);
x_91 = lean_mk_string_unchecked("neg", 3, 3);
x_92 = l_Lean_Name_mkStr2(x_90, x_91);
x_93 = l_Lean_Level_ofNat(x_87);
x_94 = lean_box(0);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
x_96 = l_Lean_Expr_const___override(x_92, x_95);
x_97 = lean_mk_string_unchecked("Int", 3, 3);
lean_inc(x_97);
x_98 = l_Lean_Name_mkStr1(x_97);
x_99 = l_Lean_Expr_const___override(x_98, x_94);
x_100 = lean_mk_string_unchecked("instNegInt", 10, 10);
x_101 = l_Lean_Name_mkStr2(x_97, x_100);
x_102 = l_Lean_Expr_const___override(x_101, x_94);
x_103 = lean_int_neg(x_86);
lean_dec(x_86);
x_104 = l_Int_toNat(x_103);
lean_dec(x_103);
x_105 = l_Lean_instToExprInt_mkNat(x_104);
x_106 = l_Lean_mkApp3(x_96, x_99, x_102, x_105);
x_78 = x_106;
goto block_81;
}
else
{
lean_object* x_107; lean_object* x_108; 
x_107 = l_Int_toNat(x_86);
lean_dec(x_86);
x_108 = l_Lean_instToExprInt_mkNat(x_107);
x_78 = x_108;
goto block_81;
}
}
block_81:
{
lean_object* x_79; lean_object* x_80; 
if (lean_is_scalar(x_72)) {
 x_79 = lean_alloc_ctor(0, 1, 0);
} else {
 x_79 = x_72;
 lean_ctor_set_tag(x_79, 0);
}
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
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_3);
x_109 = lean_ctor_get(x_74, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_74, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_111 = x_74;
} else {
 lean_dec_ref(x_74);
 x_111 = lean_box(0);
}
if (lean_is_scalar(x_111)) {
 x_112 = lean_alloc_ctor(1, 2, 0);
} else {
 x_112 = x_111;
}
lean_ctor_set(x_112, 0, x_109);
lean_ctor_set(x_112, 1, x_110);
return x_112;
}
}
}
}
else
{
uint8_t x_113; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_113 = !lean_is_exclusive(x_16);
if (x_113 == 0)
{
return x_16;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_16, 0);
x_115 = lean_ctor_get(x_16, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_16);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_reduceBin(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
x_19 = l_Lean_Meta_getIntValue_x3f(x_18, x_8, x_9, x_10, x_11, x_12);
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
x_35 = l_Lean_Meta_getIntValue_x3f(x_34, x_8, x_9, x_10, x_11, x_30);
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
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
lean_free_object(x_19);
x_45 = lean_ctor_get(x_36, 0);
lean_inc(x_45);
lean_dec(x_36);
x_46 = lean_apply_2(x_3, x_32, x_45);
x_47 = lean_unsigned_to_nat(0u);
x_48 = lean_nat_to_int(x_47);
x_49 = lean_int_dec_le(x_48, x_46);
lean_dec(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_50 = lean_mk_string_unchecked("Neg", 3, 3);
x_51 = lean_mk_string_unchecked("neg", 3, 3);
x_52 = l_Lean_Name_mkStr2(x_50, x_51);
x_53 = l_Lean_Level_ofNat(x_47);
x_54 = lean_box(0);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
x_56 = l_Lean_Expr_const___override(x_52, x_55);
x_57 = lean_mk_string_unchecked("Int", 3, 3);
lean_inc(x_57);
x_58 = l_Lean_Name_mkStr1(x_57);
x_59 = l_Lean_Expr_const___override(x_58, x_54);
x_60 = lean_mk_string_unchecked("instNegInt", 10, 10);
x_61 = l_Lean_Name_mkStr2(x_57, x_60);
x_62 = l_Lean_Expr_const___override(x_61, x_54);
x_63 = lean_int_neg(x_46);
lean_dec(x_46);
x_64 = l_Int_toNat(x_63);
lean_dec(x_63);
x_65 = l_Lean_instToExprInt_mkNat(x_64);
x_66 = l_Lean_mkApp3(x_56, x_59, x_62, x_65);
x_39 = x_66;
goto block_42;
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = l_Int_toNat(x_46);
lean_dec(x_46);
x_68 = l_Lean_instToExprInt_mkNat(x_67);
x_39 = x_68;
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
uint8_t x_69; 
lean_dec(x_33);
lean_dec(x_32);
lean_free_object(x_19);
lean_dec(x_3);
x_69 = !lean_is_exclusive(x_35);
if (x_69 == 0)
{
return x_35;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_35, 0);
x_71 = lean_ctor_get(x_35, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_35);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_73 = lean_ctor_get(x_19, 1);
lean_inc(x_73);
lean_dec(x_19);
x_74 = lean_ctor_get(x_20, 0);
lean_inc(x_74);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 x_75 = x_20;
} else {
 lean_dec_ref(x_20);
 x_75 = lean_box(0);
}
x_76 = l_Lean_Expr_appArg_x21(x_4);
x_77 = l_Lean_Meta_getIntValue_x3f(x_76, x_8, x_9, x_10, x_11, x_73);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_80 = x_77;
} else {
 lean_dec_ref(x_77);
 x_80 = lean_box(0);
}
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_80);
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_3);
x_85 = lean_box(0);
x_86 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_86, 0, x_85);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_79);
return x_87;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; 
x_88 = lean_ctor_get(x_78, 0);
lean_inc(x_88);
lean_dec(x_78);
x_89 = lean_apply_2(x_3, x_74, x_88);
x_90 = lean_unsigned_to_nat(0u);
x_91 = lean_nat_to_int(x_90);
x_92 = lean_int_dec_le(x_91, x_89);
lean_dec(x_91);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_93 = lean_mk_string_unchecked("Neg", 3, 3);
x_94 = lean_mk_string_unchecked("neg", 3, 3);
x_95 = l_Lean_Name_mkStr2(x_93, x_94);
x_96 = l_Lean_Level_ofNat(x_90);
x_97 = lean_box(0);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
x_99 = l_Lean_Expr_const___override(x_95, x_98);
x_100 = lean_mk_string_unchecked("Int", 3, 3);
lean_inc(x_100);
x_101 = l_Lean_Name_mkStr1(x_100);
x_102 = l_Lean_Expr_const___override(x_101, x_97);
x_103 = lean_mk_string_unchecked("instNegInt", 10, 10);
x_104 = l_Lean_Name_mkStr2(x_100, x_103);
x_105 = l_Lean_Expr_const___override(x_104, x_97);
x_106 = lean_int_neg(x_89);
lean_dec(x_89);
x_107 = l_Int_toNat(x_106);
lean_dec(x_106);
x_108 = l_Lean_instToExprInt_mkNat(x_107);
x_109 = l_Lean_mkApp3(x_99, x_102, x_105, x_108);
x_81 = x_109;
goto block_84;
}
else
{
lean_object* x_110; lean_object* x_111; 
x_110 = l_Int_toNat(x_89);
lean_dec(x_89);
x_111 = l_Lean_instToExprInt_mkNat(x_110);
x_81 = x_111;
goto block_84;
}
}
block_84:
{
lean_object* x_82; lean_object* x_83; 
if (lean_is_scalar(x_75)) {
 x_82 = lean_alloc_ctor(0, 1, 0);
} else {
 x_82 = x_75;
 lean_ctor_set_tag(x_82, 0);
}
lean_ctor_set(x_82, 0, x_81);
if (lean_is_scalar(x_80)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_80;
}
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_79);
return x_83;
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_3);
x_112 = lean_ctor_get(x_77, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_77, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_114 = x_77;
} else {
 lean_dec_ref(x_77);
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
}
else
{
uint8_t x_116; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
x_116 = !lean_is_exclusive(x_19);
if (x_116 == 0)
{
return x_19;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_19, 0);
x_118 = lean_ctor_get(x_19, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_19);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
return x_119;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_reduceBin___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Int_reduceBin___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Int_reduceBin___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Int_reduceBin(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Int_reduceBinIntNatOp___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_unsigned_to_nat(2u);
x_10 = l_Lean_Expr_isAppOfArity(x_3, x_1, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_8);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = l_Lean_Expr_appFn_x21(x_3);
x_15 = l_Lean_Expr_appArg_x21(x_14);
lean_dec(x_14);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_16 = l_Lean_Meta_getIntValue_x3f(x_15, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
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
x_31 = l_Lean_Expr_appArg_x21(x_3);
x_32 = l_Lean_Meta_getNatValue_x3f(x_31, x_4, x_5, x_6, x_7, x_27);
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
lean_dec(x_2);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_16, 1, x_34);
lean_ctor_set(x_16, 0, x_41);
return x_16;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
lean_free_object(x_16);
x_42 = lean_ctor_get(x_33, 0);
lean_inc(x_42);
lean_dec(x_33);
x_43 = lean_apply_2(x_2, x_29, x_42);
x_44 = lean_unsigned_to_nat(0u);
x_45 = lean_nat_to_int(x_44);
x_46 = lean_int_dec_le(x_45, x_43);
lean_dec(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_47 = lean_mk_string_unchecked("Neg", 3, 3);
x_48 = lean_mk_string_unchecked("neg", 3, 3);
x_49 = l_Lean_Name_mkStr2(x_47, x_48);
x_50 = l_Lean_Level_ofNat(x_44);
x_51 = lean_box(0);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = l_Lean_Expr_const___override(x_49, x_52);
x_54 = lean_mk_string_unchecked("Int", 3, 3);
lean_inc(x_54);
x_55 = l_Lean_Name_mkStr1(x_54);
x_56 = l_Lean_Expr_const___override(x_55, x_51);
x_57 = lean_mk_string_unchecked("instNegInt", 10, 10);
x_58 = l_Lean_Name_mkStr2(x_54, x_57);
x_59 = l_Lean_Expr_const___override(x_58, x_51);
x_60 = lean_int_neg(x_43);
lean_dec(x_43);
x_61 = l_Int_toNat(x_60);
lean_dec(x_60);
x_62 = l_Lean_instToExprInt_mkNat(x_61);
x_63 = l_Lean_mkApp3(x_53, x_56, x_59, x_62);
x_36 = x_63;
goto block_39;
}
else
{
lean_object* x_64; lean_object* x_65; 
x_64 = l_Int_toNat(x_43);
lean_dec(x_43);
x_65 = l_Lean_instToExprInt_mkNat(x_64);
x_36 = x_65;
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
uint8_t x_66; 
lean_dec(x_30);
lean_dec(x_29);
lean_free_object(x_16);
lean_dec(x_2);
x_66 = !lean_is_exclusive(x_32);
if (x_66 == 0)
{
return x_32;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_32, 0);
x_68 = lean_ctor_get(x_32, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_32);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_70 = lean_ctor_get(x_16, 1);
lean_inc(x_70);
lean_dec(x_16);
x_71 = lean_ctor_get(x_17, 0);
lean_inc(x_71);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 x_72 = x_17;
} else {
 lean_dec_ref(x_17);
 x_72 = lean_box(0);
}
x_73 = l_Lean_Expr_appArg_x21(x_3);
x_74 = l_Lean_Meta_getNatValue_x3f(x_73, x_4, x_5, x_6, x_7, x_70);
lean_dec(x_73);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_77 = x_74;
} else {
 lean_dec_ref(x_74);
 x_77 = lean_box(0);
}
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_77);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_2);
x_82 = lean_box(0);
x_83 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_83, 0, x_82);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_76);
return x_84;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_85 = lean_ctor_get(x_75, 0);
lean_inc(x_85);
lean_dec(x_75);
x_86 = lean_apply_2(x_2, x_71, x_85);
x_87 = lean_unsigned_to_nat(0u);
x_88 = lean_nat_to_int(x_87);
x_89 = lean_int_dec_le(x_88, x_86);
lean_dec(x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_90 = lean_mk_string_unchecked("Neg", 3, 3);
x_91 = lean_mk_string_unchecked("neg", 3, 3);
x_92 = l_Lean_Name_mkStr2(x_90, x_91);
x_93 = l_Lean_Level_ofNat(x_87);
x_94 = lean_box(0);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
x_96 = l_Lean_Expr_const___override(x_92, x_95);
x_97 = lean_mk_string_unchecked("Int", 3, 3);
lean_inc(x_97);
x_98 = l_Lean_Name_mkStr1(x_97);
x_99 = l_Lean_Expr_const___override(x_98, x_94);
x_100 = lean_mk_string_unchecked("instNegInt", 10, 10);
x_101 = l_Lean_Name_mkStr2(x_97, x_100);
x_102 = l_Lean_Expr_const___override(x_101, x_94);
x_103 = lean_int_neg(x_86);
lean_dec(x_86);
x_104 = l_Int_toNat(x_103);
lean_dec(x_103);
x_105 = l_Lean_instToExprInt_mkNat(x_104);
x_106 = l_Lean_mkApp3(x_96, x_99, x_102, x_105);
x_78 = x_106;
goto block_81;
}
else
{
lean_object* x_107; lean_object* x_108; 
x_107 = l_Int_toNat(x_86);
lean_dec(x_86);
x_108 = l_Lean_instToExprInt_mkNat(x_107);
x_78 = x_108;
goto block_81;
}
}
block_81:
{
lean_object* x_79; lean_object* x_80; 
if (lean_is_scalar(x_72)) {
 x_79 = lean_alloc_ctor(0, 1, 0);
} else {
 x_79 = x_72;
 lean_ctor_set_tag(x_79, 0);
}
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
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_2);
x_109 = lean_ctor_get(x_74, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_74, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_111 = x_74;
} else {
 lean_dec_ref(x_74);
 x_111 = lean_box(0);
}
if (lean_is_scalar(x_111)) {
 x_112 = lean_alloc_ctor(1, 2, 0);
} else {
 x_112 = x_111;
}
lean_ctor_set(x_112, 0, x_109);
lean_ctor_set(x_112, 1, x_110);
return x_112;
}
}
}
}
else
{
uint8_t x_113; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_113 = !lean_is_exclusive(x_16);
if (x_113 == 0)
{
return x_16;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_16, 0);
x_115 = lean_ctor_get(x_16, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_16);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_reduceBinIntNatOp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Int_reduceBinIntNatOp___redArg(x_1, x_2, x_3, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Int_reduceBinIntNatOp___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Int_reduceBinIntNatOp___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Int_reduceBinIntNatOp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Int_reduceBinIntNatOp(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Int_reduceBinPred___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_16 = l_Lean_Meta_getIntValue_x3f(x_15, x_5, x_6, x_7, x_8, x_9);
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
x_30 = l_Lean_Meta_getIntValue_x3f(x_29, x_5, x_6, x_7, x_8, x_26);
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
x_49 = l_Lean_Meta_getIntValue_x3f(x_48, x_5, x_6, x_7, x_8, x_26);
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
LEAN_EXPORT lean_object* l_Int_reduceBinPred(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
x_19 = l_Lean_Meta_getIntValue_x3f(x_18, x_8, x_9, x_10, x_11, x_12);
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
x_33 = l_Lean_Meta_getIntValue_x3f(x_32, x_8, x_9, x_10, x_11, x_29);
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
x_52 = l_Lean_Meta_getIntValue_x3f(x_51, x_8, x_9, x_10, x_11, x_29);
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
LEAN_EXPORT lean_object* l_Int_reduceBinPred___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Int_reduceBinPred___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Int_reduceBinPred___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Int_reduceBinPred(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Int_reduceBoolPred___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_16 = l_Lean_Meta_getIntValue_x3f(x_15, x_5, x_6, x_7, x_8, x_9);
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
x_32 = l_Lean_Meta_getIntValue_x3f(x_31, x_5, x_6, x_7, x_8, x_27);
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
x_63 = l_Lean_Meta_getIntValue_x3f(x_62, x_5, x_6, x_7, x_8, x_59);
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
LEAN_EXPORT lean_object* l_Int_reduceBoolPred(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
x_19 = l_Lean_Meta_getIntValue_x3f(x_18, x_8, x_9, x_10, x_11, x_12);
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
x_35 = l_Lean_Meta_getIntValue_x3f(x_34, x_8, x_9, x_10, x_11, x_30);
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
x_66 = l_Lean_Meta_getIntValue_x3f(x_65, x_8, x_9, x_10, x_11, x_62);
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
LEAN_EXPORT lean_object* l_Int_reduceBoolPred___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Int_reduceBoolPred___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Int_reduceBoolPred___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Int_reduceBoolPred(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Int_reduceNeg___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_15; uint8_t x_16; 
lean_inc(x_1);
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
lean_dec(x_1);
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
lean_dec(x_1);
goto block_14;
}
else
{
lean_object* x_19; uint8_t x_20; 
x_19 = l_Lean_Expr_appFnCleanup___redArg(x_17);
x_20 = l_Lean_Expr_isApp(x_19);
if (x_20 == 0)
{
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
goto block_14;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_21 = l_Lean_Expr_appFnCleanup___redArg(x_19);
x_22 = lean_mk_string_unchecked("Neg", 3, 3);
x_23 = lean_mk_string_unchecked("neg", 3, 3);
x_24 = l_Lean_Name_mkStr2(x_22, x_23);
x_25 = l_Lean_Expr_isConstOf(x_21, x_24);
lean_dec(x_21);
if (x_25 == 0)
{
lean_dec(x_24);
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
goto block_14;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
lean_dec(x_10);
x_26 = lean_ctor_get(x_15, 1);
lean_inc(x_26);
lean_dec(x_15);
x_27 = lean_mk_string_unchecked("OfNat", 5, 5);
x_28 = lean_mk_string_unchecked("ofNat", 5, 5);
x_29 = l_Lean_Name_mkStr2(x_27, x_28);
x_30 = lean_unsigned_to_nat(3u);
x_31 = l_Lean_Expr_isAppOfArity(x_26, x_29, x_30);
lean_dec(x_29);
if (x_31 == 0)
{
lean_object* x_32; 
lean_dec(x_1);
x_32 = l_Lean_Meta_getIntValue_x3f(x_26, x_2, x_3, x_4, x_5, x_9);
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
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_35);
lean_dec(x_24);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_34);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_43 = lean_ctor_get(x_33, 0);
lean_inc(x_43);
lean_dec(x_33);
x_44 = lean_int_neg(x_43);
lean_dec(x_43);
x_45 = lean_unsigned_to_nat(0u);
x_46 = lean_nat_to_int(x_45);
x_47 = lean_int_dec_le(x_46, x_44);
lean_dec(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_48 = l_Lean_Level_ofNat(x_45);
x_49 = lean_box(0);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
x_51 = l_Lean_Expr_const___override(x_24, x_50);
x_52 = lean_mk_string_unchecked("Int", 3, 3);
lean_inc(x_52);
x_53 = l_Lean_Name_mkStr1(x_52);
x_54 = l_Lean_Expr_const___override(x_53, x_49);
x_55 = lean_mk_string_unchecked("instNegInt", 10, 10);
x_56 = l_Lean_Name_mkStr2(x_52, x_55);
x_57 = l_Lean_Expr_const___override(x_56, x_49);
x_58 = lean_int_neg(x_44);
lean_dec(x_44);
x_59 = l_Int_toNat(x_58);
lean_dec(x_58);
x_60 = l_Lean_instToExprInt_mkNat(x_59);
x_61 = l_Lean_mkApp3(x_51, x_54, x_57, x_60);
x_36 = x_61;
goto block_39;
}
else
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_24);
x_62 = l_Int_toNat(x_44);
lean_dec(x_44);
x_63 = l_Lean_instToExprInt_mkNat(x_62);
x_36 = x_63;
goto block_39;
}
}
block_39:
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_alloc_ctor(0, 1, 0);
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
uint8_t x_64; 
lean_dec(x_24);
x_64 = !lean_is_exclusive(x_32);
if (x_64 == 0)
{
return x_32;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_32, 0);
x_66 = lean_ctor_get(x_32, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_32);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
else
{
lean_object* x_68; lean_object* x_69; 
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_68 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_68, 0, x_1);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_9);
return x_69;
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
LEAN_EXPORT lean_object* l_Int_reduceNeg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Int_reduceNeg___redArg(x_1, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Int_reduceNeg___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Int_reduceNeg___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Int_reduceNeg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Int_reduceNeg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceNeg_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_910_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_2 = lean_mk_string_unchecked("Int", 3, 3);
x_3 = lean_mk_string_unchecked("reduceNeg", 9, 9);
lean_inc(x_2);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_mk_string_unchecked("Neg", 3, 3);
x_6 = lean_mk_string_unchecked("neg", 3, 3);
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
x_20 = lean_alloc_closure((void*)(l_Int_reduceNeg___boxed), 9, 0);
x_21 = l_Lean_Meta_Simp_registerBuiltinDSimproc(x_4, x_19, x_20, x_1);
return x_21;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceNeg_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_912_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Int", 3, 3);
x_3 = lean_mk_string_unchecked("reduceNeg", 9, 9);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Int_reduceNeg___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceNeg_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_914_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Int", 3, 3);
x_3 = lean_mk_string_unchecked("reduceNeg", 9, 9);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Int_reduceNeg___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Int_isPosValue___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Int_isPosValue(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Int_isPosValue___redArg(x_1, x_6, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Int_isPosValue___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Int_isPosValue___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Int_isPosValue___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Int_isPosValue(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l___regBuiltin_Int_isPosValue_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1086_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_2 = lean_mk_string_unchecked("Int", 3, 3);
x_3 = lean_mk_string_unchecked("isPosValue", 10, 10);
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
x_20 = lean_alloc_closure((void*)(l_Int_isPosValue___boxed), 9, 0);
x_21 = l_Lean_Meta_Simp_registerBuiltinDSimproc(x_4, x_19, x_20, x_1);
return x_21;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Int_isPosValue_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1088_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Int", 3, 3);
x_3 = lean_mk_string_unchecked("isPosValue", 10, 10);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Int_isPosValue___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Int_reduceAdd___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_17 = l_Lean_Meta_getIntValue_x3f(x_16, x_2, x_3, x_4, x_5, x_6);
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
x_33 = l_Lean_Meta_getIntValue_x3f(x_32, x_2, x_3, x_4, x_5, x_28);
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
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
lean_free_object(x_17);
x_43 = lean_ctor_get(x_34, 0);
lean_inc(x_43);
lean_dec(x_34);
x_44 = lean_int_add(x_30, x_43);
lean_dec(x_43);
lean_dec(x_30);
x_45 = lean_unsigned_to_nat(0u);
x_46 = lean_nat_to_int(x_45);
x_47 = lean_int_dec_le(x_46, x_44);
lean_dec(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_48 = lean_mk_string_unchecked("Neg", 3, 3);
x_49 = lean_mk_string_unchecked("neg", 3, 3);
x_50 = l_Lean_Name_mkStr2(x_48, x_49);
x_51 = l_Lean_Level_ofNat(x_45);
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = l_Lean_Expr_const___override(x_50, x_53);
x_55 = lean_mk_string_unchecked("Int", 3, 3);
lean_inc(x_55);
x_56 = l_Lean_Name_mkStr1(x_55);
x_57 = l_Lean_Expr_const___override(x_56, x_52);
x_58 = lean_mk_string_unchecked("instNegInt", 10, 10);
x_59 = l_Lean_Name_mkStr2(x_55, x_58);
x_60 = l_Lean_Expr_const___override(x_59, x_52);
x_61 = lean_int_neg(x_44);
lean_dec(x_44);
x_62 = l_Int_toNat(x_61);
lean_dec(x_61);
x_63 = l_Lean_instToExprInt_mkNat(x_62);
x_64 = l_Lean_mkApp3(x_54, x_57, x_60, x_63);
x_37 = x_64;
goto block_40;
}
else
{
lean_object* x_65; lean_object* x_66; 
x_65 = l_Int_toNat(x_44);
lean_dec(x_44);
x_66 = l_Lean_instToExprInt_mkNat(x_65);
x_37 = x_66;
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
uint8_t x_67; 
lean_dec(x_31);
lean_dec(x_30);
lean_free_object(x_17);
x_67 = !lean_is_exclusive(x_33);
if (x_67 == 0)
{
return x_33;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_33, 0);
x_69 = lean_ctor_get(x_33, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_33);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_71 = lean_ctor_get(x_17, 1);
lean_inc(x_71);
lean_dec(x_17);
x_72 = lean_ctor_get(x_18, 0);
lean_inc(x_72);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 x_73 = x_18;
} else {
 lean_dec_ref(x_18);
 x_73 = lean_box(0);
}
x_74 = l_Lean_Expr_appArg_x21(x_1);
x_75 = l_Lean_Meta_getIntValue_x3f(x_74, x_2, x_3, x_4, x_5, x_71);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_78 = x_75;
} else {
 lean_dec_ref(x_75);
 x_78 = lean_box(0);
}
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_78);
lean_dec(x_73);
lean_dec(x_72);
x_83 = lean_box(0);
x_84 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_84, 0, x_83);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_77);
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_86 = lean_ctor_get(x_76, 0);
lean_inc(x_86);
lean_dec(x_76);
x_87 = lean_int_add(x_72, x_86);
lean_dec(x_86);
lean_dec(x_72);
x_88 = lean_unsigned_to_nat(0u);
x_89 = lean_nat_to_int(x_88);
x_90 = lean_int_dec_le(x_89, x_87);
lean_dec(x_89);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_91 = lean_mk_string_unchecked("Neg", 3, 3);
x_92 = lean_mk_string_unchecked("neg", 3, 3);
x_93 = l_Lean_Name_mkStr2(x_91, x_92);
x_94 = l_Lean_Level_ofNat(x_88);
x_95 = lean_box(0);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
x_97 = l_Lean_Expr_const___override(x_93, x_96);
x_98 = lean_mk_string_unchecked("Int", 3, 3);
lean_inc(x_98);
x_99 = l_Lean_Name_mkStr1(x_98);
x_100 = l_Lean_Expr_const___override(x_99, x_95);
x_101 = lean_mk_string_unchecked("instNegInt", 10, 10);
x_102 = l_Lean_Name_mkStr2(x_98, x_101);
x_103 = l_Lean_Expr_const___override(x_102, x_95);
x_104 = lean_int_neg(x_87);
lean_dec(x_87);
x_105 = l_Int_toNat(x_104);
lean_dec(x_104);
x_106 = l_Lean_instToExprInt_mkNat(x_105);
x_107 = l_Lean_mkApp3(x_97, x_100, x_103, x_106);
x_79 = x_107;
goto block_82;
}
else
{
lean_object* x_108; lean_object* x_109; 
x_108 = l_Int_toNat(x_87);
lean_dec(x_87);
x_109 = l_Lean_instToExprInt_mkNat(x_108);
x_79 = x_109;
goto block_82;
}
}
block_82:
{
lean_object* x_80; lean_object* x_81; 
if (lean_is_scalar(x_73)) {
 x_80 = lean_alloc_ctor(0, 1, 0);
} else {
 x_80 = x_73;
 lean_ctor_set_tag(x_80, 0);
}
lean_ctor_set(x_80, 0, x_79);
if (lean_is_scalar(x_78)) {
 x_81 = lean_alloc_ctor(0, 2, 0);
} else {
 x_81 = x_78;
}
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_77);
return x_81;
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec(x_73);
lean_dec(x_72);
x_110 = lean_ctor_get(x_75, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_75, 1);
lean_inc(x_111);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_112 = x_75;
} else {
 lean_dec_ref(x_75);
 x_112 = lean_box(0);
}
if (lean_is_scalar(x_112)) {
 x_113 = lean_alloc_ctor(1, 2, 0);
} else {
 x_113 = x_112;
}
lean_ctor_set(x_113, 0, x_110);
lean_ctor_set(x_113, 1, x_111);
return x_113;
}
}
}
}
else
{
uint8_t x_114; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_114 = !lean_is_exclusive(x_17);
if (x_114 == 0)
{
return x_17;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_17, 0);
x_116 = lean_ctor_get(x_17, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_17);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_reduceAdd(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Int_reduceAdd___redArg(x_1, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Int_reduceAdd___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Int_reduceAdd___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Int_reduceAdd___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Int_reduceAdd(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1122_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_2 = lean_mk_string_unchecked("Int", 3, 3);
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
x_23 = lean_alloc_closure((void*)(l_Int_reduceAdd___boxed), 9, 0);
x_24 = l_Lean_Meta_Simp_registerBuiltinDSimproc(x_4, x_22, x_23, x_1);
return x_24;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1124_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Int", 3, 3);
x_3 = lean_mk_string_unchecked("reduceAdd", 9, 9);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Int_reduceAdd___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1126_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Int", 3, 3);
x_3 = lean_mk_string_unchecked("reduceAdd", 9, 9);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Int_reduceAdd___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Int_reduceMul___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_17 = l_Lean_Meta_getIntValue_x3f(x_16, x_2, x_3, x_4, x_5, x_6);
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
x_33 = l_Lean_Meta_getIntValue_x3f(x_32, x_2, x_3, x_4, x_5, x_28);
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
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
lean_free_object(x_17);
x_43 = lean_ctor_get(x_34, 0);
lean_inc(x_43);
lean_dec(x_34);
x_44 = lean_int_mul(x_30, x_43);
lean_dec(x_43);
lean_dec(x_30);
x_45 = lean_unsigned_to_nat(0u);
x_46 = lean_nat_to_int(x_45);
x_47 = lean_int_dec_le(x_46, x_44);
lean_dec(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_48 = lean_mk_string_unchecked("Neg", 3, 3);
x_49 = lean_mk_string_unchecked("neg", 3, 3);
x_50 = l_Lean_Name_mkStr2(x_48, x_49);
x_51 = l_Lean_Level_ofNat(x_45);
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = l_Lean_Expr_const___override(x_50, x_53);
x_55 = lean_mk_string_unchecked("Int", 3, 3);
lean_inc(x_55);
x_56 = l_Lean_Name_mkStr1(x_55);
x_57 = l_Lean_Expr_const___override(x_56, x_52);
x_58 = lean_mk_string_unchecked("instNegInt", 10, 10);
x_59 = l_Lean_Name_mkStr2(x_55, x_58);
x_60 = l_Lean_Expr_const___override(x_59, x_52);
x_61 = lean_int_neg(x_44);
lean_dec(x_44);
x_62 = l_Int_toNat(x_61);
lean_dec(x_61);
x_63 = l_Lean_instToExprInt_mkNat(x_62);
x_64 = l_Lean_mkApp3(x_54, x_57, x_60, x_63);
x_37 = x_64;
goto block_40;
}
else
{
lean_object* x_65; lean_object* x_66; 
x_65 = l_Int_toNat(x_44);
lean_dec(x_44);
x_66 = l_Lean_instToExprInt_mkNat(x_65);
x_37 = x_66;
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
uint8_t x_67; 
lean_dec(x_31);
lean_dec(x_30);
lean_free_object(x_17);
x_67 = !lean_is_exclusive(x_33);
if (x_67 == 0)
{
return x_33;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_33, 0);
x_69 = lean_ctor_get(x_33, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_33);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_71 = lean_ctor_get(x_17, 1);
lean_inc(x_71);
lean_dec(x_17);
x_72 = lean_ctor_get(x_18, 0);
lean_inc(x_72);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 x_73 = x_18;
} else {
 lean_dec_ref(x_18);
 x_73 = lean_box(0);
}
x_74 = l_Lean_Expr_appArg_x21(x_1);
x_75 = l_Lean_Meta_getIntValue_x3f(x_74, x_2, x_3, x_4, x_5, x_71);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_78 = x_75;
} else {
 lean_dec_ref(x_75);
 x_78 = lean_box(0);
}
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_78);
lean_dec(x_73);
lean_dec(x_72);
x_83 = lean_box(0);
x_84 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_84, 0, x_83);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_77);
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_86 = lean_ctor_get(x_76, 0);
lean_inc(x_86);
lean_dec(x_76);
x_87 = lean_int_mul(x_72, x_86);
lean_dec(x_86);
lean_dec(x_72);
x_88 = lean_unsigned_to_nat(0u);
x_89 = lean_nat_to_int(x_88);
x_90 = lean_int_dec_le(x_89, x_87);
lean_dec(x_89);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_91 = lean_mk_string_unchecked("Neg", 3, 3);
x_92 = lean_mk_string_unchecked("neg", 3, 3);
x_93 = l_Lean_Name_mkStr2(x_91, x_92);
x_94 = l_Lean_Level_ofNat(x_88);
x_95 = lean_box(0);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
x_97 = l_Lean_Expr_const___override(x_93, x_96);
x_98 = lean_mk_string_unchecked("Int", 3, 3);
lean_inc(x_98);
x_99 = l_Lean_Name_mkStr1(x_98);
x_100 = l_Lean_Expr_const___override(x_99, x_95);
x_101 = lean_mk_string_unchecked("instNegInt", 10, 10);
x_102 = l_Lean_Name_mkStr2(x_98, x_101);
x_103 = l_Lean_Expr_const___override(x_102, x_95);
x_104 = lean_int_neg(x_87);
lean_dec(x_87);
x_105 = l_Int_toNat(x_104);
lean_dec(x_104);
x_106 = l_Lean_instToExprInt_mkNat(x_105);
x_107 = l_Lean_mkApp3(x_97, x_100, x_103, x_106);
x_79 = x_107;
goto block_82;
}
else
{
lean_object* x_108; lean_object* x_109; 
x_108 = l_Int_toNat(x_87);
lean_dec(x_87);
x_109 = l_Lean_instToExprInt_mkNat(x_108);
x_79 = x_109;
goto block_82;
}
}
block_82:
{
lean_object* x_80; lean_object* x_81; 
if (lean_is_scalar(x_73)) {
 x_80 = lean_alloc_ctor(0, 1, 0);
} else {
 x_80 = x_73;
 lean_ctor_set_tag(x_80, 0);
}
lean_ctor_set(x_80, 0, x_79);
if (lean_is_scalar(x_78)) {
 x_81 = lean_alloc_ctor(0, 2, 0);
} else {
 x_81 = x_78;
}
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_77);
return x_81;
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec(x_73);
lean_dec(x_72);
x_110 = lean_ctor_get(x_75, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_75, 1);
lean_inc(x_111);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_112 = x_75;
} else {
 lean_dec_ref(x_75);
 x_112 = lean_box(0);
}
if (lean_is_scalar(x_112)) {
 x_113 = lean_alloc_ctor(1, 2, 0);
} else {
 x_113 = x_112;
}
lean_ctor_set(x_113, 0, x_110);
lean_ctor_set(x_113, 1, x_111);
return x_113;
}
}
}
}
else
{
uint8_t x_114; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_114 = !lean_is_exclusive(x_17);
if (x_114 == 0)
{
return x_17;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_17, 0);
x_116 = lean_ctor_get(x_17, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_17);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_reduceMul(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Int_reduceMul___redArg(x_1, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Int_reduceMul___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Int_reduceMul___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Int_reduceMul___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Int_reduceMul(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceMul_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1160_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_2 = lean_mk_string_unchecked("Int", 3, 3);
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
x_23 = lean_alloc_closure((void*)(l_Int_reduceMul___boxed), 9, 0);
x_24 = l_Lean_Meta_Simp_registerBuiltinDSimproc(x_4, x_22, x_23, x_1);
return x_24;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceMul_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1162_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Int", 3, 3);
x_3 = lean_mk_string_unchecked("reduceMul", 9, 9);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Int_reduceMul___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceMul_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1164_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Int", 3, 3);
x_3 = lean_mk_string_unchecked("reduceMul", 9, 9);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Int_reduceMul___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Int_reduceSub___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_17 = l_Lean_Meta_getIntValue_x3f(x_16, x_2, x_3, x_4, x_5, x_6);
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
x_33 = l_Lean_Meta_getIntValue_x3f(x_32, x_2, x_3, x_4, x_5, x_28);
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
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
lean_free_object(x_17);
x_43 = lean_ctor_get(x_34, 0);
lean_inc(x_43);
lean_dec(x_34);
x_44 = lean_int_sub(x_30, x_43);
lean_dec(x_43);
lean_dec(x_30);
x_45 = lean_unsigned_to_nat(0u);
x_46 = lean_nat_to_int(x_45);
x_47 = lean_int_dec_le(x_46, x_44);
lean_dec(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_48 = lean_mk_string_unchecked("Neg", 3, 3);
x_49 = lean_mk_string_unchecked("neg", 3, 3);
x_50 = l_Lean_Name_mkStr2(x_48, x_49);
x_51 = l_Lean_Level_ofNat(x_45);
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = l_Lean_Expr_const___override(x_50, x_53);
x_55 = lean_mk_string_unchecked("Int", 3, 3);
lean_inc(x_55);
x_56 = l_Lean_Name_mkStr1(x_55);
x_57 = l_Lean_Expr_const___override(x_56, x_52);
x_58 = lean_mk_string_unchecked("instNegInt", 10, 10);
x_59 = l_Lean_Name_mkStr2(x_55, x_58);
x_60 = l_Lean_Expr_const___override(x_59, x_52);
x_61 = lean_int_neg(x_44);
lean_dec(x_44);
x_62 = l_Int_toNat(x_61);
lean_dec(x_61);
x_63 = l_Lean_instToExprInt_mkNat(x_62);
x_64 = l_Lean_mkApp3(x_54, x_57, x_60, x_63);
x_37 = x_64;
goto block_40;
}
else
{
lean_object* x_65; lean_object* x_66; 
x_65 = l_Int_toNat(x_44);
lean_dec(x_44);
x_66 = l_Lean_instToExprInt_mkNat(x_65);
x_37 = x_66;
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
uint8_t x_67; 
lean_dec(x_31);
lean_dec(x_30);
lean_free_object(x_17);
x_67 = !lean_is_exclusive(x_33);
if (x_67 == 0)
{
return x_33;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_33, 0);
x_69 = lean_ctor_get(x_33, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_33);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_71 = lean_ctor_get(x_17, 1);
lean_inc(x_71);
lean_dec(x_17);
x_72 = lean_ctor_get(x_18, 0);
lean_inc(x_72);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 x_73 = x_18;
} else {
 lean_dec_ref(x_18);
 x_73 = lean_box(0);
}
x_74 = l_Lean_Expr_appArg_x21(x_1);
x_75 = l_Lean_Meta_getIntValue_x3f(x_74, x_2, x_3, x_4, x_5, x_71);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_78 = x_75;
} else {
 lean_dec_ref(x_75);
 x_78 = lean_box(0);
}
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_78);
lean_dec(x_73);
lean_dec(x_72);
x_83 = lean_box(0);
x_84 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_84, 0, x_83);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_77);
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_86 = lean_ctor_get(x_76, 0);
lean_inc(x_86);
lean_dec(x_76);
x_87 = lean_int_sub(x_72, x_86);
lean_dec(x_86);
lean_dec(x_72);
x_88 = lean_unsigned_to_nat(0u);
x_89 = lean_nat_to_int(x_88);
x_90 = lean_int_dec_le(x_89, x_87);
lean_dec(x_89);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_91 = lean_mk_string_unchecked("Neg", 3, 3);
x_92 = lean_mk_string_unchecked("neg", 3, 3);
x_93 = l_Lean_Name_mkStr2(x_91, x_92);
x_94 = l_Lean_Level_ofNat(x_88);
x_95 = lean_box(0);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
x_97 = l_Lean_Expr_const___override(x_93, x_96);
x_98 = lean_mk_string_unchecked("Int", 3, 3);
lean_inc(x_98);
x_99 = l_Lean_Name_mkStr1(x_98);
x_100 = l_Lean_Expr_const___override(x_99, x_95);
x_101 = lean_mk_string_unchecked("instNegInt", 10, 10);
x_102 = l_Lean_Name_mkStr2(x_98, x_101);
x_103 = l_Lean_Expr_const___override(x_102, x_95);
x_104 = lean_int_neg(x_87);
lean_dec(x_87);
x_105 = l_Int_toNat(x_104);
lean_dec(x_104);
x_106 = l_Lean_instToExprInt_mkNat(x_105);
x_107 = l_Lean_mkApp3(x_97, x_100, x_103, x_106);
x_79 = x_107;
goto block_82;
}
else
{
lean_object* x_108; lean_object* x_109; 
x_108 = l_Int_toNat(x_87);
lean_dec(x_87);
x_109 = l_Lean_instToExprInt_mkNat(x_108);
x_79 = x_109;
goto block_82;
}
}
block_82:
{
lean_object* x_80; lean_object* x_81; 
if (lean_is_scalar(x_73)) {
 x_80 = lean_alloc_ctor(0, 1, 0);
} else {
 x_80 = x_73;
 lean_ctor_set_tag(x_80, 0);
}
lean_ctor_set(x_80, 0, x_79);
if (lean_is_scalar(x_78)) {
 x_81 = lean_alloc_ctor(0, 2, 0);
} else {
 x_81 = x_78;
}
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_77);
return x_81;
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec(x_73);
lean_dec(x_72);
x_110 = lean_ctor_get(x_75, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_75, 1);
lean_inc(x_111);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_112 = x_75;
} else {
 lean_dec_ref(x_75);
 x_112 = lean_box(0);
}
if (lean_is_scalar(x_112)) {
 x_113 = lean_alloc_ctor(1, 2, 0);
} else {
 x_113 = x_112;
}
lean_ctor_set(x_113, 0, x_110);
lean_ctor_set(x_113, 1, x_111);
return x_113;
}
}
}
}
else
{
uint8_t x_114; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_114 = !lean_is_exclusive(x_17);
if (x_114 == 0)
{
return x_17;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_17, 0);
x_116 = lean_ctor_get(x_17, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_17);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_reduceSub(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Int_reduceSub___redArg(x_1, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Int_reduceSub___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Int_reduceSub___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Int_reduceSub___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Int_reduceSub(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceSub_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1198_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_2 = lean_mk_string_unchecked("Int", 3, 3);
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
x_23 = lean_alloc_closure((void*)(l_Int_reduceSub___boxed), 9, 0);
x_24 = l_Lean_Meta_Simp_registerBuiltinDSimproc(x_4, x_22, x_23, x_1);
return x_24;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceSub_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1200_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Int", 3, 3);
x_3 = lean_mk_string_unchecked("reduceSub", 9, 9);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Int_reduceSub___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceSub_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1202_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Int", 3, 3);
x_3 = lean_mk_string_unchecked("reduceSub", 9, 9);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Int_reduceSub___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Int_reduceDiv___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_17 = l_Lean_Meta_getIntValue_x3f(x_16, x_2, x_3, x_4, x_5, x_6);
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
x_33 = l_Lean_Meta_getIntValue_x3f(x_32, x_2, x_3, x_4, x_5, x_28);
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
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
lean_free_object(x_17);
x_43 = lean_ctor_get(x_34, 0);
lean_inc(x_43);
lean_dec(x_34);
x_44 = lean_int_ediv(x_30, x_43);
lean_dec(x_43);
lean_dec(x_30);
x_45 = lean_unsigned_to_nat(0u);
x_46 = lean_nat_to_int(x_45);
x_47 = lean_int_dec_le(x_46, x_44);
lean_dec(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_48 = lean_mk_string_unchecked("Neg", 3, 3);
x_49 = lean_mk_string_unchecked("neg", 3, 3);
x_50 = l_Lean_Name_mkStr2(x_48, x_49);
x_51 = l_Lean_Level_ofNat(x_45);
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = l_Lean_Expr_const___override(x_50, x_53);
x_55 = lean_mk_string_unchecked("Int", 3, 3);
lean_inc(x_55);
x_56 = l_Lean_Name_mkStr1(x_55);
x_57 = l_Lean_Expr_const___override(x_56, x_52);
x_58 = lean_mk_string_unchecked("instNegInt", 10, 10);
x_59 = l_Lean_Name_mkStr2(x_55, x_58);
x_60 = l_Lean_Expr_const___override(x_59, x_52);
x_61 = lean_int_neg(x_44);
lean_dec(x_44);
x_62 = l_Int_toNat(x_61);
lean_dec(x_61);
x_63 = l_Lean_instToExprInt_mkNat(x_62);
x_64 = l_Lean_mkApp3(x_54, x_57, x_60, x_63);
x_37 = x_64;
goto block_40;
}
else
{
lean_object* x_65; lean_object* x_66; 
x_65 = l_Int_toNat(x_44);
lean_dec(x_44);
x_66 = l_Lean_instToExprInt_mkNat(x_65);
x_37 = x_66;
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
uint8_t x_67; 
lean_dec(x_31);
lean_dec(x_30);
lean_free_object(x_17);
x_67 = !lean_is_exclusive(x_33);
if (x_67 == 0)
{
return x_33;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_33, 0);
x_69 = lean_ctor_get(x_33, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_33);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_71 = lean_ctor_get(x_17, 1);
lean_inc(x_71);
lean_dec(x_17);
x_72 = lean_ctor_get(x_18, 0);
lean_inc(x_72);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 x_73 = x_18;
} else {
 lean_dec_ref(x_18);
 x_73 = lean_box(0);
}
x_74 = l_Lean_Expr_appArg_x21(x_1);
x_75 = l_Lean_Meta_getIntValue_x3f(x_74, x_2, x_3, x_4, x_5, x_71);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_78 = x_75;
} else {
 lean_dec_ref(x_75);
 x_78 = lean_box(0);
}
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_78);
lean_dec(x_73);
lean_dec(x_72);
x_83 = lean_box(0);
x_84 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_84, 0, x_83);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_77);
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_86 = lean_ctor_get(x_76, 0);
lean_inc(x_86);
lean_dec(x_76);
x_87 = lean_int_ediv(x_72, x_86);
lean_dec(x_86);
lean_dec(x_72);
x_88 = lean_unsigned_to_nat(0u);
x_89 = lean_nat_to_int(x_88);
x_90 = lean_int_dec_le(x_89, x_87);
lean_dec(x_89);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_91 = lean_mk_string_unchecked("Neg", 3, 3);
x_92 = lean_mk_string_unchecked("neg", 3, 3);
x_93 = l_Lean_Name_mkStr2(x_91, x_92);
x_94 = l_Lean_Level_ofNat(x_88);
x_95 = lean_box(0);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
x_97 = l_Lean_Expr_const___override(x_93, x_96);
x_98 = lean_mk_string_unchecked("Int", 3, 3);
lean_inc(x_98);
x_99 = l_Lean_Name_mkStr1(x_98);
x_100 = l_Lean_Expr_const___override(x_99, x_95);
x_101 = lean_mk_string_unchecked("instNegInt", 10, 10);
x_102 = l_Lean_Name_mkStr2(x_98, x_101);
x_103 = l_Lean_Expr_const___override(x_102, x_95);
x_104 = lean_int_neg(x_87);
lean_dec(x_87);
x_105 = l_Int_toNat(x_104);
lean_dec(x_104);
x_106 = l_Lean_instToExprInt_mkNat(x_105);
x_107 = l_Lean_mkApp3(x_97, x_100, x_103, x_106);
x_79 = x_107;
goto block_82;
}
else
{
lean_object* x_108; lean_object* x_109; 
x_108 = l_Int_toNat(x_87);
lean_dec(x_87);
x_109 = l_Lean_instToExprInt_mkNat(x_108);
x_79 = x_109;
goto block_82;
}
}
block_82:
{
lean_object* x_80; lean_object* x_81; 
if (lean_is_scalar(x_73)) {
 x_80 = lean_alloc_ctor(0, 1, 0);
} else {
 x_80 = x_73;
 lean_ctor_set_tag(x_80, 0);
}
lean_ctor_set(x_80, 0, x_79);
if (lean_is_scalar(x_78)) {
 x_81 = lean_alloc_ctor(0, 2, 0);
} else {
 x_81 = x_78;
}
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_77);
return x_81;
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec(x_73);
lean_dec(x_72);
x_110 = lean_ctor_get(x_75, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_75, 1);
lean_inc(x_111);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_112 = x_75;
} else {
 lean_dec_ref(x_75);
 x_112 = lean_box(0);
}
if (lean_is_scalar(x_112)) {
 x_113 = lean_alloc_ctor(1, 2, 0);
} else {
 x_113 = x_112;
}
lean_ctor_set(x_113, 0, x_110);
lean_ctor_set(x_113, 1, x_111);
return x_113;
}
}
}
}
else
{
uint8_t x_114; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_114 = !lean_is_exclusive(x_17);
if (x_114 == 0)
{
return x_17;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_17, 0);
x_116 = lean_ctor_get(x_17, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_17);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_reduceDiv(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Int_reduceDiv___redArg(x_1, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Int_reduceDiv___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Int_reduceDiv___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Int_reduceDiv___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Int_reduceDiv(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceDiv_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1236_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_2 = lean_mk_string_unchecked("Int", 3, 3);
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
x_23 = lean_alloc_closure((void*)(l_Int_reduceDiv___boxed), 9, 0);
x_24 = l_Lean_Meta_Simp_registerBuiltinDSimproc(x_4, x_22, x_23, x_1);
return x_24;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceDiv_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1238_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Int", 3, 3);
x_3 = lean_mk_string_unchecked("reduceDiv", 9, 9);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Int_reduceDiv___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceDiv_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1240_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Int", 3, 3);
x_3 = lean_mk_string_unchecked("reduceDiv", 9, 9);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Int_reduceDiv___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Int_reduceMod___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_17 = l_Lean_Meta_getIntValue_x3f(x_16, x_2, x_3, x_4, x_5, x_6);
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
x_33 = l_Lean_Meta_getIntValue_x3f(x_32, x_2, x_3, x_4, x_5, x_28);
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
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
lean_free_object(x_17);
x_43 = lean_ctor_get(x_34, 0);
lean_inc(x_43);
lean_dec(x_34);
x_44 = lean_int_emod(x_30, x_43);
lean_dec(x_43);
lean_dec(x_30);
x_45 = lean_unsigned_to_nat(0u);
x_46 = lean_nat_to_int(x_45);
x_47 = lean_int_dec_le(x_46, x_44);
lean_dec(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_48 = lean_mk_string_unchecked("Neg", 3, 3);
x_49 = lean_mk_string_unchecked("neg", 3, 3);
x_50 = l_Lean_Name_mkStr2(x_48, x_49);
x_51 = l_Lean_Level_ofNat(x_45);
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = l_Lean_Expr_const___override(x_50, x_53);
x_55 = lean_mk_string_unchecked("Int", 3, 3);
lean_inc(x_55);
x_56 = l_Lean_Name_mkStr1(x_55);
x_57 = l_Lean_Expr_const___override(x_56, x_52);
x_58 = lean_mk_string_unchecked("instNegInt", 10, 10);
x_59 = l_Lean_Name_mkStr2(x_55, x_58);
x_60 = l_Lean_Expr_const___override(x_59, x_52);
x_61 = lean_int_neg(x_44);
lean_dec(x_44);
x_62 = l_Int_toNat(x_61);
lean_dec(x_61);
x_63 = l_Lean_instToExprInt_mkNat(x_62);
x_64 = l_Lean_mkApp3(x_54, x_57, x_60, x_63);
x_37 = x_64;
goto block_40;
}
else
{
lean_object* x_65; lean_object* x_66; 
x_65 = l_Int_toNat(x_44);
lean_dec(x_44);
x_66 = l_Lean_instToExprInt_mkNat(x_65);
x_37 = x_66;
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
uint8_t x_67; 
lean_dec(x_31);
lean_dec(x_30);
lean_free_object(x_17);
x_67 = !lean_is_exclusive(x_33);
if (x_67 == 0)
{
return x_33;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_33, 0);
x_69 = lean_ctor_get(x_33, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_33);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_71 = lean_ctor_get(x_17, 1);
lean_inc(x_71);
lean_dec(x_17);
x_72 = lean_ctor_get(x_18, 0);
lean_inc(x_72);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 x_73 = x_18;
} else {
 lean_dec_ref(x_18);
 x_73 = lean_box(0);
}
x_74 = l_Lean_Expr_appArg_x21(x_1);
x_75 = l_Lean_Meta_getIntValue_x3f(x_74, x_2, x_3, x_4, x_5, x_71);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_78 = x_75;
} else {
 lean_dec_ref(x_75);
 x_78 = lean_box(0);
}
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_78);
lean_dec(x_73);
lean_dec(x_72);
x_83 = lean_box(0);
x_84 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_84, 0, x_83);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_77);
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_86 = lean_ctor_get(x_76, 0);
lean_inc(x_86);
lean_dec(x_76);
x_87 = lean_int_emod(x_72, x_86);
lean_dec(x_86);
lean_dec(x_72);
x_88 = lean_unsigned_to_nat(0u);
x_89 = lean_nat_to_int(x_88);
x_90 = lean_int_dec_le(x_89, x_87);
lean_dec(x_89);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_91 = lean_mk_string_unchecked("Neg", 3, 3);
x_92 = lean_mk_string_unchecked("neg", 3, 3);
x_93 = l_Lean_Name_mkStr2(x_91, x_92);
x_94 = l_Lean_Level_ofNat(x_88);
x_95 = lean_box(0);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
x_97 = l_Lean_Expr_const___override(x_93, x_96);
x_98 = lean_mk_string_unchecked("Int", 3, 3);
lean_inc(x_98);
x_99 = l_Lean_Name_mkStr1(x_98);
x_100 = l_Lean_Expr_const___override(x_99, x_95);
x_101 = lean_mk_string_unchecked("instNegInt", 10, 10);
x_102 = l_Lean_Name_mkStr2(x_98, x_101);
x_103 = l_Lean_Expr_const___override(x_102, x_95);
x_104 = lean_int_neg(x_87);
lean_dec(x_87);
x_105 = l_Int_toNat(x_104);
lean_dec(x_104);
x_106 = l_Lean_instToExprInt_mkNat(x_105);
x_107 = l_Lean_mkApp3(x_97, x_100, x_103, x_106);
x_79 = x_107;
goto block_82;
}
else
{
lean_object* x_108; lean_object* x_109; 
x_108 = l_Int_toNat(x_87);
lean_dec(x_87);
x_109 = l_Lean_instToExprInt_mkNat(x_108);
x_79 = x_109;
goto block_82;
}
}
block_82:
{
lean_object* x_80; lean_object* x_81; 
if (lean_is_scalar(x_73)) {
 x_80 = lean_alloc_ctor(0, 1, 0);
} else {
 x_80 = x_73;
 lean_ctor_set_tag(x_80, 0);
}
lean_ctor_set(x_80, 0, x_79);
if (lean_is_scalar(x_78)) {
 x_81 = lean_alloc_ctor(0, 2, 0);
} else {
 x_81 = x_78;
}
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_77);
return x_81;
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec(x_73);
lean_dec(x_72);
x_110 = lean_ctor_get(x_75, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_75, 1);
lean_inc(x_111);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_112 = x_75;
} else {
 lean_dec_ref(x_75);
 x_112 = lean_box(0);
}
if (lean_is_scalar(x_112)) {
 x_113 = lean_alloc_ctor(1, 2, 0);
} else {
 x_113 = x_112;
}
lean_ctor_set(x_113, 0, x_110);
lean_ctor_set(x_113, 1, x_111);
return x_113;
}
}
}
}
else
{
uint8_t x_114; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_114 = !lean_is_exclusive(x_17);
if (x_114 == 0)
{
return x_17;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_17, 0);
x_116 = lean_ctor_get(x_17, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_17);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_reduceMod(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Int_reduceMod___redArg(x_1, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Int_reduceMod___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Int_reduceMod___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Int_reduceMod___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Int_reduceMod(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceMod_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1274_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_2 = lean_mk_string_unchecked("Int", 3, 3);
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
x_23 = lean_alloc_closure((void*)(l_Int_reduceMod___boxed), 9, 0);
x_24 = l_Lean_Meta_Simp_registerBuiltinDSimproc(x_4, x_22, x_23, x_1);
return x_24;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceMod_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1276_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Int", 3, 3);
x_3 = lean_mk_string_unchecked("reduceMod", 9, 9);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Int_reduceMod___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceMod_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1278_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Int", 3, 3);
x_3 = lean_mk_string_unchecked("reduceMod", 9, 9);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Int_reduceMod___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Int_reduceTDiv___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_mk_string_unchecked("Int", 3, 3);
x_8 = lean_mk_string_unchecked("tdiv", 4, 4);
lean_inc(x_7);
x_9 = l_Lean_Name_mkStr2(x_7, x_8);
x_10 = lean_unsigned_to_nat(2u);
x_11 = l_Lean_Expr_isAppOfArity(x_1, x_9, x_10);
lean_dec(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_7);
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
x_17 = l_Lean_Meta_getIntValue_x3f(x_16, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
lean_dec(x_7);
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
x_33 = l_Lean_Meta_getIntValue_x3f(x_32, x_2, x_3, x_4, x_5, x_28);
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
lean_dec(x_7);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_17, 1, x_35);
lean_ctor_set(x_17, 0, x_42);
return x_17;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
lean_free_object(x_17);
x_43 = lean_ctor_get(x_34, 0);
lean_inc(x_43);
lean_dec(x_34);
x_44 = lean_int_div(x_30, x_43);
lean_dec(x_43);
lean_dec(x_30);
x_45 = lean_unsigned_to_nat(0u);
x_46 = lean_nat_to_int(x_45);
x_47 = lean_int_dec_le(x_46, x_44);
lean_dec(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_48 = lean_mk_string_unchecked("Neg", 3, 3);
x_49 = lean_mk_string_unchecked("neg", 3, 3);
x_50 = l_Lean_Name_mkStr2(x_48, x_49);
x_51 = l_Lean_Level_ofNat(x_45);
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = l_Lean_Expr_const___override(x_50, x_53);
lean_inc(x_7);
x_55 = l_Lean_Name_mkStr1(x_7);
x_56 = l_Lean_Expr_const___override(x_55, x_52);
x_57 = lean_mk_string_unchecked("instNegInt", 10, 10);
x_58 = l_Lean_Name_mkStr2(x_7, x_57);
x_59 = l_Lean_Expr_const___override(x_58, x_52);
x_60 = lean_int_neg(x_44);
lean_dec(x_44);
x_61 = l_Int_toNat(x_60);
lean_dec(x_60);
x_62 = l_Lean_instToExprInt_mkNat(x_61);
x_63 = l_Lean_mkApp3(x_54, x_56, x_59, x_62);
x_37 = x_63;
goto block_40;
}
else
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_7);
x_64 = l_Int_toNat(x_44);
lean_dec(x_44);
x_65 = l_Lean_instToExprInt_mkNat(x_64);
x_37 = x_65;
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
uint8_t x_66; 
lean_dec(x_31);
lean_dec(x_30);
lean_free_object(x_17);
lean_dec(x_7);
x_66 = !lean_is_exclusive(x_33);
if (x_66 == 0)
{
return x_33;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_33, 0);
x_68 = lean_ctor_get(x_33, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_33);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_70 = lean_ctor_get(x_17, 1);
lean_inc(x_70);
lean_dec(x_17);
x_71 = lean_ctor_get(x_18, 0);
lean_inc(x_71);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 x_72 = x_18;
} else {
 lean_dec_ref(x_18);
 x_72 = lean_box(0);
}
x_73 = l_Lean_Expr_appArg_x21(x_1);
x_74 = l_Lean_Meta_getIntValue_x3f(x_73, x_2, x_3, x_4, x_5, x_70);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_77 = x_74;
} else {
 lean_dec_ref(x_74);
 x_77 = lean_box(0);
}
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_77);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_7);
x_82 = lean_box(0);
x_83 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_83, 0, x_82);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_76);
return x_84;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_85 = lean_ctor_get(x_75, 0);
lean_inc(x_85);
lean_dec(x_75);
x_86 = lean_int_div(x_71, x_85);
lean_dec(x_85);
lean_dec(x_71);
x_87 = lean_unsigned_to_nat(0u);
x_88 = lean_nat_to_int(x_87);
x_89 = lean_int_dec_le(x_88, x_86);
lean_dec(x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_90 = lean_mk_string_unchecked("Neg", 3, 3);
x_91 = lean_mk_string_unchecked("neg", 3, 3);
x_92 = l_Lean_Name_mkStr2(x_90, x_91);
x_93 = l_Lean_Level_ofNat(x_87);
x_94 = lean_box(0);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
x_96 = l_Lean_Expr_const___override(x_92, x_95);
lean_inc(x_7);
x_97 = l_Lean_Name_mkStr1(x_7);
x_98 = l_Lean_Expr_const___override(x_97, x_94);
x_99 = lean_mk_string_unchecked("instNegInt", 10, 10);
x_100 = l_Lean_Name_mkStr2(x_7, x_99);
x_101 = l_Lean_Expr_const___override(x_100, x_94);
x_102 = lean_int_neg(x_86);
lean_dec(x_86);
x_103 = l_Int_toNat(x_102);
lean_dec(x_102);
x_104 = l_Lean_instToExprInt_mkNat(x_103);
x_105 = l_Lean_mkApp3(x_96, x_98, x_101, x_104);
x_78 = x_105;
goto block_81;
}
else
{
lean_object* x_106; lean_object* x_107; 
lean_dec(x_7);
x_106 = l_Int_toNat(x_86);
lean_dec(x_86);
x_107 = l_Lean_instToExprInt_mkNat(x_106);
x_78 = x_107;
goto block_81;
}
}
block_81:
{
lean_object* x_79; lean_object* x_80; 
if (lean_is_scalar(x_72)) {
 x_79 = lean_alloc_ctor(0, 1, 0);
} else {
 x_79 = x_72;
 lean_ctor_set_tag(x_79, 0);
}
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
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_7);
x_108 = lean_ctor_get(x_74, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_74, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_110 = x_74;
} else {
 lean_dec_ref(x_74);
 x_110 = lean_box(0);
}
if (lean_is_scalar(x_110)) {
 x_111 = lean_alloc_ctor(1, 2, 0);
} else {
 x_111 = x_110;
}
lean_ctor_set(x_111, 0, x_108);
lean_ctor_set(x_111, 1, x_109);
return x_111;
}
}
}
}
else
{
uint8_t x_112; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_112 = !lean_is_exclusive(x_17);
if (x_112 == 0)
{
return x_17;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_17, 0);
x_114 = lean_ctor_get(x_17, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_17);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_reduceTDiv(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Int_reduceTDiv___redArg(x_1, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Int_reduceTDiv___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Int_reduceTDiv___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Int_reduceTDiv___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Int_reduceTDiv(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceTDiv_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1296_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_2 = lean_mk_string_unchecked("Int", 3, 3);
x_3 = lean_mk_string_unchecked("reduceTDiv", 10, 10);
lean_inc(x_2);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_mk_string_unchecked("tdiv", 4, 4);
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
x_15 = lean_alloc_closure((void*)(l_Int_reduceTDiv___boxed), 9, 0);
x_16 = l_Lean_Meta_Simp_registerBuiltinDSimproc(x_4, x_14, x_15, x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceTDiv_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1298_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Int", 3, 3);
x_3 = lean_mk_string_unchecked("reduceTDiv", 10, 10);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Int_reduceTDiv___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceTDiv_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1300_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Int", 3, 3);
x_3 = lean_mk_string_unchecked("reduceTDiv", 10, 10);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Int_reduceTDiv___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Int_reduceTMod___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_mk_string_unchecked("Int", 3, 3);
x_8 = lean_mk_string_unchecked("tmod", 4, 4);
lean_inc(x_7);
x_9 = l_Lean_Name_mkStr2(x_7, x_8);
x_10 = lean_unsigned_to_nat(2u);
x_11 = l_Lean_Expr_isAppOfArity(x_1, x_9, x_10);
lean_dec(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_7);
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
x_17 = l_Lean_Meta_getIntValue_x3f(x_16, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
lean_dec(x_7);
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
x_33 = l_Lean_Meta_getIntValue_x3f(x_32, x_2, x_3, x_4, x_5, x_28);
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
lean_dec(x_7);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_17, 1, x_35);
lean_ctor_set(x_17, 0, x_42);
return x_17;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
lean_free_object(x_17);
x_43 = lean_ctor_get(x_34, 0);
lean_inc(x_43);
lean_dec(x_34);
x_44 = lean_int_mod(x_30, x_43);
lean_dec(x_43);
lean_dec(x_30);
x_45 = lean_unsigned_to_nat(0u);
x_46 = lean_nat_to_int(x_45);
x_47 = lean_int_dec_le(x_46, x_44);
lean_dec(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_48 = lean_mk_string_unchecked("Neg", 3, 3);
x_49 = lean_mk_string_unchecked("neg", 3, 3);
x_50 = l_Lean_Name_mkStr2(x_48, x_49);
x_51 = l_Lean_Level_ofNat(x_45);
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = l_Lean_Expr_const___override(x_50, x_53);
lean_inc(x_7);
x_55 = l_Lean_Name_mkStr1(x_7);
x_56 = l_Lean_Expr_const___override(x_55, x_52);
x_57 = lean_mk_string_unchecked("instNegInt", 10, 10);
x_58 = l_Lean_Name_mkStr2(x_7, x_57);
x_59 = l_Lean_Expr_const___override(x_58, x_52);
x_60 = lean_int_neg(x_44);
lean_dec(x_44);
x_61 = l_Int_toNat(x_60);
lean_dec(x_60);
x_62 = l_Lean_instToExprInt_mkNat(x_61);
x_63 = l_Lean_mkApp3(x_54, x_56, x_59, x_62);
x_37 = x_63;
goto block_40;
}
else
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_7);
x_64 = l_Int_toNat(x_44);
lean_dec(x_44);
x_65 = l_Lean_instToExprInt_mkNat(x_64);
x_37 = x_65;
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
uint8_t x_66; 
lean_dec(x_31);
lean_dec(x_30);
lean_free_object(x_17);
lean_dec(x_7);
x_66 = !lean_is_exclusive(x_33);
if (x_66 == 0)
{
return x_33;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_33, 0);
x_68 = lean_ctor_get(x_33, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_33);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_70 = lean_ctor_get(x_17, 1);
lean_inc(x_70);
lean_dec(x_17);
x_71 = lean_ctor_get(x_18, 0);
lean_inc(x_71);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 x_72 = x_18;
} else {
 lean_dec_ref(x_18);
 x_72 = lean_box(0);
}
x_73 = l_Lean_Expr_appArg_x21(x_1);
x_74 = l_Lean_Meta_getIntValue_x3f(x_73, x_2, x_3, x_4, x_5, x_70);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_77 = x_74;
} else {
 lean_dec_ref(x_74);
 x_77 = lean_box(0);
}
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_77);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_7);
x_82 = lean_box(0);
x_83 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_83, 0, x_82);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_76);
return x_84;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_85 = lean_ctor_get(x_75, 0);
lean_inc(x_85);
lean_dec(x_75);
x_86 = lean_int_mod(x_71, x_85);
lean_dec(x_85);
lean_dec(x_71);
x_87 = lean_unsigned_to_nat(0u);
x_88 = lean_nat_to_int(x_87);
x_89 = lean_int_dec_le(x_88, x_86);
lean_dec(x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_90 = lean_mk_string_unchecked("Neg", 3, 3);
x_91 = lean_mk_string_unchecked("neg", 3, 3);
x_92 = l_Lean_Name_mkStr2(x_90, x_91);
x_93 = l_Lean_Level_ofNat(x_87);
x_94 = lean_box(0);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
x_96 = l_Lean_Expr_const___override(x_92, x_95);
lean_inc(x_7);
x_97 = l_Lean_Name_mkStr1(x_7);
x_98 = l_Lean_Expr_const___override(x_97, x_94);
x_99 = lean_mk_string_unchecked("instNegInt", 10, 10);
x_100 = l_Lean_Name_mkStr2(x_7, x_99);
x_101 = l_Lean_Expr_const___override(x_100, x_94);
x_102 = lean_int_neg(x_86);
lean_dec(x_86);
x_103 = l_Int_toNat(x_102);
lean_dec(x_102);
x_104 = l_Lean_instToExprInt_mkNat(x_103);
x_105 = l_Lean_mkApp3(x_96, x_98, x_101, x_104);
x_78 = x_105;
goto block_81;
}
else
{
lean_object* x_106; lean_object* x_107; 
lean_dec(x_7);
x_106 = l_Int_toNat(x_86);
lean_dec(x_86);
x_107 = l_Lean_instToExprInt_mkNat(x_106);
x_78 = x_107;
goto block_81;
}
}
block_81:
{
lean_object* x_79; lean_object* x_80; 
if (lean_is_scalar(x_72)) {
 x_79 = lean_alloc_ctor(0, 1, 0);
} else {
 x_79 = x_72;
 lean_ctor_set_tag(x_79, 0);
}
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
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_7);
x_108 = lean_ctor_get(x_74, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_74, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_110 = x_74;
} else {
 lean_dec_ref(x_74);
 x_110 = lean_box(0);
}
if (lean_is_scalar(x_110)) {
 x_111 = lean_alloc_ctor(1, 2, 0);
} else {
 x_111 = x_110;
}
lean_ctor_set(x_111, 0, x_108);
lean_ctor_set(x_111, 1, x_109);
return x_111;
}
}
}
}
else
{
uint8_t x_112; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_112 = !lean_is_exclusive(x_17);
if (x_112 == 0)
{
return x_17;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_17, 0);
x_114 = lean_ctor_get(x_17, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_17);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_reduceTMod(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Int_reduceTMod___redArg(x_1, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Int_reduceTMod___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Int_reduceTMod___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Int_reduceTMod___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Int_reduceTMod(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceTMod_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1318_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_2 = lean_mk_string_unchecked("Int", 3, 3);
x_3 = lean_mk_string_unchecked("reduceTMod", 10, 10);
lean_inc(x_2);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_mk_string_unchecked("tmod", 4, 4);
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
x_15 = lean_alloc_closure((void*)(l_Int_reduceTMod___boxed), 9, 0);
x_16 = l_Lean_Meta_Simp_registerBuiltinDSimproc(x_4, x_14, x_15, x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceTMod_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1320_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Int", 3, 3);
x_3 = lean_mk_string_unchecked("reduceTMod", 10, 10);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Int_reduceTMod___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceTMod_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1322_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Int", 3, 3);
x_3 = lean_mk_string_unchecked("reduceTMod", 10, 10);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Int_reduceTMod___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Int_reduceFDiv___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_mk_string_unchecked("Int", 3, 3);
x_8 = lean_mk_string_unchecked("fdiv", 4, 4);
lean_inc(x_7);
x_9 = l_Lean_Name_mkStr2(x_7, x_8);
x_10 = lean_unsigned_to_nat(2u);
x_11 = l_Lean_Expr_isAppOfArity(x_1, x_9, x_10);
lean_dec(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_7);
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
x_17 = l_Lean_Meta_getIntValue_x3f(x_16, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
lean_dec(x_7);
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
x_33 = l_Lean_Meta_getIntValue_x3f(x_32, x_2, x_3, x_4, x_5, x_28);
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
lean_dec(x_7);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_17, 1, x_35);
lean_ctor_set(x_17, 0, x_42);
return x_17;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
lean_free_object(x_17);
x_43 = lean_ctor_get(x_34, 0);
lean_inc(x_43);
lean_dec(x_34);
x_44 = l_Int_fdiv(x_30, x_43);
lean_dec(x_43);
lean_dec(x_30);
x_45 = lean_unsigned_to_nat(0u);
x_46 = lean_nat_to_int(x_45);
x_47 = lean_int_dec_le(x_46, x_44);
lean_dec(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_48 = lean_mk_string_unchecked("Neg", 3, 3);
x_49 = lean_mk_string_unchecked("neg", 3, 3);
x_50 = l_Lean_Name_mkStr2(x_48, x_49);
x_51 = l_Lean_Level_ofNat(x_45);
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = l_Lean_Expr_const___override(x_50, x_53);
lean_inc(x_7);
x_55 = l_Lean_Name_mkStr1(x_7);
x_56 = l_Lean_Expr_const___override(x_55, x_52);
x_57 = lean_mk_string_unchecked("instNegInt", 10, 10);
x_58 = l_Lean_Name_mkStr2(x_7, x_57);
x_59 = l_Lean_Expr_const___override(x_58, x_52);
x_60 = lean_int_neg(x_44);
lean_dec(x_44);
x_61 = l_Int_toNat(x_60);
lean_dec(x_60);
x_62 = l_Lean_instToExprInt_mkNat(x_61);
x_63 = l_Lean_mkApp3(x_54, x_56, x_59, x_62);
x_37 = x_63;
goto block_40;
}
else
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_7);
x_64 = l_Int_toNat(x_44);
lean_dec(x_44);
x_65 = l_Lean_instToExprInt_mkNat(x_64);
x_37 = x_65;
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
uint8_t x_66; 
lean_dec(x_31);
lean_dec(x_30);
lean_free_object(x_17);
lean_dec(x_7);
x_66 = !lean_is_exclusive(x_33);
if (x_66 == 0)
{
return x_33;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_33, 0);
x_68 = lean_ctor_get(x_33, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_33);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_70 = lean_ctor_get(x_17, 1);
lean_inc(x_70);
lean_dec(x_17);
x_71 = lean_ctor_get(x_18, 0);
lean_inc(x_71);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 x_72 = x_18;
} else {
 lean_dec_ref(x_18);
 x_72 = lean_box(0);
}
x_73 = l_Lean_Expr_appArg_x21(x_1);
x_74 = l_Lean_Meta_getIntValue_x3f(x_73, x_2, x_3, x_4, x_5, x_70);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_77 = x_74;
} else {
 lean_dec_ref(x_74);
 x_77 = lean_box(0);
}
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_77);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_7);
x_82 = lean_box(0);
x_83 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_83, 0, x_82);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_76);
return x_84;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_85 = lean_ctor_get(x_75, 0);
lean_inc(x_85);
lean_dec(x_75);
x_86 = l_Int_fdiv(x_71, x_85);
lean_dec(x_85);
lean_dec(x_71);
x_87 = lean_unsigned_to_nat(0u);
x_88 = lean_nat_to_int(x_87);
x_89 = lean_int_dec_le(x_88, x_86);
lean_dec(x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_90 = lean_mk_string_unchecked("Neg", 3, 3);
x_91 = lean_mk_string_unchecked("neg", 3, 3);
x_92 = l_Lean_Name_mkStr2(x_90, x_91);
x_93 = l_Lean_Level_ofNat(x_87);
x_94 = lean_box(0);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
x_96 = l_Lean_Expr_const___override(x_92, x_95);
lean_inc(x_7);
x_97 = l_Lean_Name_mkStr1(x_7);
x_98 = l_Lean_Expr_const___override(x_97, x_94);
x_99 = lean_mk_string_unchecked("instNegInt", 10, 10);
x_100 = l_Lean_Name_mkStr2(x_7, x_99);
x_101 = l_Lean_Expr_const___override(x_100, x_94);
x_102 = lean_int_neg(x_86);
lean_dec(x_86);
x_103 = l_Int_toNat(x_102);
lean_dec(x_102);
x_104 = l_Lean_instToExprInt_mkNat(x_103);
x_105 = l_Lean_mkApp3(x_96, x_98, x_101, x_104);
x_78 = x_105;
goto block_81;
}
else
{
lean_object* x_106; lean_object* x_107; 
lean_dec(x_7);
x_106 = l_Int_toNat(x_86);
lean_dec(x_86);
x_107 = l_Lean_instToExprInt_mkNat(x_106);
x_78 = x_107;
goto block_81;
}
}
block_81:
{
lean_object* x_79; lean_object* x_80; 
if (lean_is_scalar(x_72)) {
 x_79 = lean_alloc_ctor(0, 1, 0);
} else {
 x_79 = x_72;
 lean_ctor_set_tag(x_79, 0);
}
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
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_7);
x_108 = lean_ctor_get(x_74, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_74, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_110 = x_74;
} else {
 lean_dec_ref(x_74);
 x_110 = lean_box(0);
}
if (lean_is_scalar(x_110)) {
 x_111 = lean_alloc_ctor(1, 2, 0);
} else {
 x_111 = x_110;
}
lean_ctor_set(x_111, 0, x_108);
lean_ctor_set(x_111, 1, x_109);
return x_111;
}
}
}
}
else
{
uint8_t x_112; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_112 = !lean_is_exclusive(x_17);
if (x_112 == 0)
{
return x_17;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_17, 0);
x_114 = lean_ctor_get(x_17, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_17);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_reduceFDiv(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Int_reduceFDiv___redArg(x_1, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Int_reduceFDiv___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Int_reduceFDiv___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Int_reduceFDiv___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Int_reduceFDiv(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceFDiv_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1340_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_2 = lean_mk_string_unchecked("Int", 3, 3);
x_3 = lean_mk_string_unchecked("reduceFDiv", 10, 10);
lean_inc(x_2);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_mk_string_unchecked("fdiv", 4, 4);
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
x_15 = lean_alloc_closure((void*)(l_Int_reduceFDiv___boxed), 9, 0);
x_16 = l_Lean_Meta_Simp_registerBuiltinDSimproc(x_4, x_14, x_15, x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceFDiv_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1342_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Int", 3, 3);
x_3 = lean_mk_string_unchecked("reduceFDiv", 10, 10);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Int_reduceFDiv___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceFDiv_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1344_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Int", 3, 3);
x_3 = lean_mk_string_unchecked("reduceFDiv", 10, 10);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Int_reduceFDiv___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Int_reduceFMod___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_mk_string_unchecked("Int", 3, 3);
x_8 = lean_mk_string_unchecked("fmod", 4, 4);
lean_inc(x_7);
x_9 = l_Lean_Name_mkStr2(x_7, x_8);
x_10 = lean_unsigned_to_nat(2u);
x_11 = l_Lean_Expr_isAppOfArity(x_1, x_9, x_10);
lean_dec(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_7);
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
x_17 = l_Lean_Meta_getIntValue_x3f(x_16, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
lean_dec(x_7);
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
x_33 = l_Lean_Meta_getIntValue_x3f(x_32, x_2, x_3, x_4, x_5, x_28);
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
lean_dec(x_7);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_17, 1, x_35);
lean_ctor_set(x_17, 0, x_42);
return x_17;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
lean_free_object(x_17);
x_43 = lean_ctor_get(x_34, 0);
lean_inc(x_43);
lean_dec(x_34);
x_44 = l_Int_fmod(x_30, x_43);
lean_dec(x_43);
lean_dec(x_30);
x_45 = lean_unsigned_to_nat(0u);
x_46 = lean_nat_to_int(x_45);
x_47 = lean_int_dec_le(x_46, x_44);
lean_dec(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_48 = lean_mk_string_unchecked("Neg", 3, 3);
x_49 = lean_mk_string_unchecked("neg", 3, 3);
x_50 = l_Lean_Name_mkStr2(x_48, x_49);
x_51 = l_Lean_Level_ofNat(x_45);
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = l_Lean_Expr_const___override(x_50, x_53);
lean_inc(x_7);
x_55 = l_Lean_Name_mkStr1(x_7);
x_56 = l_Lean_Expr_const___override(x_55, x_52);
x_57 = lean_mk_string_unchecked("instNegInt", 10, 10);
x_58 = l_Lean_Name_mkStr2(x_7, x_57);
x_59 = l_Lean_Expr_const___override(x_58, x_52);
x_60 = lean_int_neg(x_44);
lean_dec(x_44);
x_61 = l_Int_toNat(x_60);
lean_dec(x_60);
x_62 = l_Lean_instToExprInt_mkNat(x_61);
x_63 = l_Lean_mkApp3(x_54, x_56, x_59, x_62);
x_37 = x_63;
goto block_40;
}
else
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_7);
x_64 = l_Int_toNat(x_44);
lean_dec(x_44);
x_65 = l_Lean_instToExprInt_mkNat(x_64);
x_37 = x_65;
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
uint8_t x_66; 
lean_dec(x_31);
lean_dec(x_30);
lean_free_object(x_17);
lean_dec(x_7);
x_66 = !lean_is_exclusive(x_33);
if (x_66 == 0)
{
return x_33;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_33, 0);
x_68 = lean_ctor_get(x_33, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_33);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_70 = lean_ctor_get(x_17, 1);
lean_inc(x_70);
lean_dec(x_17);
x_71 = lean_ctor_get(x_18, 0);
lean_inc(x_71);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 x_72 = x_18;
} else {
 lean_dec_ref(x_18);
 x_72 = lean_box(0);
}
x_73 = l_Lean_Expr_appArg_x21(x_1);
x_74 = l_Lean_Meta_getIntValue_x3f(x_73, x_2, x_3, x_4, x_5, x_70);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_77 = x_74;
} else {
 lean_dec_ref(x_74);
 x_77 = lean_box(0);
}
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_77);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_7);
x_82 = lean_box(0);
x_83 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_83, 0, x_82);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_76);
return x_84;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_85 = lean_ctor_get(x_75, 0);
lean_inc(x_85);
lean_dec(x_75);
x_86 = l_Int_fmod(x_71, x_85);
lean_dec(x_85);
lean_dec(x_71);
x_87 = lean_unsigned_to_nat(0u);
x_88 = lean_nat_to_int(x_87);
x_89 = lean_int_dec_le(x_88, x_86);
lean_dec(x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_90 = lean_mk_string_unchecked("Neg", 3, 3);
x_91 = lean_mk_string_unchecked("neg", 3, 3);
x_92 = l_Lean_Name_mkStr2(x_90, x_91);
x_93 = l_Lean_Level_ofNat(x_87);
x_94 = lean_box(0);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
x_96 = l_Lean_Expr_const___override(x_92, x_95);
lean_inc(x_7);
x_97 = l_Lean_Name_mkStr1(x_7);
x_98 = l_Lean_Expr_const___override(x_97, x_94);
x_99 = lean_mk_string_unchecked("instNegInt", 10, 10);
x_100 = l_Lean_Name_mkStr2(x_7, x_99);
x_101 = l_Lean_Expr_const___override(x_100, x_94);
x_102 = lean_int_neg(x_86);
lean_dec(x_86);
x_103 = l_Int_toNat(x_102);
lean_dec(x_102);
x_104 = l_Lean_instToExprInt_mkNat(x_103);
x_105 = l_Lean_mkApp3(x_96, x_98, x_101, x_104);
x_78 = x_105;
goto block_81;
}
else
{
lean_object* x_106; lean_object* x_107; 
lean_dec(x_7);
x_106 = l_Int_toNat(x_86);
lean_dec(x_86);
x_107 = l_Lean_instToExprInt_mkNat(x_106);
x_78 = x_107;
goto block_81;
}
}
block_81:
{
lean_object* x_79; lean_object* x_80; 
if (lean_is_scalar(x_72)) {
 x_79 = lean_alloc_ctor(0, 1, 0);
} else {
 x_79 = x_72;
 lean_ctor_set_tag(x_79, 0);
}
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
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_7);
x_108 = lean_ctor_get(x_74, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_74, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_110 = x_74;
} else {
 lean_dec_ref(x_74);
 x_110 = lean_box(0);
}
if (lean_is_scalar(x_110)) {
 x_111 = lean_alloc_ctor(1, 2, 0);
} else {
 x_111 = x_110;
}
lean_ctor_set(x_111, 0, x_108);
lean_ctor_set(x_111, 1, x_109);
return x_111;
}
}
}
}
else
{
uint8_t x_112; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_112 = !lean_is_exclusive(x_17);
if (x_112 == 0)
{
return x_17;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_17, 0);
x_114 = lean_ctor_get(x_17, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_17);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_reduceFMod(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Int_reduceFMod___redArg(x_1, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Int_reduceFMod___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Int_reduceFMod___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Int_reduceFMod___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Int_reduceFMod(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceFMod_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1362_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_2 = lean_mk_string_unchecked("Int", 3, 3);
x_3 = lean_mk_string_unchecked("reduceFMod", 10, 10);
lean_inc(x_2);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_mk_string_unchecked("fmod", 4, 4);
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
x_15 = lean_alloc_closure((void*)(l_Int_reduceFMod___boxed), 9, 0);
x_16 = l_Lean_Meta_Simp_registerBuiltinDSimproc(x_4, x_14, x_15, x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceFMod_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1364_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Int", 3, 3);
x_3 = lean_mk_string_unchecked("reduceFMod", 10, 10);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Int_reduceFMod___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceFMod_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1366_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Int", 3, 3);
x_3 = lean_mk_string_unchecked("reduceFMod", 10, 10);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Int_reduceFMod___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Int_reduceBdiv___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_mk_string_unchecked("Int", 3, 3);
x_8 = lean_mk_string_unchecked("bdiv", 4, 4);
x_9 = l_Lean_Name_mkStr2(x_7, x_8);
x_10 = lean_alloc_closure((void*)(l_Int_bdiv___boxed), 2, 0);
x_11 = l_Int_reduceBinIntNatOp___redArg(x_9, x_10, x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Int_reduceBdiv(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Int_reduceBdiv___redArg(x_1, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Int_reduceBdiv___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Int_reduceBdiv___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Int_reduceBdiv___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Int_reduceBdiv(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceBdiv_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1383_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_2 = lean_mk_string_unchecked("Int", 3, 3);
x_3 = lean_mk_string_unchecked("reduceBdiv", 10, 10);
lean_inc(x_2);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_mk_string_unchecked("bdiv", 4, 4);
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
x_15 = lean_alloc_closure((void*)(l_Int_reduceBdiv___boxed), 9, 0);
x_16 = l_Lean_Meta_Simp_registerBuiltinDSimproc(x_4, x_14, x_15, x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceBdiv_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1385_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Int", 3, 3);
x_3 = lean_mk_string_unchecked("reduceBdiv", 10, 10);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Int_reduceBdiv___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceBdiv_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1387_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Int", 3, 3);
x_3 = lean_mk_string_unchecked("reduceBdiv", 10, 10);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Int_reduceBdiv___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Int_reduceBmod___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_mk_string_unchecked("Int", 3, 3);
x_8 = lean_mk_string_unchecked("bmod", 4, 4);
x_9 = l_Lean_Name_mkStr2(x_7, x_8);
x_10 = lean_alloc_closure((void*)(l_Int_bmod___boxed), 2, 0);
x_11 = l_Int_reduceBinIntNatOp___redArg(x_9, x_10, x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Int_reduceBmod(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Int_reduceBmod___redArg(x_1, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Int_reduceBmod___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Int_reduceBmod___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Int_reduceBmod___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Int_reduceBmod(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceBmod_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1404_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_2 = lean_mk_string_unchecked("Int", 3, 3);
x_3 = lean_mk_string_unchecked("reduceBmod", 10, 10);
lean_inc(x_2);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_mk_string_unchecked("bmod", 4, 4);
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
x_15 = lean_alloc_closure((void*)(l_Int_reduceBmod___boxed), 9, 0);
x_16 = l_Lean_Meta_Simp_registerBuiltinDSimproc(x_4, x_14, x_15, x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceBmod_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1406_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Int", 3, 3);
x_3 = lean_mk_string_unchecked("reduceBmod", 10, 10);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Int_reduceBmod___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceBmod_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1408_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Int", 3, 3);
x_3 = lean_mk_string_unchecked("reduceBmod", 10, 10);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Int_reduceBmod___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Int_reducePow___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
goto block_14;
}
else
{
lean_object* x_21; uint8_t x_22; 
x_21 = l_Lean_Expr_appFnCleanup___redArg(x_19);
x_22 = l_Lean_Expr_isApp(x_21);
if (x_22 == 0)
{
lean_dec(x_21);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
goto block_14;
}
else
{
lean_object* x_23; uint8_t x_24; 
x_23 = l_Lean_Expr_appFnCleanup___redArg(x_21);
x_24 = l_Lean_Expr_isApp(x_23);
if (x_24 == 0)
{
lean_dec(x_23);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
goto block_14;
}
else
{
lean_object* x_25; uint8_t x_26; 
x_25 = l_Lean_Expr_appFnCleanup___redArg(x_23);
x_26 = l_Lean_Expr_isApp(x_25);
if (x_26 == 0)
{
lean_dec(x_25);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
goto block_14;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_27 = l_Lean_Expr_appFnCleanup___redArg(x_25);
x_28 = lean_mk_string_unchecked("HPow", 4, 4);
x_29 = lean_mk_string_unchecked("hPow", 4, 4);
x_30 = l_Lean_Name_mkStr2(x_28, x_29);
x_31 = l_Lean_Expr_isConstOf(x_27, x_30);
lean_dec(x_30);
lean_dec(x_27);
if (x_31 == 0)
{
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
goto block_14;
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_10);
x_32 = lean_ctor_get(x_17, 1);
lean_inc(x_32);
lean_dec(x_17);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_33 = l_Lean_Meta_getIntValue_x3f(x_32, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
if (lean_obj_tag(x_34) == 0)
{
uint8_t x_35; 
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_35 = !lean_is_exclusive(x_33);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_33, 0);
lean_dec(x_36);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_33, 0, x_38);
return x_33;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_ctor_get(x_33, 1);
lean_inc(x_39);
lean_dec(x_33);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_39);
return x_42;
}
}
else
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_33, 1);
lean_inc(x_43);
lean_dec(x_33);
x_44 = !lean_is_exclusive(x_34);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_34, 0);
x_46 = lean_ctor_get(x_15, 1);
lean_inc(x_46);
lean_dec(x_15);
lean_inc(x_5);
lean_inc(x_4);
x_47 = l_Lean_Meta_getNatValue_x3f(x_46, x_2, x_3, x_4, x_5, x_43);
lean_dec(x_46);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
if (lean_obj_tag(x_48) == 0)
{
uint8_t x_49; 
lean_dec(x_45);
lean_dec(x_5);
lean_dec(x_4);
x_49 = !lean_is_exclusive(x_47);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_47, 0);
lean_dec(x_50);
x_51 = lean_box(0);
lean_ctor_set_tag(x_34, 2);
lean_ctor_set(x_34, 0, x_51);
lean_ctor_set(x_47, 0, x_34);
return x_47;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_47, 1);
lean_inc(x_52);
lean_dec(x_47);
x_53 = lean_box(0);
lean_ctor_set_tag(x_34, 2);
lean_ctor_set(x_34, 0, x_53);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_34);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
}
else
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_47);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_68; 
x_56 = lean_ctor_get(x_47, 1);
x_57 = lean_ctor_get(x_47, 0);
lean_dec(x_57);
x_58 = lean_ctor_get(x_48, 0);
lean_inc(x_58);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 x_59 = x_48;
} else {
 lean_dec_ref(x_48);
 x_59 = lean_box(0);
}
lean_inc(x_58);
x_60 = l_Lean_checkExponent(x_58, x_4, x_5, x_56);
lean_dec(x_5);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_63 = x_60;
} else {
 lean_dec_ref(x_60);
 x_63 = lean_box(0);
}
x_68 = lean_unbox(x_61);
lean_dec(x_61);
if (x_68 == 0)
{
lean_object* x_69; 
lean_dec(x_63);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_45);
x_69 = lean_box(0);
lean_ctor_set_tag(x_34, 2);
lean_ctor_set(x_34, 0, x_69);
lean_ctor_set(x_47, 1, x_62);
lean_ctor_set(x_47, 0, x_34);
return x_47;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
lean_free_object(x_47);
lean_free_object(x_34);
x_70 = l_Int_pow(x_45, x_58);
lean_dec(x_58);
lean_dec(x_45);
x_71 = lean_unsigned_to_nat(0u);
x_72 = lean_nat_to_int(x_71);
x_73 = lean_int_dec_le(x_72, x_70);
lean_dec(x_72);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_74 = lean_mk_string_unchecked("Neg", 3, 3);
x_75 = lean_mk_string_unchecked("neg", 3, 3);
x_76 = l_Lean_Name_mkStr2(x_74, x_75);
x_77 = l_Lean_Level_ofNat(x_71);
x_78 = lean_box(0);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
x_80 = l_Lean_Expr_const___override(x_76, x_79);
x_81 = lean_mk_string_unchecked("Int", 3, 3);
lean_inc(x_81);
x_82 = l_Lean_Name_mkStr1(x_81);
x_83 = l_Lean_Expr_const___override(x_82, x_78);
x_84 = lean_mk_string_unchecked("instNegInt", 10, 10);
x_85 = l_Lean_Name_mkStr2(x_81, x_84);
x_86 = l_Lean_Expr_const___override(x_85, x_78);
x_87 = lean_int_neg(x_70);
lean_dec(x_70);
x_88 = l_Int_toNat(x_87);
lean_dec(x_87);
x_89 = l_Lean_instToExprInt_mkNat(x_88);
x_90 = l_Lean_mkApp3(x_80, x_83, x_86, x_89);
x_64 = x_90;
goto block_67;
}
else
{
lean_object* x_91; lean_object* x_92; 
x_91 = l_Int_toNat(x_70);
lean_dec(x_70);
x_92 = l_Lean_instToExprInt_mkNat(x_91);
x_64 = x_92;
goto block_67;
}
}
block_67:
{
lean_object* x_65; lean_object* x_66; 
if (lean_is_scalar(x_59)) {
 x_65 = lean_alloc_ctor(0, 1, 0);
} else {
 x_65 = x_59;
 lean_ctor_set_tag(x_65, 0);
}
lean_ctor_set(x_65, 0, x_64);
if (lean_is_scalar(x_63)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_63;
}
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_62);
return x_66;
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_104; 
x_93 = lean_ctor_get(x_47, 1);
lean_inc(x_93);
lean_dec(x_47);
x_94 = lean_ctor_get(x_48, 0);
lean_inc(x_94);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 x_95 = x_48;
} else {
 lean_dec_ref(x_48);
 x_95 = lean_box(0);
}
lean_inc(x_94);
x_96 = l_Lean_checkExponent(x_94, x_4, x_5, x_93);
lean_dec(x_5);
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 lean_ctor_release(x_96, 1);
 x_99 = x_96;
} else {
 lean_dec_ref(x_96);
 x_99 = lean_box(0);
}
x_104 = lean_unbox(x_97);
lean_dec(x_97);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; 
lean_dec(x_99);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_45);
x_105 = lean_box(0);
lean_ctor_set_tag(x_34, 2);
lean_ctor_set(x_34, 0, x_105);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_34);
lean_ctor_set(x_106, 1, x_98);
return x_106;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; 
lean_free_object(x_34);
x_107 = l_Int_pow(x_45, x_94);
lean_dec(x_94);
lean_dec(x_45);
x_108 = lean_unsigned_to_nat(0u);
x_109 = lean_nat_to_int(x_108);
x_110 = lean_int_dec_le(x_109, x_107);
lean_dec(x_109);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_111 = lean_mk_string_unchecked("Neg", 3, 3);
x_112 = lean_mk_string_unchecked("neg", 3, 3);
x_113 = l_Lean_Name_mkStr2(x_111, x_112);
x_114 = l_Lean_Level_ofNat(x_108);
x_115 = lean_box(0);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
x_117 = l_Lean_Expr_const___override(x_113, x_116);
x_118 = lean_mk_string_unchecked("Int", 3, 3);
lean_inc(x_118);
x_119 = l_Lean_Name_mkStr1(x_118);
x_120 = l_Lean_Expr_const___override(x_119, x_115);
x_121 = lean_mk_string_unchecked("instNegInt", 10, 10);
x_122 = l_Lean_Name_mkStr2(x_118, x_121);
x_123 = l_Lean_Expr_const___override(x_122, x_115);
x_124 = lean_int_neg(x_107);
lean_dec(x_107);
x_125 = l_Int_toNat(x_124);
lean_dec(x_124);
x_126 = l_Lean_instToExprInt_mkNat(x_125);
x_127 = l_Lean_mkApp3(x_117, x_120, x_123, x_126);
x_100 = x_127;
goto block_103;
}
else
{
lean_object* x_128; lean_object* x_129; 
x_128 = l_Int_toNat(x_107);
lean_dec(x_107);
x_129 = l_Lean_instToExprInt_mkNat(x_128);
x_100 = x_129;
goto block_103;
}
}
block_103:
{
lean_object* x_101; lean_object* x_102; 
if (lean_is_scalar(x_95)) {
 x_101 = lean_alloc_ctor(0, 1, 0);
} else {
 x_101 = x_95;
 lean_ctor_set_tag(x_101, 0);
}
lean_ctor_set(x_101, 0, x_100);
if (lean_is_scalar(x_99)) {
 x_102 = lean_alloc_ctor(0, 2, 0);
} else {
 x_102 = x_99;
}
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_98);
return x_102;
}
}
}
}
else
{
uint8_t x_130; 
lean_free_object(x_34);
lean_dec(x_45);
lean_dec(x_5);
lean_dec(x_4);
x_130 = !lean_is_exclusive(x_47);
if (x_130 == 0)
{
return x_47;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = lean_ctor_get(x_47, 0);
x_132 = lean_ctor_get(x_47, 1);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_47);
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
return x_133;
}
}
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_134 = lean_ctor_get(x_34, 0);
lean_inc(x_134);
lean_dec(x_34);
x_135 = lean_ctor_get(x_15, 1);
lean_inc(x_135);
lean_dec(x_15);
lean_inc(x_5);
lean_inc(x_4);
x_136 = l_Lean_Meta_getNatValue_x3f(x_135, x_2, x_3, x_4, x_5, x_43);
lean_dec(x_135);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; 
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
lean_dec(x_134);
lean_dec(x_5);
lean_dec(x_4);
x_138 = lean_ctor_get(x_136, 1);
lean_inc(x_138);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 x_139 = x_136;
} else {
 lean_dec_ref(x_136);
 x_139 = lean_box(0);
}
x_140 = lean_box(0);
x_141 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_141, 0, x_140);
if (lean_is_scalar(x_139)) {
 x_142 = lean_alloc_ctor(0, 2, 0);
} else {
 x_142 = x_139;
}
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_138);
return x_142;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; uint8_t x_155; 
x_143 = lean_ctor_get(x_136, 1);
lean_inc(x_143);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 x_144 = x_136;
} else {
 lean_dec_ref(x_136);
 x_144 = lean_box(0);
}
x_145 = lean_ctor_get(x_137, 0);
lean_inc(x_145);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 x_146 = x_137;
} else {
 lean_dec_ref(x_137);
 x_146 = lean_box(0);
}
lean_inc(x_145);
x_147 = l_Lean_checkExponent(x_145, x_4, x_5, x_143);
lean_dec(x_5);
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_147, 1);
lean_inc(x_149);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 lean_ctor_release(x_147, 1);
 x_150 = x_147;
} else {
 lean_dec_ref(x_147);
 x_150 = lean_box(0);
}
x_155 = lean_unbox(x_148);
lean_dec(x_148);
if (x_155 == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; 
lean_dec(x_150);
lean_dec(x_146);
lean_dec(x_145);
lean_dec(x_134);
x_156 = lean_box(0);
x_157 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_157, 0, x_156);
if (lean_is_scalar(x_144)) {
 x_158 = lean_alloc_ctor(0, 2, 0);
} else {
 x_158 = x_144;
}
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_149);
return x_158;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; 
lean_dec(x_144);
x_159 = l_Int_pow(x_134, x_145);
lean_dec(x_145);
lean_dec(x_134);
x_160 = lean_unsigned_to_nat(0u);
x_161 = lean_nat_to_int(x_160);
x_162 = lean_int_dec_le(x_161, x_159);
lean_dec(x_161);
if (x_162 == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_163 = lean_mk_string_unchecked("Neg", 3, 3);
x_164 = lean_mk_string_unchecked("neg", 3, 3);
x_165 = l_Lean_Name_mkStr2(x_163, x_164);
x_166 = l_Lean_Level_ofNat(x_160);
x_167 = lean_box(0);
x_168 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_168, 0, x_166);
lean_ctor_set(x_168, 1, x_167);
x_169 = l_Lean_Expr_const___override(x_165, x_168);
x_170 = lean_mk_string_unchecked("Int", 3, 3);
lean_inc(x_170);
x_171 = l_Lean_Name_mkStr1(x_170);
x_172 = l_Lean_Expr_const___override(x_171, x_167);
x_173 = lean_mk_string_unchecked("instNegInt", 10, 10);
x_174 = l_Lean_Name_mkStr2(x_170, x_173);
x_175 = l_Lean_Expr_const___override(x_174, x_167);
x_176 = lean_int_neg(x_159);
lean_dec(x_159);
x_177 = l_Int_toNat(x_176);
lean_dec(x_176);
x_178 = l_Lean_instToExprInt_mkNat(x_177);
x_179 = l_Lean_mkApp3(x_169, x_172, x_175, x_178);
x_151 = x_179;
goto block_154;
}
else
{
lean_object* x_180; lean_object* x_181; 
x_180 = l_Int_toNat(x_159);
lean_dec(x_159);
x_181 = l_Lean_instToExprInt_mkNat(x_180);
x_151 = x_181;
goto block_154;
}
}
block_154:
{
lean_object* x_152; lean_object* x_153; 
if (lean_is_scalar(x_146)) {
 x_152 = lean_alloc_ctor(0, 1, 0);
} else {
 x_152 = x_146;
 lean_ctor_set_tag(x_152, 0);
}
lean_ctor_set(x_152, 0, x_151);
if (lean_is_scalar(x_150)) {
 x_153 = lean_alloc_ctor(0, 2, 0);
} else {
 x_153 = x_150;
}
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_153, 1, x_149);
return x_153;
}
}
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
lean_dec(x_134);
lean_dec(x_5);
lean_dec(x_4);
x_182 = lean_ctor_get(x_136, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_136, 1);
lean_inc(x_183);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 x_184 = x_136;
} else {
 lean_dec_ref(x_136);
 x_184 = lean_box(0);
}
if (lean_is_scalar(x_184)) {
 x_185 = lean_alloc_ctor(1, 2, 0);
} else {
 x_185 = x_184;
}
lean_ctor_set(x_185, 0, x_182);
lean_ctor_set(x_185, 1, x_183);
return x_185;
}
}
}
}
else
{
uint8_t x_186; 
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_186 = !lean_is_exclusive(x_33);
if (x_186 == 0)
{
return x_33;
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_187 = lean_ctor_get(x_33, 0);
x_188 = lean_ctor_get(x_33, 1);
lean_inc(x_188);
lean_inc(x_187);
lean_dec(x_33);
x_189 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_189, 0, x_187);
lean_ctor_set(x_189, 1, x_188);
return x_189;
}
}
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
LEAN_EXPORT lean_object* l_Int_reducePow(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Int_reducePow___redArg(x_1, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Int_reducePow___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Int_reducePow___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Int_reducePow___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Int_reducePow(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Int_reducePow_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1834_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_2 = lean_mk_string_unchecked("Int", 3, 3);
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
x_13 = lean_mk_string_unchecked("Nat", 3, 3);
x_14 = l_Lean_Name_mkStr1(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
x_16 = lean_box(3);
x_17 = lean_unsigned_to_nat(7u);
x_18 = lean_mk_empty_array_with_capacity(x_17);
x_19 = lean_array_push(x_18, x_9);
lean_inc(x_12);
x_20 = lean_array_push(x_19, x_12);
x_21 = lean_array_push(x_20, x_15);
x_22 = lean_array_push(x_21, x_12);
x_23 = lean_array_push(x_22, x_16);
x_24 = lean_array_push(x_23, x_16);
x_25 = lean_array_push(x_24, x_16);
x_26 = lean_alloc_closure((void*)(l_Int_reducePow___boxed), 9, 0);
x_27 = l_Lean_Meta_Simp_registerBuiltinDSimproc(x_4, x_25, x_26, x_1);
return x_27;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Int_reducePow_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1836_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Int", 3, 3);
x_3 = lean_mk_string_unchecked("reducePow", 9, 9);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Int_reducePow___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Int_reducePow_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1838_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Int", 3, 3);
x_3 = lean_mk_string_unchecked("reducePow", 9, 9);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Int_reducePow___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Int_reduceLT___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_17 = l_Lean_Meta_getIntValue_x3f(x_16, x_2, x_3, x_4, x_5, x_6);
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
x_31 = l_Lean_Meta_getIntValue_x3f(x_30, x_2, x_3, x_4, x_5, x_27);
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
x_41 = lean_int_dec_lt(x_29, x_40);
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
x_49 = l_Lean_Meta_getIntValue_x3f(x_48, x_2, x_3, x_4, x_5, x_27);
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
x_58 = lean_int_dec_lt(x_47, x_57);
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
LEAN_EXPORT lean_object* l_Int_reduceLT(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Int_reduceLT___redArg(x_1, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Int_reduceLT___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Int_reduceLT(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceLT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1873_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_2 = lean_mk_string_unchecked("Int", 3, 3);
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
x_21 = lean_alloc_closure((void*)(l_Int_reduceLT___boxed), 9, 0);
x_22 = l_Lean_Meta_Simp_registerBuiltinSimproc(x_4, x_20, x_21, x_1);
return x_22;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceLT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1875_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Int", 3, 3);
x_3 = lean_mk_string_unchecked("reduceLT", 8, 8);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Int_reduceLT___boxed), 9, 0);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceLT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1877_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Int", 3, 3);
x_3 = lean_mk_string_unchecked("reduceLT", 8, 8);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Int_reduceLT___boxed), 9, 0);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Int_reduceLE___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_mk_string_unchecked("LE", 2, 2);
x_8 = lean_mk_string_unchecked("le", 2, 2);
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
x_17 = l_Lean_Meta_getIntValue_x3f(x_16, x_2, x_3, x_4, x_5, x_6);
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
x_31 = l_Lean_Meta_getIntValue_x3f(x_30, x_2, x_3, x_4, x_5, x_27);
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
x_41 = lean_int_dec_le(x_29, x_40);
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
x_49 = l_Lean_Meta_getIntValue_x3f(x_48, x_2, x_3, x_4, x_5, x_27);
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
x_58 = lean_int_dec_le(x_47, x_57);
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
LEAN_EXPORT lean_object* l_Int_reduceLE(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Int_reduceLE___redArg(x_1, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Int_reduceLE___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Int_reduceLE(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceLE_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1912_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_2 = lean_mk_string_unchecked("Int", 3, 3);
x_3 = lean_mk_string_unchecked("reduceLE", 8, 8);
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
x_21 = lean_alloc_closure((void*)(l_Int_reduceLE___boxed), 9, 0);
x_22 = l_Lean_Meta_Simp_registerBuiltinSimproc(x_4, x_20, x_21, x_1);
return x_22;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceLE_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1914_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Int", 3, 3);
x_3 = lean_mk_string_unchecked("reduceLE", 8, 8);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Int_reduceLE___boxed), 9, 0);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceLE_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1916_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Int", 3, 3);
x_3 = lean_mk_string_unchecked("reduceLE", 8, 8);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Int_reduceLE___boxed), 9, 0);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Int_reduceGT___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_17 = l_Lean_Meta_getIntValue_x3f(x_16, x_2, x_3, x_4, x_5, x_6);
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
x_31 = l_Lean_Meta_getIntValue_x3f(x_30, x_2, x_3, x_4, x_5, x_27);
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
x_41 = lean_int_dec_lt(x_40, x_29);
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
x_49 = l_Lean_Meta_getIntValue_x3f(x_48, x_2, x_3, x_4, x_5, x_27);
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
x_58 = lean_int_dec_lt(x_57, x_47);
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
LEAN_EXPORT lean_object* l_Int_reduceGT(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Int_reduceGT___redArg(x_1, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Int_reduceGT___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Int_reduceGT(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceGT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1951_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_2 = lean_mk_string_unchecked("Int", 3, 3);
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
x_21 = lean_alloc_closure((void*)(l_Int_reduceGT___boxed), 9, 0);
x_22 = l_Lean_Meta_Simp_registerBuiltinSimproc(x_4, x_20, x_21, x_1);
return x_22;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceGT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1953_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Int", 3, 3);
x_3 = lean_mk_string_unchecked("reduceGT", 8, 8);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Int_reduceGT___boxed), 9, 0);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceGT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1955_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Int", 3, 3);
x_3 = lean_mk_string_unchecked("reduceGT", 8, 8);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Int_reduceGT___boxed), 9, 0);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Int_reduceGE___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_mk_string_unchecked("GE", 2, 2);
x_8 = lean_mk_string_unchecked("ge", 2, 2);
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
x_17 = l_Lean_Meta_getIntValue_x3f(x_16, x_2, x_3, x_4, x_5, x_6);
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
x_31 = l_Lean_Meta_getIntValue_x3f(x_30, x_2, x_3, x_4, x_5, x_27);
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
x_41 = lean_int_dec_le(x_40, x_29);
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
x_49 = l_Lean_Meta_getIntValue_x3f(x_48, x_2, x_3, x_4, x_5, x_27);
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
x_58 = lean_int_dec_le(x_57, x_47);
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
LEAN_EXPORT lean_object* l_Int_reduceGE(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Int_reduceGE___redArg(x_1, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Int_reduceGE___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Int_reduceGE(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceGE_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1990_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_2 = lean_mk_string_unchecked("Int", 3, 3);
x_3 = lean_mk_string_unchecked("reduceGE", 8, 8);
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
x_21 = lean_alloc_closure((void*)(l_Int_reduceGE___boxed), 9, 0);
x_22 = l_Lean_Meta_Simp_registerBuiltinSimproc(x_4, x_20, x_21, x_1);
return x_22;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceGE_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1992_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Int", 3, 3);
x_3 = lean_mk_string_unchecked("reduceGE", 8, 8);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Int_reduceGE___boxed), 9, 0);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceGE_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1994_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Int", 3, 3);
x_3 = lean_mk_string_unchecked("reduceGE", 8, 8);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Int_reduceGE___boxed), 9, 0);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Int_reduceEq___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = l_Lean_Expr_appFn_x21(x_1);
x_15 = l_Lean_Expr_appArg_x21(x_14);
lean_dec(x_14);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_16 = l_Lean_Meta_getIntValue_x3f(x_15, x_2, x_3, x_4, x_5, x_6);
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
lean_dec(x_2);
lean_dec(x_1);
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
x_29 = l_Lean_Expr_appArg_x21(x_1);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_30 = l_Lean_Meta_getIntValue_x3f(x_29, x_2, x_3, x_4, x_5, x_26);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
lean_dec(x_28);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; 
lean_free_object(x_17);
x_38 = lean_ctor_get(x_30, 1);
lean_inc(x_38);
lean_dec(x_30);
x_39 = lean_ctor_get(x_31, 0);
lean_inc(x_39);
lean_dec(x_31);
x_40 = lean_int_dec_eq(x_28, x_39);
lean_dec(x_39);
lean_dec(x_28);
x_41 = l_Lean_Meta_Simp_evalPropStep___redArg(x_1, x_40, x_2, x_3, x_4, x_5, x_38);
return x_41;
}
}
else
{
uint8_t x_42; 
lean_free_object(x_17);
lean_dec(x_28);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_30);
if (x_42 == 0)
{
return x_30;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_30, 0);
x_44 = lean_ctor_get(x_30, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_30);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_17, 0);
lean_inc(x_46);
lean_dec(x_17);
x_47 = l_Lean_Expr_appArg_x21(x_1);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_48 = l_Lean_Meta_getIntValue_x3f(x_47, x_2, x_3, x_4, x_5, x_26);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_46);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_51 = x_48;
} else {
 lean_dec_ref(x_48);
 x_51 = lean_box(0);
}
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_53, 0, x_52);
if (lean_is_scalar(x_51)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_51;
}
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_50);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_48, 1);
lean_inc(x_55);
lean_dec(x_48);
x_56 = lean_ctor_get(x_49, 0);
lean_inc(x_56);
lean_dec(x_49);
x_57 = lean_int_dec_eq(x_46, x_56);
lean_dec(x_56);
lean_dec(x_46);
x_58 = l_Lean_Meta_Simp_evalPropStep___redArg(x_1, x_57, x_2, x_3, x_4, x_5, x_55);
return x_58;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_46);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_59 = lean_ctor_get(x_48, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_48, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_61 = x_48;
} else {
 lean_dec_ref(x_48);
 x_61 = lean_box(0);
}
if (lean_is_scalar(x_61)) {
 x_62 = lean_alloc_ctor(1, 2, 0);
} else {
 x_62 = x_61;
}
lean_ctor_set(x_62, 0, x_59);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
}
}
}
else
{
uint8_t x_63; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_63 = !lean_is_exclusive(x_16);
if (x_63 == 0)
{
return x_16;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_16, 0);
x_65 = lean_ctor_get(x_16, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_16);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_reduceEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Int_reduceEq___redArg(x_1, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Int_reduceEq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Int_reduceEq(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_2029_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("Int", 3, 3);
x_3 = lean_mk_string_unchecked("reduceEq", 8, 8);
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
x_19 = lean_alloc_closure((void*)(l_Int_reduceEq___boxed), 9, 0);
x_20 = l_Lean_Meta_Simp_registerBuiltinSimproc(x_4, x_18, x_19, x_1);
return x_20;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_2031_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Int", 3, 3);
x_3 = lean_mk_string_unchecked("reduceEq", 8, 8);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Int_reduceEq___boxed), 9, 0);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_2033_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Int", 3, 3);
x_3 = lean_mk_string_unchecked("reduceEq", 8, 8);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Int_reduceEq___boxed), 9, 0);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Int_reduceNe___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_mk_string_unchecked("Ne", 2, 2);
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
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = l_Lean_Expr_appFn_x21(x_1);
x_15 = l_Lean_Expr_appArg_x21(x_14);
lean_dec(x_14);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_16 = l_Lean_Meta_getIntValue_x3f(x_15, x_2, x_3, x_4, x_5, x_6);
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
lean_dec(x_2);
lean_dec(x_1);
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
x_29 = l_Lean_Expr_appArg_x21(x_1);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_30 = l_Lean_Meta_getIntValue_x3f(x_29, x_2, x_3, x_4, x_5, x_26);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
lean_dec(x_28);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
lean_object* x_38; lean_object* x_39; uint8_t x_40; uint8_t x_41; lean_object* x_42; 
lean_free_object(x_17);
x_38 = lean_ctor_get(x_30, 1);
lean_inc(x_38);
lean_dec(x_30);
x_39 = lean_ctor_get(x_31, 0);
lean_inc(x_39);
lean_dec(x_31);
x_40 = lean_int_dec_eq(x_28, x_39);
lean_dec(x_39);
lean_dec(x_28);
x_41 = l_instDecidableNot___redArg(x_40);
x_42 = l_Lean_Meta_Simp_evalPropStep___redArg(x_1, x_41, x_2, x_3, x_4, x_5, x_38);
return x_42;
}
}
else
{
uint8_t x_43; 
lean_free_object(x_17);
lean_dec(x_28);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
x_48 = l_Lean_Expr_appArg_x21(x_1);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_49 = l_Lean_Meta_getIntValue_x3f(x_48, x_2, x_3, x_4, x_5, x_26);
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
lean_object* x_56; lean_object* x_57; uint8_t x_58; uint8_t x_59; lean_object* x_60; 
x_56 = lean_ctor_get(x_49, 1);
lean_inc(x_56);
lean_dec(x_49);
x_57 = lean_ctor_get(x_50, 0);
lean_inc(x_57);
lean_dec(x_50);
x_58 = lean_int_dec_eq(x_47, x_57);
lean_dec(x_57);
lean_dec(x_47);
x_59 = l_instDecidableNot___redArg(x_58);
x_60 = l_Lean_Meta_Simp_evalPropStep___redArg(x_1, x_59, x_2, x_3, x_4, x_5, x_56);
return x_60;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_47);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
LEAN_EXPORT lean_object* l_Int_reduceNe(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Int_reduceNe___redArg(x_1, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Int_reduceNe___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Int_reduceNe(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_2067_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_2 = lean_mk_string_unchecked("Int", 3, 3);
x_3 = lean_mk_string_unchecked("reduceNe", 8, 8);
lean_inc(x_2);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_mk_string_unchecked("Not", 3, 3);
x_6 = l_Lean_Name_mkStr1(x_5);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_mk_string_unchecked("Eq", 2, 2);
x_10 = l_Lean_Name_mkStr1(x_9);
x_11 = lean_unsigned_to_nat(3u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_Lean_Name_mkStr1(x_2);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_box(3);
x_17 = lean_unsigned_to_nat(5u);
x_18 = lean_mk_empty_array_with_capacity(x_17);
x_19 = lean_array_push(x_18, x_8);
x_20 = lean_array_push(x_19, x_12);
x_21 = lean_array_push(x_20, x_15);
x_22 = lean_array_push(x_21, x_16);
x_23 = lean_array_push(x_22, x_16);
x_24 = lean_alloc_closure((void*)(l_Int_reduceNe___boxed), 9, 0);
x_25 = l_Lean_Meta_Simp_registerBuiltinSimproc(x_4, x_23, x_24, x_1);
return x_25;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_2069_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Int", 3, 3);
x_3 = lean_mk_string_unchecked("reduceNe", 8, 8);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Int_reduceNe___boxed), 9, 0);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_2071_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Int", 3, 3);
x_3 = lean_mk_string_unchecked("reduceNe", 8, 8);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Int_reduceNe___boxed), 9, 0);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Int_reduceBEq___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_17 = l_Lean_Meta_getIntValue_x3f(x_16, x_2, x_3, x_4, x_5, x_6);
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
x_33 = l_Lean_Meta_getIntValue_x3f(x_32, x_2, x_3, x_4, x_5, x_28);
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
x_44 = lean_int_dec_eq(x_30, x_43);
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
x_63 = l_Lean_Meta_getIntValue_x3f(x_62, x_2, x_3, x_4, x_5, x_59);
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
x_75 = lean_int_dec_eq(x_60, x_74);
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
LEAN_EXPORT lean_object* l_Int_reduceBEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Int_reduceBEq___redArg(x_1, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Int_reduceBEq___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Int_reduceBEq___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Int_reduceBEq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Int_reduceBEq(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceBEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_2106_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_2 = lean_mk_string_unchecked("Int", 3, 3);
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
x_21 = lean_alloc_closure((void*)(l_Int_reduceBEq___boxed), 9, 0);
x_22 = l_Lean_Meta_Simp_registerBuiltinDSimproc(x_4, x_20, x_21, x_1);
return x_22;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceBEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_2108_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Int", 3, 3);
x_3 = lean_mk_string_unchecked("reduceBEq", 9, 9);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Int_reduceBEq___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceBEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_2110_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Int", 3, 3);
x_3 = lean_mk_string_unchecked("reduceBEq", 9, 9);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Int_reduceBEq___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Int_reduceBNe___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_16 = l_Lean_Meta_getIntValue_x3f(x_15, x_2, x_3, x_4, x_5, x_6);
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
x_32 = l_Lean_Meta_getIntValue_x3f(x_31, x_2, x_3, x_4, x_5, x_27);
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
x_49 = lean_int_dec_eq(x_29, x_48);
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
x_63 = l_Lean_Meta_getIntValue_x3f(x_62, x_2, x_3, x_4, x_5, x_59);
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
x_81 = lean_int_dec_eq(x_60, x_80);
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
LEAN_EXPORT lean_object* l_Int_reduceBNe(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Int_reduceBNe___redArg(x_1, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Int_reduceBNe___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Int_reduceBNe___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Int_reduceBNe___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Int_reduceBNe(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceBNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_2144_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_2 = lean_mk_string_unchecked("Int", 3, 3);
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
x_20 = lean_alloc_closure((void*)(l_Int_reduceBNe___boxed), 9, 0);
x_21 = l_Lean_Meta_Simp_registerBuiltinDSimproc(x_4, x_19, x_20, x_1);
return x_21;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceBNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_2146_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Int", 3, 3);
x_3 = lean_mk_string_unchecked("reduceBNe", 9, 9);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Int_reduceBNe___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceBNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_2148_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Int", 3, 3);
x_3 = lean_mk_string_unchecked("reduceBNe", 9, 9);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Int_reduceBNe___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Int_reduceNatCore___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = l_Lean_Expr_isAppOfArity(x_3, x_1, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_8);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Lean_Expr_appArg_x21(x_3);
x_15 = l_Lean_Meta_getIntValue_x3f(x_14, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
lean_dec(x_2);
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
x_29 = lean_apply_1(x_2, x_28);
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
x_32 = lean_apply_1(x_2, x_31);
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
x_38 = lean_apply_1(x_2, x_36);
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
lean_dec(x_2);
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
LEAN_EXPORT lean_object* l_Int_reduceNatCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = l_Lean_Expr_isAppOfArity(x_3, x_1, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_11);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = l_Lean_Expr_appArg_x21(x_3);
x_18 = l_Lean_Meta_getIntValue_x3f(x_17, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
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
x_32 = lean_apply_1(x_2, x_31);
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
x_35 = lean_apply_1(x_2, x_34);
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
x_41 = lean_apply_1(x_2, x_39);
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
lean_dec(x_2);
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
LEAN_EXPORT lean_object* l_Int_reduceNatCore___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Int_reduceNatCore___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Int_reduceNatCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Int_reduceNatCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Int_reduceAbs___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_mk_string_unchecked("Int", 3, 3);
x_8 = lean_mk_string_unchecked("natAbs", 6, 6);
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
x_16 = l_Lean_Meta_getIntValue_x3f(x_15, x_2, x_3, x_4, x_5, x_6);
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
x_30 = lean_nat_abs(x_29);
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
x_33 = lean_nat_abs(x_32);
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
x_39 = lean_nat_abs(x_37);
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
LEAN_EXPORT lean_object* l_Int_reduceAbs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Int_reduceAbs___redArg(x_1, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Int_reduceAbs___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Int_reduceAbs___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Int_reduceAbs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Int_reduceAbs(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceAbs_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_2264_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_2 = lean_mk_string_unchecked("Int", 3, 3);
x_3 = lean_mk_string_unchecked("reduceAbs", 9, 9);
lean_inc(x_2);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_mk_string_unchecked("natAbs", 6, 6);
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
x_14 = lean_alloc_closure((void*)(l_Int_reduceAbs___boxed), 9, 0);
x_15 = l_Lean_Meta_Simp_registerBuiltinDSimproc(x_4, x_13, x_14, x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceAbs_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_2266_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Int", 3, 3);
x_3 = lean_mk_string_unchecked("reduceAbs", 9, 9);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Int_reduceAbs___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceAbs_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_2268_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Int", 3, 3);
x_3 = lean_mk_string_unchecked("reduceAbs", 9, 9);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Int_reduceAbs___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Int_reduceToNat___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_mk_string_unchecked("Int", 3, 3);
x_8 = lean_mk_string_unchecked("toNat", 5, 5);
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
x_16 = l_Lean_Meta_getIntValue_x3f(x_15, x_2, x_3, x_4, x_5, x_6);
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
x_30 = l_Int_toNat(x_29);
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
x_33 = l_Int_toNat(x_32);
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
x_39 = l_Int_toNat(x_37);
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
LEAN_EXPORT lean_object* l_Int_reduceToNat(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Int_reduceToNat___redArg(x_1, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Int_reduceToNat___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Int_reduceToNat___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Int_reduceToNat___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Int_reduceToNat(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceToNat_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_2284_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_2 = lean_mk_string_unchecked("Int", 3, 3);
x_3 = lean_mk_string_unchecked("reduceToNat", 11, 11);
lean_inc(x_2);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_mk_string_unchecked("toNat", 5, 5);
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
x_14 = lean_alloc_closure((void*)(l_Int_reduceToNat___boxed), 9, 0);
x_15 = l_Lean_Meta_Simp_registerBuiltinDSimproc(x_4, x_13, x_14, x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceToNat_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_2286_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Int", 3, 3);
x_3 = lean_mk_string_unchecked("reduceToNat", 11, 11);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Int_reduceToNat___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceToNat_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_2288_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Int", 3, 3);
x_3 = lean_mk_string_unchecked("reduceToNat", 11, 11);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Int_reduceToNat___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Int_reduceNegSucc___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
goto block_14;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
lean_inc(x_15);
x_17 = l_Lean_Expr_appFnCleanup___redArg(x_15);
x_18 = lean_mk_string_unchecked("Int", 3, 3);
x_19 = lean_mk_string_unchecked("negSucc", 7, 7);
lean_inc(x_18);
x_20 = l_Lean_Name_mkStr2(x_18, x_19);
x_21 = l_Lean_Expr_isConstOf(x_17, x_20);
lean_dec(x_20);
lean_dec(x_17);
if (x_21 == 0)
{
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
goto block_14;
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_10);
x_22 = lean_ctor_get(x_15, 1);
lean_inc(x_22);
lean_dec(x_15);
x_23 = l_Lean_Meta_getNatValue_x3f(x_22, x_2, x_3, x_4, x_5, x_9);
lean_dec(x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_26 = x_23;
} else {
 lean_dec_ref(x_23);
 x_26 = lean_box(0);
}
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_26);
lean_dec(x_18);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_25);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_34 = lean_ctor_get(x_24, 0);
lean_inc(x_34);
lean_dec(x_24);
x_35 = lean_nat_to_int(x_34);
x_36 = lean_unsigned_to_nat(1u);
x_37 = lean_nat_to_int(x_36);
x_38 = lean_int_add(x_35, x_37);
lean_dec(x_37);
lean_dec(x_35);
x_39 = lean_int_neg(x_38);
lean_dec(x_38);
x_40 = lean_unsigned_to_nat(0u);
x_41 = lean_nat_to_int(x_40);
x_42 = lean_int_dec_le(x_41, x_39);
lean_dec(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_43 = lean_mk_string_unchecked("Neg", 3, 3);
x_44 = lean_mk_string_unchecked("neg", 3, 3);
x_45 = l_Lean_Name_mkStr2(x_43, x_44);
x_46 = l_Lean_Level_ofNat(x_40);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
x_49 = l_Lean_Expr_const___override(x_45, x_48);
lean_inc(x_18);
x_50 = l_Lean_Name_mkStr1(x_18);
x_51 = l_Lean_Expr_const___override(x_50, x_47);
x_52 = lean_mk_string_unchecked("instNegInt", 10, 10);
x_53 = l_Lean_Name_mkStr2(x_18, x_52);
x_54 = l_Lean_Expr_const___override(x_53, x_47);
x_55 = lean_int_neg(x_39);
lean_dec(x_39);
x_56 = l_Int_toNat(x_55);
lean_dec(x_55);
x_57 = l_Lean_instToExprInt_mkNat(x_56);
x_58 = l_Lean_mkApp3(x_49, x_51, x_54, x_57);
x_27 = x_58;
goto block_30;
}
else
{
lean_object* x_59; lean_object* x_60; 
lean_dec(x_18);
x_59 = l_Int_toNat(x_39);
lean_dec(x_39);
x_60 = l_Lean_instToExprInt_mkNat(x_59);
x_27 = x_60;
goto block_30;
}
}
block_30:
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
if (lean_is_scalar(x_26)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_26;
}
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_25);
return x_29;
}
}
else
{
uint8_t x_61; 
lean_dec(x_18);
x_61 = !lean_is_exclusive(x_23);
if (x_61 == 0)
{
return x_23;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_23, 0);
x_63 = lean_ctor_get(x_23, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_23);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
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
LEAN_EXPORT lean_object* l_Int_reduceNegSucc(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Int_reduceNegSucc___redArg(x_1, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Int_reduceNegSucc___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Int_reduceNegSucc___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Int_reduceNegSucc___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Int_reduceNegSucc(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceNegSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_2449_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_2 = lean_mk_string_unchecked("Int", 3, 3);
x_3 = lean_mk_string_unchecked("reduceNegSucc", 13, 13);
lean_inc(x_2);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_mk_string_unchecked("negSucc", 7, 7);
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
x_14 = lean_alloc_closure((void*)(l_Int_reduceNegSucc___boxed), 9, 0);
x_15 = l_Lean_Meta_Simp_registerBuiltinDSimproc(x_4, x_13, x_14, x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceNegSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_2451_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Int", 3, 3);
x_3 = lean_mk_string_unchecked("reduceNegSucc", 13, 13);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Int_reduceNegSucc___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceNegSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_2453_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Int", 3, 3);
x_3 = lean_mk_string_unchecked("reduceNegSucc", 13, 13);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Int_reduceNegSucc___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Int_reduceOfNat___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
goto block_14;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
lean_inc(x_15);
x_17 = l_Lean_Expr_appFnCleanup___redArg(x_15);
x_18 = lean_mk_string_unchecked("Int", 3, 3);
x_19 = lean_mk_string_unchecked("ofNat", 5, 5);
lean_inc(x_18);
x_20 = l_Lean_Name_mkStr2(x_18, x_19);
x_21 = l_Lean_Expr_isConstOf(x_17, x_20);
lean_dec(x_20);
lean_dec(x_17);
if (x_21 == 0)
{
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
goto block_14;
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_10);
x_22 = lean_ctor_get(x_15, 1);
lean_inc(x_22);
lean_dec(x_15);
x_23 = l_Lean_Meta_getNatValue_x3f(x_22, x_2, x_3, x_4, x_5, x_9);
lean_dec(x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_26 = x_23;
} else {
 lean_dec_ref(x_23);
 x_26 = lean_box(0);
}
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_26);
lean_dec(x_18);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_25);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_34 = lean_ctor_get(x_24, 0);
lean_inc(x_34);
lean_dec(x_24);
x_35 = lean_nat_to_int(x_34);
x_36 = lean_unsigned_to_nat(0u);
x_37 = lean_nat_to_int(x_36);
x_38 = lean_int_dec_le(x_37, x_35);
lean_dec(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_39 = lean_mk_string_unchecked("Neg", 3, 3);
x_40 = lean_mk_string_unchecked("neg", 3, 3);
x_41 = l_Lean_Name_mkStr2(x_39, x_40);
x_42 = l_Lean_Level_ofNat(x_36);
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = l_Lean_Expr_const___override(x_41, x_44);
lean_inc(x_18);
x_46 = l_Lean_Name_mkStr1(x_18);
x_47 = l_Lean_Expr_const___override(x_46, x_43);
x_48 = lean_mk_string_unchecked("instNegInt", 10, 10);
x_49 = l_Lean_Name_mkStr2(x_18, x_48);
x_50 = l_Lean_Expr_const___override(x_49, x_43);
x_51 = lean_int_neg(x_35);
lean_dec(x_35);
x_52 = l_Int_toNat(x_51);
lean_dec(x_51);
x_53 = l_Lean_instToExprInt_mkNat(x_52);
x_54 = l_Lean_mkApp3(x_45, x_47, x_50, x_53);
x_27 = x_54;
goto block_30;
}
else
{
lean_object* x_55; lean_object* x_56; 
lean_dec(x_18);
x_55 = l_Int_toNat(x_35);
lean_dec(x_35);
x_56 = l_Lean_instToExprInt_mkNat(x_55);
x_27 = x_56;
goto block_30;
}
}
block_30:
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
if (lean_is_scalar(x_26)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_26;
}
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_25);
return x_29;
}
}
else
{
uint8_t x_57; 
lean_dec(x_18);
x_57 = !lean_is_exclusive(x_23);
if (x_57 == 0)
{
return x_23;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_23, 0);
x_59 = lean_ctor_get(x_23, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_23);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
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
LEAN_EXPORT lean_object* l_Int_reduceOfNat(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Int_reduceOfNat___redArg(x_1, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Int_reduceOfNat___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Int_reduceOfNat___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Int_reduceOfNat___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Int_reduceOfNat(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceOfNat_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_2609_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_2 = lean_mk_string_unchecked("Int", 3, 3);
x_3 = lean_mk_string_unchecked("reduceOfNat", 11, 11);
lean_inc(x_2);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_mk_string_unchecked("ofNat", 5, 5);
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
x_14 = lean_alloc_closure((void*)(l_Int_reduceOfNat___boxed), 9, 0);
x_15 = l_Lean_Meta_Simp_registerBuiltinDSimproc(x_4, x_13, x_14, x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceOfNat_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_2611_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Int", 3, 3);
x_3 = lean_mk_string_unchecked("reduceOfNat", 11, 11);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Int_reduceOfNat___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceOfNat_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_2613_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Int", 3, 3);
x_3 = lean_mk_string_unchecked("reduceOfNat", 11, 11);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Int_reduceOfNat___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Int_reduceDvd___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_29 = lean_mk_string_unchecked("Int", 3, 3);
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
lean_inc(x_46);
x_47 = l_Lean_Meta_getIntValue_x3f(x_46, x_2, x_3, x_4, x_5, x_45);
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
lean_inc(x_60);
x_61 = l_Lean_Meta_getIntValue_x3f(x_60, x_2, x_3, x_4, x_5, x_57);
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
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_72 = lean_ctor_get(x_62, 0);
x_73 = lean_int_emod(x_72, x_59);
lean_dec(x_59);
lean_dec(x_72);
x_74 = lean_unsigned_to_nat(0u);
x_75 = lean_nat_to_int(x_74);
x_76 = lean_int_dec_eq(x_73, x_75);
lean_dec(x_75);
lean_dec(x_73);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_77 = lean_mk_string_unchecked("False", 5, 5);
x_78 = l_Lean_Name_mkStr1(x_77);
x_79 = l_Lean_Expr_const___override(x_78, x_32);
x_80 = lean_mk_string_unchecked("dvd_eq_false_of_mod_ne_zero", 27, 27);
x_81 = l_Lean_Name_mkStr2(x_29, x_80);
x_82 = l_Lean_Expr_const___override(x_81, x_32);
x_83 = l_Lean_reflBoolTrue;
x_84 = l_Lean_mkApp3(x_82, x_46, x_60, x_83);
lean_ctor_set(x_62, 0, x_84);
x_85 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_85, 0, x_79);
lean_ctor_set(x_85, 1, x_62);
x_86 = lean_unbox(x_35);
lean_dec(x_35);
lean_ctor_set_uint8(x_85, sizeof(void*)*2, x_86);
lean_ctor_set_tag(x_48, 0);
lean_ctor_set(x_48, 0, x_85);
lean_ctor_set(x_61, 0, x_48);
return x_61;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_87 = lean_mk_string_unchecked("True", 4, 4);
x_88 = l_Lean_Name_mkStr1(x_87);
x_89 = l_Lean_Expr_const___override(x_88, x_32);
x_90 = lean_mk_string_unchecked("dvd_eq_true_of_mod_eq_zero", 26, 26);
x_91 = l_Lean_Name_mkStr2(x_29, x_90);
x_92 = l_Lean_Expr_const___override(x_91, x_32);
x_93 = l_Lean_reflBoolTrue;
x_94 = l_Lean_mkApp3(x_92, x_46, x_60, x_93);
lean_ctor_set(x_62, 0, x_94);
x_95 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_95, 0, x_89);
lean_ctor_set(x_95, 1, x_62);
x_96 = lean_unbox(x_35);
lean_dec(x_35);
lean_ctor_set_uint8(x_95, sizeof(void*)*2, x_96);
lean_ctor_set_tag(x_48, 0);
lean_ctor_set(x_48, 0, x_95);
lean_ctor_set(x_61, 0, x_48);
return x_61;
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_97 = lean_ctor_get(x_62, 0);
lean_inc(x_97);
lean_dec(x_62);
x_98 = lean_int_emod(x_97, x_59);
lean_dec(x_59);
lean_dec(x_97);
x_99 = lean_unsigned_to_nat(0u);
x_100 = lean_nat_to_int(x_99);
x_101 = lean_int_dec_eq(x_98, x_100);
lean_dec(x_100);
lean_dec(x_98);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; 
x_102 = lean_mk_string_unchecked("False", 5, 5);
x_103 = l_Lean_Name_mkStr1(x_102);
x_104 = l_Lean_Expr_const___override(x_103, x_32);
x_105 = lean_mk_string_unchecked("dvd_eq_false_of_mod_ne_zero", 27, 27);
x_106 = l_Lean_Name_mkStr2(x_29, x_105);
x_107 = l_Lean_Expr_const___override(x_106, x_32);
x_108 = l_Lean_reflBoolTrue;
x_109 = l_Lean_mkApp3(x_107, x_46, x_60, x_108);
x_110 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_110, 0, x_109);
x_111 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_111, 0, x_104);
lean_ctor_set(x_111, 1, x_110);
x_112 = lean_unbox(x_35);
lean_dec(x_35);
lean_ctor_set_uint8(x_111, sizeof(void*)*2, x_112);
lean_ctor_set_tag(x_48, 0);
lean_ctor_set(x_48, 0, x_111);
lean_ctor_set(x_61, 0, x_48);
return x_61;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; 
x_113 = lean_mk_string_unchecked("True", 4, 4);
x_114 = l_Lean_Name_mkStr1(x_113);
x_115 = l_Lean_Expr_const___override(x_114, x_32);
x_116 = lean_mk_string_unchecked("dvd_eq_true_of_mod_eq_zero", 26, 26);
x_117 = l_Lean_Name_mkStr2(x_29, x_116);
x_118 = l_Lean_Expr_const___override(x_117, x_32);
x_119 = l_Lean_reflBoolTrue;
x_120 = l_Lean_mkApp3(x_118, x_46, x_60, x_119);
x_121 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_121, 0, x_120);
x_122 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_122, 0, x_115);
lean_ctor_set(x_122, 1, x_121);
x_123 = lean_unbox(x_35);
lean_dec(x_35);
lean_ctor_set_uint8(x_122, sizeof(void*)*2, x_123);
lean_ctor_set_tag(x_48, 0);
lean_ctor_set(x_48, 0, x_122);
lean_ctor_set(x_61, 0, x_48);
return x_61;
}
}
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; uint8_t x_130; 
x_124 = lean_ctor_get(x_61, 1);
lean_inc(x_124);
lean_dec(x_61);
x_125 = lean_ctor_get(x_62, 0);
lean_inc(x_125);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 x_126 = x_62;
} else {
 lean_dec_ref(x_62);
 x_126 = lean_box(0);
}
x_127 = lean_int_emod(x_125, x_59);
lean_dec(x_59);
lean_dec(x_125);
x_128 = lean_unsigned_to_nat(0u);
x_129 = lean_nat_to_int(x_128);
x_130 = lean_int_dec_eq(x_127, x_129);
lean_dec(x_129);
lean_dec(x_127);
if (x_130 == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; lean_object* x_142; 
x_131 = lean_mk_string_unchecked("False", 5, 5);
x_132 = l_Lean_Name_mkStr1(x_131);
x_133 = l_Lean_Expr_const___override(x_132, x_32);
x_134 = lean_mk_string_unchecked("dvd_eq_false_of_mod_ne_zero", 27, 27);
x_135 = l_Lean_Name_mkStr2(x_29, x_134);
x_136 = l_Lean_Expr_const___override(x_135, x_32);
x_137 = l_Lean_reflBoolTrue;
x_138 = l_Lean_mkApp3(x_136, x_46, x_60, x_137);
if (lean_is_scalar(x_126)) {
 x_139 = lean_alloc_ctor(1, 1, 0);
} else {
 x_139 = x_126;
}
lean_ctor_set(x_139, 0, x_138);
x_140 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_140, 0, x_133);
lean_ctor_set(x_140, 1, x_139);
x_141 = lean_unbox(x_35);
lean_dec(x_35);
lean_ctor_set_uint8(x_140, sizeof(void*)*2, x_141);
lean_ctor_set_tag(x_48, 0);
lean_ctor_set(x_48, 0, x_140);
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_48);
lean_ctor_set(x_142, 1, x_124);
return x_142;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; uint8_t x_153; lean_object* x_154; 
x_143 = lean_mk_string_unchecked("True", 4, 4);
x_144 = l_Lean_Name_mkStr1(x_143);
x_145 = l_Lean_Expr_const___override(x_144, x_32);
x_146 = lean_mk_string_unchecked("dvd_eq_true_of_mod_eq_zero", 26, 26);
x_147 = l_Lean_Name_mkStr2(x_29, x_146);
x_148 = l_Lean_Expr_const___override(x_147, x_32);
x_149 = l_Lean_reflBoolTrue;
x_150 = l_Lean_mkApp3(x_148, x_46, x_60, x_149);
if (lean_is_scalar(x_126)) {
 x_151 = lean_alloc_ctor(1, 1, 0);
} else {
 x_151 = x_126;
}
lean_ctor_set(x_151, 0, x_150);
x_152 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_152, 0, x_145);
lean_ctor_set(x_152, 1, x_151);
x_153 = lean_unbox(x_35);
lean_dec(x_35);
lean_ctor_set_uint8(x_152, sizeof(void*)*2, x_153);
lean_ctor_set_tag(x_48, 0);
lean_ctor_set(x_48, 0, x_152);
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_48);
lean_ctor_set(x_154, 1, x_124);
return x_154;
}
}
}
}
else
{
uint8_t x_155; 
lean_dec(x_60);
lean_free_object(x_48);
lean_dec(x_59);
lean_dec(x_46);
lean_dec(x_35);
lean_dec(x_29);
x_155 = !lean_is_exclusive(x_61);
if (x_155 == 0)
{
return x_61;
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_156 = lean_ctor_get(x_61, 0);
x_157 = lean_ctor_get(x_61, 1);
lean_inc(x_157);
lean_inc(x_156);
lean_dec(x_61);
x_158 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_158, 0, x_156);
lean_ctor_set(x_158, 1, x_157);
return x_158;
}
}
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_159 = lean_ctor_get(x_48, 0);
lean_inc(x_159);
lean_dec(x_48);
x_160 = lean_ctor_get(x_15, 1);
lean_inc(x_160);
lean_dec(x_15);
lean_inc(x_160);
x_161 = l_Lean_Meta_getIntValue_x3f(x_160, x_2, x_3, x_4, x_5, x_57);
lean_dec(x_2);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_162; 
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
lean_dec(x_160);
lean_dec(x_159);
lean_dec(x_46);
lean_dec(x_35);
lean_dec(x_29);
x_163 = lean_ctor_get(x_161, 1);
lean_inc(x_163);
if (lean_is_exclusive(x_161)) {
 lean_ctor_release(x_161, 0);
 lean_ctor_release(x_161, 1);
 x_164 = x_161;
} else {
 lean_dec_ref(x_161);
 x_164 = lean_box(0);
}
x_165 = lean_box(0);
x_166 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_166, 0, x_165);
if (lean_is_scalar(x_164)) {
 x_167 = lean_alloc_ctor(0, 2, 0);
} else {
 x_167 = x_164;
}
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_167, 1, x_163);
return x_167;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; uint8_t x_175; 
x_168 = lean_ctor_get(x_161, 1);
lean_inc(x_168);
if (lean_is_exclusive(x_161)) {
 lean_ctor_release(x_161, 0);
 lean_ctor_release(x_161, 1);
 x_169 = x_161;
} else {
 lean_dec_ref(x_161);
 x_169 = lean_box(0);
}
x_170 = lean_ctor_get(x_162, 0);
lean_inc(x_170);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 x_171 = x_162;
} else {
 lean_dec_ref(x_162);
 x_171 = lean_box(0);
}
x_172 = lean_int_emod(x_170, x_159);
lean_dec(x_159);
lean_dec(x_170);
x_173 = lean_unsigned_to_nat(0u);
x_174 = lean_nat_to_int(x_173);
x_175 = lean_int_dec_eq(x_172, x_174);
lean_dec(x_174);
lean_dec(x_172);
if (x_175 == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; uint8_t x_186; lean_object* x_187; lean_object* x_188; 
x_176 = lean_mk_string_unchecked("False", 5, 5);
x_177 = l_Lean_Name_mkStr1(x_176);
x_178 = l_Lean_Expr_const___override(x_177, x_32);
x_179 = lean_mk_string_unchecked("dvd_eq_false_of_mod_ne_zero", 27, 27);
x_180 = l_Lean_Name_mkStr2(x_29, x_179);
x_181 = l_Lean_Expr_const___override(x_180, x_32);
x_182 = l_Lean_reflBoolTrue;
x_183 = l_Lean_mkApp3(x_181, x_46, x_160, x_182);
if (lean_is_scalar(x_171)) {
 x_184 = lean_alloc_ctor(1, 1, 0);
} else {
 x_184 = x_171;
}
lean_ctor_set(x_184, 0, x_183);
x_185 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_185, 0, x_178);
lean_ctor_set(x_185, 1, x_184);
x_186 = lean_unbox(x_35);
lean_dec(x_35);
lean_ctor_set_uint8(x_185, sizeof(void*)*2, x_186);
x_187 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_187, 0, x_185);
if (lean_is_scalar(x_169)) {
 x_188 = lean_alloc_ctor(0, 2, 0);
} else {
 x_188 = x_169;
}
lean_ctor_set(x_188, 0, x_187);
lean_ctor_set(x_188, 1, x_168);
return x_188;
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; uint8_t x_199; lean_object* x_200; lean_object* x_201; 
x_189 = lean_mk_string_unchecked("True", 4, 4);
x_190 = l_Lean_Name_mkStr1(x_189);
x_191 = l_Lean_Expr_const___override(x_190, x_32);
x_192 = lean_mk_string_unchecked("dvd_eq_true_of_mod_eq_zero", 26, 26);
x_193 = l_Lean_Name_mkStr2(x_29, x_192);
x_194 = l_Lean_Expr_const___override(x_193, x_32);
x_195 = l_Lean_reflBoolTrue;
x_196 = l_Lean_mkApp3(x_194, x_46, x_160, x_195);
if (lean_is_scalar(x_171)) {
 x_197 = lean_alloc_ctor(1, 1, 0);
} else {
 x_197 = x_171;
}
lean_ctor_set(x_197, 0, x_196);
x_198 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_198, 0, x_191);
lean_ctor_set(x_198, 1, x_197);
x_199 = lean_unbox(x_35);
lean_dec(x_35);
lean_ctor_set_uint8(x_198, sizeof(void*)*2, x_199);
x_200 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_200, 0, x_198);
if (lean_is_scalar(x_169)) {
 x_201 = lean_alloc_ctor(0, 2, 0);
} else {
 x_201 = x_169;
}
lean_ctor_set(x_201, 0, x_200);
lean_ctor_set(x_201, 1, x_168);
return x_201;
}
}
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
lean_dec(x_160);
lean_dec(x_159);
lean_dec(x_46);
lean_dec(x_35);
lean_dec(x_29);
x_202 = lean_ctor_get(x_161, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_161, 1);
lean_inc(x_203);
if (lean_is_exclusive(x_161)) {
 lean_ctor_release(x_161, 0);
 lean_ctor_release(x_161, 1);
 x_204 = x_161;
} else {
 lean_dec_ref(x_161);
 x_204 = lean_box(0);
}
if (lean_is_scalar(x_204)) {
 x_205 = lean_alloc_ctor(1, 2, 0);
} else {
 x_205 = x_204;
}
lean_ctor_set(x_205, 0, x_202);
lean_ctor_set(x_205, 1, x_203);
return x_205;
}
}
}
}
else
{
uint8_t x_206; 
lean_dec(x_46);
lean_dec(x_35);
lean_dec(x_29);
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_206 = !lean_is_exclusive(x_47);
if (x_206 == 0)
{
return x_47;
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_207 = lean_ctor_get(x_47, 0);
x_208 = lean_ctor_get(x_47, 1);
lean_inc(x_208);
lean_inc(x_207);
lean_dec(x_47);
x_209 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_209, 0, x_207);
lean_ctor_set(x_209, 1, x_208);
return x_209;
}
}
}
}
else
{
uint8_t x_210; 
lean_dec(x_29);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_210 = !lean_is_exclusive(x_34);
if (x_210 == 0)
{
return x_34;
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_211 = lean_ctor_get(x_34, 0);
x_212 = lean_ctor_get(x_34, 1);
lean_inc(x_212);
lean_inc(x_211);
lean_dec(x_34);
x_213 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_213, 0, x_211);
lean_ctor_set(x_213, 1, x_212);
return x_213;
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
LEAN_EXPORT lean_object* l_Int_reduceDvd(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Int_reduceDvd___redArg(x_1, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Int_reduceDvd___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Int_reduceDvd(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceDvd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_3020_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_2 = lean_mk_string_unchecked("Int", 3, 3);
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
x_21 = lean_alloc_closure((void*)(l_Int_reduceDvd___boxed), 9, 0);
x_22 = l_Lean_Meta_Simp_registerBuiltinSimproc(x_4, x_20, x_21, x_1);
return x_22;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceDvd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_3022_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Int", 3, 3);
x_3 = lean_mk_string_unchecked("reduceDvd", 9, 9);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Int_reduceDvd___boxed), 9, 0);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceDvd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_3024_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Int", 3, 3);
x_3 = lean_mk_string_unchecked("reduceDvd", 9, 9);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Int_reduceDvd___boxed), 9, 0);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCastCore___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_4);
x_8 = l_Lean_Meta_getNatValue_x3f(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
lean_dec(x_4);
lean_dec(x_1);
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_8, 0);
lean_dec(x_11);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_8, 0, x_13);
return x_8;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_14);
lean_dec(x_8);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_14);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_8);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_19 = lean_ctor_get(x_8, 1);
x_20 = lean_ctor_get(x_8, 0);
lean_dec(x_20);
x_21 = lean_ctor_get(x_9, 0);
lean_inc(x_21);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 x_22 = x_9;
} else {
 lean_dec_ref(x_9);
 x_22 = lean_box(0);
}
x_23 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_1, x_4, x_19);
lean_dec(x_4);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_26 = x_23;
} else {
 lean_dec_ref(x_23);
 x_26 = lean_box(0);
}
x_31 = l_Lean_Expr_cleanupAnnotations(x_24);
x_32 = lean_mk_string_unchecked("instNatCastInt", 14, 14);
x_33 = l_Lean_Name_mkStr1(x_32);
x_34 = l_Lean_Expr_isConstOf(x_31, x_33);
lean_dec(x_33);
lean_dec(x_31);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_26);
lean_dec(x_22);
lean_dec(x_21);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_8, 1, x_25);
lean_ctor_set(x_8, 0, x_36);
return x_8;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
lean_free_object(x_8);
x_37 = lean_nat_to_int(x_21);
x_38 = lean_unsigned_to_nat(0u);
x_39 = lean_nat_to_int(x_38);
x_40 = lean_int_dec_le(x_39, x_37);
lean_dec(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_41 = lean_mk_string_unchecked("Neg", 3, 3);
x_42 = lean_mk_string_unchecked("neg", 3, 3);
x_43 = l_Lean_Name_mkStr2(x_41, x_42);
x_44 = l_Lean_Level_ofNat(x_38);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = l_Lean_Expr_const___override(x_43, x_46);
x_48 = lean_mk_string_unchecked("Int", 3, 3);
lean_inc(x_48);
x_49 = l_Lean_Name_mkStr1(x_48);
x_50 = l_Lean_Expr_const___override(x_49, x_45);
x_51 = lean_mk_string_unchecked("instNegInt", 10, 10);
x_52 = l_Lean_Name_mkStr2(x_48, x_51);
x_53 = l_Lean_Expr_const___override(x_52, x_45);
x_54 = lean_int_neg(x_37);
lean_dec(x_37);
x_55 = l_Int_toNat(x_54);
lean_dec(x_54);
x_56 = l_Lean_instToExprInt_mkNat(x_55);
x_57 = l_Lean_mkApp3(x_47, x_50, x_53, x_56);
x_27 = x_57;
goto block_30;
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = l_Int_toNat(x_37);
lean_dec(x_37);
x_59 = l_Lean_instToExprInt_mkNat(x_58);
x_27 = x_59;
goto block_30;
}
}
block_30:
{
lean_object* x_28; lean_object* x_29; 
if (lean_is_scalar(x_22)) {
 x_28 = lean_alloc_ctor(0, 1, 0);
} else {
 x_28 = x_22;
 lean_ctor_set_tag(x_28, 0);
}
lean_ctor_set(x_28, 0, x_27);
if (lean_is_scalar(x_26)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_26;
}
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_25);
return x_29;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_60 = lean_ctor_get(x_8, 1);
lean_inc(x_60);
lean_dec(x_8);
x_61 = lean_ctor_get(x_9, 0);
lean_inc(x_61);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 x_62 = x_9;
} else {
 lean_dec_ref(x_9);
 x_62 = lean_box(0);
}
x_63 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_1, x_4, x_60);
lean_dec(x_4);
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
x_71 = l_Lean_Expr_cleanupAnnotations(x_64);
x_72 = lean_mk_string_unchecked("instNatCastInt", 14, 14);
x_73 = l_Lean_Name_mkStr1(x_72);
x_74 = l_Lean_Expr_isConstOf(x_71, x_73);
lean_dec(x_73);
lean_dec(x_71);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_66);
lean_dec(x_62);
lean_dec(x_61);
x_75 = lean_box(0);
x_76 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_76, 0, x_75);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_65);
return x_77;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_78 = lean_nat_to_int(x_61);
x_79 = lean_unsigned_to_nat(0u);
x_80 = lean_nat_to_int(x_79);
x_81 = lean_int_dec_le(x_80, x_78);
lean_dec(x_80);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_82 = lean_mk_string_unchecked("Neg", 3, 3);
x_83 = lean_mk_string_unchecked("neg", 3, 3);
x_84 = l_Lean_Name_mkStr2(x_82, x_83);
x_85 = l_Lean_Level_ofNat(x_79);
x_86 = lean_box(0);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
x_88 = l_Lean_Expr_const___override(x_84, x_87);
x_89 = lean_mk_string_unchecked("Int", 3, 3);
lean_inc(x_89);
x_90 = l_Lean_Name_mkStr1(x_89);
x_91 = l_Lean_Expr_const___override(x_90, x_86);
x_92 = lean_mk_string_unchecked("instNegInt", 10, 10);
x_93 = l_Lean_Name_mkStr2(x_89, x_92);
x_94 = l_Lean_Expr_const___override(x_93, x_86);
x_95 = lean_int_neg(x_78);
lean_dec(x_78);
x_96 = l_Int_toNat(x_95);
lean_dec(x_95);
x_97 = l_Lean_instToExprInt_mkNat(x_96);
x_98 = l_Lean_mkApp3(x_88, x_91, x_94, x_97);
x_67 = x_98;
goto block_70;
}
else
{
lean_object* x_99; lean_object* x_100; 
x_99 = l_Int_toNat(x_78);
lean_dec(x_78);
x_100 = l_Lean_instToExprInt_mkNat(x_99);
x_67 = x_100;
goto block_70;
}
}
block_70:
{
lean_object* x_68; lean_object* x_69; 
if (lean_is_scalar(x_62)) {
 x_68 = lean_alloc_ctor(0, 1, 0);
} else {
 x_68 = x_62;
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
}
}
else
{
uint8_t x_101; 
lean_dec(x_4);
lean_dec(x_1);
x_101 = !lean_is_exclusive(x_8);
if (x_101 == 0)
{
return x_8;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_8, 0);
x_103 = lean_ctor_get(x_8, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_8);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
return x_104;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCastCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCastCore___redArg(x_1, x_2, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCastCore___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCastCore___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCastCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCastCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Int_reduceNatCast___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
goto block_14;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_21 = l_Lean_Expr_appFnCleanup___redArg(x_19);
x_22 = lean_mk_string_unchecked("NatCast", 7, 7);
x_23 = lean_mk_string_unchecked("natCast", 7, 7);
x_24 = l_Lean_Name_mkStr2(x_22, x_23);
x_25 = l_Lean_Expr_isConstOf(x_21, x_24);
lean_dec(x_24);
lean_dec(x_21);
if (x_25 == 0)
{
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
goto block_14;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_10);
x_26 = lean_ctor_get(x_15, 1);
lean_inc(x_26);
lean_dec(x_15);
x_27 = lean_ctor_get(x_17, 1);
lean_inc(x_27);
lean_dec(x_17);
x_28 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCastCore___redArg(x_27, x_26, x_2, x_3, x_4, x_5, x_9);
lean_dec(x_26);
return x_28;
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
LEAN_EXPORT lean_object* l_Int_reduceNatCast(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Int_reduceNatCast___redArg(x_1, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Int_reduceNatCast___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Int_reduceNatCast___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Int_reduceNatCast___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Int_reduceNatCast(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceNatCast_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_3316_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_2 = lean_mk_string_unchecked("Int", 3, 3);
x_3 = lean_mk_string_unchecked("reduceNatCast", 13, 13);
lean_inc(x_2);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_mk_string_unchecked("NatCast", 7, 7);
x_6 = lean_mk_string_unchecked("natCast", 7, 7);
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
x_20 = lean_alloc_closure((void*)(l_Int_reduceNatCast___boxed), 9, 0);
x_21 = l_Lean_Meta_Simp_registerBuiltinDSimproc(x_4, x_19, x_20, x_1);
return x_21;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceNatCast_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_3318_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Int", 3, 3);
x_3 = lean_mk_string_unchecked("reduceNatCast", 13, 13);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Int_reduceNatCast___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceNatCast_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_3320_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Int", 3, 3);
x_3 = lean_mk_string_unchecked("reduceNatCast", 13, 13);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Int_reduceNatCast___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Int_reduceNatCast_x27___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
goto block_14;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_21 = l_Lean_Expr_appFnCleanup___redArg(x_19);
x_22 = lean_mk_string_unchecked("Nat", 3, 3);
x_23 = lean_mk_string_unchecked("cast", 4, 4);
x_24 = l_Lean_Name_mkStr2(x_22, x_23);
x_25 = l_Lean_Expr_isConstOf(x_21, x_24);
lean_dec(x_24);
lean_dec(x_21);
if (x_25 == 0)
{
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
goto block_14;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_10);
x_26 = lean_ctor_get(x_15, 1);
lean_inc(x_26);
lean_dec(x_15);
x_27 = lean_ctor_get(x_17, 1);
lean_inc(x_27);
lean_dec(x_17);
x_28 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCastCore___redArg(x_27, x_26, x_2, x_3, x_4, x_5, x_9);
lean_dec(x_26);
return x_28;
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
LEAN_EXPORT lean_object* l_Int_reduceNatCast_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Int_reduceNatCast_x27___redArg(x_1, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Int_reduceNatCast_x27___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Int_reduceNatCast_x27___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Int_reduceNatCast_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Int_reduceNatCast_x27(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceNatCast_x27_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_3501_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_2 = lean_mk_string_unchecked("Int", 3, 3);
x_3 = lean_mk_string_unchecked("reduceNatCast'", 14, 14);
lean_inc(x_2);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_mk_string_unchecked("NatCast", 7, 7);
x_6 = lean_mk_string_unchecked("natCast", 7, 7);
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
x_20 = lean_alloc_closure((void*)(l_Int_reduceNatCast_x27___boxed), 9, 0);
x_21 = l_Lean_Meta_Simp_registerBuiltinDSimproc(x_4, x_19, x_20, x_1);
return x_21;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceNatCast_x27_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_3503_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Int", 3, 3);
x_3 = lean_mk_string_unchecked("reduceNatCast'", 14, 14);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Int_reduceNatCast_x27___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Int_reduceNatCast_x27_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_3505_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Int", 3, 3);
x_3 = lean_mk_string_unchecked("reduceNatCast'", 14, 14);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Int_reduceNatCast_x27___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
lean_object* initialize_Lean_ToExpr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_LitValues(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_ToExpr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_LitValues(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
if (builtin) {res = l___regBuiltin_Int_reduceNeg_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_910_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Int_reduceNeg_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_912_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Int_reduceNeg_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_914_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Int_isPosValue_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1086_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Int_isPosValue_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1088_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Int_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1122_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Int_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1124_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Int_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1126_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Int_reduceMul_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1160_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Int_reduceMul_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1162_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Int_reduceMul_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1164_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Int_reduceSub_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1198_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Int_reduceSub_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1200_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Int_reduceSub_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1202_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Int_reduceDiv_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1236_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Int_reduceDiv_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1238_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Int_reduceDiv_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1240_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Int_reduceMod_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1274_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Int_reduceMod_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1276_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Int_reduceMod_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1278_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Int_reduceTDiv_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1296_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Int_reduceTDiv_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1298_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Int_reduceTDiv_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1300_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Int_reduceTMod_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1318_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Int_reduceTMod_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1320_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Int_reduceTMod_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1322_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Int_reduceFDiv_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1340_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Int_reduceFDiv_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1342_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Int_reduceFDiv_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1344_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Int_reduceFMod_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1362_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Int_reduceFMod_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1364_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Int_reduceFMod_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1366_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Int_reduceBdiv_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1383_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Int_reduceBdiv_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1385_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Int_reduceBdiv_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1387_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Int_reduceBmod_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1404_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Int_reduceBmod_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1406_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Int_reduceBmod_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1408_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Int_reducePow_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1834_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Int_reducePow_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1836_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Int_reducePow_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1838_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Int_reduceLT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1873_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Int_reduceLT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1875_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Int_reduceLT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1877_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Int_reduceLE_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1912_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Int_reduceLE_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1914_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Int_reduceLE_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1916_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Int_reduceGT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1951_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Int_reduceGT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1953_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Int_reduceGT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1955_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Int_reduceGE_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1990_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Int_reduceGE_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1992_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Int_reduceGE_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_1994_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Int_reduceEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_2029_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Int_reduceEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_2031_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Int_reduceEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_2033_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Int_reduceNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_2067_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Int_reduceNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_2069_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Int_reduceNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_2071_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Int_reduceBEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_2106_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Int_reduceBEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_2108_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Int_reduceBEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_2110_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Int_reduceBNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_2144_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Int_reduceBNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_2146_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Int_reduceBNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_2148_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Int_reduceAbs_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_2264_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Int_reduceAbs_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_2266_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Int_reduceAbs_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_2268_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Int_reduceToNat_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_2284_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Int_reduceToNat_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_2286_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Int_reduceToNat_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_2288_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Int_reduceNegSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_2449_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Int_reduceNegSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_2451_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Int_reduceNegSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_2453_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Int_reduceOfNat_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_2609_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Int_reduceOfNat_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_2611_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Int_reduceOfNat_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_2613_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Int_reduceDvd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_3020_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Int_reduceDvd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_3022_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Int_reduceDvd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_3024_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Int_reduceNatCast_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_3316_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Int_reduceNatCast_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_3318_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Int_reduceNatCast_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_3320_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Int_reduceNatCast_x27_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_3501_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Int_reduceNatCast_x27_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_3503_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Int_reduceNatCast_x27_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int___hyg_3505_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
