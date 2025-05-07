// Lean compiler output
// Module: Lean.Meta.Tactic.Simp.BuiltinSimprocs.Char
// Imports: Lean.ToExpr Lean.Meta.LitValues Lean.Meta.Tactic.Simp.BuiltinSimprocs.UInt
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
LEAN_EXPORT lean_object* l_Char_reduceBNe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceIsDigit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_evalPropStep___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceBoolPred___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceIsUpper___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceVal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceDefault_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_1500_(lean_object*);
lean_object* l_Lean_Meta_getCharValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceToLower___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceToNat___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceOfNatAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceToNat_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_456_(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceGT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_874_(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceToLower_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_418_(lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* l_Lean_Meta_getNatValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceBoolPred___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceOfNatAux___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceBEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_isValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceToString_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_604_(lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceIsDigit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceUnary(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceToUpper___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceIsLower___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceLT___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceIsUpper_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_496_(lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceToNat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceLE_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_835_(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceToString_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_602_(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceGT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_876_(lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceUnary___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceIsAlphaNum___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceBNe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Char_isValue_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_1158_(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceToUpper_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_438_(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceLE_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_839_(lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceBEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_fromExpr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceIsWhitespace_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_478_(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceLE_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_837_(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Char_isValue_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_1154_(lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceLT___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceIsAlphaNum_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_580_(lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceIsWhitespace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceToUpper_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_440_(lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceToString___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceIsAlphaNum_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_578_(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceIsDigit_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_556_(lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceIsAlphaNum___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceBoolPred___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceIsLower_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_518_(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceToString_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_600_(lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceNe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkStrLit(lean_object*);
uint32_t l_Char_toLower(uint32_t);
LEAN_EXPORT lean_object* l_Char_reduceNe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceIsWhitespace_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_480_(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceToLower_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_416_(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceToLower_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_420_(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_990_(lean_object*);
uint32_t l_Char_toUpper(uint32_t);
LEAN_EXPORT lean_object* l_Char_reduceUnary___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_fromExpr_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceOfNatAux_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_1349_(lean_object*);
uint32_t lean_uint32_of_nat(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceToUpper_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_436_(lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceBinPred___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Char_isValue_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_1156_(lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceIsWhitespace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceNe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceBEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_1033_(lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceIsWhitespace___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceVal_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_757_(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceGT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_878_(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceLT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_798_(lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceToLower___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceToNat___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceIsUpper(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_952_(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceDefault_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_1498_(lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceBinPred___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceIsLower___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceOfNatAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceIsAlpha_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_540_(lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceIsDigit___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceLE___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceIsAlpha(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceBNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_1071_(lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceDefault___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceIsDigit_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_558_(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceBEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_1031_(lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceToNat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceEq___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_isValue___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceVal_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_761_(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceBNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_1069_(lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceIsLower(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceDefault___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceToNat_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_458_(lean_object*);
LEAN_EXPORT lean_object* l_Char_isValue___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_994_(lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceLE___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceIsUpper_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_498_(lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceLT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_800_(lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceBNe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceVal_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_759_(lean_object*);
lean_object* l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceIsLower_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_516_(lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceOfNatAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceBNe___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceIsAlpha___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceIsWhitespace_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_476_(lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceToString(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceLT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_796_(lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceToString___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_992_(lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceDefault___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceBNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_1067_(lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceDefault(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceGT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceIsAlpha_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_536_(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_956_(lean_object*);
LEAN_EXPORT lean_object* l_Char_fromExpr_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_registerBuiltinSimproc(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceDefault_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_1496_(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceToNat_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_460_(lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceGE___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkRawNatLit(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceOfNatAux_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_1345_(lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceToUpper___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceGE_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_915_(lean_object*);
lean_object* l_Lean_Meta_Simp_registerBuiltinDSimproc(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceToString___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceLE(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceIsLower___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceIsUpper___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceUnary___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceGE_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_913_(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceIsLower_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_520_(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceGE_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_917_(lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceVal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_fromExpr_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceBEq___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceVal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceToUpper___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceIsUpper___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_instDecidableNot___redArg(uint8_t);
LEAN_EXPORT lean_object* l_Char_reduceToLower___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceBEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_1029_(lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceBinPred(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceBEq___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceGT___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceToLower(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_954_(lean_object*);
lean_object* l_Lean_Meta_Simp_addSimprocBuiltinAttr(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceIsUpper_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_500_(lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceLT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceIsDigit___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_isValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceIsDigit_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_560_(lean_object*);
uint8_t lean_uint32_dec_lt(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Char_reduceGT___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceIsAlpha___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceOfNatAux_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_1347_(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceIsAlpha_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_538_(lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceIsWhitespace___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceBinPred___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceGE(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceIsAlphaNum_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_576_(lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceIsAlphaNum(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceBoolPred(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceIsAlpha___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_instDecidableEqChar(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Char_reduceToUpper(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceIsAlphaNum___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t l_Char_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceGE___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceVal___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_fromExpr_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_getCharValue_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Char_fromExpr_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_getCharValue_x3f(x_1, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Char_fromExpr_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Char_fromExpr_x3f___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Char_fromExpr_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Char_fromExpr_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Char_reduceUnary___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = l_Lean_Expr_isAppOfArity(x_5, x_2, x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_10);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = l_Lean_Expr_appArg_x21(x_5);
x_16 = l_Lean_Meta_getCharValue_x3f(x_15, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
lean_dec(x_3);
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
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_17, 0);
x_30 = lean_ctor_get(x_1, 0);
lean_inc(x_30);
lean_dec(x_1);
x_31 = lean_apply_1(x_3, x_29);
x_32 = lean_apply_1(x_30, x_31);
lean_ctor_set_tag(x_17, 0);
lean_ctor_set(x_17, 0, x_32);
return x_16;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_17, 0);
lean_inc(x_33);
lean_dec(x_17);
x_34 = lean_ctor_get(x_1, 0);
lean_inc(x_34);
lean_dec(x_1);
x_35 = lean_apply_1(x_3, x_33);
x_36 = lean_apply_1(x_34, x_35);
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_16, 0, x_37);
return x_16;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_38 = lean_ctor_get(x_16, 1);
lean_inc(x_38);
lean_dec(x_16);
x_39 = lean_ctor_get(x_17, 0);
lean_inc(x_39);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 x_40 = x_17;
} else {
 lean_dec_ref(x_17);
 x_40 = lean_box(0);
}
x_41 = lean_ctor_get(x_1, 0);
lean_inc(x_41);
lean_dec(x_1);
x_42 = lean_apply_1(x_3, x_39);
x_43 = lean_apply_1(x_41, x_42);
if (lean_is_scalar(x_40)) {
 x_44 = lean_alloc_ctor(0, 1, 0);
} else {
 x_44 = x_40;
 lean_ctor_set_tag(x_44, 0);
}
lean_ctor_set(x_44, 0, x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_38);
return x_45;
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_3);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_16);
if (x_46 == 0)
{
return x_16;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_16, 0);
x_48 = lean_ctor_get(x_16, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_16);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Char_reduceUnary(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; 
x_15 = l_Lean_Expr_isAppOfArity(x_6, x_3, x_5);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_2);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_14);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = l_Lean_Expr_appArg_x21(x_6);
x_20 = l_Lean_Meta_getCharValue_x3f(x_19, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
lean_dec(x_4);
lean_dec(x_2);
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_20, 0);
lean_dec(x_23);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_20, 0, x_25);
return x_20;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_20, 1);
lean_inc(x_26);
lean_dec(x_20);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_26);
return x_29;
}
}
else
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_20);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_20, 0);
lean_dec(x_31);
x_32 = !lean_is_exclusive(x_21);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_21, 0);
x_34 = lean_ctor_get(x_2, 0);
lean_inc(x_34);
lean_dec(x_2);
x_35 = lean_apply_1(x_4, x_33);
x_36 = lean_apply_1(x_34, x_35);
lean_ctor_set_tag(x_21, 0);
lean_ctor_set(x_21, 0, x_36);
return x_20;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_21, 0);
lean_inc(x_37);
lean_dec(x_21);
x_38 = lean_ctor_get(x_2, 0);
lean_inc(x_38);
lean_dec(x_2);
x_39 = lean_apply_1(x_4, x_37);
x_40 = lean_apply_1(x_38, x_39);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_20, 0, x_41);
return x_20;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_42 = lean_ctor_get(x_20, 1);
lean_inc(x_42);
lean_dec(x_20);
x_43 = lean_ctor_get(x_21, 0);
lean_inc(x_43);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 x_44 = x_21;
} else {
 lean_dec_ref(x_21);
 x_44 = lean_box(0);
}
x_45 = lean_ctor_get(x_2, 0);
lean_inc(x_45);
lean_dec(x_2);
x_46 = lean_apply_1(x_4, x_43);
x_47 = lean_apply_1(x_45, x_46);
if (lean_is_scalar(x_44)) {
 x_48 = lean_alloc_ctor(0, 1, 0);
} else {
 x_48 = x_44;
 lean_ctor_set_tag(x_48, 0);
}
lean_ctor_set(x_48, 0, x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_42);
return x_49;
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_4);
lean_dec(x_2);
x_50 = !lean_is_exclusive(x_20);
if (x_50 == 0)
{
return x_20;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_20, 0);
x_52 = lean_ctor_get(x_20, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_20);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Char_reduceUnary___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Char_reduceUnary___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Char_reduceUnary___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Char_reduceUnary(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Char_reduceBinPred___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_16 = l_Lean_Meta_getCharValue_x3f(x_15, x_5, x_6, x_7, x_8, x_9);
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
x_30 = l_Lean_Meta_getCharValue_x3f(x_29, x_5, x_6, x_7, x_8, x_26);
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
x_49 = l_Lean_Meta_getCharValue_x3f(x_48, x_5, x_6, x_7, x_8, x_26);
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
LEAN_EXPORT lean_object* l_Char_reduceBinPred(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
x_19 = l_Lean_Meta_getCharValue_x3f(x_18, x_8, x_9, x_10, x_11, x_12);
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
x_33 = l_Lean_Meta_getCharValue_x3f(x_32, x_8, x_9, x_10, x_11, x_29);
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
x_52 = l_Lean_Meta_getCharValue_x3f(x_51, x_8, x_9, x_10, x_11, x_29);
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
LEAN_EXPORT lean_object* l_Char_reduceBinPred___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Char_reduceBinPred___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Char_reduceBinPred___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Char_reduceBinPred(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Char_reduceBoolPred___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_16 = l_Lean_Meta_getCharValue_x3f(x_15, x_5, x_6, x_7, x_8, x_9);
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
x_32 = l_Lean_Meta_getCharValue_x3f(x_31, x_5, x_6, x_7, x_8, x_27);
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
x_63 = l_Lean_Meta_getCharValue_x3f(x_62, x_5, x_6, x_7, x_8, x_59);
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
LEAN_EXPORT lean_object* l_Char_reduceBoolPred(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
x_19 = l_Lean_Meta_getCharValue_x3f(x_18, x_8, x_9, x_10, x_11, x_12);
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
x_35 = l_Lean_Meta_getCharValue_x3f(x_34, x_8, x_9, x_10, x_11, x_30);
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
x_66 = l_Lean_Meta_getCharValue_x3f(x_65, x_8, x_9, x_10, x_11, x_62);
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
LEAN_EXPORT lean_object* l_Char_reduceBoolPred___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Char_reduceBoolPred___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Char_reduceBoolPred___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Char_reduceBoolPred(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Char_reduceToLower___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_mk_string_unchecked("Char", 4, 4);
x_8 = lean_mk_string_unchecked("toLower", 7, 7);
lean_inc(x_7);
x_9 = l_Lean_Name_mkStr2(x_7, x_8);
x_10 = lean_unsigned_to_nat(1u);
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
lean_object* x_15; lean_object* x_16; 
x_15 = l_Lean_Expr_appArg_x21(x_1);
x_16 = l_Lean_Meta_getCharValue_x3f(x_15, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
lean_dec(x_7);
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
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint32_t x_34; uint32_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_29 = lean_ctor_get(x_17, 0);
x_30 = lean_mk_string_unchecked("ofNat", 5, 5);
x_31 = l_Lean_Name_mkStr2(x_7, x_30);
x_32 = lean_box(0);
x_33 = l_Lean_Expr_const___override(x_31, x_32);
x_34 = lean_unbox_uint32(x_29);
lean_dec(x_29);
x_35 = l_Char_toLower(x_34);
x_36 = lean_uint32_to_nat(x_35);
x_37 = l_Lean_mkRawNatLit(x_36);
x_38 = l_Lean_Expr_app___override(x_33, x_37);
lean_ctor_set_tag(x_17, 0);
lean_ctor_set(x_17, 0, x_38);
return x_16;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint32_t x_44; uint32_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_39 = lean_ctor_get(x_17, 0);
lean_inc(x_39);
lean_dec(x_17);
x_40 = lean_mk_string_unchecked("ofNat", 5, 5);
x_41 = l_Lean_Name_mkStr2(x_7, x_40);
x_42 = lean_box(0);
x_43 = l_Lean_Expr_const___override(x_41, x_42);
x_44 = lean_unbox_uint32(x_39);
lean_dec(x_39);
x_45 = l_Char_toLower(x_44);
x_46 = lean_uint32_to_nat(x_45);
x_47 = l_Lean_mkRawNatLit(x_46);
x_48 = l_Lean_Expr_app___override(x_43, x_47);
x_49 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_16, 0, x_49);
return x_16;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint32_t x_57; uint32_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_50 = lean_ctor_get(x_16, 1);
lean_inc(x_50);
lean_dec(x_16);
x_51 = lean_ctor_get(x_17, 0);
lean_inc(x_51);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 x_52 = x_17;
} else {
 lean_dec_ref(x_17);
 x_52 = lean_box(0);
}
x_53 = lean_mk_string_unchecked("ofNat", 5, 5);
x_54 = l_Lean_Name_mkStr2(x_7, x_53);
x_55 = lean_box(0);
x_56 = l_Lean_Expr_const___override(x_54, x_55);
x_57 = lean_unbox_uint32(x_51);
lean_dec(x_51);
x_58 = l_Char_toLower(x_57);
x_59 = lean_uint32_to_nat(x_58);
x_60 = l_Lean_mkRawNatLit(x_59);
x_61 = l_Lean_Expr_app___override(x_56, x_60);
if (lean_is_scalar(x_52)) {
 x_62 = lean_alloc_ctor(0, 1, 0);
} else {
 x_62 = x_52;
 lean_ctor_set_tag(x_62, 0);
}
lean_ctor_set(x_62, 0, x_61);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_50);
return x_63;
}
}
}
else
{
uint8_t x_64; 
lean_dec(x_7);
x_64 = !lean_is_exclusive(x_16);
if (x_64 == 0)
{
return x_16;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_16, 0);
x_66 = lean_ctor_get(x_16, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_16);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Char_reduceToLower(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Char_reduceToLower___redArg(x_1, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Char_reduceToLower___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Char_reduceToLower___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Char_reduceToLower___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Char_reduceToLower(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceToLower_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_416_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_2 = lean_mk_string_unchecked("Char", 4, 4);
x_3 = lean_mk_string_unchecked("reduceToLower", 13, 13);
lean_inc(x_2);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_mk_string_unchecked("toLower", 7, 7);
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
x_14 = lean_alloc_closure((void*)(l_Char_reduceToLower___boxed), 9, 0);
x_15 = l_Lean_Meta_Simp_registerBuiltinDSimproc(x_4, x_13, x_14, x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceToLower_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_418_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Char", 4, 4);
x_3 = lean_mk_string_unchecked("reduceToLower", 13, 13);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Char_reduceToLower___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceToLower_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_420_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Char", 4, 4);
x_3 = lean_mk_string_unchecked("reduceToLower", 13, 13);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Char_reduceToLower___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Char_reduceToUpper___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_mk_string_unchecked("Char", 4, 4);
x_8 = lean_mk_string_unchecked("toUpper", 7, 7);
lean_inc(x_7);
x_9 = l_Lean_Name_mkStr2(x_7, x_8);
x_10 = lean_unsigned_to_nat(1u);
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
lean_object* x_15; lean_object* x_16; 
x_15 = l_Lean_Expr_appArg_x21(x_1);
x_16 = l_Lean_Meta_getCharValue_x3f(x_15, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
lean_dec(x_7);
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
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint32_t x_34; uint32_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_29 = lean_ctor_get(x_17, 0);
x_30 = lean_mk_string_unchecked("ofNat", 5, 5);
x_31 = l_Lean_Name_mkStr2(x_7, x_30);
x_32 = lean_box(0);
x_33 = l_Lean_Expr_const___override(x_31, x_32);
x_34 = lean_unbox_uint32(x_29);
lean_dec(x_29);
x_35 = l_Char_toUpper(x_34);
x_36 = lean_uint32_to_nat(x_35);
x_37 = l_Lean_mkRawNatLit(x_36);
x_38 = l_Lean_Expr_app___override(x_33, x_37);
lean_ctor_set_tag(x_17, 0);
lean_ctor_set(x_17, 0, x_38);
return x_16;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint32_t x_44; uint32_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_39 = lean_ctor_get(x_17, 0);
lean_inc(x_39);
lean_dec(x_17);
x_40 = lean_mk_string_unchecked("ofNat", 5, 5);
x_41 = l_Lean_Name_mkStr2(x_7, x_40);
x_42 = lean_box(0);
x_43 = l_Lean_Expr_const___override(x_41, x_42);
x_44 = lean_unbox_uint32(x_39);
lean_dec(x_39);
x_45 = l_Char_toUpper(x_44);
x_46 = lean_uint32_to_nat(x_45);
x_47 = l_Lean_mkRawNatLit(x_46);
x_48 = l_Lean_Expr_app___override(x_43, x_47);
x_49 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_16, 0, x_49);
return x_16;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint32_t x_57; uint32_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_50 = lean_ctor_get(x_16, 1);
lean_inc(x_50);
lean_dec(x_16);
x_51 = lean_ctor_get(x_17, 0);
lean_inc(x_51);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 x_52 = x_17;
} else {
 lean_dec_ref(x_17);
 x_52 = lean_box(0);
}
x_53 = lean_mk_string_unchecked("ofNat", 5, 5);
x_54 = l_Lean_Name_mkStr2(x_7, x_53);
x_55 = lean_box(0);
x_56 = l_Lean_Expr_const___override(x_54, x_55);
x_57 = lean_unbox_uint32(x_51);
lean_dec(x_51);
x_58 = l_Char_toUpper(x_57);
x_59 = lean_uint32_to_nat(x_58);
x_60 = l_Lean_mkRawNatLit(x_59);
x_61 = l_Lean_Expr_app___override(x_56, x_60);
if (lean_is_scalar(x_52)) {
 x_62 = lean_alloc_ctor(0, 1, 0);
} else {
 x_62 = x_52;
 lean_ctor_set_tag(x_62, 0);
}
lean_ctor_set(x_62, 0, x_61);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_50);
return x_63;
}
}
}
else
{
uint8_t x_64; 
lean_dec(x_7);
x_64 = !lean_is_exclusive(x_16);
if (x_64 == 0)
{
return x_16;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_16, 0);
x_66 = lean_ctor_get(x_16, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_16);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Char_reduceToUpper(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Char_reduceToUpper___redArg(x_1, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Char_reduceToUpper___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Char_reduceToUpper___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Char_reduceToUpper___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Char_reduceToUpper(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceToUpper_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_436_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_2 = lean_mk_string_unchecked("Char", 4, 4);
x_3 = lean_mk_string_unchecked("reduceToUpper", 13, 13);
lean_inc(x_2);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_mk_string_unchecked("toUpper", 7, 7);
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
x_14 = lean_alloc_closure((void*)(l_Char_reduceToUpper___boxed), 9, 0);
x_15 = l_Lean_Meta_Simp_registerBuiltinDSimproc(x_4, x_13, x_14, x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceToUpper_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_438_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Char", 4, 4);
x_3 = lean_mk_string_unchecked("reduceToUpper", 13, 13);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Char_reduceToUpper___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceToUpper_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_440_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Char", 4, 4);
x_3 = lean_mk_string_unchecked("reduceToUpper", 13, 13);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Char_reduceToUpper___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Char_reduceToNat___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_mk_string_unchecked("Char", 4, 4);
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
x_16 = l_Lean_Meta_getCharValue_x3f(x_15, x_2, x_3, x_4, x_5, x_6);
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
lean_object* x_29; uint32_t x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_17, 0);
x_30 = lean_unbox_uint32(x_29);
lean_dec(x_29);
x_31 = lean_uint32_to_nat(x_30);
x_32 = l_Lean_mkNatLit(x_31);
lean_ctor_set_tag(x_17, 0);
lean_ctor_set(x_17, 0, x_32);
return x_16;
}
else
{
lean_object* x_33; uint32_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_17, 0);
lean_inc(x_33);
lean_dec(x_17);
x_34 = lean_unbox_uint32(x_33);
lean_dec(x_33);
x_35 = lean_uint32_to_nat(x_34);
x_36 = l_Lean_mkNatLit(x_35);
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_16, 0, x_37);
return x_16;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint32_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_38 = lean_ctor_get(x_16, 1);
lean_inc(x_38);
lean_dec(x_16);
x_39 = lean_ctor_get(x_17, 0);
lean_inc(x_39);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 x_40 = x_17;
} else {
 lean_dec_ref(x_17);
 x_40 = lean_box(0);
}
x_41 = lean_unbox_uint32(x_39);
lean_dec(x_39);
x_42 = lean_uint32_to_nat(x_41);
x_43 = l_Lean_mkNatLit(x_42);
if (lean_is_scalar(x_40)) {
 x_44 = lean_alloc_ctor(0, 1, 0);
} else {
 x_44 = x_40;
 lean_ctor_set_tag(x_44, 0);
}
lean_ctor_set(x_44, 0, x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_38);
return x_45;
}
}
}
else
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_16);
if (x_46 == 0)
{
return x_16;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_16, 0);
x_48 = lean_ctor_get(x_16, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_16);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Char_reduceToNat(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Char_reduceToNat___redArg(x_1, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Char_reduceToNat___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Char_reduceToNat___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Char_reduceToNat___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Char_reduceToNat(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceToNat_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_456_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_2 = lean_mk_string_unchecked("Char", 4, 4);
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
x_14 = lean_alloc_closure((void*)(l_Char_reduceToNat___boxed), 9, 0);
x_15 = l_Lean_Meta_Simp_registerBuiltinDSimproc(x_4, x_13, x_14, x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceToNat_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_458_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Char", 4, 4);
x_3 = lean_mk_string_unchecked("reduceToNat", 11, 11);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Char_reduceToNat___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceToNat_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_460_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Char", 4, 4);
x_3 = lean_mk_string_unchecked("reduceToNat", 11, 11);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Char_reduceToNat___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Char_reduceIsWhitespace___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_mk_string_unchecked("Char", 4, 4);
x_8 = lean_mk_string_unchecked("isWhitespace", 12, 12);
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
x_16 = l_Lean_Meta_getCharValue_x3f(x_15, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_36; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_19 = x_16;
} else {
 lean_dec_ref(x_16);
 x_19 = lean_box(0);
}
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_19);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_39, 0, x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_18);
return x_40;
}
else
{
lean_object* x_41; uint8_t x_42; uint8_t x_48; lean_object* x_54; uint32_t x_55; uint32_t x_56; uint8_t x_57; 
x_41 = lean_ctor_get(x_17, 0);
lean_inc(x_41);
lean_dec(x_17);
x_54 = lean_unsigned_to_nat(32u);
x_55 = l_Char_ofNat(x_54);
x_56 = lean_unbox_uint32(x_41);
x_57 = l_instDecidableEqChar(x_56, x_55);
if (x_57 == 0)
{
lean_object* x_58; uint32_t x_59; uint32_t x_60; uint8_t x_61; 
x_58 = lean_unsigned_to_nat(9u);
x_59 = l_Char_ofNat(x_58);
x_60 = lean_unbox_uint32(x_41);
x_61 = l_instDecidableEqChar(x_60, x_59);
x_48 = x_61;
goto block_53;
}
else
{
x_48 = x_11;
goto block_53;
}
block_47:
{
if (x_42 == 0)
{
lean_object* x_43; uint32_t x_44; uint32_t x_45; uint8_t x_46; 
x_43 = lean_unsigned_to_nat(10u);
x_44 = l_Char_ofNat(x_43);
x_45 = lean_unbox_uint32(x_41);
lean_dec(x_41);
x_46 = l_instDecidableEqChar(x_45, x_44);
x_36 = x_46;
goto block_37;
}
else
{
lean_dec(x_41);
x_36 = x_11;
goto block_37;
}
}
block_53:
{
if (x_48 == 0)
{
lean_object* x_49; uint32_t x_50; uint32_t x_51; uint8_t x_52; 
x_49 = lean_unsigned_to_nat(13u);
x_50 = l_Char_ofNat(x_49);
x_51 = lean_unbox_uint32(x_41);
x_52 = l_instDecidableEqChar(x_51, x_50);
x_42 = x_52;
goto block_47;
}
else
{
x_42 = x_11;
goto block_47;
}
}
}
block_23:
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
if (lean_is_scalar(x_19)) {
 x_22 = lean_alloc_ctor(0, 2, 0);
} else {
 x_22 = x_19;
}
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_18);
return x_22;
}
block_29:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_mk_string_unchecked("Bool", 4, 4);
x_25 = lean_mk_string_unchecked("true", 4, 4);
x_26 = l_Lean_Name_mkStr2(x_24, x_25);
x_27 = lean_box(0);
x_28 = l_Lean_Expr_const___override(x_26, x_27);
x_20 = x_28;
goto block_23;
}
block_35:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_mk_string_unchecked("Bool", 4, 4);
x_31 = lean_mk_string_unchecked("false", 5, 5);
x_32 = l_Lean_Name_mkStr2(x_30, x_31);
x_33 = lean_box(0);
x_34 = l_Lean_Expr_const___override(x_32, x_33);
x_20 = x_34;
goto block_23;
}
block_37:
{
if (x_36 == 0)
{
if (x_11 == 0)
{
goto block_29;
}
else
{
goto block_35;
}
}
else
{
if (x_11 == 0)
{
goto block_35;
}
else
{
goto block_29;
}
}
}
}
else
{
uint8_t x_62; 
x_62 = !lean_is_exclusive(x_16);
if (x_62 == 0)
{
return x_16;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_16, 0);
x_64 = lean_ctor_get(x_16, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_16);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Char_reduceIsWhitespace(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Char_reduceIsWhitespace___redArg(x_1, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Char_reduceIsWhitespace___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Char_reduceIsWhitespace___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Char_reduceIsWhitespace___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Char_reduceIsWhitespace(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceIsWhitespace_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_476_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_2 = lean_mk_string_unchecked("Char", 4, 4);
x_3 = lean_mk_string_unchecked("reduceIsWhitespace", 18, 18);
lean_inc(x_2);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_mk_string_unchecked("isWhitespace", 12, 12);
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
x_14 = lean_alloc_closure((void*)(l_Char_reduceIsWhitespace___boxed), 9, 0);
x_15 = l_Lean_Meta_Simp_registerBuiltinDSimproc(x_4, x_13, x_14, x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceIsWhitespace_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_478_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Char", 4, 4);
x_3 = lean_mk_string_unchecked("reduceIsWhitespace", 18, 18);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Char_reduceIsWhitespace___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceIsWhitespace_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_480_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Char", 4, 4);
x_3 = lean_mk_string_unchecked("reduceIsWhitespace", 18, 18);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Char_reduceIsWhitespace___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Char_reduceIsUpper___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_mk_string_unchecked("Char", 4, 4);
x_8 = lean_mk_string_unchecked("isUpper", 7, 7);
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
x_16 = l_Lean_Meta_getCharValue_x3f(x_15, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_36; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_19 = x_16;
} else {
 lean_dec_ref(x_16);
 x_19 = lean_box(0);
}
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_19);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_39, 0, x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_18);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; uint32_t x_43; uint32_t x_44; uint8_t x_45; 
x_41 = lean_ctor_get(x_17, 0);
lean_inc(x_41);
lean_dec(x_17);
x_42 = lean_unsigned_to_nat(65u);
x_43 = lean_uint32_of_nat(x_42);
x_44 = lean_unbox_uint32(x_41);
x_45 = lean_uint32_dec_le(x_43, x_44);
if (x_45 == 0)
{
lean_dec(x_41);
x_36 = x_45;
goto block_37;
}
else
{
lean_object* x_46; uint32_t x_47; uint32_t x_48; uint8_t x_49; 
x_46 = lean_unsigned_to_nat(90u);
x_47 = lean_uint32_of_nat(x_46);
x_48 = lean_unbox_uint32(x_41);
lean_dec(x_41);
x_49 = lean_uint32_dec_le(x_48, x_47);
x_36 = x_49;
goto block_37;
}
}
block_23:
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
if (lean_is_scalar(x_19)) {
 x_22 = lean_alloc_ctor(0, 2, 0);
} else {
 x_22 = x_19;
}
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_18);
return x_22;
}
block_29:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_mk_string_unchecked("Bool", 4, 4);
x_25 = lean_mk_string_unchecked("false", 5, 5);
x_26 = l_Lean_Name_mkStr2(x_24, x_25);
x_27 = lean_box(0);
x_28 = l_Lean_Expr_const___override(x_26, x_27);
x_20 = x_28;
goto block_23;
}
block_35:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_mk_string_unchecked("Bool", 4, 4);
x_31 = lean_mk_string_unchecked("true", 4, 4);
x_32 = l_Lean_Name_mkStr2(x_30, x_31);
x_33 = lean_box(0);
x_34 = l_Lean_Expr_const___override(x_32, x_33);
x_20 = x_34;
goto block_23;
}
block_37:
{
if (x_36 == 0)
{
if (x_11 == 0)
{
goto block_35;
}
else
{
goto block_29;
}
}
else
{
if (x_11 == 0)
{
goto block_29;
}
else
{
goto block_35;
}
}
}
}
else
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_16);
if (x_50 == 0)
{
return x_16;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_16, 0);
x_52 = lean_ctor_get(x_16, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_16);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Char_reduceIsUpper(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Char_reduceIsUpper___redArg(x_1, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Char_reduceIsUpper___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Char_reduceIsUpper___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Char_reduceIsUpper___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Char_reduceIsUpper(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceIsUpper_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_496_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_2 = lean_mk_string_unchecked("Char", 4, 4);
x_3 = lean_mk_string_unchecked("reduceIsUpper", 13, 13);
lean_inc(x_2);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_mk_string_unchecked("isUpper", 7, 7);
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
x_14 = lean_alloc_closure((void*)(l_Char_reduceIsUpper___boxed), 9, 0);
x_15 = l_Lean_Meta_Simp_registerBuiltinDSimproc(x_4, x_13, x_14, x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceIsUpper_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_498_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Char", 4, 4);
x_3 = lean_mk_string_unchecked("reduceIsUpper", 13, 13);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Char_reduceIsUpper___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceIsUpper_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_500_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Char", 4, 4);
x_3 = lean_mk_string_unchecked("reduceIsUpper", 13, 13);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Char_reduceIsUpper___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Char_reduceIsLower___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_mk_string_unchecked("Char", 4, 4);
x_8 = lean_mk_string_unchecked("isLower", 7, 7);
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
x_16 = l_Lean_Meta_getCharValue_x3f(x_15, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_36; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_19 = x_16;
} else {
 lean_dec_ref(x_16);
 x_19 = lean_box(0);
}
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_19);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_39, 0, x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_18);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; uint32_t x_43; uint32_t x_44; uint8_t x_45; 
x_41 = lean_ctor_get(x_17, 0);
lean_inc(x_41);
lean_dec(x_17);
x_42 = lean_unsigned_to_nat(97u);
x_43 = lean_uint32_of_nat(x_42);
x_44 = lean_unbox_uint32(x_41);
x_45 = lean_uint32_dec_le(x_43, x_44);
if (x_45 == 0)
{
lean_dec(x_41);
x_36 = x_45;
goto block_37;
}
else
{
lean_object* x_46; uint32_t x_47; uint32_t x_48; uint8_t x_49; 
x_46 = lean_unsigned_to_nat(122u);
x_47 = lean_uint32_of_nat(x_46);
x_48 = lean_unbox_uint32(x_41);
lean_dec(x_41);
x_49 = lean_uint32_dec_le(x_48, x_47);
x_36 = x_49;
goto block_37;
}
}
block_23:
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
if (lean_is_scalar(x_19)) {
 x_22 = lean_alloc_ctor(0, 2, 0);
} else {
 x_22 = x_19;
}
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_18);
return x_22;
}
block_29:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_mk_string_unchecked("Bool", 4, 4);
x_25 = lean_mk_string_unchecked("false", 5, 5);
x_26 = l_Lean_Name_mkStr2(x_24, x_25);
x_27 = lean_box(0);
x_28 = l_Lean_Expr_const___override(x_26, x_27);
x_20 = x_28;
goto block_23;
}
block_35:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_mk_string_unchecked("Bool", 4, 4);
x_31 = lean_mk_string_unchecked("true", 4, 4);
x_32 = l_Lean_Name_mkStr2(x_30, x_31);
x_33 = lean_box(0);
x_34 = l_Lean_Expr_const___override(x_32, x_33);
x_20 = x_34;
goto block_23;
}
block_37:
{
if (x_36 == 0)
{
if (x_11 == 0)
{
goto block_35;
}
else
{
goto block_29;
}
}
else
{
if (x_11 == 0)
{
goto block_29;
}
else
{
goto block_35;
}
}
}
}
else
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_16);
if (x_50 == 0)
{
return x_16;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_16, 0);
x_52 = lean_ctor_get(x_16, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_16);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Char_reduceIsLower(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Char_reduceIsLower___redArg(x_1, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Char_reduceIsLower___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Char_reduceIsLower___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Char_reduceIsLower___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Char_reduceIsLower(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceIsLower_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_516_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_2 = lean_mk_string_unchecked("Char", 4, 4);
x_3 = lean_mk_string_unchecked("reduceIsLower", 13, 13);
lean_inc(x_2);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_mk_string_unchecked("isLower", 7, 7);
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
x_14 = lean_alloc_closure((void*)(l_Char_reduceIsLower___boxed), 9, 0);
x_15 = l_Lean_Meta_Simp_registerBuiltinDSimproc(x_4, x_13, x_14, x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceIsLower_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_518_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Char", 4, 4);
x_3 = lean_mk_string_unchecked("reduceIsLower", 13, 13);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Char_reduceIsLower___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceIsLower_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_520_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Char", 4, 4);
x_3 = lean_mk_string_unchecked("reduceIsLower", 13, 13);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Char_reduceIsLower___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Char_reduceIsAlpha___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_mk_string_unchecked("Char", 4, 4);
x_8 = lean_mk_string_unchecked("isAlpha", 7, 7);
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
x_16 = l_Lean_Meta_getCharValue_x3f(x_15, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_37; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_19 = x_16;
} else {
 lean_dec_ref(x_16);
 x_19 = lean_box(0);
}
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_19);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_40, 0, x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_18);
return x_41;
}
else
{
lean_object* x_42; uint8_t x_43; lean_object* x_53; uint32_t x_54; uint32_t x_55; uint8_t x_56; 
x_42 = lean_ctor_get(x_17, 0);
lean_inc(x_42);
lean_dec(x_17);
x_53 = lean_unsigned_to_nat(65u);
x_54 = lean_uint32_of_nat(x_53);
x_55 = lean_unbox_uint32(x_42);
x_56 = lean_uint32_dec_le(x_54, x_55);
if (x_56 == 0)
{
x_43 = x_56;
goto block_52;
}
else
{
lean_object* x_57; uint32_t x_58; uint32_t x_59; uint8_t x_60; 
x_57 = lean_unsigned_to_nat(90u);
x_58 = lean_uint32_of_nat(x_57);
x_59 = lean_unbox_uint32(x_42);
x_60 = lean_uint32_dec_le(x_59, x_58);
x_43 = x_60;
goto block_52;
}
block_52:
{
if (x_43 == 0)
{
lean_object* x_44; uint32_t x_45; uint32_t x_46; uint8_t x_47; 
x_44 = lean_unsigned_to_nat(97u);
x_45 = lean_uint32_of_nat(x_44);
x_46 = lean_unbox_uint32(x_42);
x_47 = lean_uint32_dec_le(x_45, x_46);
if (x_47 == 0)
{
lean_dec(x_42);
x_37 = x_47;
goto block_38;
}
else
{
lean_object* x_48; uint32_t x_49; uint32_t x_50; uint8_t x_51; 
x_48 = lean_unsigned_to_nat(122u);
x_49 = lean_uint32_of_nat(x_48);
x_50 = lean_unbox_uint32(x_42);
lean_dec(x_42);
x_51 = lean_uint32_dec_le(x_50, x_49);
x_37 = x_51;
goto block_38;
}
}
else
{
lean_dec(x_42);
goto block_36;
}
}
}
block_23:
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
if (lean_is_scalar(x_19)) {
 x_22 = lean_alloc_ctor(0, 2, 0);
} else {
 x_22 = x_19;
}
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_18);
return x_22;
}
block_29:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_mk_string_unchecked("Bool", 4, 4);
x_25 = lean_mk_string_unchecked("true", 4, 4);
x_26 = l_Lean_Name_mkStr2(x_24, x_25);
x_27 = lean_box(0);
x_28 = l_Lean_Expr_const___override(x_26, x_27);
x_20 = x_28;
goto block_23;
}
block_35:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_mk_string_unchecked("Bool", 4, 4);
x_31 = lean_mk_string_unchecked("false", 5, 5);
x_32 = l_Lean_Name_mkStr2(x_30, x_31);
x_33 = lean_box(0);
x_34 = l_Lean_Expr_const___override(x_32, x_33);
x_20 = x_34;
goto block_23;
}
block_36:
{
if (x_11 == 0)
{
goto block_35;
}
else
{
goto block_29;
}
}
block_38:
{
if (x_37 == 0)
{
if (x_11 == 0)
{
goto block_29;
}
else
{
goto block_35;
}
}
else
{
goto block_36;
}
}
}
else
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_16);
if (x_61 == 0)
{
return x_16;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_16, 0);
x_63 = lean_ctor_get(x_16, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_16);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Char_reduceIsAlpha(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Char_reduceIsAlpha___redArg(x_1, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Char_reduceIsAlpha___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Char_reduceIsAlpha___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Char_reduceIsAlpha___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Char_reduceIsAlpha(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceIsAlpha_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_536_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_2 = lean_mk_string_unchecked("Char", 4, 4);
x_3 = lean_mk_string_unchecked("reduceIsAlpha", 13, 13);
lean_inc(x_2);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_mk_string_unchecked("isAlpha", 7, 7);
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
x_14 = lean_alloc_closure((void*)(l_Char_reduceIsAlpha___boxed), 9, 0);
x_15 = l_Lean_Meta_Simp_registerBuiltinDSimproc(x_4, x_13, x_14, x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceIsAlpha_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_538_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Char", 4, 4);
x_3 = lean_mk_string_unchecked("reduceIsAlpha", 13, 13);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Char_reduceIsAlpha___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceIsAlpha_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_540_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Char", 4, 4);
x_3 = lean_mk_string_unchecked("reduceIsAlpha", 13, 13);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Char_reduceIsAlpha___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Char_reduceIsDigit___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_mk_string_unchecked("Char", 4, 4);
x_8 = lean_mk_string_unchecked("isDigit", 7, 7);
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
x_16 = l_Lean_Meta_getCharValue_x3f(x_15, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_36; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_19 = x_16;
} else {
 lean_dec_ref(x_16);
 x_19 = lean_box(0);
}
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_19);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_39, 0, x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_18);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; uint32_t x_43; uint32_t x_44; uint8_t x_45; 
x_41 = lean_ctor_get(x_17, 0);
lean_inc(x_41);
lean_dec(x_17);
x_42 = lean_unsigned_to_nat(48u);
x_43 = lean_uint32_of_nat(x_42);
x_44 = lean_unbox_uint32(x_41);
x_45 = lean_uint32_dec_le(x_43, x_44);
if (x_45 == 0)
{
lean_dec(x_41);
x_36 = x_45;
goto block_37;
}
else
{
lean_object* x_46; uint32_t x_47; uint32_t x_48; uint8_t x_49; 
x_46 = lean_unsigned_to_nat(57u);
x_47 = lean_uint32_of_nat(x_46);
x_48 = lean_unbox_uint32(x_41);
lean_dec(x_41);
x_49 = lean_uint32_dec_le(x_48, x_47);
x_36 = x_49;
goto block_37;
}
}
block_23:
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
if (lean_is_scalar(x_19)) {
 x_22 = lean_alloc_ctor(0, 2, 0);
} else {
 x_22 = x_19;
}
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_18);
return x_22;
}
block_29:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_mk_string_unchecked("Bool", 4, 4);
x_25 = lean_mk_string_unchecked("false", 5, 5);
x_26 = l_Lean_Name_mkStr2(x_24, x_25);
x_27 = lean_box(0);
x_28 = l_Lean_Expr_const___override(x_26, x_27);
x_20 = x_28;
goto block_23;
}
block_35:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_mk_string_unchecked("Bool", 4, 4);
x_31 = lean_mk_string_unchecked("true", 4, 4);
x_32 = l_Lean_Name_mkStr2(x_30, x_31);
x_33 = lean_box(0);
x_34 = l_Lean_Expr_const___override(x_32, x_33);
x_20 = x_34;
goto block_23;
}
block_37:
{
if (x_36 == 0)
{
if (x_11 == 0)
{
goto block_35;
}
else
{
goto block_29;
}
}
else
{
if (x_11 == 0)
{
goto block_29;
}
else
{
goto block_35;
}
}
}
}
else
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_16);
if (x_50 == 0)
{
return x_16;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_16, 0);
x_52 = lean_ctor_get(x_16, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_16);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Char_reduceIsDigit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Char_reduceIsDigit___redArg(x_1, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Char_reduceIsDigit___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Char_reduceIsDigit___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Char_reduceIsDigit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Char_reduceIsDigit(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceIsDigit_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_556_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_2 = lean_mk_string_unchecked("Char", 4, 4);
x_3 = lean_mk_string_unchecked("reduceIsDigit", 13, 13);
lean_inc(x_2);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_mk_string_unchecked("isDigit", 7, 7);
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
x_14 = lean_alloc_closure((void*)(l_Char_reduceIsDigit___boxed), 9, 0);
x_15 = l_Lean_Meta_Simp_registerBuiltinDSimproc(x_4, x_13, x_14, x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceIsDigit_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_558_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Char", 4, 4);
x_3 = lean_mk_string_unchecked("reduceIsDigit", 13, 13);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Char_reduceIsDigit___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceIsDigit_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_560_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Char", 4, 4);
x_3 = lean_mk_string_unchecked("reduceIsDigit", 13, 13);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Char_reduceIsDigit___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Char_reduceIsAlphaNum___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_mk_string_unchecked("Char", 4, 4);
x_8 = lean_mk_string_unchecked("isAlphanum", 10, 10);
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
x_16 = l_Lean_Meta_getCharValue_x3f(x_15, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_36; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_19 = x_16;
} else {
 lean_dec_ref(x_16);
 x_19 = lean_box(0);
}
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_19);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_39, 0, x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_18);
return x_40;
}
else
{
lean_object* x_41; uint8_t x_42; uint8_t x_52; lean_object* x_62; uint32_t x_63; uint32_t x_64; uint8_t x_65; 
x_41 = lean_ctor_get(x_17, 0);
lean_inc(x_41);
lean_dec(x_17);
x_62 = lean_unsigned_to_nat(65u);
x_63 = lean_uint32_of_nat(x_62);
x_64 = lean_unbox_uint32(x_41);
x_65 = lean_uint32_dec_le(x_63, x_64);
if (x_65 == 0)
{
x_52 = x_65;
goto block_61;
}
else
{
lean_object* x_66; uint32_t x_67; uint32_t x_68; uint8_t x_69; 
x_66 = lean_unsigned_to_nat(90u);
x_67 = lean_uint32_of_nat(x_66);
x_68 = lean_unbox_uint32(x_41);
x_69 = lean_uint32_dec_le(x_68, x_67);
x_52 = x_69;
goto block_61;
}
block_51:
{
if (x_42 == 0)
{
lean_object* x_43; uint32_t x_44; uint32_t x_45; uint8_t x_46; 
x_43 = lean_unsigned_to_nat(48u);
x_44 = lean_uint32_of_nat(x_43);
x_45 = lean_unbox_uint32(x_41);
x_46 = lean_uint32_dec_le(x_44, x_45);
if (x_46 == 0)
{
lean_dec(x_41);
x_36 = x_46;
goto block_37;
}
else
{
lean_object* x_47; uint32_t x_48; uint32_t x_49; uint8_t x_50; 
x_47 = lean_unsigned_to_nat(57u);
x_48 = lean_uint32_of_nat(x_47);
x_49 = lean_unbox_uint32(x_41);
lean_dec(x_41);
x_50 = lean_uint32_dec_le(x_49, x_48);
x_36 = x_50;
goto block_37;
}
}
else
{
lean_dec(x_41);
x_36 = x_11;
goto block_37;
}
}
block_61:
{
if (x_52 == 0)
{
lean_object* x_53; uint32_t x_54; uint32_t x_55; uint8_t x_56; 
x_53 = lean_unsigned_to_nat(97u);
x_54 = lean_uint32_of_nat(x_53);
x_55 = lean_unbox_uint32(x_41);
x_56 = lean_uint32_dec_le(x_54, x_55);
if (x_56 == 0)
{
x_42 = x_56;
goto block_51;
}
else
{
lean_object* x_57; uint32_t x_58; uint32_t x_59; uint8_t x_60; 
x_57 = lean_unsigned_to_nat(122u);
x_58 = lean_uint32_of_nat(x_57);
x_59 = lean_unbox_uint32(x_41);
x_60 = lean_uint32_dec_le(x_59, x_58);
x_42 = x_60;
goto block_51;
}
}
else
{
lean_dec(x_41);
x_36 = x_11;
goto block_37;
}
}
}
block_23:
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
if (lean_is_scalar(x_19)) {
 x_22 = lean_alloc_ctor(0, 2, 0);
} else {
 x_22 = x_19;
}
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_18);
return x_22;
}
block_29:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_mk_string_unchecked("Bool", 4, 4);
x_25 = lean_mk_string_unchecked("true", 4, 4);
x_26 = l_Lean_Name_mkStr2(x_24, x_25);
x_27 = lean_box(0);
x_28 = l_Lean_Expr_const___override(x_26, x_27);
x_20 = x_28;
goto block_23;
}
block_35:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_mk_string_unchecked("Bool", 4, 4);
x_31 = lean_mk_string_unchecked("false", 5, 5);
x_32 = l_Lean_Name_mkStr2(x_30, x_31);
x_33 = lean_box(0);
x_34 = l_Lean_Expr_const___override(x_32, x_33);
x_20 = x_34;
goto block_23;
}
block_37:
{
if (x_36 == 0)
{
if (x_11 == 0)
{
goto block_29;
}
else
{
goto block_35;
}
}
else
{
if (x_11 == 0)
{
goto block_35;
}
else
{
goto block_29;
}
}
}
}
else
{
uint8_t x_70; 
x_70 = !lean_is_exclusive(x_16);
if (x_70 == 0)
{
return x_16;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_16, 0);
x_72 = lean_ctor_get(x_16, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_16);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Char_reduceIsAlphaNum(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Char_reduceIsAlphaNum___redArg(x_1, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Char_reduceIsAlphaNum___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Char_reduceIsAlphaNum___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Char_reduceIsAlphaNum___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Char_reduceIsAlphaNum(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceIsAlphaNum_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_576_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_2 = lean_mk_string_unchecked("Char", 4, 4);
x_3 = lean_mk_string_unchecked("reduceIsAlphaNum", 16, 16);
lean_inc(x_2);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_mk_string_unchecked("isAlphanum", 10, 10);
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
x_14 = lean_alloc_closure((void*)(l_Char_reduceIsAlphaNum___boxed), 9, 0);
x_15 = l_Lean_Meta_Simp_registerBuiltinDSimproc(x_4, x_13, x_14, x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceIsAlphaNum_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_578_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Char", 4, 4);
x_3 = lean_mk_string_unchecked("reduceIsAlphaNum", 16, 16);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Char_reduceIsAlphaNum___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceIsAlphaNum_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_580_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Char", 4, 4);
x_3 = lean_mk_string_unchecked("reduceIsAlphaNum", 16, 16);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Char_reduceIsAlphaNum___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Char_reduceToString___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_mk_string_unchecked("ToString", 8, 8);
x_8 = lean_mk_string_unchecked("toString", 8, 8);
x_9 = l_Lean_Name_mkStr2(x_7, x_8);
x_10 = lean_unsigned_to_nat(3u);
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
x_16 = l_Lean_Meta_getCharValue_x3f(x_15, x_2, x_3, x_4, x_5, x_6);
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
lean_object* x_29; lean_object* x_30; uint32_t x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_17, 0);
x_30 = lean_mk_string_unchecked("", 0, 0);
x_31 = lean_unbox_uint32(x_29);
lean_dec(x_29);
x_32 = lean_string_push(x_30, x_31);
x_33 = l_Lean_mkStrLit(x_32);
lean_ctor_set_tag(x_17, 0);
lean_ctor_set(x_17, 0, x_33);
return x_16;
}
else
{
lean_object* x_34; lean_object* x_35; uint32_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_34 = lean_ctor_get(x_17, 0);
lean_inc(x_34);
lean_dec(x_17);
x_35 = lean_mk_string_unchecked("", 0, 0);
x_36 = lean_unbox_uint32(x_34);
lean_dec(x_34);
x_37 = lean_string_push(x_35, x_36);
x_38 = l_Lean_mkStrLit(x_37);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_16, 0, x_39);
return x_16;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint32_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_40 = lean_ctor_get(x_16, 1);
lean_inc(x_40);
lean_dec(x_16);
x_41 = lean_ctor_get(x_17, 0);
lean_inc(x_41);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 x_42 = x_17;
} else {
 lean_dec_ref(x_17);
 x_42 = lean_box(0);
}
x_43 = lean_mk_string_unchecked("", 0, 0);
x_44 = lean_unbox_uint32(x_41);
lean_dec(x_41);
x_45 = lean_string_push(x_43, x_44);
x_46 = l_Lean_mkStrLit(x_45);
if (lean_is_scalar(x_42)) {
 x_47 = lean_alloc_ctor(0, 1, 0);
} else {
 x_47 = x_42;
 lean_ctor_set_tag(x_47, 0);
}
lean_ctor_set(x_47, 0, x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_40);
return x_48;
}
}
}
else
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_16);
if (x_49 == 0)
{
return x_16;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_16, 0);
x_51 = lean_ctor_get(x_16, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_16);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Char_reduceToString(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Char_reduceToString___redArg(x_1, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Char_reduceToString___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Char_reduceToString___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Char_reduceToString___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Char_reduceToString(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceToString_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_600_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_2 = lean_mk_string_unchecked("Char", 4, 4);
x_3 = lean_mk_string_unchecked("reduceToString", 14, 14);
lean_inc(x_2);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_mk_string_unchecked("ToString", 8, 8);
x_6 = lean_mk_string_unchecked("toString", 8, 8);
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
x_20 = lean_alloc_closure((void*)(l_Char_reduceToString___boxed), 9, 0);
x_21 = l_Lean_Meta_Simp_registerBuiltinDSimproc(x_4, x_19, x_20, x_1);
return x_21;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceToString_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_602_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Char", 4, 4);
x_3 = lean_mk_string_unchecked("reduceToString", 14, 14);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Char_reduceToString___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceToString_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_604_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Char", 4, 4);
x_3 = lean_mk_string_unchecked("reduceToString", 14, 14);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Char_reduceToString___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Char_reduceVal___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_18 = lean_mk_string_unchecked("Char", 4, 4);
x_19 = lean_mk_string_unchecked("val", 3, 3);
x_20 = l_Lean_Name_mkStr2(x_18, x_19);
x_21 = l_Lean_Expr_isConstOf(x_17, x_20);
lean_dec(x_20);
lean_dec(x_17);
if (x_21 == 0)
{
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
x_23 = l_Lean_Meta_getCharValue_x3f(x_22, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_23);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_23, 0);
lean_dec(x_26);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_23, 0, x_28);
return x_23;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_23, 1);
lean_inc(x_29);
lean_dec(x_23);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_29);
return x_32;
}
}
else
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_23);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_ctor_get(x_23, 0);
lean_dec(x_34);
x_35 = !lean_is_exclusive(x_24);
if (x_35 == 0)
{
lean_object* x_36; uint32_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_36 = lean_ctor_get(x_24, 0);
x_37 = lean_unbox_uint32(x_36);
lean_dec(x_36);
x_38 = lean_uint32_to_nat(x_37);
x_39 = l_Lean_mkRawNatLit(x_38);
x_40 = lean_mk_string_unchecked("OfNat", 5, 5);
x_41 = lean_mk_string_unchecked("ofNat", 5, 5);
x_42 = l_Lean_Name_mkStr2(x_40, x_41);
x_43 = lean_unsigned_to_nat(0u);
x_44 = l_Lean_Level_ofNat(x_43);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = l_Lean_Expr_const___override(x_42, x_46);
x_48 = lean_mk_string_unchecked("UInt32", 6, 6);
lean_inc(x_48);
x_49 = l_Lean_Name_mkStr1(x_48);
x_50 = l_Lean_Expr_const___override(x_49, x_45);
x_51 = lean_mk_string_unchecked("instOfNat", 9, 9);
x_52 = l_Lean_Name_mkStr2(x_48, x_51);
x_53 = l_Lean_Expr_const___override(x_52, x_45);
lean_inc(x_39);
x_54 = l_Lean_Expr_app___override(x_53, x_39);
x_55 = l_Lean_mkApp3(x_47, x_50, x_39, x_54);
lean_ctor_set_tag(x_24, 0);
lean_ctor_set(x_24, 0, x_55);
return x_23;
}
else
{
lean_object* x_56; uint32_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_56 = lean_ctor_get(x_24, 0);
lean_inc(x_56);
lean_dec(x_24);
x_57 = lean_unbox_uint32(x_56);
lean_dec(x_56);
x_58 = lean_uint32_to_nat(x_57);
x_59 = l_Lean_mkRawNatLit(x_58);
x_60 = lean_mk_string_unchecked("OfNat", 5, 5);
x_61 = lean_mk_string_unchecked("ofNat", 5, 5);
x_62 = l_Lean_Name_mkStr2(x_60, x_61);
x_63 = lean_unsigned_to_nat(0u);
x_64 = l_Lean_Level_ofNat(x_63);
x_65 = lean_box(0);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
x_67 = l_Lean_Expr_const___override(x_62, x_66);
x_68 = lean_mk_string_unchecked("UInt32", 6, 6);
lean_inc(x_68);
x_69 = l_Lean_Name_mkStr1(x_68);
x_70 = l_Lean_Expr_const___override(x_69, x_65);
x_71 = lean_mk_string_unchecked("instOfNat", 9, 9);
x_72 = l_Lean_Name_mkStr2(x_68, x_71);
x_73 = l_Lean_Expr_const___override(x_72, x_65);
lean_inc(x_59);
x_74 = l_Lean_Expr_app___override(x_73, x_59);
x_75 = l_Lean_mkApp3(x_67, x_70, x_59, x_74);
x_76 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_23, 0, x_76);
return x_23;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; uint32_t x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_77 = lean_ctor_get(x_23, 1);
lean_inc(x_77);
lean_dec(x_23);
x_78 = lean_ctor_get(x_24, 0);
lean_inc(x_78);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 x_79 = x_24;
} else {
 lean_dec_ref(x_24);
 x_79 = lean_box(0);
}
x_80 = lean_unbox_uint32(x_78);
lean_dec(x_78);
x_81 = lean_uint32_to_nat(x_80);
x_82 = l_Lean_mkRawNatLit(x_81);
x_83 = lean_mk_string_unchecked("OfNat", 5, 5);
x_84 = lean_mk_string_unchecked("ofNat", 5, 5);
x_85 = l_Lean_Name_mkStr2(x_83, x_84);
x_86 = lean_unsigned_to_nat(0u);
x_87 = l_Lean_Level_ofNat(x_86);
x_88 = lean_box(0);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
x_90 = l_Lean_Expr_const___override(x_85, x_89);
x_91 = lean_mk_string_unchecked("UInt32", 6, 6);
lean_inc(x_91);
x_92 = l_Lean_Name_mkStr1(x_91);
x_93 = l_Lean_Expr_const___override(x_92, x_88);
x_94 = lean_mk_string_unchecked("instOfNat", 9, 9);
x_95 = l_Lean_Name_mkStr2(x_91, x_94);
x_96 = l_Lean_Expr_const___override(x_95, x_88);
lean_inc(x_82);
x_97 = l_Lean_Expr_app___override(x_96, x_82);
x_98 = l_Lean_mkApp3(x_90, x_93, x_82, x_97);
if (lean_is_scalar(x_79)) {
 x_99 = lean_alloc_ctor(0, 1, 0);
} else {
 x_99 = x_79;
 lean_ctor_set_tag(x_99, 0);
}
lean_ctor_set(x_99, 0, x_98);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_77);
return x_100;
}
}
}
else
{
uint8_t x_101; 
x_101 = !lean_is_exclusive(x_23);
if (x_101 == 0)
{
return x_23;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_23, 0);
x_103 = lean_ctor_get(x_23, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_23);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
return x_104;
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
LEAN_EXPORT lean_object* l_Char_reduceVal(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Char_reduceVal___redArg(x_1, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Char_reduceVal___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Char_reduceVal___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Char_reduceVal___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Char_reduceVal(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceVal_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_757_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_2 = lean_mk_string_unchecked("Char", 4, 4);
x_3 = lean_mk_string_unchecked("reduceVal", 9, 9);
lean_inc(x_2);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = l_Lean_Name_mkStr1(x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_alloc_ctor(6, 3, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
lean_ctor_set(x_7, 2, x_6);
x_8 = lean_box(3);
x_9 = lean_unsigned_to_nat(2u);
x_10 = lean_mk_empty_array_with_capacity(x_9);
x_11 = lean_array_push(x_10, x_7);
x_12 = lean_array_push(x_11, x_8);
x_13 = lean_alloc_closure((void*)(l_Char_reduceVal___boxed), 9, 0);
x_14 = l_Lean_Meta_Simp_registerBuiltinDSimproc(x_4, x_12, x_13, x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceVal_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_759_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Char", 4, 4);
x_3 = lean_mk_string_unchecked("reduceVal", 9, 9);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Char_reduceVal___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceVal_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_761_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Char", 4, 4);
x_3 = lean_mk_string_unchecked("reduceVal", 9, 9);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Char_reduceVal___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Char_reduceLT___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_17 = l_Lean_Meta_getCharValue_x3f(x_16, x_2, x_3, x_4, x_5, x_6);
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
x_31 = l_Lean_Meta_getCharValue_x3f(x_30, x_2, x_3, x_4, x_5, x_27);
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
lean_object* x_39; lean_object* x_40; uint32_t x_41; uint32_t x_42; uint8_t x_43; lean_object* x_44; 
lean_free_object(x_18);
x_39 = lean_ctor_get(x_31, 1);
lean_inc(x_39);
lean_dec(x_31);
x_40 = lean_ctor_get(x_32, 0);
lean_inc(x_40);
lean_dec(x_32);
x_41 = lean_unbox_uint32(x_29);
lean_dec(x_29);
x_42 = lean_unbox_uint32(x_40);
lean_dec(x_40);
x_43 = lean_uint32_dec_lt(x_41, x_42);
x_44 = l_Lean_Meta_Simp_evalPropStep___redArg(x_1, x_43, x_2, x_3, x_4, x_5, x_39);
return x_44;
}
}
else
{
uint8_t x_45; 
lean_free_object(x_18);
lean_dec(x_29);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_31);
if (x_45 == 0)
{
return x_31;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_31, 0);
x_47 = lean_ctor_get(x_31, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_31);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_18, 0);
lean_inc(x_49);
lean_dec(x_18);
x_50 = l_Lean_Expr_appArg_x21(x_1);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_51 = l_Lean_Meta_getCharValue_x3f(x_50, x_2, x_3, x_4, x_5, x_27);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_49);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_54 = x_51;
} else {
 lean_dec_ref(x_51);
 x_54 = lean_box(0);
}
x_55 = lean_box(0);
x_56 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_56, 0, x_55);
if (lean_is_scalar(x_54)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_54;
}
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_53);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; uint32_t x_60; uint32_t x_61; uint8_t x_62; lean_object* x_63; 
x_58 = lean_ctor_get(x_51, 1);
lean_inc(x_58);
lean_dec(x_51);
x_59 = lean_ctor_get(x_52, 0);
lean_inc(x_59);
lean_dec(x_52);
x_60 = lean_unbox_uint32(x_49);
lean_dec(x_49);
x_61 = lean_unbox_uint32(x_59);
lean_dec(x_59);
x_62 = lean_uint32_dec_lt(x_60, x_61);
x_63 = l_Lean_Meta_Simp_evalPropStep___redArg(x_1, x_62, x_2, x_3, x_4, x_5, x_58);
return x_63;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_49);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_64 = lean_ctor_get(x_51, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_51, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_66 = x_51;
} else {
 lean_dec_ref(x_51);
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_68 = !lean_is_exclusive(x_17);
if (x_68 == 0)
{
return x_17;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_17, 0);
x_70 = lean_ctor_get(x_17, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_17);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Char_reduceLT(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Char_reduceLT___redArg(x_1, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Char_reduceLT___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Char_reduceLT(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceLT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_796_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_2 = lean_mk_string_unchecked("Char", 4, 4);
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
x_21 = lean_alloc_closure((void*)(l_Char_reduceLT___boxed), 9, 0);
x_22 = l_Lean_Meta_Simp_registerBuiltinSimproc(x_4, x_20, x_21, x_1);
return x_22;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceLT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_798_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Char", 4, 4);
x_3 = lean_mk_string_unchecked("reduceLT", 8, 8);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Char_reduceLT___boxed), 9, 0);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceLT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_800_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Char", 4, 4);
x_3 = lean_mk_string_unchecked("reduceLT", 8, 8);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Char_reduceLT___boxed), 9, 0);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Char_reduceLE___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_17 = l_Lean_Meta_getCharValue_x3f(x_16, x_2, x_3, x_4, x_5, x_6);
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
x_31 = l_Lean_Meta_getCharValue_x3f(x_30, x_2, x_3, x_4, x_5, x_27);
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
lean_object* x_39; lean_object* x_40; uint32_t x_41; uint32_t x_42; uint8_t x_43; lean_object* x_44; 
lean_free_object(x_18);
x_39 = lean_ctor_get(x_31, 1);
lean_inc(x_39);
lean_dec(x_31);
x_40 = lean_ctor_get(x_32, 0);
lean_inc(x_40);
lean_dec(x_32);
x_41 = lean_unbox_uint32(x_29);
lean_dec(x_29);
x_42 = lean_unbox_uint32(x_40);
lean_dec(x_40);
x_43 = lean_uint32_dec_le(x_41, x_42);
x_44 = l_Lean_Meta_Simp_evalPropStep___redArg(x_1, x_43, x_2, x_3, x_4, x_5, x_39);
return x_44;
}
}
else
{
uint8_t x_45; 
lean_free_object(x_18);
lean_dec(x_29);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_31);
if (x_45 == 0)
{
return x_31;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_31, 0);
x_47 = lean_ctor_get(x_31, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_31);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_18, 0);
lean_inc(x_49);
lean_dec(x_18);
x_50 = l_Lean_Expr_appArg_x21(x_1);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_51 = l_Lean_Meta_getCharValue_x3f(x_50, x_2, x_3, x_4, x_5, x_27);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_49);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_54 = x_51;
} else {
 lean_dec_ref(x_51);
 x_54 = lean_box(0);
}
x_55 = lean_box(0);
x_56 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_56, 0, x_55);
if (lean_is_scalar(x_54)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_54;
}
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_53);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; uint32_t x_60; uint32_t x_61; uint8_t x_62; lean_object* x_63; 
x_58 = lean_ctor_get(x_51, 1);
lean_inc(x_58);
lean_dec(x_51);
x_59 = lean_ctor_get(x_52, 0);
lean_inc(x_59);
lean_dec(x_52);
x_60 = lean_unbox_uint32(x_49);
lean_dec(x_49);
x_61 = lean_unbox_uint32(x_59);
lean_dec(x_59);
x_62 = lean_uint32_dec_le(x_60, x_61);
x_63 = l_Lean_Meta_Simp_evalPropStep___redArg(x_1, x_62, x_2, x_3, x_4, x_5, x_58);
return x_63;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_49);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_64 = lean_ctor_get(x_51, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_51, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_66 = x_51;
} else {
 lean_dec_ref(x_51);
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_68 = !lean_is_exclusive(x_17);
if (x_68 == 0)
{
return x_17;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_17, 0);
x_70 = lean_ctor_get(x_17, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_17);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Char_reduceLE(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Char_reduceLE___redArg(x_1, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Char_reduceLE___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Char_reduceLE(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceLE_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_835_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_2 = lean_mk_string_unchecked("Char", 4, 4);
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
x_21 = lean_alloc_closure((void*)(l_Char_reduceLE___boxed), 9, 0);
x_22 = l_Lean_Meta_Simp_registerBuiltinSimproc(x_4, x_20, x_21, x_1);
return x_22;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceLE_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_837_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Char", 4, 4);
x_3 = lean_mk_string_unchecked("reduceLE", 8, 8);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Char_reduceLE___boxed), 9, 0);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceLE_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_839_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Char", 4, 4);
x_3 = lean_mk_string_unchecked("reduceLE", 8, 8);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Char_reduceLE___boxed), 9, 0);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Char_reduceGT___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_17 = l_Lean_Meta_getCharValue_x3f(x_16, x_2, x_3, x_4, x_5, x_6);
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
x_31 = l_Lean_Meta_getCharValue_x3f(x_30, x_2, x_3, x_4, x_5, x_27);
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
lean_object* x_39; lean_object* x_40; uint32_t x_41; uint32_t x_42; uint8_t x_43; lean_object* x_44; 
lean_free_object(x_18);
x_39 = lean_ctor_get(x_31, 1);
lean_inc(x_39);
lean_dec(x_31);
x_40 = lean_ctor_get(x_32, 0);
lean_inc(x_40);
lean_dec(x_32);
x_41 = lean_unbox_uint32(x_40);
lean_dec(x_40);
x_42 = lean_unbox_uint32(x_29);
lean_dec(x_29);
x_43 = lean_uint32_dec_lt(x_41, x_42);
x_44 = l_Lean_Meta_Simp_evalPropStep___redArg(x_1, x_43, x_2, x_3, x_4, x_5, x_39);
return x_44;
}
}
else
{
uint8_t x_45; 
lean_free_object(x_18);
lean_dec(x_29);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_31);
if (x_45 == 0)
{
return x_31;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_31, 0);
x_47 = lean_ctor_get(x_31, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_31);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_18, 0);
lean_inc(x_49);
lean_dec(x_18);
x_50 = l_Lean_Expr_appArg_x21(x_1);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_51 = l_Lean_Meta_getCharValue_x3f(x_50, x_2, x_3, x_4, x_5, x_27);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_49);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_54 = x_51;
} else {
 lean_dec_ref(x_51);
 x_54 = lean_box(0);
}
x_55 = lean_box(0);
x_56 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_56, 0, x_55);
if (lean_is_scalar(x_54)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_54;
}
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_53);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; uint32_t x_60; uint32_t x_61; uint8_t x_62; lean_object* x_63; 
x_58 = lean_ctor_get(x_51, 1);
lean_inc(x_58);
lean_dec(x_51);
x_59 = lean_ctor_get(x_52, 0);
lean_inc(x_59);
lean_dec(x_52);
x_60 = lean_unbox_uint32(x_59);
lean_dec(x_59);
x_61 = lean_unbox_uint32(x_49);
lean_dec(x_49);
x_62 = lean_uint32_dec_lt(x_60, x_61);
x_63 = l_Lean_Meta_Simp_evalPropStep___redArg(x_1, x_62, x_2, x_3, x_4, x_5, x_58);
return x_63;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_49);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_64 = lean_ctor_get(x_51, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_51, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_66 = x_51;
} else {
 lean_dec_ref(x_51);
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_68 = !lean_is_exclusive(x_17);
if (x_68 == 0)
{
return x_17;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_17, 0);
x_70 = lean_ctor_get(x_17, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_17);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Char_reduceGT(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Char_reduceGT___redArg(x_1, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Char_reduceGT___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Char_reduceGT(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceGT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_874_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_2 = lean_mk_string_unchecked("Char", 4, 4);
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
x_21 = lean_alloc_closure((void*)(l_Char_reduceGT___boxed), 9, 0);
x_22 = l_Lean_Meta_Simp_registerBuiltinSimproc(x_4, x_20, x_21, x_1);
return x_22;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceGT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_876_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Char", 4, 4);
x_3 = lean_mk_string_unchecked("reduceGT", 8, 8);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Char_reduceGT___boxed), 9, 0);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceGT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_878_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Char", 4, 4);
x_3 = lean_mk_string_unchecked("reduceGT", 8, 8);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Char_reduceGT___boxed), 9, 0);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Char_reduceGE___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_17 = l_Lean_Meta_getCharValue_x3f(x_16, x_2, x_3, x_4, x_5, x_6);
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
x_31 = l_Lean_Meta_getCharValue_x3f(x_30, x_2, x_3, x_4, x_5, x_27);
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
lean_object* x_39; lean_object* x_40; uint32_t x_41; uint32_t x_42; uint8_t x_43; lean_object* x_44; 
lean_free_object(x_18);
x_39 = lean_ctor_get(x_31, 1);
lean_inc(x_39);
lean_dec(x_31);
x_40 = lean_ctor_get(x_32, 0);
lean_inc(x_40);
lean_dec(x_32);
x_41 = lean_unbox_uint32(x_40);
lean_dec(x_40);
x_42 = lean_unbox_uint32(x_29);
lean_dec(x_29);
x_43 = lean_uint32_dec_le(x_41, x_42);
x_44 = l_Lean_Meta_Simp_evalPropStep___redArg(x_1, x_43, x_2, x_3, x_4, x_5, x_39);
return x_44;
}
}
else
{
uint8_t x_45; 
lean_free_object(x_18);
lean_dec(x_29);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_31);
if (x_45 == 0)
{
return x_31;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_31, 0);
x_47 = lean_ctor_get(x_31, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_31);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_18, 0);
lean_inc(x_49);
lean_dec(x_18);
x_50 = l_Lean_Expr_appArg_x21(x_1);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_51 = l_Lean_Meta_getCharValue_x3f(x_50, x_2, x_3, x_4, x_5, x_27);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_49);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_54 = x_51;
} else {
 lean_dec_ref(x_51);
 x_54 = lean_box(0);
}
x_55 = lean_box(0);
x_56 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_56, 0, x_55);
if (lean_is_scalar(x_54)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_54;
}
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_53);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; uint32_t x_60; uint32_t x_61; uint8_t x_62; lean_object* x_63; 
x_58 = lean_ctor_get(x_51, 1);
lean_inc(x_58);
lean_dec(x_51);
x_59 = lean_ctor_get(x_52, 0);
lean_inc(x_59);
lean_dec(x_52);
x_60 = lean_unbox_uint32(x_59);
lean_dec(x_59);
x_61 = lean_unbox_uint32(x_49);
lean_dec(x_49);
x_62 = lean_uint32_dec_le(x_60, x_61);
x_63 = l_Lean_Meta_Simp_evalPropStep___redArg(x_1, x_62, x_2, x_3, x_4, x_5, x_58);
return x_63;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_49);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_64 = lean_ctor_get(x_51, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_51, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_66 = x_51;
} else {
 lean_dec_ref(x_51);
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_68 = !lean_is_exclusive(x_17);
if (x_68 == 0)
{
return x_17;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_17, 0);
x_70 = lean_ctor_get(x_17, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_17);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Char_reduceGE(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Char_reduceGE___redArg(x_1, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Char_reduceGE___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Char_reduceGE(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceGE_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_913_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_2 = lean_mk_string_unchecked("Char", 4, 4);
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
x_21 = lean_alloc_closure((void*)(l_Char_reduceGE___boxed), 9, 0);
x_22 = l_Lean_Meta_Simp_registerBuiltinSimproc(x_4, x_20, x_21, x_1);
return x_22;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceGE_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_915_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Char", 4, 4);
x_3 = lean_mk_string_unchecked("reduceGE", 8, 8);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Char_reduceGE___boxed), 9, 0);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceGE_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_917_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Char", 4, 4);
x_3 = lean_mk_string_unchecked("reduceGE", 8, 8);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Char_reduceGE___boxed), 9, 0);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Char_reduceEq___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_16 = l_Lean_Meta_getCharValue_x3f(x_15, x_2, x_3, x_4, x_5, x_6);
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
x_30 = l_Lean_Meta_getCharValue_x3f(x_29, x_2, x_3, x_4, x_5, x_26);
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
lean_object* x_38; lean_object* x_39; uint32_t x_40; uint32_t x_41; uint8_t x_42; lean_object* x_43; 
lean_free_object(x_17);
x_38 = lean_ctor_get(x_30, 1);
lean_inc(x_38);
lean_dec(x_30);
x_39 = lean_ctor_get(x_31, 0);
lean_inc(x_39);
lean_dec(x_31);
x_40 = lean_unbox_uint32(x_28);
lean_dec(x_28);
x_41 = lean_unbox_uint32(x_39);
lean_dec(x_39);
x_42 = l_instDecidableEqChar(x_40, x_41);
x_43 = l_Lean_Meta_Simp_evalPropStep___redArg(x_1, x_42, x_2, x_3, x_4, x_5, x_38);
return x_43;
}
}
else
{
uint8_t x_44; 
lean_free_object(x_17);
lean_dec(x_28);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_44 = !lean_is_exclusive(x_30);
if (x_44 == 0)
{
return x_30;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_30, 0);
x_46 = lean_ctor_get(x_30, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_30);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_17, 0);
lean_inc(x_48);
lean_dec(x_17);
x_49 = l_Lean_Expr_appArg_x21(x_1);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_50 = l_Lean_Meta_getCharValue_x3f(x_49, x_2, x_3, x_4, x_5, x_26);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_48);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_53 = x_50;
} else {
 lean_dec_ref(x_50);
 x_53 = lean_box(0);
}
x_54 = lean_box(0);
x_55 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_55, 0, x_54);
if (lean_is_scalar(x_53)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_53;
}
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_52);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; uint32_t x_59; uint32_t x_60; uint8_t x_61; lean_object* x_62; 
x_57 = lean_ctor_get(x_50, 1);
lean_inc(x_57);
lean_dec(x_50);
x_58 = lean_ctor_get(x_51, 0);
lean_inc(x_58);
lean_dec(x_51);
x_59 = lean_unbox_uint32(x_48);
lean_dec(x_48);
x_60 = lean_unbox_uint32(x_58);
lean_dec(x_58);
x_61 = l_instDecidableEqChar(x_59, x_60);
x_62 = l_Lean_Meta_Simp_evalPropStep___redArg(x_1, x_61, x_2, x_3, x_4, x_5, x_57);
return x_62;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_48);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_63 = lean_ctor_get(x_50, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_50, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_65 = x_50;
} else {
 lean_dec_ref(x_50);
 x_65 = lean_box(0);
}
if (lean_is_scalar(x_65)) {
 x_66 = lean_alloc_ctor(1, 2, 0);
} else {
 x_66 = x_65;
}
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_64);
return x_66;
}
}
}
}
else
{
uint8_t x_67; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_67 = !lean_is_exclusive(x_16);
if (x_67 == 0)
{
return x_16;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_16, 0);
x_69 = lean_ctor_get(x_16, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_16);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Char_reduceEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Char_reduceEq___redArg(x_1, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Char_reduceEq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Char_reduceEq(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_952_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("Char", 4, 4);
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
x_19 = lean_alloc_closure((void*)(l_Char_reduceEq___boxed), 9, 0);
x_20 = l_Lean_Meta_Simp_registerBuiltinSimproc(x_4, x_18, x_19, x_1);
return x_20;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_954_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Char", 4, 4);
x_3 = lean_mk_string_unchecked("reduceEq", 8, 8);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Char_reduceEq___boxed), 9, 0);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_956_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Char", 4, 4);
x_3 = lean_mk_string_unchecked("reduceEq", 8, 8);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Char_reduceEq___boxed), 9, 0);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Char_reduceNe___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_16 = l_Lean_Meta_getCharValue_x3f(x_15, x_2, x_3, x_4, x_5, x_6);
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
x_30 = l_Lean_Meta_getCharValue_x3f(x_29, x_2, x_3, x_4, x_5, x_26);
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
lean_object* x_38; lean_object* x_39; uint32_t x_40; uint32_t x_41; uint8_t x_42; uint8_t x_43; lean_object* x_44; 
lean_free_object(x_17);
x_38 = lean_ctor_get(x_30, 1);
lean_inc(x_38);
lean_dec(x_30);
x_39 = lean_ctor_get(x_31, 0);
lean_inc(x_39);
lean_dec(x_31);
x_40 = lean_unbox_uint32(x_28);
lean_dec(x_28);
x_41 = lean_unbox_uint32(x_39);
lean_dec(x_39);
x_42 = l_instDecidableEqChar(x_40, x_41);
x_43 = l_instDecidableNot___redArg(x_42);
x_44 = l_Lean_Meta_Simp_evalPropStep___redArg(x_1, x_43, x_2, x_3, x_4, x_5, x_38);
return x_44;
}
}
else
{
uint8_t x_45; 
lean_free_object(x_17);
lean_dec(x_28);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_30);
if (x_45 == 0)
{
return x_30;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_30, 0);
x_47 = lean_ctor_get(x_30, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_30);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_17, 0);
lean_inc(x_49);
lean_dec(x_17);
x_50 = l_Lean_Expr_appArg_x21(x_1);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_51 = l_Lean_Meta_getCharValue_x3f(x_50, x_2, x_3, x_4, x_5, x_26);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_49);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_54 = x_51;
} else {
 lean_dec_ref(x_51);
 x_54 = lean_box(0);
}
x_55 = lean_box(0);
x_56 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_56, 0, x_55);
if (lean_is_scalar(x_54)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_54;
}
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_53);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; uint32_t x_60; uint32_t x_61; uint8_t x_62; uint8_t x_63; lean_object* x_64; 
x_58 = lean_ctor_get(x_51, 1);
lean_inc(x_58);
lean_dec(x_51);
x_59 = lean_ctor_get(x_52, 0);
lean_inc(x_59);
lean_dec(x_52);
x_60 = lean_unbox_uint32(x_49);
lean_dec(x_49);
x_61 = lean_unbox_uint32(x_59);
lean_dec(x_59);
x_62 = l_instDecidableEqChar(x_60, x_61);
x_63 = l_instDecidableNot___redArg(x_62);
x_64 = l_Lean_Meta_Simp_evalPropStep___redArg(x_1, x_63, x_2, x_3, x_4, x_5, x_58);
return x_64;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_49);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_65 = lean_ctor_get(x_51, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_51, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_67 = x_51;
} else {
 lean_dec_ref(x_51);
 x_67 = lean_box(0);
}
if (lean_is_scalar(x_67)) {
 x_68 = lean_alloc_ctor(1, 2, 0);
} else {
 x_68 = x_67;
}
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_66);
return x_68;
}
}
}
}
else
{
uint8_t x_69; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_69 = !lean_is_exclusive(x_16);
if (x_69 == 0)
{
return x_16;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_16, 0);
x_71 = lean_ctor_get(x_16, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_16);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Char_reduceNe(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Char_reduceNe___redArg(x_1, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Char_reduceNe___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Char_reduceNe(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_990_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_2 = lean_mk_string_unchecked("Char", 4, 4);
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
x_24 = lean_alloc_closure((void*)(l_Char_reduceNe___boxed), 9, 0);
x_25 = l_Lean_Meta_Simp_registerBuiltinSimproc(x_4, x_23, x_24, x_1);
return x_25;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_992_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Char", 4, 4);
x_3 = lean_mk_string_unchecked("reduceNe", 8, 8);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Char_reduceNe___boxed), 9, 0);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_994_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Char", 4, 4);
x_3 = lean_mk_string_unchecked("reduceNe", 8, 8);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Char_reduceNe___boxed), 9, 0);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Char_reduceBEq___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_17 = l_Lean_Meta_getCharValue_x3f(x_16, x_2, x_3, x_4, x_5, x_6);
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
x_33 = l_Lean_Meta_getCharValue_x3f(x_32, x_2, x_3, x_4, x_5, x_28);
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
lean_object* x_43; uint32_t x_44; uint32_t x_45; uint8_t x_46; 
lean_free_object(x_17);
x_43 = lean_ctor_get(x_34, 0);
lean_inc(x_43);
lean_dec(x_34);
x_44 = lean_unbox_uint32(x_30);
lean_dec(x_30);
x_45 = lean_unbox_uint32(x_43);
lean_dec(x_43);
x_46 = l_instDecidableEqChar(x_44, x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_47 = lean_mk_string_unchecked("Bool", 4, 4);
x_48 = lean_mk_string_unchecked("false", 5, 5);
x_49 = l_Lean_Name_mkStr2(x_47, x_48);
x_50 = lean_box(0);
x_51 = l_Lean_Expr_const___override(x_49, x_50);
x_37 = x_51;
goto block_40;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_52 = lean_mk_string_unchecked("Bool", 4, 4);
x_53 = lean_mk_string_unchecked("true", 4, 4);
x_54 = l_Lean_Name_mkStr2(x_52, x_53);
x_55 = lean_box(0);
x_56 = l_Lean_Expr_const___override(x_54, x_55);
x_37 = x_56;
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
uint8_t x_57; 
lean_dec(x_31);
lean_dec(x_30);
lean_free_object(x_17);
x_57 = !lean_is_exclusive(x_33);
if (x_57 == 0)
{
return x_33;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_33, 0);
x_59 = lean_ctor_get(x_33, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_33);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_61 = lean_ctor_get(x_17, 1);
lean_inc(x_61);
lean_dec(x_17);
x_62 = lean_ctor_get(x_18, 0);
lean_inc(x_62);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 x_63 = x_18;
} else {
 lean_dec_ref(x_18);
 x_63 = lean_box(0);
}
x_64 = l_Lean_Expr_appArg_x21(x_1);
x_65 = l_Lean_Meta_getCharValue_x3f(x_64, x_2, x_3, x_4, x_5, x_61);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_68 = x_65;
} else {
 lean_dec_ref(x_65);
 x_68 = lean_box(0);
}
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_68);
lean_dec(x_63);
lean_dec(x_62);
x_73 = lean_box(0);
x_74 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_74, 0, x_73);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_67);
return x_75;
}
else
{
lean_object* x_76; uint32_t x_77; uint32_t x_78; uint8_t x_79; 
x_76 = lean_ctor_get(x_66, 0);
lean_inc(x_76);
lean_dec(x_66);
x_77 = lean_unbox_uint32(x_62);
lean_dec(x_62);
x_78 = lean_unbox_uint32(x_76);
lean_dec(x_76);
x_79 = l_instDecidableEqChar(x_77, x_78);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_80 = lean_mk_string_unchecked("Bool", 4, 4);
x_81 = lean_mk_string_unchecked("false", 5, 5);
x_82 = l_Lean_Name_mkStr2(x_80, x_81);
x_83 = lean_box(0);
x_84 = l_Lean_Expr_const___override(x_82, x_83);
x_69 = x_84;
goto block_72;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_85 = lean_mk_string_unchecked("Bool", 4, 4);
x_86 = lean_mk_string_unchecked("true", 4, 4);
x_87 = l_Lean_Name_mkStr2(x_85, x_86);
x_88 = lean_box(0);
x_89 = l_Lean_Expr_const___override(x_87, x_88);
x_69 = x_89;
goto block_72;
}
}
block_72:
{
lean_object* x_70; lean_object* x_71; 
if (lean_is_scalar(x_63)) {
 x_70 = lean_alloc_ctor(0, 1, 0);
} else {
 x_70 = x_63;
 lean_ctor_set_tag(x_70, 0);
}
lean_ctor_set(x_70, 0, x_69);
if (lean_is_scalar(x_68)) {
 x_71 = lean_alloc_ctor(0, 2, 0);
} else {
 x_71 = x_68;
}
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_67);
return x_71;
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_63);
lean_dec(x_62);
x_90 = lean_ctor_get(x_65, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_65, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_92 = x_65;
} else {
 lean_dec_ref(x_65);
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_94 = !lean_is_exclusive(x_17);
if (x_94 == 0)
{
return x_17;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_17, 0);
x_96 = lean_ctor_get(x_17, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_17);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Char_reduceBEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Char_reduceBEq___redArg(x_1, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Char_reduceBEq___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Char_reduceBEq___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Char_reduceBEq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Char_reduceBEq(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceBEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_1029_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_2 = lean_mk_string_unchecked("Char", 4, 4);
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
x_21 = lean_alloc_closure((void*)(l_Char_reduceBEq___boxed), 9, 0);
x_22 = l_Lean_Meta_Simp_registerBuiltinDSimproc(x_4, x_20, x_21, x_1);
return x_22;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceBEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_1031_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Char", 4, 4);
x_3 = lean_mk_string_unchecked("reduceBEq", 9, 9);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Char_reduceBEq___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceBEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_1033_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Char", 4, 4);
x_3 = lean_mk_string_unchecked("reduceBEq", 9, 9);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Char_reduceBEq___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Char_reduceBNe___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_16 = l_Lean_Meta_getCharValue_x3f(x_15, x_2, x_3, x_4, x_5, x_6);
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
x_32 = l_Lean_Meta_getCharValue_x3f(x_31, x_2, x_3, x_4, x_5, x_27);
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
lean_object* x_48; uint32_t x_49; uint32_t x_50; uint8_t x_51; 
lean_free_object(x_16);
x_48 = lean_ctor_get(x_33, 0);
lean_inc(x_48);
lean_dec(x_33);
x_49 = lean_unbox_uint32(x_29);
lean_dec(x_29);
x_50 = lean_unbox_uint32(x_48);
lean_dec(x_48);
x_51 = l_instDecidableEqChar(x_49, x_50);
if (x_51 == 0)
{
if (x_10 == 0)
{
goto block_45;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_52 = lean_mk_string_unchecked("Bool", 4, 4);
x_53 = lean_mk_string_unchecked("true", 4, 4);
x_54 = l_Lean_Name_mkStr2(x_52, x_53);
x_55 = lean_box(0);
x_56 = l_Lean_Expr_const___override(x_54, x_55);
x_36 = x_56;
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
uint8_t x_57; 
lean_dec(x_30);
lean_dec(x_29);
lean_free_object(x_16);
x_57 = !lean_is_exclusive(x_32);
if (x_57 == 0)
{
return x_32;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_32, 0);
x_59 = lean_ctor_get(x_32, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_32);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_61 = lean_ctor_get(x_16, 1);
lean_inc(x_61);
lean_dec(x_16);
x_62 = lean_ctor_get(x_17, 0);
lean_inc(x_62);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 x_63 = x_17;
} else {
 lean_dec_ref(x_17);
 x_63 = lean_box(0);
}
x_64 = l_Lean_Expr_appArg_x21(x_1);
x_65 = l_Lean_Meta_getCharValue_x3f(x_64, x_2, x_3, x_4, x_5, x_61);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_68 = x_65;
} else {
 lean_dec_ref(x_65);
 x_68 = lean_box(0);
}
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_68);
lean_dec(x_63);
lean_dec(x_62);
x_79 = lean_box(0);
x_80 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_80, 0, x_79);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_67);
return x_81;
}
else
{
lean_object* x_82; uint32_t x_83; uint32_t x_84; uint8_t x_85; 
x_82 = lean_ctor_get(x_66, 0);
lean_inc(x_82);
lean_dec(x_66);
x_83 = lean_unbox_uint32(x_62);
lean_dec(x_62);
x_84 = lean_unbox_uint32(x_82);
lean_dec(x_82);
x_85 = l_instDecidableEqChar(x_83, x_84);
if (x_85 == 0)
{
if (x_10 == 0)
{
goto block_78;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_86 = lean_mk_string_unchecked("Bool", 4, 4);
x_87 = lean_mk_string_unchecked("true", 4, 4);
x_88 = l_Lean_Name_mkStr2(x_86, x_87);
x_89 = lean_box(0);
x_90 = l_Lean_Expr_const___override(x_88, x_89);
x_69 = x_90;
goto block_72;
}
}
else
{
goto block_78;
}
}
block_72:
{
lean_object* x_70; lean_object* x_71; 
if (lean_is_scalar(x_63)) {
 x_70 = lean_alloc_ctor(0, 1, 0);
} else {
 x_70 = x_63;
 lean_ctor_set_tag(x_70, 0);
}
lean_ctor_set(x_70, 0, x_69);
if (lean_is_scalar(x_68)) {
 x_71 = lean_alloc_ctor(0, 2, 0);
} else {
 x_71 = x_68;
}
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_67);
return x_71;
}
block_78:
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_73 = lean_mk_string_unchecked("Bool", 4, 4);
x_74 = lean_mk_string_unchecked("false", 5, 5);
x_75 = l_Lean_Name_mkStr2(x_73, x_74);
x_76 = lean_box(0);
x_77 = l_Lean_Expr_const___override(x_75, x_76);
x_69 = x_77;
goto block_72;
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_63);
lean_dec(x_62);
x_91 = lean_ctor_get(x_65, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_65, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_93 = x_65;
} else {
 lean_dec_ref(x_65);
 x_93 = lean_box(0);
}
if (lean_is_scalar(x_93)) {
 x_94 = lean_alloc_ctor(1, 2, 0);
} else {
 x_94 = x_93;
}
lean_ctor_set(x_94, 0, x_91);
lean_ctor_set(x_94, 1, x_92);
return x_94;
}
}
}
}
else
{
uint8_t x_95; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_95 = !lean_is_exclusive(x_16);
if (x_95 == 0)
{
return x_16;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_16, 0);
x_97 = lean_ctor_get(x_16, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_16);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Char_reduceBNe(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Char_reduceBNe___redArg(x_1, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Char_reduceBNe___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Char_reduceBNe___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Char_reduceBNe___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Char_reduceBNe(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceBNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_1067_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_2 = lean_mk_string_unchecked("Char", 4, 4);
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
x_20 = lean_alloc_closure((void*)(l_Char_reduceBNe___boxed), 9, 0);
x_21 = l_Lean_Meta_Simp_registerBuiltinDSimproc(x_4, x_19, x_20, x_1);
return x_21;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceBNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_1069_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Char", 4, 4);
x_3 = lean_mk_string_unchecked("reduceBNe", 9, 9);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Char_reduceBNe___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceBNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_1071_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Char", 4, 4);
x_3 = lean_mk_string_unchecked("reduceBNe", 9, 9);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Char_reduceBNe___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Char_isValue___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_1);
x_7 = l_Lean_Meta_getCharValue_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
lean_dec(x_1);
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_7, 0);
lean_dec(x_10);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_7, 0, x_12);
return x_7;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_13);
lean_dec(x_7);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_7);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_7, 0);
lean_dec(x_18);
x_19 = !lean_is_exclusive(x_8);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_8, 0);
lean_dec(x_20);
lean_ctor_set_tag(x_8, 0);
lean_ctor_set(x_8, 0, x_1);
return x_7;
}
else
{
lean_object* x_21; 
lean_dec(x_8);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_1);
lean_ctor_set(x_7, 0, x_21);
return x_7;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_7, 1);
lean_inc(x_22);
lean_dec(x_7);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 x_23 = x_8;
} else {
 lean_dec_ref(x_8);
 x_23 = lean_box(0);
}
if (lean_is_scalar(x_23)) {
 x_24 = lean_alloc_ctor(0, 1, 0);
} else {
 x_24 = x_23;
 lean_ctor_set_tag(x_24, 0);
}
lean_ctor_set(x_24, 0, x_1);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_22);
return x_25;
}
}
}
else
{
uint8_t x_26; 
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_7);
if (x_26 == 0)
{
return x_7;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_7, 0);
x_28 = lean_ctor_get(x_7, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_7);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l_Char_isValue(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Char_isValue___redArg(x_1, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Char_isValue___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Char_isValue___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Char_isValue___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Char_isValue(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Char_isValue_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_1154_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_2 = lean_mk_string_unchecked("Char", 4, 4);
x_3 = lean_mk_string_unchecked("isValue", 7, 7);
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
x_14 = lean_alloc_closure((void*)(l_Char_isValue___boxed), 9, 0);
x_15 = l_Lean_Meta_Simp_registerBuiltinDSimproc(x_4, x_13, x_14, x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Char_isValue_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_1156_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Char", 4, 4);
x_3 = lean_mk_string_unchecked("isValue", 7, 7);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(0);
x_6 = lean_alloc_closure((void*)(l_Char_isValue___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Char_isValue_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_1158_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Char", 4, 4);
x_3 = lean_mk_string_unchecked("isValue", 7, 7);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(0);
x_6 = lean_alloc_closure((void*)(l_Char_isValue___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Char_reduceOfNatAux___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_17 = l_Lean_Expr_appFnCleanup___redArg(x_15);
x_18 = l_Lean_Expr_isApp(x_17);
if (x_18 == 0)
{
lean_dec(x_17);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
goto block_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
lean_inc(x_17);
x_19 = l_Lean_Expr_appFnCleanup___redArg(x_17);
x_20 = lean_mk_string_unchecked("Char", 4, 4);
x_21 = lean_mk_string_unchecked("ofNatAux", 8, 8);
lean_inc(x_20);
x_22 = l_Lean_Name_mkStr2(x_20, x_21);
x_23 = l_Lean_Expr_isConstOf(x_19, x_22);
lean_dec(x_22);
lean_dec(x_19);
if (x_23 == 0)
{
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
goto block_14;
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_10);
x_24 = lean_ctor_get(x_17, 1);
lean_inc(x_24);
lean_dec(x_17);
x_25 = l_Lean_Meta_getNatValue_x3f(x_24, x_2, x_3, x_4, x_5, x_9);
lean_dec(x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
lean_dec(x_20);
x_27 = !lean_is_exclusive(x_25);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_25, 0);
lean_dec(x_28);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_25, 0, x_30);
return x_25;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_25, 1);
lean_inc(x_31);
lean_dec(x_25);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_31);
return x_34;
}
}
else
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_25);
if (x_35 == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_25, 0);
lean_dec(x_36);
x_37 = !lean_is_exclusive(x_26);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint32_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_38 = lean_ctor_get(x_26, 0);
x_39 = lean_mk_string_unchecked("ofNat", 5, 5);
x_40 = l_Lean_Name_mkStr2(x_20, x_39);
x_41 = lean_box(0);
x_42 = l_Lean_Expr_const___override(x_40, x_41);
x_43 = l_Char_ofNat(x_38);
lean_dec(x_38);
x_44 = lean_uint32_to_nat(x_43);
x_45 = l_Lean_mkRawNatLit(x_44);
x_46 = l_Lean_Expr_app___override(x_42, x_45);
lean_ctor_set_tag(x_26, 0);
lean_ctor_set(x_26, 0, x_46);
return x_25;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint32_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_47 = lean_ctor_get(x_26, 0);
lean_inc(x_47);
lean_dec(x_26);
x_48 = lean_mk_string_unchecked("ofNat", 5, 5);
x_49 = l_Lean_Name_mkStr2(x_20, x_48);
x_50 = lean_box(0);
x_51 = l_Lean_Expr_const___override(x_49, x_50);
x_52 = l_Char_ofNat(x_47);
lean_dec(x_47);
x_53 = lean_uint32_to_nat(x_52);
x_54 = l_Lean_mkRawNatLit(x_53);
x_55 = l_Lean_Expr_app___override(x_51, x_54);
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_25, 0, x_56);
return x_25;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint32_t x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_57 = lean_ctor_get(x_25, 1);
lean_inc(x_57);
lean_dec(x_25);
x_58 = lean_ctor_get(x_26, 0);
lean_inc(x_58);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 x_59 = x_26;
} else {
 lean_dec_ref(x_26);
 x_59 = lean_box(0);
}
x_60 = lean_mk_string_unchecked("ofNat", 5, 5);
x_61 = l_Lean_Name_mkStr2(x_20, x_60);
x_62 = lean_box(0);
x_63 = l_Lean_Expr_const___override(x_61, x_62);
x_64 = l_Char_ofNat(x_58);
lean_dec(x_58);
x_65 = lean_uint32_to_nat(x_64);
x_66 = l_Lean_mkRawNatLit(x_65);
x_67 = l_Lean_Expr_app___override(x_63, x_66);
if (lean_is_scalar(x_59)) {
 x_68 = lean_alloc_ctor(0, 1, 0);
} else {
 x_68 = x_59;
 lean_ctor_set_tag(x_68, 0);
}
lean_ctor_set(x_68, 0, x_67);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_57);
return x_69;
}
}
}
else
{
uint8_t x_70; 
lean_dec(x_20);
x_70 = !lean_is_exclusive(x_25);
if (x_70 == 0)
{
return x_25;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_25, 0);
x_72 = lean_ctor_get(x_25, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_25);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
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
LEAN_EXPORT lean_object* l_Char_reduceOfNatAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Char_reduceOfNatAux___redArg(x_1, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Char_reduceOfNatAux___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Char_reduceOfNatAux___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Char_reduceOfNatAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Char_reduceOfNatAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceOfNatAux_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_1345_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_2 = lean_mk_string_unchecked("Char", 4, 4);
x_3 = lean_mk_string_unchecked("reduceOfNatAux", 14, 14);
lean_inc(x_2);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_mk_string_unchecked("ofNatAux", 8, 8);
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
x_15 = lean_alloc_closure((void*)(l_Char_reduceOfNatAux___boxed), 9, 0);
x_16 = l_Lean_Meta_Simp_registerBuiltinDSimproc(x_4, x_14, x_15, x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceOfNatAux_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_1347_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Char", 4, 4);
x_3 = lean_mk_string_unchecked("reduceOfNatAux", 14, 14);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Char_reduceOfNatAux___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceOfNatAux_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_1349_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Char", 4, 4);
x_3 = lean_mk_string_unchecked("reduceOfNatAux", 14, 14);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Char_reduceOfNatAux___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Char_reduceDefault___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_12; uint8_t x_13; 
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
goto block_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = l_Lean_Expr_appFnCleanup___redArg(x_14);
x_17 = lean_mk_string_unchecked("Inhabited", 9, 9);
x_18 = lean_mk_string_unchecked("default", 7, 7);
x_19 = l_Lean_Name_mkStr2(x_17, x_18);
x_20 = l_Lean_Expr_isConstOf(x_16, x_19);
lean_dec(x_19);
lean_dec(x_16);
if (x_20 == 0)
{
goto block_11;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint32_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_7);
x_21 = lean_unsigned_to_nat(65u);
x_22 = lean_mk_string_unchecked("Char", 4, 4);
x_23 = lean_mk_string_unchecked("ofNat", 5, 5);
x_24 = l_Lean_Name_mkStr2(x_22, x_23);
x_25 = lean_box(0);
x_26 = l_Lean_Expr_const___override(x_24, x_25);
x_27 = l_Char_ofNat(x_21);
x_28 = lean_uint32_to_nat(x_27);
x_29 = l_Lean_mkRawNatLit(x_28);
x_30 = l_Lean_Expr_app___override(x_26, x_29);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_6);
return x_32;
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
LEAN_EXPORT lean_object* l_Char_reduceDefault(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Char_reduceDefault___redArg(x_1, x_6, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Char_reduceDefault___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Char_reduceDefault___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Char_reduceDefault___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Char_reduceDefault(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceDefault_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_1496_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("Char", 4, 4);
x_3 = lean_mk_string_unchecked("reduceDefault", 13, 13);
lean_inc(x_2);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_mk_string_unchecked("Inhabited", 9, 9);
x_6 = lean_mk_string_unchecked("default", 7, 7);
x_7 = l_Lean_Name_mkStr2(x_5, x_6);
x_8 = lean_unsigned_to_nat(2u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Lean_Name_mkStr1(x_2);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_box(3);
x_14 = lean_unsigned_to_nat(3u);
x_15 = lean_mk_empty_array_with_capacity(x_14);
x_16 = lean_array_push(x_15, x_9);
x_17 = lean_array_push(x_16, x_12);
x_18 = lean_array_push(x_17, x_13);
x_19 = lean_alloc_closure((void*)(l_Char_reduceDefault___boxed), 9, 0);
x_20 = l_Lean_Meta_Simp_registerBuiltinDSimproc(x_4, x_18, x_19, x_1);
return x_20;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceDefault_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_1498_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Char", 4, 4);
x_3 = lean_mk_string_unchecked("reduceDefault", 13, 13);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Char_reduceDefault___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Char_reduceDefault_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_1500_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Char", 4, 4);
x_3 = lean_mk_string_unchecked("reduceDefault", 13, 13);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Char_reduceDefault___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
lean_object* initialize_Lean_ToExpr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_LitValues(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_UInt(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_ToExpr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_LitValues(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_UInt(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
if (builtin) {res = l___regBuiltin_Char_reduceToLower_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_416_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Char_reduceToLower_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_418_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Char_reduceToLower_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_420_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Char_reduceToUpper_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_436_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Char_reduceToUpper_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_438_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Char_reduceToUpper_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_440_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Char_reduceToNat_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_456_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Char_reduceToNat_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_458_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Char_reduceToNat_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_460_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Char_reduceIsWhitespace_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_476_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Char_reduceIsWhitespace_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_478_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Char_reduceIsWhitespace_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_480_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Char_reduceIsUpper_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_496_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Char_reduceIsUpper_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_498_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Char_reduceIsUpper_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_500_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Char_reduceIsLower_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_516_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Char_reduceIsLower_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_518_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Char_reduceIsLower_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_520_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Char_reduceIsAlpha_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_536_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Char_reduceIsAlpha_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_538_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Char_reduceIsAlpha_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_540_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Char_reduceIsDigit_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_556_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Char_reduceIsDigit_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_558_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Char_reduceIsDigit_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_560_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Char_reduceIsAlphaNum_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_576_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Char_reduceIsAlphaNum_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_578_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Char_reduceIsAlphaNum_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_580_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Char_reduceToString_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_600_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Char_reduceToString_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_602_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Char_reduceToString_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_604_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Char_reduceVal_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_757_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Char_reduceVal_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_759_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Char_reduceVal_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_761_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Char_reduceLT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_796_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Char_reduceLT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_798_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Char_reduceLT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_800_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Char_reduceLE_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_835_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Char_reduceLE_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_837_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Char_reduceLE_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_839_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Char_reduceGT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_874_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Char_reduceGT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_876_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Char_reduceGT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_878_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Char_reduceGE_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_913_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Char_reduceGE_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_915_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Char_reduceGE_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_917_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Char_reduceEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_952_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Char_reduceEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_954_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Char_reduceEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_956_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Char_reduceNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_990_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Char_reduceNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_992_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Char_reduceNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_994_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Char_reduceBEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_1029_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Char_reduceBEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_1031_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Char_reduceBEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_1033_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Char_reduceBNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_1067_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Char_reduceBNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_1069_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Char_reduceBNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_1071_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Char_isValue_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_1154_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Char_isValue_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_1156_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Char_isValue_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_1158_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Char_reduceOfNatAux_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_1345_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Char_reduceOfNatAux_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_1347_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Char_reduceOfNatAux_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_1349_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Char_reduceDefault_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_1496_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Char_reduceDefault_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_1498_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Char_reduceDefault_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char___hyg_1500_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
