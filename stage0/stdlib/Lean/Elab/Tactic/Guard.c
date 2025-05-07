// Lean compiler output
// Module: Lean.Elab.Tactic.Guard
// Imports: Init.Guard Lean.Elab.Command Lean.Elab.Tactic.Conv.Basic Lean.Meta.Basic Lean.Meta.Eval
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_logUnassignedUsingErrorInfos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainTarget___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange__1(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getFVarId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___redArg(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Lean_Elab_Term_withoutErrToSorryImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind(lean_object*);
lean_object* l_Lean_Elab_Term_elabTermEnsuringType(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp__1(lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_MatchKind_isEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVars___at___Lean_Elab_Tactic_getMainTarget_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_evalExpr(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange__1(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget__1(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange__1(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_MatchKind_isEq___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd__1(lean_object*);
lean_object* l_Lean_Elab_Tactic_elabTerm(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_find(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_commandElabAttribute;
lean_object* l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__4___redArg(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange__1(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv__1(lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange__1(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVars___at___Lean_Elab_Term_MVarErrorInfo_logError_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_MatchKind_isEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind(lean_object*);
lean_object* l_Lean_Elab_Tactic_Conv_getLhs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withMainContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange__1(lean_object*);
lean_object* l_Lean_withoutModifyingState___at___Lean_Meta_addPPExplicitToExposeDiff_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange__1(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_isExprDefEqGuarded(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange__1(lean_object*);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind(lean_object*);
lean_object* l_Lean_Elab_Command_liftTermElabM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_runTermElabM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_value_x3f(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_MatchKind_isEq___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_consumeMData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("colon", 5, 5);
lean_inc(x_3);
lean_inc(x_2);
x_5 = l_Lean_Name_mkStr3(x_2, x_3, x_4);
lean_inc(x_1);
x_6 = l_Lean_Syntax_isOfKind(x_1, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(0);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
lean_dec(x_1);
x_10 = lean_mk_string_unchecked("colonR", 6, 6);
lean_inc(x_3);
lean_inc(x_2);
x_11 = l_Lean_Name_mkStr3(x_2, x_3, x_10);
lean_inc(x_9);
x_12 = l_Lean_Syntax_isOfKind(x_9, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_mk_string_unchecked("colonD", 6, 6);
lean_inc(x_3);
lean_inc(x_2);
x_14 = l_Lean_Name_mkStr3(x_2, x_3, x_13);
lean_inc(x_9);
x_15 = l_Lean_Syntax_isOfKind(x_9, x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_mk_string_unchecked("colonS", 6, 6);
lean_inc(x_3);
lean_inc(x_2);
x_17 = l_Lean_Name_mkStr3(x_2, x_3, x_16);
lean_inc(x_9);
x_18 = l_Lean_Syntax_isOfKind(x_9, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_mk_string_unchecked("colonA", 6, 6);
x_20 = l_Lean_Name_mkStr3(x_2, x_3, x_19);
x_21 = l_Lean_Syntax_isOfKind(x_9, x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_box(0);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_box(2);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; 
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
x_27 = lean_box(1);
x_28 = lean_alloc_ctor(1, 0, 1);
x_29 = lean_unbox(x_27);
lean_ctor_set_uint8(x_28, 0, x_29);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_28);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; 
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
x_31 = lean_box(2);
x_32 = lean_alloc_ctor(1, 0, 1);
x_33 = lean_unbox(x_31);
lean_ctor_set_uint8(x_32, 0, x_33);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_32);
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("colonEq", 7, 7);
lean_inc(x_3);
lean_inc(x_2);
x_5 = l_Lean_Name_mkStr3(x_2, x_3, x_4);
lean_inc(x_1);
x_6 = l_Lean_Syntax_isOfKind(x_1, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(0);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
lean_dec(x_1);
x_10 = lean_mk_string_unchecked("colonEqR", 8, 8);
lean_inc(x_3);
lean_inc(x_2);
x_11 = l_Lean_Name_mkStr3(x_2, x_3, x_10);
lean_inc(x_9);
x_12 = l_Lean_Syntax_isOfKind(x_9, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_mk_string_unchecked("colonEqD", 8, 8);
lean_inc(x_3);
lean_inc(x_2);
x_14 = l_Lean_Name_mkStr3(x_2, x_3, x_13);
lean_inc(x_9);
x_15 = l_Lean_Syntax_isOfKind(x_9, x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_mk_string_unchecked("colonEqS", 8, 8);
lean_inc(x_3);
lean_inc(x_2);
x_17 = l_Lean_Name_mkStr3(x_2, x_3, x_16);
lean_inc(x_9);
x_18 = l_Lean_Syntax_isOfKind(x_9, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_mk_string_unchecked("colonEqA", 8, 8);
x_20 = l_Lean_Name_mkStr3(x_2, x_3, x_19);
x_21 = l_Lean_Syntax_isOfKind(x_9, x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_box(0);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_box(2);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; 
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
x_27 = lean_box(1);
x_28 = lean_alloc_ctor(1, 0, 1);
x_29 = lean_unbox(x_27);
lean_ctor_set_uint8(x_28, 0, x_29);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_28);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; 
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
x_31 = lean_box(2);
x_32 = lean_alloc_ctor(1, 0, 1);
x_33 = lean_unbox(x_31);
lean_ctor_set_uint8(x_32, 0, x_33);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_32);
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("equal", 5, 5);
lean_inc(x_3);
lean_inc(x_2);
x_5 = l_Lean_Name_mkStr3(x_2, x_3, x_4);
lean_inc(x_1);
x_6 = l_Lean_Syntax_isOfKind(x_1, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(0);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
lean_dec(x_1);
x_10 = lean_mk_string_unchecked("equalR", 6, 6);
lean_inc(x_3);
lean_inc(x_2);
x_11 = l_Lean_Name_mkStr3(x_2, x_3, x_10);
lean_inc(x_9);
x_12 = l_Lean_Syntax_isOfKind(x_9, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_mk_string_unchecked("equalD", 6, 6);
lean_inc(x_3);
lean_inc(x_2);
x_14 = l_Lean_Name_mkStr3(x_2, x_3, x_13);
lean_inc(x_9);
x_15 = l_Lean_Syntax_isOfKind(x_9, x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_mk_string_unchecked("equalS", 6, 6);
lean_inc(x_3);
lean_inc(x_2);
x_17 = l_Lean_Name_mkStr3(x_2, x_3, x_16);
lean_inc(x_9);
x_18 = l_Lean_Syntax_isOfKind(x_9, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_mk_string_unchecked("equalA", 6, 6);
x_20 = l_Lean_Name_mkStr3(x_2, x_3, x_19);
x_21 = l_Lean_Syntax_isOfKind(x_9, x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_box(0);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_box(2);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; 
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
x_27 = lean_box(1);
x_28 = lean_alloc_ctor(1, 0, 1);
x_29 = lean_unbox(x_27);
lean_ctor_set_uint8(x_28, 0, x_29);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_28);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; 
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
x_31 = lean_box(2);
x_32 = lean_alloc_ctor(1, 0, 1);
x_33 = lean_unbox(x_31);
lean_ctor_set_uint8(x_32, 0, x_33);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_32);
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_MatchKind_isEq___lam__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_45 = l_Lean_Meta_isExprDefEqGuarded(x_2, x_3, x_44, x_5, x_6, x_7, x_8);
lean_dec(x_44);
return x_45;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_MatchKind_isEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_9 = l_Lean_Expr_consumeMData(x_1);
lean_dec(x_1);
x_10 = l_Lean_Expr_consumeMData(x_2);
lean_dec(x_2);
x_11 = lean_expr_eqv(x_9, x_10);
lean_dec(x_10);
lean_dec(x_9);
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_8);
return x_13;
}
case 1:
{
uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get_uint8(x_3, 0);
x_15 = lean_box(x_14);
x_16 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardExpr_MatchKind_isEq___lam__0___boxed), 8, 3);
lean_closure_set(x_16, 0, x_15);
lean_closure_set(x_16, 1, x_1);
lean_closure_set(x_16, 2, x_2);
x_17 = l_Lean_withoutModifyingState___at___Lean_Meta_addPPExplicitToExposeDiff_spec__0___redArg(x_16, x_4, x_5, x_6, x_7, x_8);
return x_17;
}
default: 
{
uint8_t x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_18 = lean_expr_eqv(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_19 = lean_box(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_8);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_MatchKind_isEq___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
lean_dec(x_1);
x_10 = l_Lean_Elab_Tactic_GuardExpr_MatchKind_isEq___lam__0(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_MatchKind_isEq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Tactic_GuardExpr_MatchKind_isEq(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind___lam__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_inc(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_2);
x_13 = l_Lean_Elab_Term_elabTerm(x_1, x_2, x_3, x_3, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_16 = l_Lean_Elab_Term_elabTerm(x_4, x_2, x_3, x_3, x_6, x_7, x_8, x_9, x_10, x_11, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_14);
x_19 = lean_infer_type(x_14, x_8, x_9, x_10, x_11, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_17);
x_22 = lean_infer_type(x_17, x_8, x_9, x_10, x_11, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_25 = l_Lean_Meta_isExprDefEqGuarded(x_20, x_23, x_8, x_9, x_10, x_11, x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_box(0);
x_28 = lean_unbox(x_27);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_29 = l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(x_28, x_6, x_7, x_8, x_9, x_10, x_11, x_26);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = l_Lean_instantiateMVars___at___Lean_Elab_Term_MVarErrorInfo_logError_spec__0___redArg(x_14, x_9, x_30);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_Lean_instantiateMVars___at___Lean_Elab_Term_MVarErrorInfo_logError_spec__0___redArg(x_17, x_9, x_33);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l_Lean_Elab_Tactic_GuardExpr_MatchKind_isEq(x_32, x_35, x_5, x_8, x_9, x_10, x_11, x_36);
return x_37;
}
else
{
uint8_t x_38; 
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_38 = !lean_is_exclusive(x_29);
if (x_38 == 0)
{
return x_29;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_29, 0);
x_40 = lean_ctor_get(x_29, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_29);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_25;
}
}
else
{
uint8_t x_42; 
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_42 = !lean_is_exclusive(x_22);
if (x_42 == 0)
{
return x_22;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_22, 0);
x_44 = lean_ctor_get(x_22, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_22);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_46 = !lean_is_exclusive(x_19);
if (x_46 == 0)
{
return x_19;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_19, 0);
x_48 = lean_ctor_get(x_19, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_19);
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
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
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
else
{
uint8_t x_54; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_54 = !lean_is_exclusive(x_13);
if (x_54 == 0)
{
return x_13;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_13, 0);
x_56 = lean_ctor_get(x_13, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_13);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_box(0);
x_12 = lean_box(1);
x_13 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind___lam__0___boxed), 12, 5);
lean_closure_set(x_13, 0, x_2);
lean_closure_set(x_13, 1, x_11);
lean_closure_set(x_13, 2, x_12);
lean_closure_set(x_13, 3, x_3);
lean_closure_set(x_13, 4, x_1);
x_14 = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Term_withoutErrToSorry___at___Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_withoutErrToSorry___at___Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_3);
lean_dec(x_3);
x_14 = l_Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind___lam__0(x_1, x_2, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_5);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_16; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_16 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
lean_dec(x_1);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_18 = l_Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind(x_17, x_2, x_3, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_unbox(x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_mk_string_unchecked("failed: ", 8, 8);
x_23 = l_Lean_stringToMessageData(x_22);
lean_dec(x_22);
x_24 = l_Lean_MessageData_ofSyntax(x_4);
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_mk_string_unchecked("", 0, 0);
x_27 = l_Lean_stringToMessageData(x_26);
lean_dec(x_26);
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_MessageData_ofSyntax(x_5);
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_mk_string_unchecked(" ", 1, 1);
x_32 = l_Lean_stringToMessageData(x_31);
lean_dec(x_31);
x_33 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_32);
x_34 = l_Lean_MessageData_ofSyntax(x_6);
x_35 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_mk_string_unchecked(" is not true", 12, 12);
x_37 = l_Lean_stringToMessageData(x_36);
lean_dec(x_36);
x_38 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_37);
x_39 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___redArg(x_38, x_11, x_12, x_13, x_14, x_21);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
return x_39;
}
else
{
uint8_t x_40; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_40 = !lean_is_exclusive(x_18);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_18, 0);
lean_dec(x_41);
x_42 = lean_box(0);
lean_ctor_set(x_18, 0, x_42);
return x_18;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_18, 1);
lean_inc(x_43);
lean_dec(x_18);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_46 = !lean_is_exclusive(x_18);
if (x_46 == 0)
{
return x_18;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_18, 0);
x_48 = lean_ctor_get(x_18, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_18);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_mk_string_unchecked("Lean", 4, 4);
x_12 = lean_mk_string_unchecked("Parser", 6, 6);
x_13 = lean_mk_string_unchecked("Tactic", 6, 6);
x_14 = lean_mk_string_unchecked("guardExpr", 9, 9);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_15 = l_Lean_Name_mkStr4(x_11, x_12, x_13, x_14);
lean_inc(x_1);
x_16 = l_Lean_Syntax_isOfKind(x_1, x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_mk_string_unchecked("guardExprConv", 13, 13);
lean_inc(x_12);
lean_inc(x_11);
x_18 = l_Lean_Name_mkStr4(x_11, x_12, x_13, x_17);
lean_inc(x_1);
x_19 = l_Lean_Syntax_isOfKind(x_1, x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_20 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_10);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_21 = lean_unsigned_to_nat(2u);
x_22 = l_Lean_Syntax_getArg(x_1, x_21);
x_23 = lean_mk_string_unchecked("equal", 5, 5);
x_24 = l_Lean_Name_mkStr3(x_11, x_12, x_23);
lean_inc(x_22);
x_25 = l_Lean_Syntax_isOfKind(x_22, x_24);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_26 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_10);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_27 = lean_unsigned_to_nat(1u);
x_28 = l_Lean_Syntax_getArg(x_1, x_27);
x_29 = lean_unsigned_to_nat(3u);
x_30 = l_Lean_Syntax_getArg(x_1, x_29);
lean_dec(x_1);
lean_inc(x_22);
x_31 = l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind(x_22);
lean_inc(x_30);
lean_inc(x_28);
x_32 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___boxed), 15, 6);
lean_closure_set(x_32, 0, x_31);
lean_closure_set(x_32, 1, x_28);
lean_closure_set(x_32, 2, x_30);
lean_closure_set(x_32, 3, x_28);
lean_closure_set(x_32, 4, x_22);
lean_closure_set(x_32, 5, x_30);
x_33 = l_Lean_Elab_Tactic_withMainContext___redArg(x_32, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_33;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
lean_dec(x_13);
x_34 = lean_unsigned_to_nat(2u);
x_35 = l_Lean_Syntax_getArg(x_1, x_34);
x_36 = lean_mk_string_unchecked("equal", 5, 5);
x_37 = l_Lean_Name_mkStr3(x_11, x_12, x_36);
lean_inc(x_35);
x_38 = l_Lean_Syntax_isOfKind(x_35, x_37);
lean_dec(x_37);
if (x_38 == 0)
{
lean_object* x_39; 
lean_dec(x_35);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_39 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_10);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_40 = lean_unsigned_to_nat(1u);
x_41 = l_Lean_Syntax_getArg(x_1, x_40);
x_42 = lean_unsigned_to_nat(3u);
x_43 = l_Lean_Syntax_getArg(x_1, x_42);
lean_dec(x_1);
lean_inc(x_35);
x_44 = l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind(x_35);
lean_inc(x_43);
lean_inc(x_41);
x_45 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___boxed), 15, 6);
lean_closure_set(x_45, 0, x_44);
lean_closure_set(x_45, 1, x_41);
lean_closure_set(x_45, 2, x_43);
lean_closure_set(x_45, 3, x_41);
lean_closure_set(x_45, 4, x_35);
lean_closure_set(x_45, 5, x_43);
x_46 = l_Lean_Elab_Tactic_withMainContext___redArg(x_45, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_46;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
return x_11;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Tactic", 6, 6);
x_6 = lean_mk_string_unchecked("guardExpr", 9, 9);
lean_inc(x_5);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("Elab", 4, 4);
x_9 = lean_mk_string_unchecked("GuardExpr", 9, 9);
x_10 = lean_mk_string_unchecked("evalGuardExpr", 13, 13);
x_11 = l_Lean_Name_mkStr5(x_3, x_8, x_5, x_9, x_10);
x_12 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___boxed), 10, 0);
x_13 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_11, x_12, x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Elab", 4, 4);
x_4 = lean_mk_string_unchecked("Tactic", 6, 6);
x_5 = lean_mk_string_unchecked("GuardExpr", 9, 9);
x_6 = lean_mk_string_unchecked("evalGuardExpr", 13, 13);
x_7 = l_Lean_Name_mkStr5(x_2, x_3, x_4, x_5, x_6);
x_8 = lean_unsigned_to_nat(75u);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_unsigned_to_nat(82u);
x_12 = lean_unsigned_to_nat(31u);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_9);
lean_ctor_set(x_14, 2, x_13);
lean_ctor_set(x_14, 3, x_12);
x_15 = lean_unsigned_to_nat(4u);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_8);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_unsigned_to_nat(17u);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_8);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_15);
lean_ctor_set(x_19, 2, x_18);
lean_ctor_set(x_19, 3, x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_14);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_addBuiltinDeclarationRanges(x_7, x_20, x_1);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
return x_11;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv__1___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_2 = lean_alloc_closure((void*)(l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv__1___lam__0___boxed), 10, 0);
x_3 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Tactic", 6, 6);
x_7 = lean_mk_string_unchecked("guardExprConv", 13, 13);
lean_inc(x_6);
lean_inc(x_4);
x_8 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_7);
x_9 = lean_mk_string_unchecked("Elab", 4, 4);
x_10 = lean_mk_string_unchecked("GuardExpr", 9, 9);
x_11 = lean_mk_string_unchecked("evalGuardExprConv", 17, 17);
x_12 = l_Lean_Name_mkStr5(x_4, x_9, x_6, x_10, x_11);
x_13 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_3, x_8, x_12, x_2, x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv__1___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv__1___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
return x_11;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Elab", 4, 4);
x_4 = lean_mk_string_unchecked("Tactic", 6, 6);
x_5 = lean_mk_string_unchecked("GuardExpr", 9, 9);
x_6 = lean_mk_string_unchecked("evalGuardExprConv", 17, 17);
x_7 = l_Lean_Name_mkStr5(x_2, x_3, x_4, x_5, x_6);
x_8 = lean_unsigned_to_nat(86u);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_unsigned_to_nat(47u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_9);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_11);
x_14 = lean_unsigned_to_nat(4u);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_unsigned_to_nat(21u);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_8);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_14);
lean_ctor_set(x_18, 2, x_17);
lean_ctor_set(x_18, 3, x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_addBuiltinDeclarationRanges(x_7, x_19, x_1);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_68; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_68 = lean_apply_9(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = l_Lean_instantiateMVars___at___Lean_Elab_Tactic_getMainTarget_spec__0___redArg(x_69, x_9, x_70);
x_13 = x_71;
goto block_67;
}
else
{
x_13 = x_68;
goto block_67;
}
block_67:
{
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_14);
x_16 = lean_infer_type(x_14, x_8, x_9, x_10, x_11, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_17);
x_20 = lean_box(0);
x_21 = lean_unbox(x_20);
lean_inc(x_11);
lean_inc(x_9);
lean_inc(x_8);
x_22 = l_Lean_Elab_Tactic_elabTerm(x_1, x_19, x_21, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_18);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind(x_2);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
lean_dec(x_23);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_26 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_24);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
lean_dec(x_25);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_14);
lean_inc(x_23);
x_28 = l_Lean_Elab_Tactic_GuardExpr_MatchKind_isEq(x_23, x_14, x_27, x_8, x_9, x_10, x_11, x_24);
lean_dec(x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_unbox(x_29);
lean_dec(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = lean_mk_string_unchecked("target of main goal is", 22, 22);
x_33 = l_Lean_stringToMessageData(x_32);
lean_dec(x_32);
x_34 = l_Lean_indentExpr(x_14);
x_35 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_mk_string_unchecked("\nnot", 4, 4);
x_37 = l_Lean_stringToMessageData(x_36);
lean_dec(x_36);
x_38 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_37);
x_39 = l_Lean_indentExpr(x_23);
x_40 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_mk_string_unchecked("", 0, 0);
x_42 = l_Lean_stringToMessageData(x_41);
lean_dec(x_41);
x_43 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_43, 0, x_40);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___redArg(x_43, x_8, x_9, x_10, x_11, x_31);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_44;
}
else
{
uint8_t x_45; 
lean_dec(x_23);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_45 = !lean_is_exclusive(x_28);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_28, 0);
lean_dec(x_46);
x_47 = lean_box(0);
lean_ctor_set(x_28, 0, x_47);
return x_28;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_28, 1);
lean_inc(x_48);
lean_dec(x_28);
x_49 = lean_box(0);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_23);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_51 = !lean_is_exclusive(x_28);
if (x_51 == 0)
{
return x_28;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_28, 0);
x_53 = lean_ctor_get(x_28, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_28);
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
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_55 = !lean_is_exclusive(x_22);
if (x_55 == 0)
{
return x_22;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_22, 0);
x_57 = lean_ctor_get(x_22, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_22);
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
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_59 = !lean_is_exclusive(x_16);
if (x_59 == 0)
{
return x_16;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_16, 0);
x_61 = lean_ctor_get(x_16, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_16);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
else
{
uint8_t x_63; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_63 = !lean_is_exclusive(x_13);
if (x_63 == 0)
{
return x_13;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_13, 0);
x_65 = lean_ctor_get(x_13, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_13);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_26 = lean_mk_string_unchecked("Lean", 4, 4);
x_27 = lean_mk_string_unchecked("Parser", 6, 6);
x_28 = lean_mk_string_unchecked("Tactic", 6, 6);
x_29 = lean_mk_string_unchecked("guardTarget", 11, 11);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
x_30 = l_Lean_Name_mkStr4(x_26, x_27, x_28, x_29);
lean_inc(x_1);
x_31 = l_Lean_Syntax_isOfKind(x_1, x_30);
lean_dec(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = lean_mk_string_unchecked("guardTargetConv", 15, 15);
x_33 = l_Lean_Name_mkStr4(x_26, x_27, x_28, x_32);
lean_inc(x_1);
x_34 = l_Lean_Syntax_isOfKind(x_1, x_33);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_35 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_10);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_36 = lean_unsigned_to_nat(1u);
x_37 = lean_unsigned_to_nat(2u);
x_38 = l_Lean_Syntax_getArg(x_1, x_37);
x_39 = l_Lean_Syntax_getArg(x_1, x_36);
lean_dec(x_1);
x_40 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_getLhs___boxed), 9, 0);
x_11 = x_39;
x_12 = x_38;
x_13 = x_40;
x_14 = x_2;
x_15 = x_3;
x_16 = x_4;
x_17 = x_5;
x_18 = x_6;
x_19 = x_7;
x_20 = x_8;
x_21 = x_9;
x_22 = x_10;
goto block_25;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
x_41 = lean_unsigned_to_nat(1u);
x_42 = lean_unsigned_to_nat(2u);
x_43 = l_Lean_Syntax_getArg(x_1, x_42);
x_44 = l_Lean_Syntax_getArg(x_1, x_41);
lean_dec(x_1);
x_45 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_getMainTarget___boxed), 9, 0);
x_11 = x_44;
x_12 = x_43;
x_13 = x_45;
x_14 = x_2;
x_15 = x_3;
x_16 = x_4;
x_17 = x_5;
x_18 = x_6;
x_19 = x_7;
x_20 = x_8;
x_21 = x_9;
x_22 = x_10;
goto block_25;
}
block_25:
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lam__0), 12, 3);
lean_closure_set(x_23, 0, x_12);
lean_closure_set(x_23, 1, x_11);
lean_closure_set(x_23, 2, x_13);
x_24 = l_Lean_Elab_Tactic_withMainContext___redArg(x_23, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
return x_11;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Tactic", 6, 6);
x_6 = lean_mk_string_unchecked("guardTarget", 11, 11);
lean_inc(x_5);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("Elab", 4, 4);
x_9 = lean_mk_string_unchecked("GuardExpr", 9, 9);
x_10 = lean_mk_string_unchecked("evalGuardTarget", 15, 15);
x_11 = l_Lean_Name_mkStr5(x_3, x_8, x_5, x_9, x_10);
x_12 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___boxed), 10, 0);
x_13 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_11, x_12, x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Elab", 4, 4);
x_4 = lean_mk_string_unchecked("Tactic", 6, 6);
x_5 = lean_mk_string_unchecked("GuardExpr", 9, 9);
x_6 = lean_mk_string_unchecked("evalGuardTarget", 15, 15);
x_7 = l_Lean_Name_mkStr5(x_2, x_3, x_4, x_5, x_6);
x_8 = lean_unsigned_to_nat(89u);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_unsigned_to_nat(99u);
x_12 = lean_unsigned_to_nat(31u);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_9);
lean_ctor_set(x_14, 2, x_13);
lean_ctor_set(x_14, 3, x_12);
x_15 = lean_unsigned_to_nat(4u);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_8);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_unsigned_to_nat(19u);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_8);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_15);
lean_ctor_set(x_19, 2, x_18);
lean_ctor_set(x_19, 3, x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_14);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_addBuiltinDeclarationRanges(x_7, x_20, x_1);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
return x_11;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv__1___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_2 = lean_alloc_closure((void*)(l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv__1___lam__0___boxed), 10, 0);
x_3 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Tactic", 6, 6);
x_7 = lean_mk_string_unchecked("guardTargetConv", 15, 15);
lean_inc(x_6);
lean_inc(x_4);
x_8 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_7);
x_9 = lean_mk_string_unchecked("Elab", 4, 4);
x_10 = lean_mk_string_unchecked("GuardExpr", 9, 9);
x_11 = lean_mk_string_unchecked("evalGuardTargetConv", 19, 19);
x_12 = l_Lean_Name_mkStr5(x_4, x_9, x_6, x_10, x_11);
x_13 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_3, x_8, x_12, x_2, x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv__1___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv__1___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
return x_11;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Elab", 4, 4);
x_4 = lean_mk_string_unchecked("Tactic", 6, 6);
x_5 = lean_mk_string_unchecked("GuardExpr", 9, 9);
x_6 = lean_mk_string_unchecked("evalGuardTargetConv", 19, 19);
x_7 = l_Lean_Name_mkStr5(x_2, x_3, x_4, x_5, x_6);
x_8 = lean_unsigned_to_nat(103u);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_unsigned_to_nat(51u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_9);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_11);
x_14 = lean_unsigned_to_nat(4u);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_unsigned_to_nat(23u);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_8);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_14);
lean_ctor_set(x_18, 2, x_17);
lean_ctor_set(x_18, 3, x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_addBuiltinDeclarationRanges(x_7, x_19, x_1);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_LocalDecl_value_x3f(x_1);
if (lean_obj_tag(x_16) == 0)
{
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_3);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_15);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_2);
x_19 = lean_mk_string_unchecked("", 0, 0);
x_20 = l_Lean_stringToMessageData(x_19);
lean_dec(x_19);
x_21 = l_Lean_MessageData_ofSyntax(x_3);
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_mk_string_unchecked(" is not a let binding", 21, 21);
x_24 = l_Lean_stringToMessageData(x_23);
lean_dec(x_23);
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___redArg(x_25, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
return x_26;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_1);
x_27 = lean_mk_string_unchecked("", 0, 0);
x_28 = l_Lean_stringToMessageData(x_27);
lean_dec(x_27);
x_29 = l_Lean_MessageData_ofSyntax(x_3);
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_mk_string_unchecked(" is a let binding", 17, 17);
x_32 = l_Lean_stringToMessageData(x_31);
lean_dec(x_31);
x_33 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_32);
x_34 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___redArg(x_33, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
return x_34;
}
else
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_35; 
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_35 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_15);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_16, 0);
lean_inc(x_36);
lean_dec(x_16);
x_37 = lean_ctor_get(x_2, 0);
lean_inc(x_37);
lean_dec(x_2);
x_38 = lean_ctor_get(x_4, 0);
lean_inc(x_38);
lean_dec(x_4);
x_39 = l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind(x_38);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; 
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_40 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_15);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_120; 
x_41 = lean_ctor_get(x_39, 0);
lean_inc(x_41);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 x_42 = x_39;
} else {
 lean_dec_ref(x_39);
 x_42 = lean_box(0);
}
x_120 = lean_ctor_get(x_1, 3);
lean_inc(x_120);
lean_dec(x_1);
x_43 = x_120;
goto block_119;
block_119:
{
lean_object* x_44; lean_object* x_45; 
if (lean_is_scalar(x_42)) {
 x_44 = lean_alloc_ctor(1, 1, 0);
} else {
 x_44 = x_42;
}
lean_ctor_set(x_44, 0, x_43);
lean_inc(x_14);
lean_inc(x_12);
lean_inc(x_11);
x_45 = l_Lean_Elab_Tactic_elabTerm(x_37, x_44, x_5, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = l_Lean_instantiateMVars___at___Lean_Elab_Tactic_getMainTarget_spec__0___redArg(x_36, x_12, x_47);
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_48, 0);
x_51 = lean_ctor_get(x_48, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_50);
lean_inc(x_46);
x_52 = l_Lean_Elab_Tactic_GuardExpr_MatchKind_isEq(x_46, x_50, x_41, x_11, x_12, x_13, x_14, x_51);
lean_dec(x_41);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; uint8_t x_54; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_unbox(x_53);
lean_dec(x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
lean_dec(x_52);
x_56 = lean_mk_string_unchecked("hypothesis ", 11, 11);
x_57 = l_Lean_stringToMessageData(x_56);
lean_dec(x_56);
x_58 = l_Lean_MessageData_ofSyntax(x_3);
lean_ctor_set_tag(x_48, 7);
lean_ctor_set(x_48, 1, x_58);
lean_ctor_set(x_48, 0, x_57);
x_59 = lean_mk_string_unchecked(" has value", 10, 10);
x_60 = l_Lean_stringToMessageData(x_59);
lean_dec(x_59);
x_61 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_61, 0, x_48);
lean_ctor_set(x_61, 1, x_60);
x_62 = l_Lean_indentExpr(x_50);
x_63 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
x_64 = lean_mk_string_unchecked("\nnot", 4, 4);
x_65 = l_Lean_stringToMessageData(x_64);
lean_dec(x_64);
x_66 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_65);
x_67 = l_Lean_indentExpr(x_46);
x_68 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
x_69 = lean_mk_string_unchecked("", 0, 0);
x_70 = l_Lean_stringToMessageData(x_69);
lean_dec(x_69);
x_71 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_71, 0, x_68);
lean_ctor_set(x_71, 1, x_70);
x_72 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___redArg(x_71, x_11, x_12, x_13, x_14, x_55);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
return x_72;
}
else
{
uint8_t x_73; 
lean_free_object(x_48);
lean_dec(x_50);
lean_dec(x_46);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_3);
x_73 = !lean_is_exclusive(x_52);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_52, 0);
lean_dec(x_74);
x_75 = lean_box(0);
lean_ctor_set(x_52, 0, x_75);
return x_52;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_52, 1);
lean_inc(x_76);
lean_dec(x_52);
x_77 = lean_box(0);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
}
}
else
{
uint8_t x_79; 
lean_free_object(x_48);
lean_dec(x_50);
lean_dec(x_46);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_3);
x_79 = !lean_is_exclusive(x_52);
if (x_79 == 0)
{
return x_52;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_52, 0);
x_81 = lean_ctor_get(x_52, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_52);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_48, 0);
x_84 = lean_ctor_get(x_48, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_48);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_83);
lean_inc(x_46);
x_85 = l_Lean_Elab_Tactic_GuardExpr_MatchKind_isEq(x_46, x_83, x_41, x_11, x_12, x_13, x_14, x_84);
lean_dec(x_41);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; uint8_t x_87; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_unbox(x_86);
lean_dec(x_86);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_88 = lean_ctor_get(x_85, 1);
lean_inc(x_88);
lean_dec(x_85);
x_89 = lean_mk_string_unchecked("hypothesis ", 11, 11);
x_90 = l_Lean_stringToMessageData(x_89);
lean_dec(x_89);
x_91 = l_Lean_MessageData_ofSyntax(x_3);
x_92 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
x_93 = lean_mk_string_unchecked(" has value", 10, 10);
x_94 = l_Lean_stringToMessageData(x_93);
lean_dec(x_93);
x_95 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_95, 0, x_92);
lean_ctor_set(x_95, 1, x_94);
x_96 = l_Lean_indentExpr(x_83);
x_97 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
x_98 = lean_mk_string_unchecked("\nnot", 4, 4);
x_99 = l_Lean_stringToMessageData(x_98);
lean_dec(x_98);
x_100 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_100, 0, x_97);
lean_ctor_set(x_100, 1, x_99);
x_101 = l_Lean_indentExpr(x_46);
x_102 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
x_103 = lean_mk_string_unchecked("", 0, 0);
x_104 = l_Lean_stringToMessageData(x_103);
lean_dec(x_103);
x_105 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_105, 0, x_102);
lean_ctor_set(x_105, 1, x_104);
x_106 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___redArg(x_105, x_11, x_12, x_13, x_14, x_88);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
return x_106;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_dec(x_83);
lean_dec(x_46);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_3);
x_107 = lean_ctor_get(x_85, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_108 = x_85;
} else {
 lean_dec_ref(x_85);
 x_108 = lean_box(0);
}
x_109 = lean_box(0);
if (lean_is_scalar(x_108)) {
 x_110 = lean_alloc_ctor(0, 2, 0);
} else {
 x_110 = x_108;
}
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_107);
return x_110;
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
lean_dec(x_83);
lean_dec(x_46);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_3);
x_111 = lean_ctor_get(x_85, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_85, 1);
lean_inc(x_112);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_113 = x_85;
} else {
 lean_dec_ref(x_85);
 x_113 = lean_box(0);
}
if (lean_is_scalar(x_113)) {
 x_114 = lean_alloc_ctor(1, 2, 0);
} else {
 x_114 = x_113;
}
lean_ctor_set(x_114, 0, x_111);
lean_ctor_set(x_114, 1, x_112);
return x_114;
}
}
}
else
{
uint8_t x_115; 
lean_dec(x_41);
lean_dec(x_36);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_3);
x_115 = !lean_is_exclusive(x_45);
if (x_115 == 0)
{
return x_45;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_45, 0);
x_117 = lean_ctor_get(x_45, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_45);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
return x_118;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_106; 
lean_inc(x_14);
lean_inc(x_12);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_106 = l_Lean_Elab_Tactic_getFVarId(x_1, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec(x_106);
x_109 = lean_ctor_get(x_11, 2);
lean_inc(x_109);
x_110 = lean_local_ctx_find(x_109, x_107);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_111 = lean_mk_string_unchecked("hypothesis ", 11, 11);
x_112 = l_Lean_stringToMessageData(x_111);
lean_dec(x_111);
x_113 = l_Lean_MessageData_ofSyntax(x_1);
x_114 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
x_115 = lean_mk_string_unchecked(" not found", 10, 10);
x_116 = l_Lean_stringToMessageData(x_115);
lean_dec(x_115);
x_117 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_117, 0, x_114);
lean_ctor_set(x_117, 1, x_116);
x_118 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___redArg(x_117, x_11, x_12, x_13, x_14, x_108);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_119 = !lean_is_exclusive(x_118);
if (x_119 == 0)
{
return x_118;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_118, 0);
x_121 = lean_ctor_get(x_118, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_118);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_ctor_get(x_110, 0);
lean_inc(x_123);
lean_dec(x_110);
x_124 = lean_box(x_4);
lean_inc(x_1);
lean_inc(x_123);
x_125 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___boxed), 15, 5);
lean_closure_set(x_125, 0, x_123);
lean_closure_set(x_125, 1, x_2);
lean_closure_set(x_125, 2, x_1);
lean_closure_set(x_125, 3, x_3);
lean_closure_set(x_125, 4, x_124);
if (lean_obj_tag(x_5) == 0)
{
lean_dec(x_123);
lean_dec(x_6);
lean_dec(x_1);
x_93 = x_125;
x_94 = x_7;
x_95 = x_8;
x_96 = x_9;
x_97 = x_10;
x_98 = x_11;
x_99 = x_12;
x_100 = x_13;
x_101 = x_14;
x_102 = x_108;
goto block_105;
}
else
{
if (lean_obj_tag(x_6) == 0)
{
lean_dec(x_123);
lean_dec(x_5);
lean_dec(x_1);
x_93 = x_125;
x_94 = x_7;
x_95 = x_8;
x_96 = x_9;
x_97 = x_10;
x_98 = x_11;
x_99 = x_12;
x_100 = x_13;
x_101 = x_14;
x_102 = x_108;
goto block_105;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_5, 0);
lean_inc(x_126);
lean_dec(x_5);
x_127 = lean_ctor_get(x_6, 0);
lean_inc(x_127);
lean_dec(x_6);
x_128 = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind(x_126);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; 
lean_dec(x_127);
lean_dec(x_125);
lean_dec(x_123);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_129 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_108);
return x_129;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_128, 0);
lean_inc(x_130);
lean_dec(x_128);
x_131 = lean_box(0);
lean_inc(x_14);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_132 = l_Lean_Elab_Tactic_elabTerm(x_127, x_131, x_4, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_108);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
lean_dec(x_132);
x_135 = lean_ctor_get(x_123, 3);
lean_inc(x_135);
lean_dec(x_123);
x_16 = x_9;
x_17 = x_13;
x_18 = x_10;
x_19 = x_125;
x_20 = x_134;
x_21 = x_14;
x_22 = x_133;
x_23 = x_130;
x_24 = x_11;
x_25 = x_8;
x_26 = x_7;
x_27 = x_12;
x_28 = x_135;
goto block_92;
}
else
{
uint8_t x_136; 
lean_dec(x_130);
lean_dec(x_125);
lean_dec(x_123);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_136 = !lean_is_exclusive(x_132);
if (x_136 == 0)
{
return x_132;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_137 = lean_ctor_get(x_132, 0);
x_138 = lean_ctor_get(x_132, 1);
lean_inc(x_138);
lean_inc(x_137);
lean_dec(x_132);
x_139 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_139, 0, x_137);
lean_ctor_set(x_139, 1, x_138);
return x_139;
}
}
}
}
}
}
}
else
{
uint8_t x_140; 
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
lean_dec(x_2);
lean_dec(x_1);
x_140 = !lean_is_exclusive(x_106);
if (x_140 == 0)
{
return x_106;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_ctor_get(x_106, 0);
x_142 = lean_ctor_get(x_106, 1);
lean_inc(x_142);
lean_inc(x_141);
lean_dec(x_106);
x_143 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_142);
return x_143;
}
}
block_92:
{
lean_object* x_29; uint8_t x_30; 
x_29 = l_Lean_instantiateMVars___at___Lean_Elab_Tactic_getMainTarget_spec__0___redArg(x_28, x_27, x_20);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_21);
lean_inc(x_17);
lean_inc(x_27);
lean_inc(x_24);
lean_inc(x_31);
lean_inc(x_22);
x_33 = l_Lean_Elab_Tactic_GuardExpr_MatchKind_isEq(x_22, x_31, x_23, x_24, x_27, x_17, x_21, x_32);
lean_dec(x_23);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_unbox(x_34);
lean_dec(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_16);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = lean_mk_string_unchecked("hypothesis ", 11, 11);
x_38 = l_Lean_stringToMessageData(x_37);
lean_dec(x_37);
x_39 = l_Lean_MessageData_ofSyntax(x_1);
lean_ctor_set_tag(x_29, 7);
lean_ctor_set(x_29, 1, x_39);
lean_ctor_set(x_29, 0, x_38);
x_40 = lean_mk_string_unchecked(" has type", 9, 9);
x_41 = l_Lean_stringToMessageData(x_40);
lean_dec(x_40);
x_42 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_42, 0, x_29);
lean_ctor_set(x_42, 1, x_41);
x_43 = l_Lean_indentExpr(x_31);
x_44 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_mk_string_unchecked("\nnot", 4, 4);
x_46 = l_Lean_stringToMessageData(x_45);
lean_dec(x_45);
x_47 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_47, 0, x_44);
lean_ctor_set(x_47, 1, x_46);
x_48 = l_Lean_indentExpr(x_22);
x_49 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_mk_string_unchecked("", 0, 0);
x_51 = l_Lean_stringToMessageData(x_50);
lean_dec(x_50);
x_52 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_52, 0, x_49);
lean_ctor_set(x_52, 1, x_51);
x_53 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___redArg(x_52, x_24, x_27, x_17, x_21, x_36);
lean_dec(x_21);
lean_dec(x_17);
lean_dec(x_27);
lean_dec(x_24);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_free_object(x_29);
lean_dec(x_31);
lean_dec(x_22);
lean_dec(x_1);
x_54 = lean_ctor_get(x_33, 1);
lean_inc(x_54);
lean_dec(x_33);
x_55 = lean_box(0);
x_56 = lean_apply_10(x_19, x_55, x_26, x_25, x_16, x_18, x_24, x_27, x_17, x_21, x_54);
return x_56;
}
}
else
{
uint8_t x_57; 
lean_free_object(x_29);
lean_dec(x_31);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_1);
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
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_29, 0);
x_62 = lean_ctor_get(x_29, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_29);
lean_inc(x_21);
lean_inc(x_17);
lean_inc(x_27);
lean_inc(x_24);
lean_inc(x_61);
lean_inc(x_22);
x_63 = l_Lean_Elab_Tactic_GuardExpr_MatchKind_isEq(x_22, x_61, x_23, x_24, x_27, x_17, x_21, x_62);
lean_dec(x_23);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; uint8_t x_65; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_unbox(x_64);
lean_dec(x_64);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_16);
x_66 = lean_ctor_get(x_63, 1);
lean_inc(x_66);
lean_dec(x_63);
x_67 = lean_mk_string_unchecked("hypothesis ", 11, 11);
x_68 = l_Lean_stringToMessageData(x_67);
lean_dec(x_67);
x_69 = l_Lean_MessageData_ofSyntax(x_1);
x_70 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
x_71 = lean_mk_string_unchecked(" has type", 9, 9);
x_72 = l_Lean_stringToMessageData(x_71);
lean_dec(x_71);
x_73 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_73, 0, x_70);
lean_ctor_set(x_73, 1, x_72);
x_74 = l_Lean_indentExpr(x_61);
x_75 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
x_76 = lean_mk_string_unchecked("\nnot", 4, 4);
x_77 = l_Lean_stringToMessageData(x_76);
lean_dec(x_76);
x_78 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_78, 0, x_75);
lean_ctor_set(x_78, 1, x_77);
x_79 = l_Lean_indentExpr(x_22);
x_80 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
x_81 = lean_mk_string_unchecked("", 0, 0);
x_82 = l_Lean_stringToMessageData(x_81);
lean_dec(x_81);
x_83 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_83, 0, x_80);
lean_ctor_set(x_83, 1, x_82);
x_84 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___redArg(x_83, x_24, x_27, x_17, x_21, x_66);
lean_dec(x_21);
lean_dec(x_17);
lean_dec(x_27);
lean_dec(x_24);
return x_84;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_61);
lean_dec(x_22);
lean_dec(x_1);
x_85 = lean_ctor_get(x_63, 1);
lean_inc(x_85);
lean_dec(x_63);
x_86 = lean_box(0);
x_87 = lean_apply_10(x_19, x_86, x_26, x_25, x_16, x_18, x_24, x_27, x_17, x_21, x_85);
return x_87;
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_61);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_1);
x_88 = lean_ctor_get(x_63, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_63, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_90 = x_63;
} else {
 lean_dec_ref(x_63);
 x_90 = lean_box(0);
}
if (lean_is_scalar(x_90)) {
 x_91 = lean_alloc_ctor(1, 2, 0);
} else {
 x_91 = x_90;
}
lean_ctor_set(x_91, 0, x_88);
lean_ctor_set(x_91, 1, x_89);
return x_91;
}
}
}
block_105:
{
lean_object* x_103; lean_object* x_104; 
x_103 = lean_box(0);
x_104 = lean_apply_10(x_93, x_103, x_94, x_95, x_96, x_97, x_98, x_99, x_100, x_101, x_102);
return x_104;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_LocalDecl_value_x3f(x_1);
if (lean_obj_tag(x_15) == 0)
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_3);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_14);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_2);
x_18 = lean_mk_string_unchecked("", 0, 0);
x_19 = l_Lean_stringToMessageData(x_18);
lean_dec(x_18);
x_20 = l_Lean_MessageData_ofSyntax(x_3);
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_mk_string_unchecked(" is not a let binding", 21, 21);
x_23 = l_Lean_stringToMessageData(x_22);
lean_dec(x_22);
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___redArg(x_24, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_25;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_26 = lean_mk_string_unchecked("", 0, 0);
x_27 = l_Lean_stringToMessageData(x_26);
lean_dec(x_26);
x_28 = l_Lean_MessageData_ofSyntax(x_3);
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_mk_string_unchecked(" is a let binding", 17, 17);
x_31 = l_Lean_stringToMessageData(x_30);
lean_dec(x_30);
x_32 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___redArg(x_32, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_33;
}
else
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_34; 
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_34 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_14);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_15, 0);
lean_inc(x_35);
lean_dec(x_15);
x_36 = lean_ctor_get(x_2, 0);
lean_inc(x_36);
lean_dec(x_2);
x_37 = lean_ctor_get(x_4, 0);
lean_inc(x_37);
lean_dec(x_4);
x_38 = l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind(x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; 
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_39 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_14);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_121; 
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 x_41 = x_38;
} else {
 lean_dec_ref(x_38);
 x_41 = lean_box(0);
}
x_121 = lean_ctor_get(x_1, 3);
lean_inc(x_121);
lean_dec(x_1);
x_42 = x_121;
goto block_120;
block_120:
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; 
if (lean_is_scalar(x_41)) {
 x_43 = lean_alloc_ctor(1, 1, 0);
} else {
 x_43 = x_41;
}
lean_ctor_set(x_43, 0, x_42);
x_44 = lean_box(0);
x_45 = lean_unbox(x_44);
lean_inc(x_13);
lean_inc(x_11);
lean_inc(x_10);
x_46 = l_Lean_Elab_Tactic_elabTerm(x_36, x_43, x_45, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = l_Lean_instantiateMVars___at___Lean_Elab_Tactic_getMainTarget_spec__0___redArg(x_35, x_11, x_48);
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_49, 0);
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_51);
lean_inc(x_47);
x_53 = l_Lean_Elab_Tactic_GuardExpr_MatchKind_isEq(x_47, x_51, x_40, x_10, x_11, x_12, x_13, x_52);
lean_dec(x_40);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; uint8_t x_55; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_unbox(x_54);
lean_dec(x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_56 = lean_ctor_get(x_53, 1);
lean_inc(x_56);
lean_dec(x_53);
x_57 = lean_mk_string_unchecked("hypothesis ", 11, 11);
x_58 = l_Lean_stringToMessageData(x_57);
lean_dec(x_57);
x_59 = l_Lean_MessageData_ofSyntax(x_3);
lean_ctor_set_tag(x_49, 7);
lean_ctor_set(x_49, 1, x_59);
lean_ctor_set(x_49, 0, x_58);
x_60 = lean_mk_string_unchecked(" has value", 10, 10);
x_61 = l_Lean_stringToMessageData(x_60);
lean_dec(x_60);
x_62 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_62, 0, x_49);
lean_ctor_set(x_62, 1, x_61);
x_63 = l_Lean_indentExpr(x_51);
x_64 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
x_65 = lean_mk_string_unchecked("\nnot", 4, 4);
x_66 = l_Lean_stringToMessageData(x_65);
lean_dec(x_65);
x_67 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_67, 0, x_64);
lean_ctor_set(x_67, 1, x_66);
x_68 = l_Lean_indentExpr(x_47);
x_69 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_mk_string_unchecked("", 0, 0);
x_71 = l_Lean_stringToMessageData(x_70);
lean_dec(x_70);
x_72 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_72, 0, x_69);
lean_ctor_set(x_72, 1, x_71);
x_73 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___redArg(x_72, x_10, x_11, x_12, x_13, x_56);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_73;
}
else
{
uint8_t x_74; 
lean_free_object(x_49);
lean_dec(x_51);
lean_dec(x_47);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_3);
x_74 = !lean_is_exclusive(x_53);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_53, 0);
lean_dec(x_75);
x_76 = lean_box(0);
lean_ctor_set(x_53, 0, x_76);
return x_53;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_53, 1);
lean_inc(x_77);
lean_dec(x_53);
x_78 = lean_box(0);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_77);
return x_79;
}
}
}
else
{
uint8_t x_80; 
lean_free_object(x_49);
lean_dec(x_51);
lean_dec(x_47);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_3);
x_80 = !lean_is_exclusive(x_53);
if (x_80 == 0)
{
return x_53;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_53, 0);
x_82 = lean_ctor_get(x_53, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_53);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_49, 0);
x_85 = lean_ctor_get(x_49, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_49);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_84);
lean_inc(x_47);
x_86 = l_Lean_Elab_Tactic_GuardExpr_MatchKind_isEq(x_47, x_84, x_40, x_10, x_11, x_12, x_13, x_85);
lean_dec(x_40);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; uint8_t x_88; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_unbox(x_87);
lean_dec(x_87);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_89 = lean_ctor_get(x_86, 1);
lean_inc(x_89);
lean_dec(x_86);
x_90 = lean_mk_string_unchecked("hypothesis ", 11, 11);
x_91 = l_Lean_stringToMessageData(x_90);
lean_dec(x_90);
x_92 = l_Lean_MessageData_ofSyntax(x_3);
x_93 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
x_94 = lean_mk_string_unchecked(" has value", 10, 10);
x_95 = l_Lean_stringToMessageData(x_94);
lean_dec(x_94);
x_96 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_96, 0, x_93);
lean_ctor_set(x_96, 1, x_95);
x_97 = l_Lean_indentExpr(x_84);
x_98 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
x_99 = lean_mk_string_unchecked("\nnot", 4, 4);
x_100 = l_Lean_stringToMessageData(x_99);
lean_dec(x_99);
x_101 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_101, 0, x_98);
lean_ctor_set(x_101, 1, x_100);
x_102 = l_Lean_indentExpr(x_47);
x_103 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
x_104 = lean_mk_string_unchecked("", 0, 0);
x_105 = l_Lean_stringToMessageData(x_104);
lean_dec(x_104);
x_106 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_106, 0, x_103);
lean_ctor_set(x_106, 1, x_105);
x_107 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___redArg(x_106, x_10, x_11, x_12, x_13, x_89);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_107;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
lean_dec(x_84);
lean_dec(x_47);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_3);
x_108 = lean_ctor_get(x_86, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_109 = x_86;
} else {
 lean_dec_ref(x_86);
 x_109 = lean_box(0);
}
x_110 = lean_box(0);
if (lean_is_scalar(x_109)) {
 x_111 = lean_alloc_ctor(0, 2, 0);
} else {
 x_111 = x_109;
}
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_108);
return x_111;
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_84);
lean_dec(x_47);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_3);
x_112 = lean_ctor_get(x_86, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_86, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_114 = x_86;
} else {
 lean_dec_ref(x_86);
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
else
{
uint8_t x_116; 
lean_dec(x_40);
lean_dec(x_35);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_3);
x_116 = !lean_is_exclusive(x_46);
if (x_116 == 0)
{
return x_46;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_46, 0);
x_118 = lean_ctor_get(x_46, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_46);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
return x_119;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_105; 
lean_inc(x_13);
lean_inc(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_105 = l_Lean_Elab_Tactic_getFVarId(x_1, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
x_108 = lean_ctor_get(x_10, 2);
lean_inc(x_108);
x_109 = lean_local_ctx_find(x_108, x_106);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_110 = lean_mk_string_unchecked("hypothesis ", 11, 11);
x_111 = l_Lean_stringToMessageData(x_110);
lean_dec(x_110);
x_112 = l_Lean_MessageData_ofSyntax(x_1);
x_113 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
x_114 = lean_mk_string_unchecked(" not found", 10, 10);
x_115 = l_Lean_stringToMessageData(x_114);
lean_dec(x_114);
x_116 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_116, 0, x_113);
lean_ctor_set(x_116, 1, x_115);
x_117 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___redArg(x_116, x_10, x_11, x_12, x_13, x_107);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_118 = !lean_is_exclusive(x_117);
if (x_118 == 0)
{
return x_117;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_117, 0);
x_120 = lean_ctor_get(x_117, 1);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_117);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
return x_121;
}
}
else
{
lean_object* x_122; lean_object* x_123; 
x_122 = lean_ctor_get(x_109, 0);
lean_inc(x_122);
lean_dec(x_109);
lean_inc(x_1);
lean_inc(x_122);
x_123 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__2___boxed), 14, 4);
lean_closure_set(x_123, 0, x_122);
lean_closure_set(x_123, 1, x_2);
lean_closure_set(x_123, 2, x_1);
lean_closure_set(x_123, 3, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_dec(x_122);
lean_dec(x_5);
lean_dec(x_1);
x_92 = x_123;
x_93 = x_6;
x_94 = x_7;
x_95 = x_8;
x_96 = x_9;
x_97 = x_10;
x_98 = x_11;
x_99 = x_12;
x_100 = x_13;
x_101 = x_107;
goto block_104;
}
else
{
if (lean_obj_tag(x_5) == 0)
{
lean_dec(x_122);
lean_dec(x_4);
lean_dec(x_1);
x_92 = x_123;
x_93 = x_6;
x_94 = x_7;
x_95 = x_8;
x_96 = x_9;
x_97 = x_10;
x_98 = x_11;
x_99 = x_12;
x_100 = x_13;
x_101 = x_107;
goto block_104;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_4, 0);
lean_inc(x_124);
lean_dec(x_4);
x_125 = lean_ctor_get(x_5, 0);
lean_inc(x_125);
lean_dec(x_5);
x_126 = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind(x_124);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; 
lean_dec(x_125);
lean_dec(x_123);
lean_dec(x_122);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_127 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_107);
return x_127;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; uint8_t x_131; lean_object* x_132; 
x_128 = lean_ctor_get(x_126, 0);
lean_inc(x_128);
lean_dec(x_126);
x_129 = lean_box(0);
x_130 = lean_box(0);
x_131 = lean_unbox(x_130);
lean_inc(x_13);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_132 = l_Lean_Elab_Tactic_elabTerm(x_125, x_129, x_131, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_107);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
lean_dec(x_132);
x_135 = lean_ctor_get(x_122, 3);
lean_inc(x_135);
lean_dec(x_122);
x_15 = x_12;
x_16 = x_11;
x_17 = x_134;
x_18 = x_8;
x_19 = x_128;
x_20 = x_13;
x_21 = x_6;
x_22 = x_133;
x_23 = x_9;
x_24 = x_123;
x_25 = x_7;
x_26 = x_10;
x_27 = x_135;
goto block_91;
}
else
{
uint8_t x_136; 
lean_dec(x_128);
lean_dec(x_123);
lean_dec(x_122);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_136 = !lean_is_exclusive(x_132);
if (x_136 == 0)
{
return x_132;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_137 = lean_ctor_get(x_132, 0);
x_138 = lean_ctor_get(x_132, 1);
lean_inc(x_138);
lean_inc(x_137);
lean_dec(x_132);
x_139 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_139, 0, x_137);
lean_ctor_set(x_139, 1, x_138);
return x_139;
}
}
}
}
}
}
}
else
{
uint8_t x_140; 
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
lean_dec(x_2);
lean_dec(x_1);
x_140 = !lean_is_exclusive(x_105);
if (x_140 == 0)
{
return x_105;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_ctor_get(x_105, 0);
x_142 = lean_ctor_get(x_105, 1);
lean_inc(x_142);
lean_inc(x_141);
lean_dec(x_105);
x_143 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_142);
return x_143;
}
}
block_91:
{
lean_object* x_28; uint8_t x_29; 
x_28 = l_Lean_instantiateMVars___at___Lean_Elab_Tactic_getMainTarget_spec__0___redArg(x_27, x_16, x_17);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_20);
lean_inc(x_15);
lean_inc(x_16);
lean_inc(x_26);
lean_inc(x_30);
lean_inc(x_22);
x_32 = l_Lean_Elab_Tactic_GuardExpr_MatchKind_isEq(x_22, x_30, x_19, x_26, x_16, x_15, x_20, x_31);
lean_dec(x_19);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_unbox(x_33);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_18);
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec(x_32);
x_36 = lean_mk_string_unchecked("hypothesis ", 11, 11);
x_37 = l_Lean_stringToMessageData(x_36);
lean_dec(x_36);
x_38 = l_Lean_MessageData_ofSyntax(x_1);
lean_ctor_set_tag(x_28, 7);
lean_ctor_set(x_28, 1, x_38);
lean_ctor_set(x_28, 0, x_37);
x_39 = lean_mk_string_unchecked(" has type", 9, 9);
x_40 = l_Lean_stringToMessageData(x_39);
lean_dec(x_39);
x_41 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_41, 0, x_28);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Lean_indentExpr(x_30);
x_43 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_mk_string_unchecked("\nnot", 4, 4);
x_45 = l_Lean_stringToMessageData(x_44);
lean_dec(x_44);
x_46 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_45);
x_47 = l_Lean_indentExpr(x_22);
x_48 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_mk_string_unchecked("", 0, 0);
x_50 = l_Lean_stringToMessageData(x_49);
lean_dec(x_49);
x_51 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_51, 0, x_48);
lean_ctor_set(x_51, 1, x_50);
x_52 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___redArg(x_51, x_26, x_16, x_15, x_20, x_35);
lean_dec(x_20);
lean_dec(x_15);
lean_dec(x_16);
lean_dec(x_26);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_free_object(x_28);
lean_dec(x_30);
lean_dec(x_22);
lean_dec(x_1);
x_53 = lean_ctor_get(x_32, 1);
lean_inc(x_53);
lean_dec(x_32);
x_54 = lean_box(0);
x_55 = lean_apply_10(x_24, x_54, x_21, x_25, x_18, x_23, x_26, x_16, x_15, x_20, x_53);
return x_55;
}
}
else
{
uint8_t x_56; 
lean_free_object(x_28);
lean_dec(x_30);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_1);
x_56 = !lean_is_exclusive(x_32);
if (x_56 == 0)
{
return x_32;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_32, 0);
x_58 = lean_ctor_get(x_32, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_32);
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
x_60 = lean_ctor_get(x_28, 0);
x_61 = lean_ctor_get(x_28, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_28);
lean_inc(x_20);
lean_inc(x_15);
lean_inc(x_16);
lean_inc(x_26);
lean_inc(x_60);
lean_inc(x_22);
x_62 = l_Lean_Elab_Tactic_GuardExpr_MatchKind_isEq(x_22, x_60, x_19, x_26, x_16, x_15, x_20, x_61);
lean_dec(x_19);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; uint8_t x_64; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_unbox(x_63);
lean_dec(x_63);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_18);
x_65 = lean_ctor_get(x_62, 1);
lean_inc(x_65);
lean_dec(x_62);
x_66 = lean_mk_string_unchecked("hypothesis ", 11, 11);
x_67 = l_Lean_stringToMessageData(x_66);
lean_dec(x_66);
x_68 = l_Lean_MessageData_ofSyntax(x_1);
x_69 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_mk_string_unchecked(" has type", 9, 9);
x_71 = l_Lean_stringToMessageData(x_70);
lean_dec(x_70);
x_72 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_72, 0, x_69);
lean_ctor_set(x_72, 1, x_71);
x_73 = l_Lean_indentExpr(x_60);
x_74 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
x_75 = lean_mk_string_unchecked("\nnot", 4, 4);
x_76 = l_Lean_stringToMessageData(x_75);
lean_dec(x_75);
x_77 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_77, 0, x_74);
lean_ctor_set(x_77, 1, x_76);
x_78 = l_Lean_indentExpr(x_22);
x_79 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
x_80 = lean_mk_string_unchecked("", 0, 0);
x_81 = l_Lean_stringToMessageData(x_80);
lean_dec(x_80);
x_82 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_82, 0, x_79);
lean_ctor_set(x_82, 1, x_81);
x_83 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___redArg(x_82, x_26, x_16, x_15, x_20, x_65);
lean_dec(x_20);
lean_dec(x_15);
lean_dec(x_16);
lean_dec(x_26);
return x_83;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_60);
lean_dec(x_22);
lean_dec(x_1);
x_84 = lean_ctor_get(x_62, 1);
lean_inc(x_84);
lean_dec(x_62);
x_85 = lean_box(0);
x_86 = lean_apply_10(x_24, x_85, x_21, x_25, x_18, x_23, x_26, x_16, x_15, x_20, x_84);
return x_86;
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_60);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_1);
x_87 = lean_ctor_get(x_62, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_62, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_89 = x_62;
} else {
 lean_dec_ref(x_62);
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
block_104:
{
lean_object* x_102; lean_object* x_103; 
x_102 = lean_box(0);
x_103 = lean_apply_10(x_92, x_102, x_93, x_94, x_95, x_96, x_97, x_98, x_99, x_100, x_101);
return x_103;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_mk_string_unchecked("Lean", 4, 4);
x_12 = lean_mk_string_unchecked("Parser", 6, 6);
x_13 = lean_mk_string_unchecked("Tactic", 6, 6);
x_14 = lean_mk_string_unchecked("guardHyp", 8, 8);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_15 = l_Lean_Name_mkStr4(x_11, x_12, x_13, x_14);
lean_inc(x_1);
x_16 = l_Lean_Syntax_isOfKind(x_1, x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_mk_string_unchecked("guardHypConv", 12, 12);
x_18 = l_Lean_Name_mkStr4(x_11, x_12, x_13, x_17);
lean_inc(x_1);
x_19 = l_Lean_Syntax_isOfKind(x_1, x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_20 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_10);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_64; uint8_t x_65; 
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_unsigned_to_nat(1u);
x_23 = l_Lean_Syntax_getArg(x_1, x_22);
x_41 = lean_unsigned_to_nat(2u);
x_64 = l_Lean_Syntax_getArg(x_1, x_41);
x_65 = l_Lean_Syntax_isNone(x_64);
if (x_65 == 0)
{
uint8_t x_66; 
lean_inc(x_64);
x_66 = l_Lean_Syntax_matchesNull(x_64, x_41);
if (x_66 == 0)
{
lean_object* x_67; 
lean_dec(x_64);
lean_dec(x_23);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_67 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_10);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_68 = l_Lean_Syntax_getArg(x_64, x_22);
x_69 = l_Lean_Syntax_getArg(x_64, x_21);
lean_dec(x_64);
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_69);
x_71 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_71, 0, x_68);
x_42 = x_70;
x_43 = x_71;
x_44 = x_2;
x_45 = x_3;
x_46 = x_4;
x_47 = x_5;
x_48 = x_6;
x_49 = x_7;
x_50 = x_8;
x_51 = x_9;
x_52 = x_10;
goto block_63;
}
}
else
{
lean_object* x_72; 
lean_dec(x_64);
x_72 = lean_box(0);
x_42 = x_72;
x_43 = x_72;
x_44 = x_2;
x_45 = x_3;
x_46 = x_4;
x_47 = x_5;
x_48 = x_6;
x_49 = x_7;
x_50 = x_8;
x_51 = x_9;
x_52 = x_10;
goto block_63;
}
block_40:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_box(x_16);
x_38 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__1___boxed), 15, 6);
lean_closure_set(x_38, 0, x_23);
lean_closure_set(x_38, 1, x_36);
lean_closure_set(x_38, 2, x_35);
lean_closure_set(x_38, 3, x_37);
lean_closure_set(x_38, 4, x_29);
lean_closure_set(x_38, 5, x_34);
x_39 = l_Lean_Elab_Tactic_withMainContext___redArg(x_38, x_32, x_26, x_30, x_33, x_28, x_25, x_31, x_27, x_24);
return x_39;
}
block_63:
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_53 = lean_unsigned_to_nat(3u);
x_54 = l_Lean_Syntax_getArg(x_1, x_53);
lean_dec(x_1);
x_55 = l_Lean_Syntax_isNone(x_54);
if (x_55 == 0)
{
uint8_t x_56; 
lean_inc(x_54);
x_56 = l_Lean_Syntax_matchesNull(x_54, x_41);
if (x_56 == 0)
{
lean_object* x_57; 
lean_dec(x_54);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_23);
x_57 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_52);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_58 = l_Lean_Syntax_getArg(x_54, x_22);
x_59 = l_Lean_Syntax_getArg(x_54, x_21);
lean_dec(x_54);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_59);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_58);
x_24 = x_52;
x_25 = x_49;
x_26 = x_45;
x_27 = x_51;
x_28 = x_48;
x_29 = x_42;
x_30 = x_46;
x_31 = x_50;
x_32 = x_44;
x_33 = x_47;
x_34 = x_43;
x_35 = x_60;
x_36 = x_61;
goto block_40;
}
}
else
{
lean_object* x_62; 
lean_dec(x_54);
x_62 = lean_box(0);
x_24 = x_52;
x_25 = x_49;
x_26 = x_45;
x_27 = x_51;
x_28 = x_48;
x_29 = x_42;
x_30 = x_46;
x_31 = x_50;
x_32 = x_44;
x_33 = x_47;
x_34 = x_43;
x_35 = x_62;
x_36 = x_62;
goto block_40;
}
}
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_115; uint8_t x_116; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_73 = lean_unsigned_to_nat(0u);
x_74 = lean_unsigned_to_nat(1u);
x_75 = l_Lean_Syntax_getArg(x_1, x_74);
x_92 = lean_unsigned_to_nat(2u);
x_115 = l_Lean_Syntax_getArg(x_1, x_92);
x_116 = l_Lean_Syntax_isNone(x_115);
if (x_116 == 0)
{
uint8_t x_117; 
lean_inc(x_115);
x_117 = l_Lean_Syntax_matchesNull(x_115, x_92);
if (x_117 == 0)
{
lean_object* x_118; 
lean_dec(x_115);
lean_dec(x_75);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_118 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_10);
return x_118;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_119 = l_Lean_Syntax_getArg(x_115, x_74);
x_120 = l_Lean_Syntax_getArg(x_115, x_73);
lean_dec(x_115);
x_121 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_121, 0, x_120);
x_122 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_122, 0, x_119);
x_93 = x_121;
x_94 = x_122;
x_95 = x_2;
x_96 = x_3;
x_97 = x_4;
x_98 = x_5;
x_99 = x_6;
x_100 = x_7;
x_101 = x_8;
x_102 = x_9;
x_103 = x_10;
goto block_114;
}
}
else
{
lean_object* x_123; 
lean_dec(x_115);
x_123 = lean_box(0);
x_93 = x_123;
x_94 = x_123;
x_95 = x_2;
x_96 = x_3;
x_97 = x_4;
x_98 = x_5;
x_99 = x_6;
x_100 = x_7;
x_101 = x_8;
x_102 = x_9;
x_103 = x_10;
goto block_114;
}
block_91:
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__3), 14, 5);
lean_closure_set(x_89, 0, x_75);
lean_closure_set(x_89, 1, x_88);
lean_closure_set(x_89, 2, x_87);
lean_closure_set(x_89, 3, x_80);
lean_closure_set(x_89, 4, x_78);
x_90 = l_Lean_Elab_Tactic_withMainContext___redArg(x_89, x_76, x_79, x_86, x_81, x_82, x_77, x_84, x_85, x_83);
return x_90;
}
block_114:
{
lean_object* x_104; lean_object* x_105; uint8_t x_106; 
x_104 = lean_unsigned_to_nat(3u);
x_105 = l_Lean_Syntax_getArg(x_1, x_104);
lean_dec(x_1);
x_106 = l_Lean_Syntax_isNone(x_105);
if (x_106 == 0)
{
uint8_t x_107; 
lean_inc(x_105);
x_107 = l_Lean_Syntax_matchesNull(x_105, x_92);
if (x_107 == 0)
{
lean_object* x_108; 
lean_dec(x_105);
lean_dec(x_102);
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_75);
x_108 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_103);
return x_108;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_109 = l_Lean_Syntax_getArg(x_105, x_74);
x_110 = l_Lean_Syntax_getArg(x_105, x_73);
lean_dec(x_105);
x_111 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_111, 0, x_110);
x_112 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_112, 0, x_109);
x_76 = x_95;
x_77 = x_100;
x_78 = x_94;
x_79 = x_96;
x_80 = x_93;
x_81 = x_98;
x_82 = x_99;
x_83 = x_103;
x_84 = x_101;
x_85 = x_102;
x_86 = x_97;
x_87 = x_111;
x_88 = x_112;
goto block_91;
}
}
else
{
lean_object* x_113; 
lean_dec(x_105);
x_113 = lean_box(0);
x_76 = x_95;
x_77 = x_100;
x_78 = x_94;
x_79 = x_96;
x_80 = x_93;
x_81 = x_98;
x_82 = x_99;
x_83 = x_103;
x_84 = x_101;
x_85 = x_102;
x_86 = x_97;
x_87 = x_113;
x_88 = x_113;
goto block_91;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_5);
lean_dec(x_5);
x_17 = l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0(x_1, x_2, x_3, x_4, x_16, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_6);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_4);
lean_dec(x_4);
x_17 = l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__1(x_1, x_2, x_3, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_5);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
return x_11;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Tactic", 6, 6);
x_6 = lean_mk_string_unchecked("guardHyp", 8, 8);
lean_inc(x_5);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("Elab", 4, 4);
x_9 = lean_mk_string_unchecked("GuardExpr", 9, 9);
x_10 = lean_mk_string_unchecked("evalGuardHyp", 12, 12);
x_11 = l_Lean_Name_mkStr5(x_3, x_8, x_5, x_9, x_10);
x_12 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___boxed), 10, 0);
x_13 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_11, x_12, x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Elab", 4, 4);
x_4 = lean_mk_string_unchecked("Tactic", 6, 6);
x_5 = lean_mk_string_unchecked("GuardExpr", 9, 9);
x_6 = lean_mk_string_unchecked("evalGuardHyp", 12, 12);
x_7 = l_Lean_Name_mkStr5(x_2, x_3, x_4, x_5, x_6);
x_8 = lean_unsigned_to_nat(106u);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_unsigned_to_nat(130u);
x_12 = lean_unsigned_to_nat(31u);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_9);
lean_ctor_set(x_14, 2, x_13);
lean_ctor_set(x_14, 3, x_12);
x_15 = lean_unsigned_to_nat(4u);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_8);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_unsigned_to_nat(16u);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_8);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_15);
lean_ctor_set(x_19, 2, x_18);
lean_ctor_set(x_19, 3, x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_14);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_addBuiltinDeclarationRanges(x_7, x_20, x_1);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
return x_11;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv__1___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_2 = lean_alloc_closure((void*)(l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv__1___lam__0___boxed), 10, 0);
x_3 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Tactic", 6, 6);
x_7 = lean_mk_string_unchecked("guardHypConv", 12, 12);
lean_inc(x_6);
lean_inc(x_4);
x_8 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_7);
x_9 = lean_mk_string_unchecked("Elab", 4, 4);
x_10 = lean_mk_string_unchecked("GuardExpr", 9, 9);
x_11 = lean_mk_string_unchecked("evalGuardHypConv", 16, 16);
x_12 = l_Lean_Name_mkStr5(x_4, x_9, x_6, x_10, x_11);
x_13 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_3, x_8, x_12, x_2, x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv__1___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv__1___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
return x_11;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Elab", 4, 4);
x_4 = lean_mk_string_unchecked("Tactic", 6, 6);
x_5 = lean_mk_string_unchecked("GuardExpr", 9, 9);
x_6 = lean_mk_string_unchecked("evalGuardHypConv", 16, 16);
x_7 = l_Lean_Name_mkStr5(x_2, x_3, x_4, x_5, x_6);
x_8 = lean_unsigned_to_nat(133u);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_unsigned_to_nat(45u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_9);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_11);
x_14 = lean_unsigned_to_nat(4u);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_unsigned_to_nat(20u);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_8);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_14);
lean_ctor_set(x_18, 2, x_17);
lean_ctor_set(x_18, 3, x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_addBuiltinDeclarationRanges(x_7, x_19, x_1);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind(x_1);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
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
x_16 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__4___redArg(x_14);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_18 = l_Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind(x_17, x_2, x_3, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_unbox(x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_mk_string_unchecked("failed: ", 8, 8);
x_23 = l_Lean_stringToMessageData(x_22);
lean_dec(x_22);
x_24 = l_Lean_MessageData_ofSyntax(x_4);
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_mk_string_unchecked("", 0, 0);
x_27 = l_Lean_stringToMessageData(x_26);
lean_dec(x_26);
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_MessageData_ofSyntax(x_5);
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_mk_string_unchecked(" ", 1, 1);
x_32 = l_Lean_stringToMessageData(x_31);
lean_dec(x_31);
x_33 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_32);
x_34 = l_Lean_MessageData_ofSyntax(x_6);
x_35 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_mk_string_unchecked(" is not true", 12, 12);
x_37 = l_Lean_stringToMessageData(x_36);
lean_dec(x_36);
x_38 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_37);
x_39 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_38, x_8, x_9, x_10, x_11, x_12, x_13, x_21);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_39;
}
else
{
uint8_t x_40; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_40 = !lean_is_exclusive(x_18);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_18, 0);
lean_dec(x_41);
x_42 = lean_box(0);
lean_ctor_set(x_18, 0, x_42);
return x_18;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_18, 1);
lean_inc(x_43);
lean_dec(x_18);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_46 = !lean_is_exclusive(x_18);
if (x_46 == 0)
{
return x_18;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_18, 0);
x_48 = lean_ctor_get(x_18, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_18);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_mk_string_unchecked("Lean", 4, 4);
x_6 = lean_mk_string_unchecked("Parser", 6, 6);
x_7 = lean_mk_string_unchecked("Command", 7, 7);
x_8 = lean_mk_string_unchecked("guardExprCmd", 12, 12);
lean_inc(x_6);
lean_inc(x_5);
x_9 = l_Lean_Name_mkStr4(x_5, x_6, x_7, x_8);
lean_inc(x_1);
x_10 = l_Lean_Syntax_isOfKind(x_1, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_11 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_2, x_3, x_4);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_unsigned_to_nat(2u);
x_13 = l_Lean_Syntax_getArg(x_1, x_12);
x_14 = lean_mk_string_unchecked("equal", 5, 5);
x_15 = l_Lean_Name_mkStr3(x_5, x_6, x_14);
lean_inc(x_13);
x_16 = l_Lean_Syntax_isOfKind(x_13, x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_13);
lean_dec(x_1);
x_17 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_2, x_3, x_4);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_unsigned_to_nat(1u);
x_19 = l_Lean_Syntax_getArg(x_1, x_18);
x_20 = lean_unsigned_to_nat(3u);
x_21 = l_Lean_Syntax_getArg(x_1, x_20);
lean_dec(x_1);
lean_inc(x_21);
lean_inc(x_19);
lean_inc(x_13);
x_22 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___lam__0___boxed), 14, 6);
lean_closure_set(x_22, 0, x_13);
lean_closure_set(x_22, 1, x_19);
lean_closure_set(x_22, 2, x_21);
lean_closure_set(x_22, 3, x_19);
lean_closure_set(x_22, 4, x_13);
lean_closure_set(x_22, 5, x_21);
x_23 = l_Lean_Elab_Command_runTermElabM___redArg(x_22, x_2, x_3, x_4);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_7);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_2 = l_Lean_Elab_Command_commandElabAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Command", 7, 7);
x_6 = lean_mk_string_unchecked("guardExprCmd", 12, 12);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("Elab", 4, 4);
x_9 = lean_mk_string_unchecked("Tactic", 6, 6);
x_10 = lean_mk_string_unchecked("GuardExpr", 9, 9);
x_11 = lean_mk_string_unchecked("evalGuardExprCmd", 16, 16);
x_12 = l_Lean_Name_mkStr5(x_3, x_8, x_9, x_10, x_11);
x_13 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___boxed), 4, 0);
x_14 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_12, x_13, x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Elab", 4, 4);
x_4 = lean_mk_string_unchecked("Tactic", 6, 6);
x_5 = lean_mk_string_unchecked("GuardExpr", 9, 9);
x_6 = lean_mk_string_unchecked("evalGuardExprCmd", 16, 16);
x_7 = l_Lean_Name_mkStr5(x_2, x_3, x_4, x_5, x_6);
x_8 = lean_unsigned_to_nat(136u);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_unsigned_to_nat(143u);
x_12 = lean_unsigned_to_nat(31u);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_9);
lean_ctor_set(x_14, 2, x_13);
lean_ctor_set(x_14, 3, x_12);
x_15 = lean_unsigned_to_nat(4u);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_8);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_unsigned_to_nat(20u);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_8);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_15);
lean_ctor_set(x_19, 2, x_18);
lean_ctor_set(x_19, 3, x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_14);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_addBuiltinDeclarationRanges(x_7, x_20, x_1);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_7 = lean_mk_string_unchecked("Bool", 4, 4);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_box(0);
x_10 = l_Lean_Expr_const___override(x_8, x_9);
x_11 = lean_box(1);
x_12 = lean_unbox(x_11);
x_13 = l_Lean_Meta_evalExpr(lean_box(0), x_10, x_1, x_12, x_2, x_3, x_4, x_5, x_6);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lam__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_12 = l_Lean_Elab_Term_elabTermEnsuringType(x_1, x_2, x_3, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_box(0);
x_16 = lean_unbox(x_15);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_17 = l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = l_Lean_instantiateMVars___at___Lean_Elab_Term_MVarErrorInfo_logError_spec__0___redArg(x_13, x_8, x_18);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
x_23 = l_Lean_Meta_getMVars(x_21, x_7, x_8, x_9, x_10, x_22);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_ctor_get(x_23, 1);
x_27 = l_Array_isEmpty___redArg(x_25);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
lean_free_object(x_23);
lean_free_object(x_19);
lean_dec(x_21);
x_28 = lean_box(0);
x_29 = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(x_25, x_28, x_5, x_6, x_7, x_8, x_9, x_10, x_26);
lean_dec(x_7);
lean_dec(x_25);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_29, 0);
lean_dec(x_31);
x_32 = lean_box(0);
lean_ctor_set(x_29, 0, x_32);
return x_29;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_29, 1);
lean_inc(x_33);
lean_dec(x_29);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
}
else
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_29);
if (x_36 == 0)
{
return x_29;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_29, 0);
x_38 = lean_ctor_get(x_29, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_29);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
lean_object* x_40; 
lean_dec(x_25);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_21);
x_40 = l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1(x_21, x_7, x_8, x_9, x_10, x_26);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_unbox(x_41);
lean_dec(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_dec(x_40);
x_44 = lean_mk_string_unchecked("expression", 10, 10);
x_45 = l_Lean_stringToMessageData(x_44);
lean_dec(x_44);
x_46 = l_Lean_indentExpr(x_21);
lean_ctor_set_tag(x_23, 7);
lean_ctor_set(x_23, 1, x_46);
lean_ctor_set(x_23, 0, x_45);
x_47 = lean_mk_string_unchecked("\ndid not evaluate to `true`", 27, 27);
x_48 = l_Lean_stringToMessageData(x_47);
lean_dec(x_47);
lean_ctor_set_tag(x_19, 7);
lean_ctor_set(x_19, 1, x_48);
lean_ctor_set(x_19, 0, x_23);
x_49 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_19, x_5, x_6, x_7, x_8, x_9, x_10, x_43);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_49;
}
else
{
uint8_t x_50; 
lean_free_object(x_23);
lean_free_object(x_19);
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_50 = !lean_is_exclusive(x_40);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_40, 0);
lean_dec(x_51);
x_52 = lean_box(0);
lean_ctor_set(x_40, 0, x_52);
return x_40;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_40, 1);
lean_inc(x_53);
lean_dec(x_40);
x_54 = lean_box(0);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
return x_55;
}
}
}
else
{
uint8_t x_56; 
lean_free_object(x_23);
lean_free_object(x_19);
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_56 = !lean_is_exclusive(x_40);
if (x_56 == 0)
{
return x_40;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_40, 0);
x_58 = lean_ctor_get(x_40, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_40);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
}
else
{
lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_60 = lean_ctor_get(x_23, 0);
x_61 = lean_ctor_get(x_23, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_23);
x_62 = l_Array_isEmpty___redArg(x_60);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; 
lean_free_object(x_19);
lean_dec(x_21);
x_63 = lean_box(0);
x_64 = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(x_60, x_63, x_5, x_6, x_7, x_8, x_9, x_10, x_61);
lean_dec(x_7);
lean_dec(x_60);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_66 = x_64;
} else {
 lean_dec_ref(x_64);
 x_66 = lean_box(0);
}
x_67 = lean_box(0);
if (lean_is_scalar(x_66)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_66;
}
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_65);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_69 = lean_ctor_get(x_64, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_64, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_71 = x_64;
} else {
 lean_dec_ref(x_64);
 x_71 = lean_box(0);
}
if (lean_is_scalar(x_71)) {
 x_72 = lean_alloc_ctor(1, 2, 0);
} else {
 x_72 = x_71;
}
lean_ctor_set(x_72, 0, x_69);
lean_ctor_set(x_72, 1, x_70);
return x_72;
}
}
else
{
lean_object* x_73; 
lean_dec(x_60);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_21);
x_73 = l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1(x_21, x_7, x_8, x_9, x_10, x_61);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; uint8_t x_75; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_unbox(x_74);
lean_dec(x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_76 = lean_ctor_get(x_73, 1);
lean_inc(x_76);
lean_dec(x_73);
x_77 = lean_mk_string_unchecked("expression", 10, 10);
x_78 = l_Lean_stringToMessageData(x_77);
lean_dec(x_77);
x_79 = l_Lean_indentExpr(x_21);
x_80 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
x_81 = lean_mk_string_unchecked("\ndid not evaluate to `true`", 27, 27);
x_82 = l_Lean_stringToMessageData(x_81);
lean_dec(x_81);
lean_ctor_set_tag(x_19, 7);
lean_ctor_set(x_19, 1, x_82);
lean_ctor_set(x_19, 0, x_80);
x_83 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_19, x_5, x_6, x_7, x_8, x_9, x_10, x_76);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_83;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_free_object(x_19);
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_84 = lean_ctor_get(x_73, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_85 = x_73;
} else {
 lean_dec_ref(x_73);
 x_85 = lean_box(0);
}
x_86 = lean_box(0);
if (lean_is_scalar(x_85)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
} else {
 x_87 = x_85;
}
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_84);
return x_87;
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_free_object(x_19);
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_88 = lean_ctor_get(x_73, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_73, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_90 = x_73;
} else {
 lean_dec_ref(x_73);
 x_90 = lean_box(0);
}
if (lean_is_scalar(x_90)) {
 x_91 = lean_alloc_ctor(1, 2, 0);
} else {
 x_91 = x_90;
}
lean_ctor_set(x_91, 0, x_88);
lean_ctor_set(x_91, 1, x_89);
return x_91;
}
}
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; 
x_92 = lean_ctor_get(x_19, 0);
x_93 = lean_ctor_get(x_19, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_19);
lean_inc(x_92);
x_94 = l_Lean_Meta_getMVars(x_92, x_7, x_8, x_9, x_10, x_93);
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_97 = x_94;
} else {
 lean_dec_ref(x_94);
 x_97 = lean_box(0);
}
x_98 = l_Array_isEmpty___redArg(x_95);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; 
lean_dec(x_97);
lean_dec(x_92);
x_99 = lean_box(0);
x_100 = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(x_95, x_99, x_5, x_6, x_7, x_8, x_9, x_10, x_96);
lean_dec(x_7);
lean_dec(x_95);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_101 = lean_ctor_get(x_100, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_102 = x_100;
} else {
 lean_dec_ref(x_100);
 x_102 = lean_box(0);
}
x_103 = lean_box(0);
if (lean_is_scalar(x_102)) {
 x_104 = lean_alloc_ctor(0, 2, 0);
} else {
 x_104 = x_102;
}
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_101);
return x_104;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_105 = lean_ctor_get(x_100, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_100, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_107 = x_100;
} else {
 lean_dec_ref(x_100);
 x_107 = lean_box(0);
}
if (lean_is_scalar(x_107)) {
 x_108 = lean_alloc_ctor(1, 2, 0);
} else {
 x_108 = x_107;
}
lean_ctor_set(x_108, 0, x_105);
lean_ctor_set(x_108, 1, x_106);
return x_108;
}
}
else
{
lean_object* x_109; 
lean_dec(x_95);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_92);
x_109 = l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1(x_92, x_7, x_8, x_9, x_10, x_96);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; uint8_t x_111; 
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_unbox(x_110);
lean_dec(x_110);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_112 = lean_ctor_get(x_109, 1);
lean_inc(x_112);
lean_dec(x_109);
x_113 = lean_mk_string_unchecked("expression", 10, 10);
x_114 = l_Lean_stringToMessageData(x_113);
lean_dec(x_113);
x_115 = l_Lean_indentExpr(x_92);
if (lean_is_scalar(x_97)) {
 x_116 = lean_alloc_ctor(7, 2, 0);
} else {
 x_116 = x_97;
 lean_ctor_set_tag(x_116, 7);
}
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
x_117 = lean_mk_string_unchecked("\ndid not evaluate to `true`", 27, 27);
x_118 = l_Lean_stringToMessageData(x_117);
lean_dec(x_117);
x_119 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_119, 0, x_116);
lean_ctor_set(x_119, 1, x_118);
x_120 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_119, x_5, x_6, x_7, x_8, x_9, x_10, x_112);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_120;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
lean_dec(x_97);
lean_dec(x_92);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_121 = lean_ctor_get(x_109, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_122 = x_109;
} else {
 lean_dec_ref(x_109);
 x_122 = lean_box(0);
}
x_123 = lean_box(0);
if (lean_is_scalar(x_122)) {
 x_124 = lean_alloc_ctor(0, 2, 0);
} else {
 x_124 = x_122;
}
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_121);
return x_124;
}
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
lean_dec(x_97);
lean_dec(x_92);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_125 = lean_ctor_get(x_109, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_109, 1);
lean_inc(x_126);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_127 = x_109;
} else {
 lean_dec_ref(x_109);
 x_127 = lean_box(0);
}
if (lean_is_scalar(x_127)) {
 x_128 = lean_alloc_ctor(1, 2, 0);
} else {
 x_128 = x_127;
}
lean_ctor_set(x_128, 0, x_125);
lean_ctor_set(x_128, 1, x_126);
return x_128;
}
}
}
}
else
{
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_17;
}
}
else
{
uint8_t x_129; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_129 = !lean_is_exclusive(x_12);
if (x_129 == 0)
{
return x_12;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_12, 0);
x_131 = lean_ctor_get(x_12, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_12);
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
return x_132;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_mk_string_unchecked("Lean", 4, 4);
x_6 = lean_mk_string_unchecked("Parser", 6, 6);
x_7 = lean_mk_string_unchecked("Command", 7, 7);
x_8 = lean_mk_string_unchecked("guardCmd", 8, 8);
x_9 = l_Lean_Name_mkStr4(x_5, x_6, x_7, x_8);
lean_inc(x_1);
x_10 = l_Lean_Syntax_isOfKind(x_1, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_1);
x_11 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_2, x_3, x_4);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = l_Lean_Syntax_getArg(x_1, x_12);
lean_dec(x_1);
x_14 = lean_mk_string_unchecked("Bool", 4, 4);
x_15 = l_Lean_Name_mkStr1(x_14);
x_16 = lean_box(0);
x_17 = l_Lean_Expr_const___override(x_15, x_16);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_box(0);
x_20 = lean_box(x_10);
x_21 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lam__0___boxed), 11, 4);
lean_closure_set(x_21, 0, x_13);
lean_closure_set(x_21, 1, x_18);
lean_closure_set(x_21, 2, x_20);
lean_closure_set(x_21, 3, x_19);
x_22 = l_Lean_Elab_Command_liftTermElabM___redArg(x_21, x_2, x_3, x_4);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_3);
lean_dec(x_3);
x_13 = l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lam__0(x_1, x_2, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_2 = l_Lean_Elab_Command_commandElabAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Command", 7, 7);
x_6 = lean_mk_string_unchecked("guardCmd", 8, 8);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("Elab", 4, 4);
x_9 = lean_mk_string_unchecked("Tactic", 6, 6);
x_10 = lean_mk_string_unchecked("GuardExpr", 9, 9);
x_11 = lean_mk_string_unchecked("evalGuardCmd", 12, 12);
x_12 = l_Lean_Name_mkStr5(x_3, x_8, x_9, x_10, x_11);
x_13 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___boxed), 4, 0);
x_14 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_12, x_13, x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Elab", 4, 4);
x_4 = lean_mk_string_unchecked("Tactic", 6, 6);
x_5 = lean_mk_string_unchecked("GuardExpr", 9, 9);
x_6 = lean_mk_string_unchecked("evalGuardCmd", 12, 12);
x_7 = l_Lean_Name_mkStr5(x_2, x_3, x_4, x_5, x_6);
x_8 = lean_unsigned_to_nat(146u);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_unsigned_to_nat(158u);
x_12 = lean_unsigned_to_nat(31u);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_9);
lean_ctor_set(x_14, 2, x_13);
lean_ctor_set(x_14, 3, x_12);
x_15 = lean_unsigned_to_nat(4u);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_8);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_unsigned_to_nat(16u);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_8);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_15);
lean_ctor_set(x_19, 2, x_18);
lean_ctor_set(x_19, 3, x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_14);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_addBuiltinDeclarationRanges(x_7, x_20, x_1);
return x_21;
}
}
lean_object* initialize_Init_Guard(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Command(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Conv_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Eval(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Guard(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Guard(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Command(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Conv_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Eval(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
