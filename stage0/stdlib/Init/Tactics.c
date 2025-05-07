// Lean compiler output
// Module: Init.Tactics
// Imports: Init.Notation
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
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_fail;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticShow__;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticSimp_x3f_x21____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_specialize;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticBv__omega__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSimp_x3f_x21__;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_applyRules;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_SolveByElim_using__;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__letrec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tactic___x3c_x3b_x3e____1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSuffices__;
LEAN_EXPORT lean_object* l_tacticGet__elem__tactic__trivial;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__rwSeq__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticRwa______1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticNorm__cast______1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_constructor;
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_simp;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticAc__nf__;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticHave____1___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticAdmit__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__Tactics______macroRules__term_u2039___u203a__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_induction;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_bvNormalizeMacro;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_locationWildcard;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticExfalso__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticHave____1___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticRfl_x27__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_acNf0;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticRfl__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_by_x3f;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_classical;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_split;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticStop____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_location;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticHave____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_funInduction;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticDsimp_x3f_x21____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_simpArg;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacDepIfThenElse;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticHaveI__;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticAnd__intros;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_right;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_rewrites__forbidden;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__showTermElab__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_anyGoals;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticSorry__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticAssumption__mod__cast____1(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticLetI____1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticTrivial__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticAssumption__mod__cast____1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_contradiction;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_simpStar;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticTrivial;
lean_object* l_Lean_Syntax_getArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__showTermElab__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticExists___x2c_x2c__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticLetI__;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tactic___x3c_x3b_x3e____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_intros;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticRfl;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticAc__nf____1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_optConfig;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_withReducibleAndInstances;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticHave_x27___x3a_x3d__;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticNext___x3d_x3e____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticUnhygienic____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_case;
LEAN_EXPORT lean_object* l_tacticGet__elem__tactic;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticNomatch___x2c_x2c__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSimp__all_x3f_x21__;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__by_x3f__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_SolveByElim_erase;
LEAN_EXPORT lean_object* l___aux__Init__Tactics______macroRules__tacticGet__elem__tactic__trivial__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_repeat_x27;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticTrivial__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_liftLets;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSimpa_x3f__;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_replace;
lean_object* l_Array_mkArray0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_left;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticNext___x3d_x3e__;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticSuffices____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_rename;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticRefine__lift__;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticTrivial__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSimpa_x3f_x21__;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_rewrites_x3f;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__bvNormalizeMacro__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_discharger;
LEAN_EXPORT lean_object* l___aux__Init__Tactics______macroRules__tacticGet__elem__tactic__trivial__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticSimpa_x3f____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticInfer__instance;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_cases;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticTrivial__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_dsimp;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticRefine__lift_x27____1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_locationType;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_simpAllTrace;
lean_object* l_Array_mkArray1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_intro;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_sleep;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_dsimpTraceArgsRest;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_simpTraceArgsRest;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticShow____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_apply;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_exact_x3f;
LEAN_EXPORT lean_object* l___aux__Init__Tactics______macroRules__tacticGet__elem__tactic__trivial__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticHave_x27____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_generalizeArg;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__bvDecideMacro__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_withReducible;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_showTerm;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticExists___x2c_x2c__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_SolveByElim_arg;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticLet_x27__;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticSimpa_x3f_x21____1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_dsimpTrace;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__rwSeq__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_applyAssumption;
lean_object* l_Array_empty(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticRwa______1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticTrivial__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_refine_x27;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticLet_x27____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticNext___x3d_x3e____1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_rwRuleSeq;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_SolveByElim_args;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticAdmit__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSorry;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_simpLemma;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_nativeDecide;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_skip;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_case_x27;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_symm;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_acRfl;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__bvNormalizeMacro__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_congr;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticStop__;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticExfalso;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_simpa;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_injection;
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_changeWith;
LEAN_EXPORT lean_object* l_term_u2039___u203a;
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticRefine__lift_x27__;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticHaveI____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticTrivial__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_pushCast;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticNomatch___x2c_x2c;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_paren;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticLet____1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticTrivial__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_rwRule;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_done;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__letrec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_normCast0;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_rotateLeft;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticTrivial__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_falseOrByContra;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticNomatch___x2c_x2c__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__bvDecideMacro__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Macro_throwError___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_repeat1_x27;
LEAN_EXPORT lean_object* l___aux__Init__Tactics______macroRules__tacticGet__elem__tactic__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_substVars;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_posConfigItem;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticSuffices____1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__Tactics______macroRules__tacticGet__elem__tactic__trivial__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticNofun__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticNofun;
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_withUnfoldingAll;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_rotateRight;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_inductionAlt;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_dbgTrace;
LEAN_EXPORT lean_object* l___aux__Init__Tactics______macroRules__tacticGet__elem__tactic__1___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticRfl__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticAdmit;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_inductionAltLHS;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticHave_x27___x3a_x3d____1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_configItem;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticRefine__lift____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_simpAllTraceArgsRest;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__bvTraceMacro__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_subst;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_as__aux__lemma;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticStop____1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_bvDecideMacro;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_withAnnotateState;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticTry__;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_simpPre;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_rwSeq;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_simpTrace;
LEAN_EXPORT lean_object* l___aux__Init__Tactics______macroRules__tacticGet__elem__tactic__trivial__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticLetI____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_generalize;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_simpErase;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticTrivial__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticInfer__instance__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_delta;
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticHave_x27____1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticDsimp_x3f_x21____1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_exposeNames;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_simpPost;
lean_object* l_Lean_Macro_throwUnsupported(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticRfl_x27;
LEAN_EXPORT lean_object* l_Lean_Parser_Syntax_exact_x3f;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticSorry__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_eqRefl;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticLet____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticHave____1___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_appendCore___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticDsimp_x3f_x21__;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticSimp__all_x3f_x21____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_elimTarget;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticExists___x2c_x2c;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticHave_x27___x3a_x3d____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticNorm__cast____;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_first;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticTrivial__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_rewriteSeq;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticRwa____;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticSimp_x3f_x21____1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tactic___x3c_x3b_x3e__;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_locationHyp;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_simp;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_injections;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticAssumption__mod__cast__;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticRfl__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticRfl__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_normCastLabel;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticSimpa_x21____1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_valConfigItem;
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_norm__cast;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticNofun__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_symmSaturate;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_inductionAlts;
extern lean_object* l_Lean_binderIdent;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticSimpa_x3f____1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticShow____1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticAc__nf____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_allGoals;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_dsimpArg;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_decide;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticNorm__cast______1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_letrec;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_substEqs;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_revert;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_SolveByElim_star;
extern lean_object* l_Lean_Parser_Tactic_caseArg;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_extractLets;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticHave__;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticUnhygienic__;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacIfThenElse;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticSimpa_x3f_x21____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_omega;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_clear;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_traceState;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_dsimpArgs;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_exact;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_normCastAddElim;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_simpArgs;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_simpaArgsRest;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticLet_x27____1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticHave____1___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticRfl__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticAnd__intros__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticHaveI____1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticBv__omega;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_config;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_negConfigItem;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_focus;
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_wf__preprocess;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_apply_x3f;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_bvTraceMacro;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_change;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticRepeat__;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticRepeat____1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticTry____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_assumption;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticLet__;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticRepeat____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticTry____1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_showTermElab;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticSimpa_x21____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__by_x3f__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_suggestPremises;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticRefine__lift_x27____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_traceMessage;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticHave_x27__;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSimpa_x21__;
lean_object* l_String_toSubstring_x27(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_renameI;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_refine;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_failIfSuccess;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_runTac;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_simpAll;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_funCases;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__bvTraceMacro__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_applyRfl;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_unfold;
LEAN_EXPORT lean_object* l___aux__Init__Tactics______macroRules__term_u2039___u203a__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticRefine__lift____1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticSimp__all_x3f_x21____1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_solveByElim;
static lean_object* _init_l_Lean_Parser_Tactic_as__aux__lemma() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("as_aux_lemma", 12, 12);
lean_inc(x_4);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_10, 0, x_4);
x_11 = lean_unbox(x_9);
lean_ctor_set_uint8(x_10, sizeof(void*)*1, x_11);
x_12 = lean_mk_string_unchecked(" => ", 4, 4);
x_13 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_13, 0, x_12);
lean_inc(x_8);
x_14 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_14, 0, x_8);
lean_ctor_set(x_14, 1, x_10);
lean_ctor_set(x_14, 2, x_13);
x_15 = lean_mk_string_unchecked("tacticSeq", 9, 9);
x_16 = l_Lean_Name_mkStr1(x_15);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_18, 0, x_8);
lean_ctor_set(x_18, 1, x_14);
lean_ctor_set(x_18, 2, x_17);
x_19 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_19, 0, x_5);
lean_ctor_set(x_19, 1, x_6);
lean_ctor_set(x_19, 2, x_18);
return x_19;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_withAnnotateState() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("withAnnotateState", 17, 17);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("with_annotate_state ", 20, 20);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_unbox(x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_12);
x_13 = lean_mk_string_unchecked("rawStx", 6, 6);
x_14 = l_Lean_Name_mkStr1(x_13);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
lean_inc(x_8);
x_17 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_17, 0, x_8);
lean_ctor_set(x_17, 1, x_11);
lean_ctor_set(x_17, 2, x_16);
x_18 = lean_mk_string_unchecked("ppSpace", 7, 7);
x_19 = l_Lean_Name_mkStr1(x_18);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
lean_inc(x_8);
x_21 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_21, 0, x_8);
lean_ctor_set(x_21, 1, x_17);
lean_ctor_set(x_21, 2, x_20);
x_22 = lean_mk_string_unchecked("tactic", 6, 6);
x_23 = l_Lean_Name_mkStr1(x_22);
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_15);
x_25 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_25, 0, x_8);
lean_ctor_set(x_25, 1, x_21);
lean_ctor_set(x_25, 2, x_24);
x_26 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_26, 0, x_5);
lean_ctor_set(x_26, 1, x_6);
lean_ctor_set(x_26, 2, x_25);
return x_26;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_intro() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("intro", 5, 5);
lean_inc(x_4);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_10, 0, x_4);
x_11 = lean_unbox(x_9);
lean_ctor_set_uint8(x_10, sizeof(void*)*1, x_11);
x_12 = lean_mk_string_unchecked("notFollowedBy", 13, 13);
x_13 = l_Lean_Name_mkStr1(x_12);
x_14 = lean_mk_string_unchecked("|", 1, 1);
x_15 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
lean_inc(x_8);
x_17 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_17, 0, x_8);
lean_ctor_set(x_17, 1, x_10);
lean_ctor_set(x_17, 2, x_16);
x_18 = lean_mk_string_unchecked("many", 4, 4);
x_19 = l_Lean_Name_mkStr1(x_18);
x_20 = lean_mk_string_unchecked("ppSpace", 7, 7);
x_21 = l_Lean_Name_mkStr1(x_20);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_mk_string_unchecked("colGt", 5, 5);
x_24 = l_Lean_Name_mkStr1(x_23);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
lean_inc(x_8);
x_26 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_26, 0, x_8);
lean_ctor_set(x_26, 1, x_22);
lean_ctor_set(x_26, 2, x_25);
x_27 = lean_mk_string_unchecked("term", 4, 4);
x_28 = l_Lean_Name_mkStr1(x_27);
x_29 = lean_unsigned_to_nat(1024u);
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
lean_inc(x_8);
x_31 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_31, 0, x_8);
lean_ctor_set(x_31, 1, x_26);
lean_ctor_set(x_31, 2, x_30);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_19);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_33, 0, x_8);
lean_ctor_set(x_33, 1, x_17);
lean_ctor_set(x_33, 2, x_32);
x_34 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_34, 0, x_5);
lean_ctor_set(x_34, 1, x_6);
lean_ctor_set(x_34, 2, x_33);
return x_34;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_intros() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("intros", 6, 6);
lean_inc(x_4);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_10, 0, x_4);
x_11 = lean_unbox(x_9);
lean_ctor_set_uint8(x_10, sizeof(void*)*1, x_11);
x_12 = lean_mk_string_unchecked("many", 4, 4);
x_13 = l_Lean_Name_mkStr1(x_12);
x_14 = lean_mk_string_unchecked("ppSpace", 7, 7);
x_15 = l_Lean_Name_mkStr1(x_14);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_mk_string_unchecked("colGt", 5, 5);
x_18 = l_Lean_Name_mkStr1(x_17);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
lean_inc(x_8);
x_20 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_20, 0, x_8);
lean_ctor_set(x_20, 1, x_16);
lean_ctor_set(x_20, 2, x_19);
x_21 = lean_mk_string_unchecked("orelse", 6, 6);
x_22 = l_Lean_Name_mkStr1(x_21);
x_23 = lean_mk_string_unchecked("ident", 5, 5);
x_24 = l_Lean_Name_mkStr1(x_23);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_mk_string_unchecked("hole", 4, 4);
x_27 = l_Lean_Name_mkStr1(x_26);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_29, 0, x_22);
lean_ctor_set(x_29, 1, x_25);
lean_ctor_set(x_29, 2, x_28);
lean_inc(x_8);
x_30 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_30, 0, x_8);
lean_ctor_set(x_30, 1, x_20);
lean_ctor_set(x_30, 2, x_29);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_13);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_32, 0, x_8);
lean_ctor_set(x_32, 1, x_10);
lean_ctor_set(x_32, 2, x_31);
x_33 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_33, 0, x_5);
lean_ctor_set(x_33, 1, x_6);
lean_ctor_set(x_33, 2, x_32);
return x_33;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rename() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("rename", 6, 6);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("rename ", 7, 7);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_unbox(x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_12);
x_13 = lean_mk_string_unchecked("term", 4, 4);
x_14 = l_Lean_Name_mkStr1(x_13);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
lean_inc(x_8);
x_17 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_17, 0, x_8);
lean_ctor_set(x_17, 1, x_11);
lean_ctor_set(x_17, 2, x_16);
x_18 = lean_mk_string_unchecked(" => ", 4, 4);
x_19 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_19, 0, x_18);
lean_inc(x_8);
x_20 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_20, 0, x_8);
lean_ctor_set(x_20, 1, x_17);
lean_ctor_set(x_20, 2, x_19);
x_21 = lean_mk_string_unchecked("ident", 5, 5);
x_22 = l_Lean_Name_mkStr1(x_21);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_24, 0, x_8);
lean_ctor_set(x_24, 1, x_20);
lean_ctor_set(x_24, 2, x_23);
x_25 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_25, 0, x_5);
lean_ctor_set(x_25, 1, x_6);
lean_ctor_set(x_25, 2, x_24);
return x_25;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_revert() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("revert", 6, 6);
lean_inc(x_4);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_10, 0, x_4);
x_11 = lean_unbox(x_9);
lean_ctor_set_uint8(x_10, sizeof(void*)*1, x_11);
x_12 = lean_mk_string_unchecked("many1", 5, 5);
x_13 = l_Lean_Name_mkStr1(x_12);
x_14 = lean_mk_string_unchecked("ppSpace", 7, 7);
x_15 = l_Lean_Name_mkStr1(x_14);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_mk_string_unchecked("colGt", 5, 5);
x_18 = l_Lean_Name_mkStr1(x_17);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
lean_inc(x_8);
x_20 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_20, 0, x_8);
lean_ctor_set(x_20, 1, x_16);
lean_ctor_set(x_20, 2, x_19);
x_21 = lean_mk_string_unchecked("term", 4, 4);
x_22 = l_Lean_Name_mkStr1(x_21);
x_23 = lean_unsigned_to_nat(1024u);
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
lean_inc(x_8);
x_25 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_25, 0, x_8);
lean_ctor_set(x_25, 1, x_20);
lean_ctor_set(x_25, 2, x_24);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_13);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_27, 0, x_8);
lean_ctor_set(x_27, 1, x_10);
lean_ctor_set(x_27, 2, x_26);
x_28 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_28, 0, x_5);
lean_ctor_set(x_28, 1, x_6);
lean_ctor_set(x_28, 2, x_27);
return x_28;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_clear() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("clear", 5, 5);
lean_inc(x_4);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_10, 0, x_4);
x_11 = lean_unbox(x_9);
lean_ctor_set_uint8(x_10, sizeof(void*)*1, x_11);
x_12 = lean_mk_string_unchecked("many1", 5, 5);
x_13 = l_Lean_Name_mkStr1(x_12);
x_14 = lean_mk_string_unchecked("ppSpace", 7, 7);
x_15 = l_Lean_Name_mkStr1(x_14);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_mk_string_unchecked("colGt", 5, 5);
x_18 = l_Lean_Name_mkStr1(x_17);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
lean_inc(x_8);
x_20 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_20, 0, x_8);
lean_ctor_set(x_20, 1, x_16);
lean_ctor_set(x_20, 2, x_19);
x_21 = lean_mk_string_unchecked("term", 4, 4);
x_22 = l_Lean_Name_mkStr1(x_21);
x_23 = lean_unsigned_to_nat(1024u);
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
lean_inc(x_8);
x_25 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_25, 0, x_8);
lean_ctor_set(x_25, 1, x_20);
lean_ctor_set(x_25, 2, x_24);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_13);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_27, 0, x_8);
lean_ctor_set(x_27, 1, x_10);
lean_ctor_set(x_27, 2, x_26);
x_28 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_28, 0, x_5);
lean_ctor_set(x_28, 1, x_6);
lean_ctor_set(x_28, 2, x_27);
return x_28;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_subst() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("subst", 5, 5);
lean_inc(x_4);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_10, 0, x_4);
x_11 = lean_unbox(x_9);
lean_ctor_set_uint8(x_10, sizeof(void*)*1, x_11);
x_12 = lean_mk_string_unchecked("many1", 5, 5);
x_13 = l_Lean_Name_mkStr1(x_12);
x_14 = lean_mk_string_unchecked("ppSpace", 7, 7);
x_15 = l_Lean_Name_mkStr1(x_14);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_mk_string_unchecked("colGt", 5, 5);
x_18 = l_Lean_Name_mkStr1(x_17);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
lean_inc(x_8);
x_20 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_20, 0, x_8);
lean_ctor_set(x_20, 1, x_16);
lean_ctor_set(x_20, 2, x_19);
x_21 = lean_mk_string_unchecked("term", 4, 4);
x_22 = l_Lean_Name_mkStr1(x_21);
x_23 = lean_unsigned_to_nat(1024u);
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
lean_inc(x_8);
x_25 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_25, 0, x_8);
lean_ctor_set(x_25, 1, x_20);
lean_ctor_set(x_25, 2, x_24);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_13);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_27, 0, x_8);
lean_ctor_set(x_27, 1, x_10);
lean_ctor_set(x_27, 2, x_26);
x_28 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_28, 0, x_5);
lean_ctor_set(x_28, 1, x_6);
lean_ctor_set(x_28, 2, x_27);
return x_28;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_substVars() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("substVars", 9, 9);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1024u);
x_7 = lean_mk_string_unchecked("subst_vars", 10, 10);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_9, 0, x_7);
x_10 = lean_unbox(x_8);
lean_ctor_set_uint8(x_9, sizeof(void*)*1, x_10);
x_11 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_6);
lean_ctor_set(x_11, 2, x_9);
return x_11;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_assumption() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("assumption", 10, 10);
lean_inc(x_4);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1024u);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_8, 0, x_4);
x_9 = lean_unbox(x_7);
lean_ctor_set_uint8(x_8, sizeof(void*)*1, x_9);
x_10 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_6);
lean_ctor_set(x_10, 2, x_8);
return x_10;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_contradiction() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("contradiction", 13, 13);
lean_inc(x_4);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1024u);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_8, 0, x_4);
x_9 = lean_unbox(x_7);
lean_ctor_set_uint8(x_8, sizeof(void*)*1, x_9);
x_10 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_6);
lean_ctor_set(x_10, 2, x_8);
return x_10;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_falseOrByContra() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("falseOrByContra", 15, 15);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1024u);
x_7 = lean_mk_string_unchecked("false_or_by_contra", 18, 18);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_9, 0, x_7);
x_10 = lean_unbox(x_8);
lean_ctor_set_uint8(x_9, sizeof(void*)*1, x_10);
x_11 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_6);
lean_ctor_set(x_11, 2, x_9);
return x_11;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_apply() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("apply", 5, 5);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("apply ", 6, 6);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_unbox(x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_12);
x_13 = lean_mk_string_unchecked("term", 4, 4);
x_14 = l_Lean_Name_mkStr1(x_13);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_17, 0, x_8);
lean_ctor_set(x_17, 1, x_11);
lean_ctor_set(x_17, 2, x_16);
x_18 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_18, 0, x_5);
lean_ctor_set(x_18, 1, x_6);
lean_ctor_set(x_18, 2, x_17);
return x_18;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_exact() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("exact", 5, 5);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("exact ", 6, 6);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_unbox(x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_12);
x_13 = lean_mk_string_unchecked("term", 4, 4);
x_14 = l_Lean_Name_mkStr1(x_13);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_17, 0, x_8);
lean_ctor_set(x_17, 1, x_11);
lean_ctor_set(x_17, 2, x_16);
x_18 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_18, 0, x_5);
lean_ctor_set(x_18, 1, x_6);
lean_ctor_set(x_18, 2, x_17);
return x_18;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_refine() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("refine", 6, 6);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("refine ", 7, 7);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_unbox(x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_12);
x_13 = lean_mk_string_unchecked("term", 4, 4);
x_14 = l_Lean_Name_mkStr1(x_13);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_17, 0, x_8);
lean_ctor_set(x_17, 1, x_11);
lean_ctor_set(x_17, 2, x_16);
x_18 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_18, 0, x_5);
lean_ctor_set(x_18, 1, x_6);
lean_ctor_set(x_18, 2, x_17);
return x_18;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_refine_x27() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("refine'", 7, 7);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("refine' ", 8, 8);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_unbox(x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_12);
x_13 = lean_mk_string_unchecked("term", 4, 4);
x_14 = l_Lean_Name_mkStr1(x_13);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_17, 0, x_8);
lean_ctor_set(x_17, 1, x_11);
lean_ctor_set(x_17, 2, x_16);
x_18 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_18, 0, x_5);
lean_ctor_set(x_18, 1, x_6);
lean_ctor_set(x_18, 2, x_17);
return x_18;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticExfalso() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("tacticExfalso", 13, 13);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1024u);
x_7 = lean_mk_string_unchecked("exfalso", 7, 7);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_9, 0, x_7);
x_10 = lean_unbox(x_8);
lean_ctor_set_uint8(x_9, sizeof(void*)*1, x_10);
x_11 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_6);
lean_ctor_set(x_11, 2, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticExfalso__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Tactic", 6, 6);
x_7 = lean_mk_string_unchecked("tacticExfalso", 13, 13);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_8 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_7);
x_9 = l_Lean_Syntax_isOfKind(x_1, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_10 = lean_box(1);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_12 = lean_ctor_get(x_2, 5);
lean_inc(x_12);
x_13 = lean_box(0);
x_14 = lean_unbox(x_13);
x_15 = l_Lean_SourceInfo_fromRef(x_12, x_14);
lean_dec(x_12);
x_16 = lean_ctor_get(x_2, 2);
lean_inc(x_16);
x_17 = lean_ctor_get(x_2, 1);
lean_inc(x_17);
lean_dec(x_2);
x_18 = lean_mk_string_unchecked("refine", 6, 6);
lean_inc(x_18);
lean_inc(x_5);
lean_inc(x_4);
x_19 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_18);
lean_inc(x_15);
x_20 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_20, 0, x_15);
lean_ctor_set(x_20, 1, x_18);
x_21 = lean_mk_string_unchecked("Term", 4, 4);
x_22 = lean_mk_string_unchecked("app", 3, 3);
lean_inc(x_21);
lean_inc(x_5);
lean_inc(x_4);
x_23 = l_Lean_Name_mkStr4(x_4, x_5, x_21, x_22);
x_24 = lean_mk_string_unchecked("False.elim", 10, 10);
x_25 = l_String_toSubstring_x27(x_24);
x_26 = lean_mk_string_unchecked("False", 5, 5);
x_27 = lean_mk_string_unchecked("elim", 4, 4);
x_28 = l_Lean_Name_mkStr2(x_26, x_27);
lean_inc(x_28);
x_29 = l_Lean_addMacroScope(x_17, x_28, x_16);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
lean_inc(x_15);
x_34 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_34, 0, x_15);
lean_ctor_set(x_34, 1, x_25);
lean_ctor_set(x_34, 2, x_29);
lean_ctor_set(x_34, 3, x_33);
x_35 = lean_mk_string_unchecked("null", 4, 4);
x_36 = l_Lean_Name_mkStr1(x_35);
x_37 = lean_mk_string_unchecked("syntheticHole", 13, 13);
x_38 = l_Lean_Name_mkStr4(x_4, x_5, x_21, x_37);
x_39 = lean_mk_string_unchecked("\?", 1, 1);
lean_inc(x_15);
x_40 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_40, 0, x_15);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_mk_string_unchecked("_", 1, 1);
lean_inc(x_15);
x_42 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_42, 0, x_15);
lean_ctor_set(x_42, 1, x_41);
lean_inc(x_15);
x_43 = l_Lean_Syntax_node2(x_15, x_38, x_40, x_42);
lean_inc(x_15);
x_44 = l_Lean_Syntax_node1(x_15, x_36, x_43);
lean_inc(x_15);
x_45 = l_Lean_Syntax_node2(x_15, x_23, x_34, x_44);
x_46 = l_Lean_Syntax_node2(x_15, x_19, x_20, x_45);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_3);
return x_47;
}
}
}
static lean_object* _init_l_Lean_Parser_Tactic_constructor() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("constructor", 11, 11);
lean_inc(x_4);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1024u);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_8, 0, x_4);
x_9 = lean_unbox(x_7);
lean_ctor_set_uint8(x_8, sizeof(void*)*1, x_9);
x_10 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_6);
lean_ctor_set(x_10, 2, x_8);
return x_10;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_left() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("left", 4, 4);
lean_inc(x_4);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1024u);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_8, 0, x_4);
x_9 = lean_unbox(x_7);
lean_ctor_set_uint8(x_8, sizeof(void*)*1, x_9);
x_10 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_6);
lean_ctor_set(x_10, 2, x_8);
return x_10;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_right() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("right", 5, 5);
lean_inc(x_4);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1024u);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_8, 0, x_4);
x_9 = lean_unbox(x_7);
lean_ctor_set_uint8(x_8, sizeof(void*)*1, x_9);
x_10 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_6);
lean_ctor_set(x_10, 2, x_8);
return x_10;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_case() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("case", 4, 4);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("case ", 5, 5);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_unbox(x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_12);
x_13 = l_Lean_Parser_Tactic_caseArg;
x_14 = lean_mk_string_unchecked(" | ", 3, 3);
lean_inc(x_14);
x_15 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(11, 3, 1);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_14);
lean_ctor_set(x_16, 2, x_15);
x_17 = lean_unbox(x_10);
lean_ctor_set_uint8(x_16, sizeof(void*)*3, x_17);
lean_inc(x_8);
x_18 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_18, 0, x_8);
lean_ctor_set(x_18, 1, x_11);
lean_ctor_set(x_18, 2, x_16);
x_19 = lean_mk_string_unchecked(" => ", 4, 4);
x_20 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_20, 0, x_19);
lean_inc(x_8);
x_21 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_21, 0, x_8);
lean_ctor_set(x_21, 1, x_18);
lean_ctor_set(x_21, 2, x_20);
x_22 = lean_mk_string_unchecked("tacticSeq", 9, 9);
x_23 = l_Lean_Name_mkStr1(x_22);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_25, 0, x_8);
lean_ctor_set(x_25, 1, x_21);
lean_ctor_set(x_25, 2, x_24);
x_26 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_26, 0, x_5);
lean_ctor_set(x_26, 1, x_6);
lean_ctor_set(x_26, 2, x_25);
return x_26;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_case_x27() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("case'", 5, 5);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("case' ", 6, 6);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_unbox(x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_12);
x_13 = l_Lean_Parser_Tactic_caseArg;
x_14 = lean_mk_string_unchecked(" | ", 3, 3);
lean_inc(x_14);
x_15 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(11, 3, 1);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_14);
lean_ctor_set(x_16, 2, x_15);
x_17 = lean_unbox(x_10);
lean_ctor_set_uint8(x_16, sizeof(void*)*3, x_17);
lean_inc(x_8);
x_18 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_18, 0, x_8);
lean_ctor_set(x_18, 1, x_11);
lean_ctor_set(x_18, 2, x_16);
x_19 = lean_mk_string_unchecked(" => ", 4, 4);
x_20 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_20, 0, x_19);
lean_inc(x_8);
x_21 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_21, 0, x_8);
lean_ctor_set(x_21, 1, x_18);
lean_ctor_set(x_21, 2, x_20);
x_22 = lean_mk_string_unchecked("tacticSeq", 9, 9);
x_23 = l_Lean_Name_mkStr1(x_22);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_25, 0, x_8);
lean_ctor_set(x_25, 1, x_21);
lean_ctor_set(x_25, 2, x_24);
x_26 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_26, 0, x_5);
lean_ctor_set(x_26, 1, x_6);
lean_ctor_set(x_26, 2, x_25);
return x_26;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticNext___x3d_x3e__() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("tacticNext_=>_", 14, 14);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("next ", 5, 5);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_unbox(x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_12);
x_13 = lean_mk_string_unchecked("many", 4, 4);
x_14 = l_Lean_Name_mkStr1(x_13);
x_15 = l_Lean_binderIdent;
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
lean_inc(x_8);
x_17 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_17, 0, x_8);
lean_ctor_set(x_17, 1, x_11);
lean_ctor_set(x_17, 2, x_16);
x_18 = lean_mk_string_unchecked(" => ", 4, 4);
x_19 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_19, 0, x_18);
lean_inc(x_8);
x_20 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_20, 0, x_8);
lean_ctor_set(x_20, 1, x_17);
lean_ctor_set(x_20, 2, x_19);
x_21 = lean_mk_string_unchecked("tacticSeq", 9, 9);
x_22 = l_Lean_Name_mkStr1(x_21);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_24, 0, x_8);
lean_ctor_set(x_24, 1, x_20);
lean_ctor_set(x_24, 2, x_23);
x_25 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_25, 0, x_5);
lean_ctor_set(x_25, 1, x_6);
lean_ctor_set(x_25, 2, x_24);
return x_25;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticNext___x3d_x3e____1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Tactic", 6, 6);
x_7 = lean_mk_string_unchecked("tacticNext_=>_", 14, 14);
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
x_10 = lean_box(1);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_unsigned_to_nat(1u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
x_15 = lean_unsigned_to_nat(2u);
x_16 = lean_unsigned_to_nat(3u);
x_17 = l_Lean_Syntax_getArg(x_1, x_16);
x_18 = l_Lean_Syntax_getArg(x_1, x_15);
x_19 = lean_mk_string_unchecked("binderIdent", 11, 11);
lean_inc(x_4);
x_20 = l_Lean_Name_mkStr2(x_4, x_19);
x_21 = l_Lean_Syntax_getArgs(x_14);
lean_dec(x_14);
x_22 = l_Lean_Syntax_getArg(x_1, x_12);
lean_dec(x_1);
x_23 = lean_ctor_get(x_2, 5);
x_24 = l_Lean_replaceRef(x_18, x_23);
x_25 = lean_box(0);
x_26 = lean_unbox(x_25);
x_27 = l_Lean_SourceInfo_fromRef(x_24, x_26);
lean_dec(x_24);
x_28 = lean_mk_string_unchecked("case", 4, 4);
lean_inc(x_28);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_29 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_28);
x_30 = l_Lean_SourceInfo_fromRef(x_22, x_9);
lean_dec(x_22);
x_31 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_28);
x_32 = lean_mk_string_unchecked("null", 4, 4);
x_33 = l_Lean_Name_mkStr1(x_32);
x_34 = lean_mk_string_unchecked("caseArg", 7, 7);
lean_inc(x_5);
lean_inc(x_4);
x_35 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_34);
x_36 = lean_mk_string_unchecked("Term", 4, 4);
x_37 = lean_mk_string_unchecked("hole", 4, 4);
x_38 = l_Lean_Name_mkStr4(x_4, x_5, x_36, x_37);
x_39 = lean_mk_string_unchecked("_", 1, 1);
lean_inc(x_27);
x_40 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_40, 0, x_27);
lean_ctor_set(x_40, 1, x_39);
lean_inc(x_27);
x_41 = l_Lean_Syntax_node1(x_27, x_38, x_40);
lean_inc(x_27);
x_42 = l_Lean_Syntax_node1(x_27, x_20, x_41);
x_43 = l_Array_mkArray0(lean_box(0));
x_44 = l_Array_appendCore___redArg(x_43, x_21);
lean_dec(x_21);
lean_inc(x_33);
lean_inc(x_27);
x_45 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_45, 0, x_27);
lean_ctor_set(x_45, 1, x_33);
lean_ctor_set(x_45, 2, x_44);
lean_inc(x_27);
x_46 = l_Lean_Syntax_node2(x_27, x_35, x_42, x_45);
lean_inc(x_27);
x_47 = l_Lean_Syntax_node1(x_27, x_33, x_46);
x_48 = l_Lean_SourceInfo_fromRef(x_18, x_9);
lean_dec(x_18);
x_49 = lean_mk_string_unchecked("=>", 2, 2);
x_50 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
x_51 = l_Lean_Syntax_node4(x_27, x_29, x_31, x_47, x_50, x_17);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_3);
return x_52;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticNext___x3d_x3e____1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticNext___x3d_x3e____1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_allGoals() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("allGoals", 8, 8);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("all_goals ", 10, 10);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_unbox(x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_12);
x_13 = lean_mk_string_unchecked("tacticSeq", 9, 9);
x_14 = l_Lean_Name_mkStr1(x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_16, 0, x_8);
lean_ctor_set(x_16, 1, x_11);
lean_ctor_set(x_16, 2, x_15);
x_17 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_17, 0, x_5);
lean_ctor_set(x_17, 1, x_6);
lean_ctor_set(x_17, 2, x_16);
return x_17;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_anyGoals() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("anyGoals", 8, 8);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("any_goals ", 10, 10);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_unbox(x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_12);
x_13 = lean_mk_string_unchecked("tacticSeq", 9, 9);
x_14 = l_Lean_Name_mkStr1(x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_16, 0, x_8);
lean_ctor_set(x_16, 1, x_11);
lean_ctor_set(x_16, 2, x_15);
x_17 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_17, 0, x_5);
lean_ctor_set(x_17, 1, x_6);
lean_ctor_set(x_17, 2, x_16);
return x_17;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_focus() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("focus", 5, 5);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("focus ", 6, 6);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_unbox(x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_12);
x_13 = lean_mk_string_unchecked("tacticSeq", 9, 9);
x_14 = l_Lean_Name_mkStr1(x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_16, 0, x_8);
lean_ctor_set(x_16, 1, x_11);
lean_ctor_set(x_16, 2, x_15);
x_17 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_17, 0, x_5);
lean_ctor_set(x_17, 1, x_6);
lean_ctor_set(x_17, 2, x_16);
return x_17;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_skip() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("skip", 4, 4);
lean_inc(x_4);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1024u);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_8, 0, x_4);
x_9 = lean_unbox(x_7);
lean_ctor_set_uint8(x_8, sizeof(void*)*1, x_9);
x_10 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_6);
lean_ctor_set(x_10, 2, x_8);
return x_10;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_done() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("done", 4, 4);
lean_inc(x_4);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1024u);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_8, 0, x_4);
x_9 = lean_unbox(x_7);
lean_ctor_set_uint8(x_8, sizeof(void*)*1, x_9);
x_10 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_6);
lean_ctor_set(x_10, 2, x_8);
return x_10;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_traceState() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("traceState", 10, 10);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1024u);
x_7 = lean_mk_string_unchecked("trace_state", 11, 11);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_9, 0, x_7);
x_10 = lean_unbox(x_8);
lean_ctor_set_uint8(x_9, sizeof(void*)*1, x_10);
x_11 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_6);
lean_ctor_set(x_11, 2, x_9);
return x_11;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_traceMessage() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("traceMessage", 12, 12);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("trace ", 6, 6);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_unbox(x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_12);
x_13 = lean_mk_string_unchecked("str", 3, 3);
x_14 = l_Lean_Name_mkStr1(x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_16, 0, x_8);
lean_ctor_set(x_16, 1, x_11);
lean_ctor_set(x_16, 2, x_15);
x_17 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_17, 0, x_5);
lean_ctor_set(x_17, 1, x_6);
lean_ctor_set(x_17, 2, x_16);
return x_17;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_failIfSuccess() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("failIfSuccess", 13, 13);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("fail_if_success ", 16, 16);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_unbox(x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_12);
x_13 = lean_mk_string_unchecked("tacticSeq", 9, 9);
x_14 = l_Lean_Name_mkStr1(x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_16, 0, x_8);
lean_ctor_set(x_16, 1, x_11);
lean_ctor_set(x_16, 2, x_15);
x_17 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_17, 0, x_5);
lean_ctor_set(x_17, 1, x_6);
lean_ctor_set(x_17, 2, x_16);
return x_17;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_paren() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("paren", 5, 5);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1024u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("(", 1, 1);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_unbox(x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_12);
x_13 = lean_mk_string_unchecked("withoutPosition", 15, 15);
x_14 = l_Lean_Name_mkStr1(x_13);
x_15 = lean_mk_string_unchecked("tacticSeq", 9, 9);
x_16 = l_Lean_Name_mkStr1(x_15);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_14);
lean_ctor_set(x_18, 1, x_17);
lean_inc(x_8);
x_19 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_19, 0, x_8);
lean_ctor_set(x_19, 1, x_11);
lean_ctor_set(x_19, 2, x_18);
x_20 = lean_mk_string_unchecked(")", 1, 1);
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
static lean_object* _init_l_Lean_Parser_Tactic_withReducible() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("withReducible", 13, 13);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("with_reducible ", 15, 15);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_unbox(x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_12);
x_13 = lean_mk_string_unchecked("tacticSeq", 9, 9);
x_14 = l_Lean_Name_mkStr1(x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_16, 0, x_8);
lean_ctor_set(x_16, 1, x_11);
lean_ctor_set(x_16, 2, x_15);
x_17 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_17, 0, x_5);
lean_ctor_set(x_17, 1, x_6);
lean_ctor_set(x_17, 2, x_16);
return x_17;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_withReducibleAndInstances() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("withReducibleAndInstances", 25, 25);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("with_reducible_and_instances ", 29, 29);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_unbox(x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_12);
x_13 = lean_mk_string_unchecked("tacticSeq", 9, 9);
x_14 = l_Lean_Name_mkStr1(x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_16, 0, x_8);
lean_ctor_set(x_16, 1, x_11);
lean_ctor_set(x_16, 2, x_15);
x_17 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_17, 0, x_5);
lean_ctor_set(x_17, 1, x_6);
lean_ctor_set(x_17, 2, x_16);
return x_17;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_withUnfoldingAll() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("withUnfoldingAll", 16, 16);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("with_unfolding_all ", 19, 19);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_unbox(x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_12);
x_13 = lean_mk_string_unchecked("tacticSeq", 9, 9);
x_14 = l_Lean_Name_mkStr1(x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_16, 0, x_8);
lean_ctor_set(x_16, 1, x_11);
lean_ctor_set(x_16, 2, x_15);
x_17 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_17, 0, x_5);
lean_ctor_set(x_17, 1, x_6);
lean_ctor_set(x_17, 2, x_16);
return x_17;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_first() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("first", 5, 5);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("first ", 6, 6);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_unbox(x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_12);
x_13 = lean_mk_string_unchecked("withPosition", 12, 12);
x_14 = l_Lean_Name_mkStr1(x_13);
x_15 = lean_mk_string_unchecked("many1", 5, 5);
x_16 = l_Lean_Name_mkStr1(x_15);
x_17 = lean_mk_string_unchecked("group", 5, 5);
x_18 = l_Lean_Name_mkStr1(x_17);
x_19 = lean_mk_string_unchecked("ppDedent", 8, 8);
x_20 = l_Lean_Name_mkStr1(x_19);
x_21 = lean_mk_string_unchecked("ppLine", 6, 6);
x_22 = l_Lean_Name_mkStr1(x_21);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_mk_string_unchecked("colGe", 5, 5);
x_26 = l_Lean_Name_mkStr1(x_25);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_26);
lean_inc(x_8);
x_28 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_28, 0, x_8);
lean_ctor_set(x_28, 1, x_24);
lean_ctor_set(x_28, 2, x_27);
x_29 = lean_mk_string_unchecked("| ", 2, 2);
x_30 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_30, 0, x_29);
lean_inc(x_8);
x_31 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_31, 0, x_8);
lean_ctor_set(x_31, 1, x_28);
lean_ctor_set(x_31, 2, x_30);
x_32 = lean_mk_string_unchecked("tacticSeq", 9, 9);
x_33 = l_Lean_Name_mkStr1(x_32);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_33);
lean_inc(x_8);
x_35 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_35, 0, x_8);
lean_ctor_set(x_35, 1, x_31);
lean_ctor_set(x_35, 2, x_34);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_18);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_16);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_14);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_39, 0, x_8);
lean_ctor_set(x_39, 1, x_11);
lean_ctor_set(x_39, 2, x_38);
x_40 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_40, 0, x_5);
lean_ctor_set(x_40, 1, x_6);
lean_ctor_set(x_40, 2, x_39);
return x_40;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rotateLeft() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("rotateLeft", 10, 10);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("rotate_left", 11, 11);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_unbox(x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_12);
x_13 = lean_mk_string_unchecked("optional", 8, 8);
x_14 = l_Lean_Name_mkStr1(x_13);
x_15 = lean_mk_string_unchecked("ppSpace", 7, 7);
x_16 = l_Lean_Name_mkStr1(x_15);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_mk_string_unchecked("num", 3, 3);
x_19 = l_Lean_Name_mkStr1(x_18);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
lean_inc(x_8);
x_21 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_21, 0, x_8);
lean_ctor_set(x_21, 1, x_17);
lean_ctor_set(x_21, 2, x_20);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_14);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_23, 0, x_8);
lean_ctor_set(x_23, 1, x_11);
lean_ctor_set(x_23, 2, x_22);
x_24 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_24, 0, x_5);
lean_ctor_set(x_24, 1, x_6);
lean_ctor_set(x_24, 2, x_23);
return x_24;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rotateRight() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("rotateRight", 11, 11);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("rotate_right", 12, 12);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_unbox(x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_12);
x_13 = lean_mk_string_unchecked("optional", 8, 8);
x_14 = l_Lean_Name_mkStr1(x_13);
x_15 = lean_mk_string_unchecked("ppSpace", 7, 7);
x_16 = l_Lean_Name_mkStr1(x_15);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_mk_string_unchecked("num", 3, 3);
x_19 = l_Lean_Name_mkStr1(x_18);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
lean_inc(x_8);
x_21 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_21, 0, x_8);
lean_ctor_set(x_21, 1, x_17);
lean_ctor_set(x_21, 2, x_20);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_14);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_23, 0, x_8);
lean_ctor_set(x_23, 1, x_11);
lean_ctor_set(x_23, 2, x_22);
x_24 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_24, 0, x_5);
lean_ctor_set(x_24, 1, x_6);
lean_ctor_set(x_24, 2, x_23);
return x_24;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticTry__() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("tacticTry_", 10, 10);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("try ", 4, 4);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_unbox(x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_12);
x_13 = lean_mk_string_unchecked("tacticSeq", 9, 9);
x_14 = l_Lean_Name_mkStr1(x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_16, 0, x_8);
lean_ctor_set(x_16, 1, x_11);
lean_ctor_set(x_16, 2, x_15);
x_17 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_17, 0, x_5);
lean_ctor_set(x_17, 1, x_6);
lean_ctor_set(x_17, 2, x_16);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticTry____1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Tactic", 6, 6);
x_7 = lean_mk_string_unchecked("tacticTry_", 10, 10);
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
x_10 = lean_box(1);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = l_Lean_Syntax_getArg(x_1, x_12);
lean_dec(x_1);
x_14 = lean_mk_string_unchecked("tacticSeq", 9, 9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_15 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_14);
x_16 = lean_ctor_get(x_2, 5);
x_17 = lean_box(0);
x_18 = lean_unbox(x_17);
x_19 = l_Lean_SourceInfo_fromRef(x_16, x_18);
x_20 = lean_mk_string_unchecked("first", 5, 5);
lean_inc(x_20);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_21 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_20);
lean_inc(x_19);
x_22 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_20);
x_23 = lean_mk_string_unchecked("null", 4, 4);
x_24 = l_Lean_Name_mkStr1(x_23);
x_25 = lean_mk_string_unchecked("group", 5, 5);
x_26 = l_Lean_Name_mkStr1(x_25);
x_27 = lean_mk_string_unchecked("|", 1, 1);
lean_inc(x_19);
x_28 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_28, 0, x_19);
lean_ctor_set(x_28, 1, x_27);
lean_inc(x_28);
lean_inc(x_26);
lean_inc(x_19);
x_29 = l_Lean_Syntax_node2(x_19, x_26, x_28, x_13);
x_30 = lean_mk_string_unchecked("tacticSeq1Indented", 18, 18);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_31 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_30);
x_32 = lean_mk_string_unchecked("skip", 4, 4);
lean_inc(x_32);
x_33 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_32);
lean_inc(x_19);
x_34 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_34, 0, x_19);
lean_ctor_set(x_34, 1, x_32);
lean_inc(x_19);
x_35 = l_Lean_Syntax_node1(x_19, x_33, x_34);
lean_inc(x_24);
lean_inc(x_19);
x_36 = l_Lean_Syntax_node1(x_19, x_24, x_35);
lean_inc(x_19);
x_37 = l_Lean_Syntax_node1(x_19, x_31, x_36);
lean_inc(x_19);
x_38 = l_Lean_Syntax_node1(x_19, x_15, x_37);
lean_inc(x_19);
x_39 = l_Lean_Syntax_node2(x_19, x_26, x_28, x_38);
lean_inc(x_19);
x_40 = l_Lean_Syntax_node2(x_19, x_24, x_29, x_39);
x_41 = l_Lean_Syntax_node2(x_19, x_21, x_22, x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_3);
return x_42;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticTry____1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticTry____1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tactic___x3c_x3b_x3e__() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("tactic_<;>_", 11, 11);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_mk_string_unchecked("andthen", 7, 7);
x_9 = l_Lean_Name_mkStr1(x_8);
x_10 = lean_mk_string_unchecked(" <;> ", 5, 5);
x_11 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_mk_string_unchecked("tactic", 6, 6);
x_13 = l_Lean_Name_mkStr1(x_12);
x_14 = lean_unsigned_to_nat(2u);
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_16, 0, x_9);
lean_ctor_set(x_16, 1, x_11);
lean_ctor_set(x_16, 2, x_15);
x_17 = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(x_17, 0, x_5);
lean_ctor_set(x_17, 1, x_6);
lean_ctor_set(x_17, 2, x_7);
lean_ctor_set(x_17, 3, x_16);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tactic___x3c_x3b_x3e____1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Tactic", 6, 6);
x_7 = lean_mk_string_unchecked("tactic_<;>_", 11, 11);
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
x_10 = lean_box(1);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Lean_Syntax_getArg(x_1, x_12);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_unsigned_to_nat(2u);
x_16 = l_Lean_Syntax_getArg(x_1, x_15);
x_17 = l_Lean_Syntax_getArg(x_1, x_14);
lean_dec(x_1);
x_18 = lean_ctor_get(x_2, 5);
x_19 = lean_box(0);
x_20 = lean_unbox(x_19);
x_21 = l_Lean_SourceInfo_fromRef(x_18, x_20);
x_22 = lean_mk_string_unchecked("focus", 5, 5);
lean_inc(x_22);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_23 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_22);
lean_inc(x_21);
x_24 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_22);
x_25 = lean_mk_string_unchecked("tacticSeq", 9, 9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_26 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_25);
x_27 = lean_mk_string_unchecked("tacticSeq1Indented", 18, 18);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_28 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_27);
x_29 = lean_mk_string_unchecked("null", 4, 4);
x_30 = l_Lean_Name_mkStr1(x_29);
x_31 = l_Array_mkArray0(lean_box(0));
lean_inc(x_30);
lean_inc(x_21);
x_32 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_32, 0, x_21);
lean_ctor_set(x_32, 1, x_30);
lean_ctor_set(x_32, 2, x_31);
x_33 = lean_mk_string_unchecked("withAnnotateState", 17, 17);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_34 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_33);
x_35 = lean_mk_string_unchecked("with_annotate_state", 19, 19);
lean_inc(x_21);
x_36 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_36, 0, x_21);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_mk_string_unchecked("skip", 4, 4);
lean_inc(x_37);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_38 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_37);
lean_inc(x_21);
x_39 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_39, 0, x_21);
lean_ctor_set(x_39, 1, x_37);
lean_inc(x_21);
x_40 = l_Lean_Syntax_node1(x_21, x_38, x_39);
lean_inc(x_21);
x_41 = l_Lean_Syntax_node3(x_21, x_34, x_36, x_17, x_40);
x_42 = lean_mk_string_unchecked("allGoals", 8, 8);
x_43 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_42);
x_44 = lean_mk_string_unchecked("all_goals", 9, 9);
lean_inc(x_21);
x_45 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_45, 0, x_21);
lean_ctor_set(x_45, 1, x_44);
lean_inc(x_30);
lean_inc(x_21);
x_46 = l_Lean_Syntax_node1(x_21, x_30, x_16);
lean_inc(x_28);
lean_inc(x_21);
x_47 = l_Lean_Syntax_node1(x_21, x_28, x_46);
lean_inc(x_26);
lean_inc(x_21);
x_48 = l_Lean_Syntax_node1(x_21, x_26, x_47);
lean_inc(x_21);
x_49 = l_Lean_Syntax_node2(x_21, x_43, x_45, x_48);
lean_inc(x_32);
lean_inc(x_21);
x_50 = l_Lean_Syntax_node5(x_21, x_30, x_13, x_32, x_41, x_32, x_49);
lean_inc(x_21);
x_51 = l_Lean_Syntax_node1(x_21, x_28, x_50);
lean_inc(x_21);
x_52 = l_Lean_Syntax_node1(x_21, x_26, x_51);
x_53 = l_Lean_Syntax_node2(x_21, x_23, x_24, x_52);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_3);
return x_54;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tactic___x3c_x3b_x3e____1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tactic___x3c_x3b_x3e____1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_fail() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("fail", 4, 4);
lean_inc(x_4);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_10, 0, x_4);
x_11 = lean_unbox(x_9);
lean_ctor_set_uint8(x_10, sizeof(void*)*1, x_11);
x_12 = lean_mk_string_unchecked("optional", 8, 8);
x_13 = l_Lean_Name_mkStr1(x_12);
x_14 = lean_mk_string_unchecked("ppSpace", 7, 7);
x_15 = l_Lean_Name_mkStr1(x_14);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_mk_string_unchecked("str", 3, 3);
x_18 = l_Lean_Name_mkStr1(x_17);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
lean_inc(x_8);
x_20 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_20, 0, x_8);
lean_ctor_set(x_20, 1, x_16);
lean_ctor_set(x_20, 2, x_19);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_13);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_22, 0, x_8);
lean_ctor_set(x_22, 1, x_10);
lean_ctor_set(x_22, 2, x_21);
x_23 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_23, 0, x_5);
lean_ctor_set(x_23, 1, x_6);
lean_ctor_set(x_23, 2, x_22);
return x_23;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_eqRefl() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("eqRefl", 6, 6);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1024u);
x_7 = lean_mk_string_unchecked("eq_refl", 7, 7);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_9, 0, x_7);
x_10 = lean_unbox(x_8);
lean_ctor_set_uint8(x_9, sizeof(void*)*1, x_10);
x_11 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_6);
lean_ctor_set(x_11, 2, x_9);
return x_11;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticRfl() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("tacticRfl", 9, 9);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1024u);
x_7 = lean_mk_string_unchecked("rfl", 3, 3);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_9, 0, x_7);
x_10 = lean_unbox(x_8);
lean_ctor_set_uint8(x_9, sizeof(void*)*1, x_10);
x_11 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_6);
lean_ctor_set(x_11, 2, x_9);
return x_11;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_applyRfl() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("applyRfl", 8, 8);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1024u);
x_7 = lean_mk_string_unchecked("apply_rfl", 9, 9);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_9, 0, x_7);
x_10 = lean_unbox(x_8);
lean_ctor_set_uint8(x_9, sizeof(void*)*1, x_10);
x_11 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_6);
lean_ctor_set(x_11, 2, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticRfl__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Tactic", 6, 6);
x_7 = lean_mk_string_unchecked("tacticRfl", 9, 9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_8 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_7);
x_9 = l_Lean_Syntax_isOfKind(x_1, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_10 = lean_box(1);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_12 = lean_ctor_get(x_2, 5);
x_13 = lean_box(0);
x_14 = lean_unbox(x_13);
x_15 = l_Lean_SourceInfo_fromRef(x_12, x_14);
x_16 = lean_mk_string_unchecked("applyRfl", 8, 8);
x_17 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_16);
x_18 = lean_mk_string_unchecked("apply_rfl", 9, 9);
lean_inc(x_15);
x_19 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_19, 0, x_15);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_Syntax_node1(x_15, x_17, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_3);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticRfl__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticRfl__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticRfl__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Tactic", 6, 6);
x_7 = lean_mk_string_unchecked("tacticRfl", 9, 9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_8 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_7);
x_9 = l_Lean_Syntax_isOfKind(x_1, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_10 = lean_box(1);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_12 = lean_ctor_get(x_2, 5);
x_13 = lean_box(0);
x_14 = lean_unbox(x_13);
x_15 = l_Lean_SourceInfo_fromRef(x_12, x_14);
x_16 = lean_mk_string_unchecked("eqRefl", 6, 6);
x_17 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_16);
x_18 = lean_mk_string_unchecked("eq_refl", 7, 7);
lean_inc(x_15);
x_19 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_19, 0, x_15);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_Syntax_node1(x_15, x_17, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_3);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticRfl__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticRfl__2(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticRfl__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Tactic", 6, 6);
x_7 = lean_mk_string_unchecked("tacticRfl", 9, 9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_8 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_7);
x_9 = l_Lean_Syntax_isOfKind(x_1, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_10 = lean_box(1);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_12 = lean_ctor_get(x_2, 5);
lean_inc(x_12);
x_13 = lean_box(0);
x_14 = lean_unbox(x_13);
x_15 = l_Lean_SourceInfo_fromRef(x_12, x_14);
lean_dec(x_12);
x_16 = lean_ctor_get(x_2, 2);
lean_inc(x_16);
x_17 = lean_ctor_get(x_2, 1);
lean_inc(x_17);
lean_dec(x_2);
x_18 = lean_mk_string_unchecked("exact", 5, 5);
lean_inc(x_18);
x_19 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_18);
lean_inc(x_15);
x_20 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_20, 0, x_15);
lean_ctor_set(x_20, 1, x_18);
x_21 = lean_mk_string_unchecked("HEq.rfl", 7, 7);
x_22 = l_String_toSubstring_x27(x_21);
x_23 = lean_mk_string_unchecked("HEq", 3, 3);
x_24 = lean_mk_string_unchecked("rfl", 3, 3);
x_25 = l_Lean_Name_mkStr2(x_23, x_24);
lean_inc(x_25);
x_26 = l_Lean_addMacroScope(x_17, x_25, x_16);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
lean_inc(x_15);
x_31 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_31, 0, x_15);
lean_ctor_set(x_31, 1, x_22);
lean_ctor_set(x_31, 2, x_26);
lean_ctor_set(x_31, 3, x_30);
x_32 = l_Lean_Syntax_node2(x_15, x_19, x_20, x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_3);
return x_33;
}
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticRfl_x27() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("tacticRfl'", 10, 10);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1024u);
x_7 = lean_mk_string_unchecked("rfl'", 4, 4);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_9, 0, x_7);
x_10 = lean_unbox(x_8);
lean_ctor_set_uint8(x_9, sizeof(void*)*1, x_10);
x_11 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_6);
lean_ctor_set(x_11, 2, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticRfl_x27__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Tactic", 6, 6);
x_7 = lean_mk_string_unchecked("tacticRfl'", 10, 10);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_8 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_7);
x_9 = l_Lean_Syntax_isOfKind(x_1, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_10 = lean_box(1);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_12 = lean_ctor_get(x_2, 5);
lean_inc(x_12);
x_13 = lean_box(0);
x_14 = lean_unbox(x_13);
x_15 = l_Lean_SourceInfo_fromRef(x_12, x_14);
lean_dec(x_12);
x_16 = lean_ctor_get(x_2, 2);
lean_inc(x_16);
x_17 = lean_ctor_get(x_2, 1);
lean_inc(x_17);
lean_dec(x_2);
x_18 = lean_mk_string_unchecked("set_option", 10, 10);
lean_inc(x_18);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_19 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_18);
lean_inc(x_15);
x_20 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_20, 0, x_15);
lean_ctor_set(x_20, 1, x_18);
x_21 = lean_mk_string_unchecked("smartUnfolding", 14, 14);
lean_inc(x_21);
x_22 = l_String_toSubstring_x27(x_21);
x_23 = l_Lean_Name_mkStr1(x_21);
x_24 = l_Lean_addMacroScope(x_17, x_23, x_16);
x_25 = lean_box(0);
lean_inc(x_15);
x_26 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_26, 0, x_15);
lean_ctor_set(x_26, 1, x_22);
lean_ctor_set(x_26, 2, x_24);
lean_ctor_set(x_26, 3, x_25);
x_27 = lean_mk_string_unchecked("null", 4, 4);
x_28 = l_Lean_Name_mkStr1(x_27);
x_29 = l_Array_mkArray0(lean_box(0));
lean_inc(x_28);
lean_inc(x_15);
x_30 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_30, 0, x_15);
lean_ctor_set(x_30, 1, x_28);
lean_ctor_set(x_30, 2, x_29);
x_31 = lean_mk_string_unchecked("false", 5, 5);
lean_inc(x_15);
x_32 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_32, 0, x_15);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_mk_string_unchecked("in", 2, 2);
lean_inc(x_15);
x_34 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_34, 0, x_15);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_mk_string_unchecked("tacticSeq", 9, 9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_36 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_35);
x_37 = lean_mk_string_unchecked("tacticSeq1Indented", 18, 18);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_38 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_37);
x_39 = lean_mk_string_unchecked("withUnfoldingAll", 16, 16);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_40 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_39);
x_41 = lean_mk_string_unchecked("with_unfolding_all", 18, 18);
lean_inc(x_15);
x_42 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_42, 0, x_15);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_mk_string_unchecked("tacticRfl", 9, 9);
x_44 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_43);
x_45 = lean_mk_string_unchecked("rfl", 3, 3);
lean_inc(x_15);
x_46 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_46, 0, x_15);
lean_ctor_set(x_46, 1, x_45);
lean_inc(x_15);
x_47 = l_Lean_Syntax_node1(x_15, x_44, x_46);
lean_inc(x_28);
lean_inc(x_15);
x_48 = l_Lean_Syntax_node1(x_15, x_28, x_47);
lean_inc(x_38);
lean_inc(x_15);
x_49 = l_Lean_Syntax_node1(x_15, x_38, x_48);
lean_inc(x_36);
lean_inc(x_15);
x_50 = l_Lean_Syntax_node1(x_15, x_36, x_49);
lean_inc(x_15);
x_51 = l_Lean_Syntax_node2(x_15, x_40, x_42, x_50);
lean_inc(x_15);
x_52 = l_Lean_Syntax_node1(x_15, x_28, x_51);
lean_inc(x_15);
x_53 = l_Lean_Syntax_node1(x_15, x_38, x_52);
lean_inc(x_15);
x_54 = l_Lean_Syntax_node1(x_15, x_36, x_53);
x_55 = l_Lean_Syntax_node6(x_15, x_19, x_20, x_26, x_30, x_32, x_34, x_54);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_3);
return x_56;
}
}
}
static lean_object* _init_l_Lean_Parser_Tactic_acRfl() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("acRfl", 5, 5);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1024u);
x_7 = lean_mk_string_unchecked("ac_rfl", 6, 6);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_9, 0, x_7);
x_10 = lean_unbox(x_8);
lean_ctor_set_uint8(x_9, sizeof(void*)*1, x_10);
x_11 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_6);
lean_ctor_set(x_11, 2, x_9);
return x_11;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSorry() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("tacticSorry", 11, 11);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1024u);
x_7 = lean_mk_string_unchecked("sorry", 5, 5);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_9, 0, x_7);
x_10 = lean_unbox(x_8);
lean_ctor_set_uint8(x_9, sizeof(void*)*1, x_10);
x_11 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_6);
lean_ctor_set(x_11, 2, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticSorry__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Tactic", 6, 6);
x_7 = lean_mk_string_unchecked("tacticSorry", 11, 11);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_8 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_7);
x_9 = l_Lean_Syntax_isOfKind(x_1, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_10 = lean_box(1);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_12 = lean_ctor_get(x_2, 5);
x_13 = lean_box(0);
x_14 = lean_unbox(x_13);
x_15 = l_Lean_SourceInfo_fromRef(x_12, x_14);
x_16 = lean_mk_string_unchecked("exact", 5, 5);
lean_inc(x_16);
lean_inc(x_5);
lean_inc(x_4);
x_17 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_16);
lean_inc(x_15);
x_18 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_16);
x_19 = lean_mk_string_unchecked("Term", 4, 4);
x_20 = lean_mk_string_unchecked("sorry", 5, 5);
lean_inc(x_20);
x_21 = l_Lean_Name_mkStr4(x_4, x_5, x_19, x_20);
lean_inc(x_15);
x_22 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_22, 0, x_15);
lean_ctor_set(x_22, 1, x_20);
lean_inc(x_15);
x_23 = l_Lean_Syntax_node1(x_15, x_21, x_22);
x_24 = l_Lean_Syntax_node2(x_15, x_17, x_18, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_3);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticSorry__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticSorry__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticAdmit() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("tacticAdmit", 11, 11);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1024u);
x_7 = lean_mk_string_unchecked("admit", 5, 5);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_9, 0, x_7);
x_10 = lean_unbox(x_8);
lean_ctor_set_uint8(x_9, sizeof(void*)*1, x_10);
x_11 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_6);
lean_ctor_set(x_11, 2, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticAdmit__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Tactic", 6, 6);
x_7 = lean_mk_string_unchecked("tacticAdmit", 11, 11);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_8 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_7);
x_9 = l_Lean_Syntax_isOfKind(x_1, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_10 = lean_box(1);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_12 = lean_ctor_get(x_2, 5);
x_13 = lean_box(0);
x_14 = lean_unbox(x_13);
x_15 = l_Lean_SourceInfo_fromRef(x_12, x_14);
x_16 = lean_mk_string_unchecked("tacticSorry", 11, 11);
x_17 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_16);
x_18 = lean_mk_string_unchecked("sorry", 5, 5);
lean_inc(x_15);
x_19 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_19, 0, x_15);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_Syntax_node1(x_15, x_17, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_3);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticAdmit__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticAdmit__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticInfer__instance() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("tacticInfer_instance", 20, 20);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1024u);
x_7 = lean_mk_string_unchecked("infer_instance", 14, 14);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_9, 0, x_7);
x_10 = lean_unbox(x_8);
lean_ctor_set_uint8(x_9, sizeof(void*)*1, x_10);
x_11 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_6);
lean_ctor_set(x_11, 2, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticInfer__instance__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Tactic", 6, 6);
x_7 = lean_mk_string_unchecked("tacticInfer_instance", 20, 20);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_8 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_7);
x_9 = l_Lean_Syntax_isOfKind(x_1, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_10 = lean_box(1);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_12 = lean_ctor_get(x_2, 5);
lean_inc(x_12);
x_13 = lean_box(0);
x_14 = lean_unbox(x_13);
x_15 = l_Lean_SourceInfo_fromRef(x_12, x_14);
lean_dec(x_12);
x_16 = lean_ctor_get(x_2, 2);
lean_inc(x_16);
x_17 = lean_ctor_get(x_2, 1);
lean_inc(x_17);
lean_dec(x_2);
x_18 = lean_mk_string_unchecked("exact", 5, 5);
lean_inc(x_18);
x_19 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_18);
lean_inc(x_15);
x_20 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_20, 0, x_15);
lean_ctor_set(x_20, 1, x_18);
x_21 = lean_mk_string_unchecked("inferInstance", 13, 13);
lean_inc(x_21);
x_22 = l_String_toSubstring_x27(x_21);
x_23 = l_Lean_Name_mkStr1(x_21);
lean_inc(x_23);
x_24 = l_Lean_addMacroScope(x_17, x_23, x_16);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
lean_inc(x_15);
x_29 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_29, 0, x_15);
lean_ctor_set(x_29, 1, x_22);
lean_ctor_set(x_29, 2, x_24);
lean_ctor_set(x_29, 3, x_28);
x_30 = l_Lean_Syntax_node2(x_15, x_19, x_20, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_3);
return x_31;
}
}
}
static lean_object* _init_l_Lean_Parser_Tactic_posConfigItem() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_1 = lean_mk_string_unchecked("posConfigItem", 13, 13);
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Tactic", 6, 6);
lean_inc(x_1);
x_5 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_1);
x_6 = lean_mk_string_unchecked("andthen", 7, 7);
x_7 = l_Lean_Name_mkStr1(x_6);
x_8 = lean_mk_string_unchecked(" +", 2, 2);
x_9 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_mk_string_unchecked("noWs", 4, 4);
x_11 = l_Lean_Name_mkStr1(x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
lean_inc(x_7);
x_13 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_9);
lean_ctor_set(x_13, 2, x_12);
x_14 = lean_mk_string_unchecked("ident", 5, 5);
x_15 = l_Lean_Name_mkStr1(x_14);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_17, 0, x_7);
lean_ctor_set(x_17, 1, x_13);
lean_ctor_set(x_17, 2, x_16);
x_18 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_5);
lean_ctor_set(x_18, 2, x_17);
return x_18;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_negConfigItem() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_1 = lean_mk_string_unchecked("negConfigItem", 13, 13);
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Tactic", 6, 6);
lean_inc(x_1);
x_5 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_1);
x_6 = lean_mk_string_unchecked("andthen", 7, 7);
x_7 = l_Lean_Name_mkStr1(x_6);
x_8 = lean_mk_string_unchecked(" -", 2, 2);
x_9 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_mk_string_unchecked("noWs", 4, 4);
x_11 = l_Lean_Name_mkStr1(x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
lean_inc(x_7);
x_13 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_9);
lean_ctor_set(x_13, 2, x_12);
x_14 = lean_mk_string_unchecked("ident", 5, 5);
x_15 = l_Lean_Name_mkStr1(x_14);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_17, 0, x_7);
lean_ctor_set(x_17, 1, x_13);
lean_ctor_set(x_17, 2, x_16);
x_18 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_5);
lean_ctor_set(x_18, 2, x_17);
return x_18;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_valConfigItem() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_1 = lean_mk_string_unchecked("valConfigItem", 13, 13);
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Tactic", 6, 6);
lean_inc(x_1);
x_5 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_1);
x_6 = lean_mk_string_unchecked("andthen", 7, 7);
x_7 = l_Lean_Name_mkStr1(x_6);
x_8 = lean_mk_string_unchecked("atomic", 6, 6);
x_9 = l_Lean_Name_mkStr1(x_8);
x_10 = lean_mk_string_unchecked(" (", 2, 2);
x_11 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_mk_string_unchecked("notFollowedBy", 13, 13);
x_13 = l_Lean_Name_mkStr1(x_12);
x_14 = lean_mk_string_unchecked("orelse", 6, 6);
x_15 = l_Lean_Name_mkStr1(x_14);
x_16 = lean_mk_string_unchecked("discharger", 10, 10);
x_17 = lean_mk_string_unchecked("token", 5, 5);
lean_inc(x_16);
lean_inc(x_17);
x_18 = l_Lean_Name_mkStr2(x_17, x_16);
x_19 = lean_box(0);
lean_inc(x_16);
x_20 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_20, 0, x_16);
x_21 = lean_unbox(x_19);
lean_ctor_set_uint8(x_20, sizeof(void*)*1, x_21);
x_22 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_22, 0, x_16);
lean_ctor_set(x_22, 1, x_18);
lean_ctor_set(x_22, 2, x_20);
x_23 = lean_mk_string_unchecked("disch", 5, 5);
lean_inc(x_23);
lean_inc(x_17);
x_24 = l_Lean_Name_mkStr2(x_17, x_23);
lean_inc(x_23);
x_25 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_25, 0, x_23);
x_26 = lean_unbox(x_19);
lean_ctor_set_uint8(x_25, sizeof(void*)*1, x_26);
x_27 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_27, 0, x_23);
lean_ctor_set(x_27, 1, x_24);
lean_ctor_set(x_27, 2, x_25);
lean_inc(x_15);
x_28 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_28, 0, x_15);
lean_ctor_set(x_28, 1, x_22);
lean_ctor_set(x_28, 2, x_27);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_13);
lean_ctor_set(x_29, 1, x_28);
lean_inc(x_7);
x_30 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_30, 0, x_7);
lean_ctor_set(x_30, 1, x_11);
lean_ctor_set(x_30, 2, x_29);
x_31 = lean_mk_string_unchecked("ident", 5, 5);
x_32 = l_Lean_Name_mkStr1(x_31);
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = lean_mk_string_unchecked("config", 6, 6);
lean_inc(x_34);
x_35 = l_Lean_Name_mkStr2(x_17, x_34);
lean_inc(x_34);
x_36 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_36, 0, x_34);
x_37 = lean_unbox(x_19);
lean_ctor_set_uint8(x_36, sizeof(void*)*1, x_37);
x_38 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_38, 0, x_34);
lean_ctor_set(x_38, 1, x_35);
lean_ctor_set(x_38, 2, x_36);
x_39 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_39, 0, x_15);
lean_ctor_set(x_39, 1, x_33);
lean_ctor_set(x_39, 2, x_38);
lean_inc(x_7);
x_40 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_40, 0, x_7);
lean_ctor_set(x_40, 1, x_30);
lean_ctor_set(x_40, 2, x_39);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_9);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_mk_string_unchecked(" := ", 4, 4);
x_43 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_43, 0, x_42);
lean_inc(x_7);
x_44 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_44, 0, x_7);
lean_ctor_set(x_44, 1, x_41);
lean_ctor_set(x_44, 2, x_43);
x_45 = lean_mk_string_unchecked("withoutPosition", 15, 15);
x_46 = l_Lean_Name_mkStr1(x_45);
x_47 = lean_mk_string_unchecked("term", 4, 4);
x_48 = l_Lean_Name_mkStr1(x_47);
x_49 = lean_unsigned_to_nat(0u);
x_50 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_46);
lean_ctor_set(x_51, 1, x_50);
lean_inc(x_7);
x_52 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_52, 0, x_7);
lean_ctor_set(x_52, 1, x_44);
lean_ctor_set(x_52, 2, x_51);
x_53 = lean_mk_string_unchecked(")", 1, 1);
x_54 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_55 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_55, 0, x_7);
lean_ctor_set(x_55, 1, x_52);
lean_ctor_set(x_55, 2, x_54);
x_56 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_56, 0, x_1);
lean_ctor_set(x_56, 1, x_5);
lean_ctor_set(x_56, 2, x_55);
return x_56;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_configItem() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_1 = lean_mk_string_unchecked("configItem", 10, 10);
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Tactic", 6, 6);
lean_inc(x_1);
x_5 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_1);
x_6 = lean_mk_string_unchecked("orelse", 6, 6);
x_7 = l_Lean_Name_mkStr1(x_6);
x_8 = l_Lean_Parser_Tactic_posConfigItem;
x_9 = l_Lean_Parser_Tactic_negConfigItem;
x_10 = l_Lean_Parser_Tactic_valConfigItem;
lean_inc(x_7);
x_11 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_9);
lean_ctor_set(x_11, 2, x_10);
x_12 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set(x_12, 1, x_8);
lean_ctor_set(x_12, 2, x_11);
x_13 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_5);
lean_ctor_set(x_13, 2, x_12);
return x_13;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_optConfig() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_1 = lean_mk_string_unchecked("optConfig", 9, 9);
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Tactic", 6, 6);
lean_inc(x_1);
x_5 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_1);
x_6 = lean_mk_string_unchecked("many", 4, 4);
x_7 = l_Lean_Name_mkStr1(x_6);
x_8 = lean_mk_string_unchecked("andthen", 7, 7);
x_9 = l_Lean_Name_mkStr1(x_8);
x_10 = lean_mk_string_unchecked("colGt", 5, 5);
x_11 = l_Lean_Name_mkStr1(x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = l_Lean_Parser_Tactic_configItem;
x_14 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_14, 0, x_9);
lean_ctor_set(x_14, 1, x_12);
lean_ctor_set(x_14, 2, x_13);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_5);
lean_ctor_set(x_16, 2, x_15);
return x_16;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_config() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_1 = lean_mk_string_unchecked("config", 6, 6);
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Tactic", 6, 6);
lean_inc(x_1);
x_5 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_1);
x_6 = lean_mk_string_unchecked("andthen", 7, 7);
x_7 = l_Lean_Name_mkStr1(x_6);
x_8 = lean_mk_string_unchecked("atomic", 6, 6);
x_9 = l_Lean_Name_mkStr1(x_8);
x_10 = lean_mk_string_unchecked(" (", 2, 2);
x_11 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_box(0);
lean_inc(x_1);
x_13 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_13, 0, x_1);
x_14 = lean_unbox(x_12);
lean_ctor_set_uint8(x_13, sizeof(void*)*1, x_14);
lean_inc(x_7);
x_15 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_11);
lean_ctor_set(x_15, 2, x_13);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_9);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_mk_string_unchecked(" := ", 4, 4);
x_18 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_18, 0, x_17);
lean_inc(x_7);
x_19 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_19, 0, x_7);
lean_ctor_set(x_19, 1, x_16);
lean_ctor_set(x_19, 2, x_18);
x_20 = lean_mk_string_unchecked("withoutPosition", 15, 15);
x_21 = l_Lean_Name_mkStr1(x_20);
x_22 = lean_mk_string_unchecked("term", 4, 4);
x_23 = l_Lean_Name_mkStr1(x_22);
x_24 = lean_unsigned_to_nat(0u);
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_21);
lean_ctor_set(x_26, 1, x_25);
lean_inc(x_7);
x_27 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_27, 0, x_7);
lean_ctor_set(x_27, 1, x_19);
lean_ctor_set(x_27, 2, x_26);
x_28 = lean_mk_string_unchecked(")", 1, 1);
x_29 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_30, 0, x_7);
lean_ctor_set(x_30, 1, x_27);
lean_ctor_set(x_30, 2, x_29);
x_31 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_31, 0, x_1);
lean_ctor_set(x_31, 1, x_5);
lean_ctor_set(x_31, 2, x_30);
return x_31;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_locationWildcard() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_1 = lean_mk_string_unchecked("locationWildcard", 16, 16);
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Tactic", 6, 6);
lean_inc(x_1);
x_5 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_1);
x_6 = lean_mk_string_unchecked(" *", 2, 2);
x_7 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_5);
lean_ctor_set(x_8, 2, x_7);
return x_8;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_locationType() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_1 = lean_mk_string_unchecked("locationType", 12, 12);
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Tactic", 6, 6);
lean_inc(x_1);
x_5 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_1);
x_6 = lean_mk_string_unchecked("patternIgnore", 13, 13);
x_7 = l_Lean_Name_mkStr1(x_6);
x_8 = lean_mk_string_unchecked("orelse", 6, 6);
x_9 = l_Lean_Name_mkStr1(x_8);
x_10 = lean_mk_string_unchecked("group", 5, 5);
x_11 = l_Lean_Name_mkStr1(x_10);
x_12 = lean_mk_string_unchecked("atomic", 6, 6);
x_13 = l_Lean_Name_mkStr1(x_12);
x_14 = lean_mk_string_unchecked("andthen", 7, 7);
x_15 = l_Lean_Name_mkStr1(x_14);
x_16 = lean_mk_string_unchecked("|", 1, 1);
x_17 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_mk_string_unchecked("noWs", 4, 4);
x_19 = l_Lean_Name_mkStr1(x_18);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
lean_inc(x_15);
x_21 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_21, 0, x_15);
lean_ctor_set(x_21, 1, x_17);
lean_ctor_set(x_21, 2, x_20);
x_22 = lean_mk_string_unchecked("-", 1, 1);
x_23 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_24, 0, x_15);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 2, x_23);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_13);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_11);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_mk_string_unchecked("⊢", 3, 1);
x_28 = lean_mk_string_unchecked("token", 5, 5);
lean_inc(x_27);
x_29 = l_Lean_Name_mkStr2(x_28, x_27);
lean_inc(x_27);
x_30 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_30, 0, x_27);
x_31 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_31, 0, x_27);
lean_ctor_set(x_31, 1, x_29);
lean_ctor_set(x_31, 2, x_30);
x_32 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_32, 0, x_9);
lean_ctor_set(x_32, 1, x_26);
lean_ctor_set(x_32, 2, x_31);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_7);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_34, 0, x_1);
lean_ctor_set(x_34, 1, x_5);
lean_ctor_set(x_34, 2, x_33);
return x_34;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_locationHyp() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_1 = lean_mk_string_unchecked("locationHyp", 11, 11);
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Tactic", 6, 6);
lean_inc(x_1);
x_5 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_1);
x_6 = lean_mk_string_unchecked("many1", 5, 5);
x_7 = l_Lean_Name_mkStr1(x_6);
x_8 = lean_mk_string_unchecked("andthen", 7, 7);
x_9 = l_Lean_Name_mkStr1(x_8);
x_10 = lean_mk_string_unchecked("ppSpace", 7, 7);
x_11 = l_Lean_Name_mkStr1(x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_mk_string_unchecked("colGt", 5, 5);
x_14 = l_Lean_Name_mkStr1(x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
lean_inc(x_9);
x_16 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_16, 0, x_9);
lean_ctor_set(x_16, 1, x_12);
lean_ctor_set(x_16, 2, x_15);
x_17 = lean_mk_string_unchecked("orelse", 6, 6);
x_18 = l_Lean_Name_mkStr1(x_17);
x_19 = lean_mk_string_unchecked("term", 4, 4);
x_20 = l_Lean_Name_mkStr1(x_19);
x_21 = lean_unsigned_to_nat(1024u);
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_Parser_Tactic_locationType;
x_24 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_24, 0, x_18);
lean_ctor_set(x_24, 1, x_22);
lean_ctor_set(x_24, 2, x_23);
x_25 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_25, 0, x_9);
lean_ctor_set(x_25, 1, x_16);
lean_ctor_set(x_25, 2, x_24);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_7);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_27, 0, x_1);
lean_ctor_set(x_27, 1, x_5);
lean_ctor_set(x_27, 2, x_26);
return x_27;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_location() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_1 = lean_mk_string_unchecked("location", 8, 8);
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Tactic", 6, 6);
lean_inc(x_1);
x_5 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_1);
x_6 = lean_mk_string_unchecked("withPosition", 12, 12);
x_7 = l_Lean_Name_mkStr1(x_6);
x_8 = lean_mk_string_unchecked("ppGroup", 7, 7);
x_9 = l_Lean_Name_mkStr1(x_8);
x_10 = lean_mk_string_unchecked("andthen", 7, 7);
x_11 = l_Lean_Name_mkStr1(x_10);
x_12 = lean_mk_string_unchecked(" at", 3, 3);
x_13 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_mk_string_unchecked("orelse", 6, 6);
x_15 = l_Lean_Name_mkStr1(x_14);
x_16 = l_Lean_Parser_Tactic_locationWildcard;
x_17 = l_Lean_Parser_Tactic_locationHyp;
x_18 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_16);
lean_ctor_set(x_18, 2, x_17);
x_19 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_19, 0, x_11);
lean_ctor_set(x_19, 1, x_13);
lean_ctor_set(x_19, 2, x_18);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_9);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_7);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_22, 0, x_1);
lean_ctor_set(x_22, 1, x_5);
lean_ctor_set(x_22, 2, x_21);
return x_22;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_change() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("change", 6, 6);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("change ", 7, 7);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_unbox(x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_12);
x_13 = lean_mk_string_unchecked("term", 4, 4);
x_14 = l_Lean_Name_mkStr1(x_13);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
lean_inc(x_8);
x_17 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_17, 0, x_8);
lean_ctor_set(x_17, 1, x_11);
lean_ctor_set(x_17, 2, x_16);
x_18 = lean_mk_string_unchecked("optional", 8, 8);
x_19 = l_Lean_Name_mkStr1(x_18);
x_20 = l_Lean_Parser_Tactic_location;
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_22, 0, x_8);
lean_ctor_set(x_22, 1, x_17);
lean_ctor_set(x_22, 2, x_21);
x_23 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_23, 0, x_5);
lean_ctor_set(x_23, 1, x_6);
lean_ctor_set(x_23, 2, x_22);
return x_23;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_changeWith() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("changeWith", 10, 10);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("change ", 7, 7);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_unbox(x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_12);
x_13 = lean_mk_string_unchecked("term", 4, 4);
x_14 = l_Lean_Name_mkStr1(x_13);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
lean_inc(x_16);
lean_inc(x_8);
x_17 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_17, 0, x_8);
lean_ctor_set(x_17, 1, x_11);
lean_ctor_set(x_17, 2, x_16);
x_18 = lean_mk_string_unchecked(" with ", 6, 6);
x_19 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_19, 0, x_18);
lean_inc(x_8);
x_20 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_20, 0, x_8);
lean_ctor_set(x_20, 1, x_17);
lean_ctor_set(x_20, 2, x_19);
lean_inc(x_8);
x_21 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_21, 0, x_8);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set(x_21, 2, x_16);
x_22 = lean_mk_string_unchecked("optional", 8, 8);
x_23 = l_Lean_Name_mkStr1(x_22);
x_24 = l_Lean_Parser_Tactic_location;
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_26, 0, x_8);
lean_ctor_set(x_26, 1, x_21);
lean_ctor_set(x_26, 2, x_25);
x_27 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_27, 0, x_5);
lean_ctor_set(x_27, 1, x_6);
lean_ctor_set(x_27, 2, x_26);
return x_27;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_extractLets() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("extractLets", 11, 11);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("extract_lets ", 13, 13);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_unbox(x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_12);
x_13 = l_Lean_Parser_Tactic_optConfig;
lean_inc(x_8);
x_14 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_14, 0, x_8);
lean_ctor_set(x_14, 1, x_11);
lean_ctor_set(x_14, 2, x_13);
x_15 = lean_mk_string_unchecked("many", 4, 4);
x_16 = l_Lean_Name_mkStr1(x_15);
x_17 = lean_mk_string_unchecked("ppSpace", 7, 7);
x_18 = l_Lean_Name_mkStr1(x_17);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_mk_string_unchecked("colGt", 5, 5);
x_21 = l_Lean_Name_mkStr1(x_20);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
lean_inc(x_8);
x_23 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_23, 0, x_8);
lean_ctor_set(x_23, 1, x_19);
lean_ctor_set(x_23, 2, x_22);
x_24 = lean_mk_string_unchecked("orelse", 6, 6);
x_25 = l_Lean_Name_mkStr1(x_24);
x_26 = lean_mk_string_unchecked("ident", 5, 5);
x_27 = l_Lean_Name_mkStr1(x_26);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = lean_mk_string_unchecked("hole", 4, 4);
x_30 = l_Lean_Name_mkStr1(x_29);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_32, 0, x_25);
lean_ctor_set(x_32, 1, x_28);
lean_ctor_set(x_32, 2, x_31);
lean_inc(x_8);
x_33 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_33, 0, x_8);
lean_ctor_set(x_33, 1, x_23);
lean_ctor_set(x_33, 2, x_32);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_16);
lean_ctor_set(x_34, 1, x_33);
lean_inc(x_8);
x_35 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_35, 0, x_8);
lean_ctor_set(x_35, 1, x_14);
lean_ctor_set(x_35, 2, x_34);
x_36 = lean_mk_string_unchecked("optional", 8, 8);
x_37 = l_Lean_Name_mkStr1(x_36);
x_38 = l_Lean_Parser_Tactic_location;
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_40, 0, x_8);
lean_ctor_set(x_40, 1, x_35);
lean_ctor_set(x_40, 2, x_39);
x_41 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_41, 0, x_5);
lean_ctor_set(x_41, 1, x_6);
lean_ctor_set(x_41, 2, x_40);
return x_41;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_liftLets() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("liftLets", 8, 8);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("lift_lets ", 10, 10);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_unbox(x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_12);
x_13 = l_Lean_Parser_Tactic_optConfig;
lean_inc(x_8);
x_14 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_14, 0, x_8);
lean_ctor_set(x_14, 1, x_11);
lean_ctor_set(x_14, 2, x_13);
x_15 = lean_mk_string_unchecked("optional", 8, 8);
x_16 = l_Lean_Name_mkStr1(x_15);
x_17 = l_Lean_Parser_Tactic_location;
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_19, 0, x_8);
lean_ctor_set(x_19, 1, x_14);
lean_ctor_set(x_19, 2, x_18);
x_20 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_20, 0, x_5);
lean_ctor_set(x_20, 1, x_6);
lean_ctor_set(x_20, 2, x_19);
return x_20;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rwRule() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_1 = lean_mk_string_unchecked("rwRule", 6, 6);
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Tactic", 6, 6);
lean_inc(x_1);
x_5 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_1);
x_6 = lean_mk_string_unchecked("andthen", 7, 7);
x_7 = l_Lean_Name_mkStr1(x_6);
x_8 = lean_mk_string_unchecked("optional", 8, 8);
x_9 = l_Lean_Name_mkStr1(x_8);
x_10 = lean_mk_string_unchecked("patternIgnore", 13, 13);
x_11 = l_Lean_Name_mkStr1(x_10);
x_12 = lean_mk_string_unchecked("orelse", 6, 6);
x_13 = l_Lean_Name_mkStr1(x_12);
x_14 = lean_mk_string_unchecked("← ", 4, 2);
x_15 = lean_mk_string_unchecked("token", 5, 5);
lean_inc(x_14);
lean_inc(x_15);
x_16 = l_Lean_Name_mkStr2(x_15, x_14);
lean_inc(x_14);
x_17 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_17, 0, x_14);
x_18 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_18, 0, x_14);
lean_ctor_set(x_18, 1, x_16);
lean_ctor_set(x_18, 2, x_17);
x_19 = lean_mk_string_unchecked("<- ", 3, 3);
lean_inc(x_19);
x_20 = l_Lean_Name_mkStr2(x_15, x_19);
lean_inc(x_19);
x_21 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_21, 0, x_19);
x_22 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_20);
lean_ctor_set(x_22, 2, x_21);
x_23 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_23, 0, x_13);
lean_ctor_set(x_23, 1, x_18);
lean_ctor_set(x_23, 2, x_22);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_11);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_9);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_mk_string_unchecked("term", 4, 4);
x_27 = l_Lean_Name_mkStr1(x_26);
x_28 = lean_unsigned_to_nat(0u);
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_30, 0, x_7);
lean_ctor_set(x_30, 1, x_25);
lean_ctor_set(x_30, 2, x_29);
x_31 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_31, 0, x_1);
lean_ctor_set(x_31, 1, x_5);
lean_ctor_set(x_31, 2, x_30);
return x_31;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rwRuleSeq() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_1 = lean_mk_string_unchecked("rwRuleSeq", 9, 9);
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Tactic", 6, 6);
lean_inc(x_1);
x_5 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_1);
x_6 = lean_mk_string_unchecked("andthen", 7, 7);
x_7 = l_Lean_Name_mkStr1(x_6);
x_8 = lean_mk_string_unchecked(" [", 2, 2);
x_9 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_mk_string_unchecked("withoutPosition", 15, 15);
x_11 = l_Lean_Name_mkStr1(x_10);
x_12 = l_Lean_Parser_Tactic_rwRule;
x_13 = lean_mk_string_unchecked(",", 1, 1);
x_14 = lean_mk_string_unchecked(", ", 2, 2);
x_15 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_box(1);
x_17 = lean_alloc_ctor(10, 3, 1);
lean_ctor_set(x_17, 0, x_12);
lean_ctor_set(x_17, 1, x_13);
lean_ctor_set(x_17, 2, x_15);
x_18 = lean_unbox(x_16);
lean_ctor_set_uint8(x_17, sizeof(void*)*3, x_18);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_11);
lean_ctor_set(x_19, 1, x_17);
lean_inc(x_7);
x_20 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_20, 0, x_7);
lean_ctor_set(x_20, 1, x_9);
lean_ctor_set(x_20, 2, x_19);
x_21 = lean_mk_string_unchecked("]", 1, 1);
x_22 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_23, 0, x_7);
lean_ctor_set(x_23, 1, x_20);
lean_ctor_set(x_23, 2, x_22);
x_24 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_24, 0, x_1);
lean_ctor_set(x_24, 1, x_5);
lean_ctor_set(x_24, 2, x_23);
return x_24;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rewriteSeq() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("rewriteSeq", 10, 10);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("rewrite", 7, 7);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_unbox(x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_12);
x_13 = l_Lean_Parser_Tactic_optConfig;
lean_inc(x_8);
x_14 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_14, 0, x_8);
lean_ctor_set(x_14, 1, x_11);
lean_ctor_set(x_14, 2, x_13);
x_15 = l_Lean_Parser_Tactic_rwRuleSeq;
lean_inc(x_8);
x_16 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_16, 0, x_8);
lean_ctor_set(x_16, 1, x_14);
lean_ctor_set(x_16, 2, x_15);
x_17 = lean_mk_string_unchecked("optional", 8, 8);
x_18 = l_Lean_Name_mkStr1(x_17);
x_19 = l_Lean_Parser_Tactic_location;
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_21, 0, x_8);
lean_ctor_set(x_21, 1, x_16);
lean_ctor_set(x_21, 2, x_20);
x_22 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_22, 0, x_5);
lean_ctor_set(x_22, 1, x_6);
lean_ctor_set(x_22, 2, x_21);
return x_22;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rwSeq() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("rwSeq", 5, 5);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("rw ", 3, 3);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_unbox(x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_12);
x_13 = l_Lean_Parser_Tactic_optConfig;
lean_inc(x_8);
x_14 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_14, 0, x_8);
lean_ctor_set(x_14, 1, x_11);
lean_ctor_set(x_14, 2, x_13);
x_15 = l_Lean_Parser_Tactic_rwRuleSeq;
lean_inc(x_8);
x_16 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_16, 0, x_8);
lean_ctor_set(x_16, 1, x_14);
lean_ctor_set(x_16, 2, x_15);
x_17 = lean_mk_string_unchecked("optional", 8, 8);
x_18 = l_Lean_Name_mkStr1(x_17);
x_19 = l_Lean_Parser_Tactic_location;
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_21, 0, x_8);
lean_ctor_set(x_21, 1, x_16);
lean_ctor_set(x_21, 2, x_20);
x_22 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_22, 0, x_5);
lean_ctor_set(x_22, 1, x_6);
lean_ctor_set(x_22, 2, x_21);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__rwSeq__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Tactic", 6, 6);
x_7 = lean_mk_string_unchecked("rwSeq", 5, 5);
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
x_10 = lean_box(1);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = l_Lean_Syntax_getArg(x_1, x_12);
x_73 = lean_unsigned_to_nat(2u);
x_74 = l_Lean_Syntax_getArg(x_1, x_73);
x_120 = lean_unsigned_to_nat(3u);
x_121 = l_Lean_Syntax_getArg(x_1, x_120);
lean_dec(x_1);
x_122 = l_Lean_Syntax_getOptional_x3f(x_121);
lean_dec(x_121);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; 
x_123 = lean_box(0);
x_75 = x_123;
goto block_119;
}
else
{
uint8_t x_124; 
x_124 = !lean_is_exclusive(x_122);
if (x_124 == 0)
{
x_75 = x_122;
goto block_119;
}
else
{
lean_object* x_125; lean_object* x_126; 
x_125 = lean_ctor_get(x_122, 0);
lean_inc(x_125);
lean_dec(x_122);
x_126 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_126, 0, x_125);
x_75 = x_126;
goto block_119;
}
}
block_72:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_26 = l_Array_appendCore___redArg(x_14, x_25);
lean_dec(x_25);
lean_inc(x_21);
lean_inc(x_24);
x_27 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_21);
lean_ctor_set(x_27, 2, x_26);
lean_inc(x_24);
x_28 = l_Lean_Syntax_node4(x_24, x_19, x_20, x_13, x_17, x_27);
x_29 = lean_mk_string_unchecked(";", 1, 1);
lean_inc(x_24);
x_30 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_30, 0, x_24);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_mk_string_unchecked("withAnnotateState", 17, 17);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_32 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_31);
x_33 = lean_mk_string_unchecked("with_annotate_state", 19, 19);
lean_inc(x_24);
x_34 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_34, 0, x_24);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_mk_string_unchecked("tacticTry_", 10, 10);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_36 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_35);
x_37 = lean_mk_string_unchecked("try", 3, 3);
lean_inc(x_24);
x_38 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_38, 0, x_24);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_mk_string_unchecked("withReducible", 13, 13);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_40 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_39);
x_41 = lean_mk_string_unchecked("with_reducible", 14, 14);
lean_inc(x_24);
x_42 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_42, 0, x_24);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_mk_string_unchecked("tacticRfl", 9, 9);
x_44 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_43);
x_45 = lean_mk_string_unchecked("rfl", 3, 3);
lean_inc(x_24);
x_46 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_46, 0, x_24);
lean_ctor_set(x_46, 1, x_45);
lean_inc(x_24);
x_47 = l_Lean_Syntax_node1(x_24, x_44, x_46);
lean_inc(x_21);
lean_inc(x_24);
x_48 = l_Lean_Syntax_node1(x_24, x_21, x_47);
lean_inc(x_23);
lean_inc(x_24);
x_49 = l_Lean_Syntax_node1(x_24, x_23, x_48);
lean_inc(x_22);
lean_inc(x_24);
x_50 = l_Lean_Syntax_node1(x_24, x_22, x_49);
lean_inc(x_24);
x_51 = l_Lean_Syntax_node2(x_24, x_40, x_42, x_50);
lean_inc(x_21);
lean_inc(x_24);
x_52 = l_Lean_Syntax_node1(x_24, x_21, x_51);
lean_inc(x_23);
lean_inc(x_24);
x_53 = l_Lean_Syntax_node1(x_24, x_23, x_52);
lean_inc(x_22);
lean_inc(x_24);
x_54 = l_Lean_Syntax_node1(x_24, x_22, x_53);
x_55 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_24);
x_56 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_56, 0, x_24);
lean_ctor_set(x_56, 1, x_55);
lean_inc(x_56);
lean_inc(x_18);
lean_inc(x_16);
lean_inc(x_24);
x_57 = l_Lean_Syntax_node3(x_24, x_16, x_18, x_54, x_56);
lean_inc(x_21);
lean_inc(x_24);
x_58 = l_Lean_Syntax_node1(x_24, x_21, x_57);
lean_inc(x_23);
lean_inc(x_24);
x_59 = l_Lean_Syntax_node1(x_24, x_23, x_58);
lean_inc(x_22);
lean_inc(x_24);
x_60 = l_Lean_Syntax_node1(x_24, x_22, x_59);
lean_inc(x_24);
x_61 = l_Lean_Syntax_node2(x_24, x_36, x_38, x_60);
lean_inc(x_21);
lean_inc(x_24);
x_62 = l_Lean_Syntax_node1(x_24, x_21, x_61);
lean_inc(x_23);
lean_inc(x_24);
x_63 = l_Lean_Syntax_node1(x_24, x_23, x_62);
lean_inc(x_22);
lean_inc(x_24);
x_64 = l_Lean_Syntax_node1(x_24, x_22, x_63);
lean_inc(x_56);
lean_inc(x_18);
lean_inc(x_16);
lean_inc(x_24);
x_65 = l_Lean_Syntax_node3(x_24, x_16, x_18, x_64, x_56);
lean_inc(x_24);
x_66 = l_Lean_Syntax_node3(x_24, x_32, x_34, x_15, x_65);
lean_inc(x_24);
x_67 = l_Lean_Syntax_node3(x_24, x_21, x_28, x_30, x_66);
lean_inc(x_24);
x_68 = l_Lean_Syntax_node1(x_24, x_23, x_67);
lean_inc(x_24);
x_69 = l_Lean_Syntax_node1(x_24, x_22, x_68);
x_70 = l_Lean_Syntax_node3(x_24, x_16, x_18, x_69, x_56);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_3);
return x_71;
}
block_119:
{
lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_76 = lean_mk_string_unchecked("rwRuleSeq", 9, 9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_77 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_76);
lean_inc(x_74);
x_78 = l_Lean_Syntax_isOfKind(x_74, x_77);
if (x_78 == 0)
{
lean_object* x_79; uint8_t x_80; 
lean_dec(x_77);
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_79 = l_Lean_Macro_throwUnsupported(lean_box(0), x_2, x_3);
x_80 = !lean_is_exclusive(x_79);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_79, 0);
lean_dec(x_81);
x_82 = lean_box(1);
lean_ctor_set(x_79, 0, x_82);
return x_79;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_79, 1);
lean_inc(x_83);
lean_dec(x_79);
x_84 = lean_box(1);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_83);
return x_85;
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_86 = l_Lean_Syntax_getArg(x_74, x_12);
x_87 = l_Lean_Syntax_getArg(x_74, x_73);
lean_dec(x_74);
x_88 = l_Lean_Syntax_getArgs(x_86);
lean_dec(x_86);
x_89 = lean_ctor_get(x_2, 5);
x_90 = lean_box(0);
x_91 = lean_unbox(x_90);
x_92 = l_Lean_SourceInfo_fromRef(x_89, x_91);
x_93 = lean_mk_string_unchecked("paren", 5, 5);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_94 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_93);
x_95 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_92);
x_96 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_96, 0, x_92);
lean_ctor_set(x_96, 1, x_95);
x_97 = lean_mk_string_unchecked("tacticSeq", 9, 9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_98 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_97);
x_99 = lean_mk_string_unchecked("tacticSeq1Indented", 18, 18);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_100 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_99);
x_101 = lean_mk_string_unchecked("null", 4, 4);
x_102 = l_Lean_Name_mkStr1(x_101);
x_103 = lean_mk_string_unchecked("rewriteSeq", 10, 10);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_104 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_103);
x_105 = lean_mk_string_unchecked("rewrite", 7, 7);
lean_inc(x_92);
x_106 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_106, 0, x_92);
lean_ctor_set(x_106, 1, x_105);
x_107 = lean_mk_string_unchecked("[", 1, 1);
lean_inc(x_92);
x_108 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_108, 0, x_92);
lean_ctor_set(x_108, 1, x_107);
x_109 = l_Array_mkArray0(lean_box(0));
lean_inc(x_109);
x_110 = l_Array_appendCore___redArg(x_109, x_88);
lean_dec(x_88);
lean_inc(x_102);
lean_inc(x_92);
x_111 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_111, 0, x_92);
lean_ctor_set(x_111, 1, x_102);
lean_ctor_set(x_111, 2, x_110);
x_112 = lean_mk_string_unchecked("]", 1, 1);
lean_inc(x_92);
x_113 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_113, 0, x_92);
lean_ctor_set(x_113, 1, x_112);
lean_inc(x_92);
x_114 = l_Lean_Syntax_node3(x_92, x_77, x_108, x_111, x_113);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_115; 
x_115 = l_Array_empty(lean_box(0));
x_14 = x_109;
x_15 = x_87;
x_16 = x_94;
x_17 = x_114;
x_18 = x_96;
x_19 = x_104;
x_20 = x_106;
x_21 = x_102;
x_22 = x_98;
x_23 = x_100;
x_24 = x_92;
x_25 = x_115;
goto block_72;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_75, 0);
lean_inc(x_116);
lean_dec(x_75);
x_117 = l_Array_empty(lean_box(0));
x_118 = lean_array_push(x_117, x_116);
x_14 = x_109;
x_15 = x_87;
x_16 = x_94;
x_17 = x_114;
x_18 = x_96;
x_19 = x_104;
x_20 = x_106;
x_21 = x_102;
x_22 = x_98;
x_23 = x_100;
x_24 = x_92;
x_25 = x_118;
goto block_72;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__rwSeq__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__rwSeq__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticRwa____() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("tacticRwa__", 11, 11);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("rwa ", 4, 4);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_unbox(x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_12);
x_13 = l_Lean_Parser_Tactic_rwRuleSeq;
lean_inc(x_8);
x_14 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_14, 0, x_8);
lean_ctor_set(x_14, 1, x_11);
lean_ctor_set(x_14, 2, x_13);
x_15 = lean_mk_string_unchecked("optional", 8, 8);
x_16 = l_Lean_Name_mkStr1(x_15);
x_17 = l_Lean_Parser_Tactic_location;
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_19, 0, x_8);
lean_ctor_set(x_19, 1, x_14);
lean_ctor_set(x_19, 2, x_18);
x_20 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_20, 0, x_5);
lean_ctor_set(x_20, 1, x_6);
lean_ctor_set(x_20, 2, x_19);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticRwa______1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Tactic", 6, 6);
x_7 = lean_mk_string_unchecked("tacticRwa__", 11, 11);
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
x_10 = lean_box(1);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_42; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = l_Lean_Syntax_getArg(x_1, x_12);
x_70 = lean_unsigned_to_nat(2u);
x_71 = l_Lean_Syntax_getArg(x_1, x_70);
lean_dec(x_1);
x_72 = l_Lean_Syntax_getOptional_x3f(x_71);
lean_dec(x_71);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; 
x_73 = lean_box(0);
x_42 = x_73;
goto block_69;
}
else
{
uint8_t x_74; 
x_74 = !lean_is_exclusive(x_72);
if (x_74 == 0)
{
x_42 = x_72;
goto block_69;
}
else
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_72, 0);
lean_inc(x_75);
lean_dec(x_72);
x_76 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_76, 0, x_75);
x_42 = x_76;
goto block_69;
}
}
block_41:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_25 = l_Array_appendCore___redArg(x_23, x_24);
lean_dec(x_24);
lean_inc(x_18);
lean_inc(x_20);
x_26 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_26, 0, x_20);
lean_ctor_set(x_26, 1, x_18);
lean_ctor_set(x_26, 2, x_25);
lean_inc(x_20);
x_27 = l_Lean_Syntax_node4(x_20, x_17, x_22, x_14, x_13, x_26);
x_28 = lean_mk_string_unchecked(";", 1, 1);
lean_inc(x_20);
x_29 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_29, 0, x_20);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_mk_string_unchecked("assumption", 10, 10);
lean_inc(x_30);
x_31 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_30);
lean_inc(x_20);
x_32 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_32, 0, x_20);
lean_ctor_set(x_32, 1, x_30);
lean_inc(x_20);
x_33 = l_Lean_Syntax_node1(x_20, x_31, x_32);
lean_inc(x_20);
x_34 = l_Lean_Syntax_node3(x_20, x_18, x_27, x_29, x_33);
lean_inc(x_20);
x_35 = l_Lean_Syntax_node1(x_20, x_16, x_34);
lean_inc(x_20);
x_36 = l_Lean_Syntax_node1(x_20, x_19, x_35);
x_37 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_20);
x_38 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_38, 0, x_20);
lean_ctor_set(x_38, 1, x_37);
x_39 = l_Lean_Syntax_node3(x_20, x_21, x_15, x_36, x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_3);
return x_40;
}
block_69:
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_43 = lean_ctor_get(x_2, 5);
x_44 = lean_box(0);
x_45 = lean_unbox(x_44);
x_46 = l_Lean_SourceInfo_fromRef(x_43, x_45);
x_47 = lean_mk_string_unchecked("paren", 5, 5);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_48 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_47);
x_49 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_46);
x_50 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_50, 0, x_46);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_mk_string_unchecked("tacticSeq", 9, 9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_52 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_51);
x_53 = lean_mk_string_unchecked("tacticSeq1Indented", 18, 18);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_54 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_53);
x_55 = lean_mk_string_unchecked("null", 4, 4);
x_56 = l_Lean_Name_mkStr1(x_55);
x_57 = lean_mk_string_unchecked("rwSeq", 5, 5);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_58 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_57);
x_59 = lean_mk_string_unchecked("rw", 2, 2);
lean_inc(x_46);
x_60 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_60, 0, x_46);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_mk_string_unchecked("optConfig", 9, 9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_62 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_61);
x_63 = l_Array_mkArray0(lean_box(0));
lean_inc(x_63);
lean_inc(x_56);
lean_inc(x_46);
x_64 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_64, 0, x_46);
lean_ctor_set(x_64, 1, x_56);
lean_ctor_set(x_64, 2, x_63);
lean_inc(x_46);
x_65 = l_Lean_Syntax_node1(x_46, x_62, x_64);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_66; 
x_66 = l_Array_empty(lean_box(0));
x_14 = x_65;
x_15 = x_50;
x_16 = x_54;
x_17 = x_58;
x_18 = x_56;
x_19 = x_52;
x_20 = x_46;
x_21 = x_48;
x_22 = x_60;
x_23 = x_63;
x_24 = x_66;
goto block_41;
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_42, 0);
lean_inc(x_67);
lean_dec(x_42);
x_68 = l_Array_mkArray1___redArg(x_67);
x_14 = x_65;
x_15 = x_50;
x_16 = x_54;
x_17 = x_58;
x_18 = x_56;
x_19 = x_52;
x_20 = x_46;
x_21 = x_48;
x_22 = x_60;
x_23 = x_63;
x_24 = x_68;
goto block_41;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticRwa______1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticRwa______1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_injection() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("injection", 9, 9);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("injection ", 10, 10);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_unbox(x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_12);
x_13 = lean_mk_string_unchecked("term", 4, 4);
x_14 = l_Lean_Name_mkStr1(x_13);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
lean_inc(x_8);
x_17 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_17, 0, x_8);
lean_ctor_set(x_17, 1, x_11);
lean_ctor_set(x_17, 2, x_16);
x_18 = lean_mk_string_unchecked("optional", 8, 8);
x_19 = l_Lean_Name_mkStr1(x_18);
x_20 = lean_mk_string_unchecked(" with", 5, 5);
x_21 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_mk_string_unchecked("many1", 5, 5);
x_23 = l_Lean_Name_mkStr1(x_22);
x_24 = lean_mk_string_unchecked("ppSpace", 7, 7);
x_25 = l_Lean_Name_mkStr1(x_24);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_mk_string_unchecked("colGt", 5, 5);
x_28 = l_Lean_Name_mkStr1(x_27);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_28);
lean_inc(x_8);
x_30 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_30, 0, x_8);
lean_ctor_set(x_30, 1, x_26);
lean_ctor_set(x_30, 2, x_29);
x_31 = lean_mk_string_unchecked("orelse", 6, 6);
x_32 = l_Lean_Name_mkStr1(x_31);
x_33 = lean_mk_string_unchecked("ident", 5, 5);
x_34 = l_Lean_Name_mkStr1(x_33);
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_34);
x_36 = lean_mk_string_unchecked("hole", 4, 4);
x_37 = l_Lean_Name_mkStr1(x_36);
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_37);
x_39 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_39, 0, x_32);
lean_ctor_set(x_39, 1, x_35);
lean_ctor_set(x_39, 2, x_38);
lean_inc(x_8);
x_40 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_40, 0, x_8);
lean_ctor_set(x_40, 1, x_30);
lean_ctor_set(x_40, 2, x_39);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_23);
lean_ctor_set(x_41, 1, x_40);
lean_inc(x_8);
x_42 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_42, 0, x_8);
lean_ctor_set(x_42, 1, x_21);
lean_ctor_set(x_42, 2, x_41);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_19);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_44, 0, x_8);
lean_ctor_set(x_44, 1, x_17);
lean_ctor_set(x_44, 2, x_43);
x_45 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_45, 0, x_5);
lean_ctor_set(x_45, 1, x_6);
lean_ctor_set(x_45, 2, x_44);
return x_45;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_injections() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("injections", 10, 10);
lean_inc(x_4);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_10, 0, x_4);
x_11 = lean_unbox(x_9);
lean_ctor_set_uint8(x_10, sizeof(void*)*1, x_11);
x_12 = lean_mk_string_unchecked("many", 4, 4);
x_13 = l_Lean_Name_mkStr1(x_12);
x_14 = lean_mk_string_unchecked("ppSpace", 7, 7);
x_15 = l_Lean_Name_mkStr1(x_14);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_mk_string_unchecked("colGt", 5, 5);
x_18 = l_Lean_Name_mkStr1(x_17);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
lean_inc(x_8);
x_20 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_20, 0, x_8);
lean_ctor_set(x_20, 1, x_16);
lean_ctor_set(x_20, 2, x_19);
x_21 = lean_mk_string_unchecked("orelse", 6, 6);
x_22 = l_Lean_Name_mkStr1(x_21);
x_23 = lean_mk_string_unchecked("ident", 5, 5);
x_24 = l_Lean_Name_mkStr1(x_23);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_mk_string_unchecked("hole", 4, 4);
x_27 = l_Lean_Name_mkStr1(x_26);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_29, 0, x_22);
lean_ctor_set(x_29, 1, x_25);
lean_ctor_set(x_29, 2, x_28);
lean_inc(x_8);
x_30 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_30, 0, x_8);
lean_ctor_set(x_30, 1, x_20);
lean_ctor_set(x_30, 2, x_29);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_13);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_32, 0, x_8);
lean_ctor_set(x_32, 1, x_10);
lean_ctor_set(x_32, 2, x_31);
x_33 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_33, 0, x_5);
lean_ctor_set(x_33, 1, x_6);
lean_ctor_set(x_33, 2, x_32);
return x_33;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_discharger() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_1 = lean_mk_string_unchecked("discharger", 10, 10);
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Tactic", 6, 6);
lean_inc(x_1);
x_5 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_1);
x_6 = lean_mk_string_unchecked("andthen", 7, 7);
x_7 = l_Lean_Name_mkStr1(x_6);
x_8 = lean_mk_string_unchecked("atomic", 6, 6);
x_9 = l_Lean_Name_mkStr1(x_8);
x_10 = lean_mk_string_unchecked(" (", 2, 2);
x_11 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_mk_string_unchecked("patternIgnore", 13, 13);
x_13 = l_Lean_Name_mkStr1(x_12);
x_14 = lean_mk_string_unchecked("orelse", 6, 6);
x_15 = l_Lean_Name_mkStr1(x_14);
x_16 = lean_mk_string_unchecked("token", 5, 5);
lean_inc(x_1);
lean_inc(x_16);
x_17 = l_Lean_Name_mkStr2(x_16, x_1);
x_18 = lean_box(0);
lean_inc(x_1);
x_19 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_19, 0, x_1);
x_20 = lean_unbox(x_18);
lean_ctor_set_uint8(x_19, sizeof(void*)*1, x_20);
lean_inc(x_1);
x_21 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_21, 0, x_1);
lean_ctor_set(x_21, 1, x_17);
lean_ctor_set(x_21, 2, x_19);
x_22 = lean_mk_string_unchecked("disch", 5, 5);
lean_inc(x_22);
x_23 = l_Lean_Name_mkStr2(x_16, x_22);
lean_inc(x_22);
x_24 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_24, 0, x_22);
x_25 = lean_unbox(x_18);
lean_ctor_set_uint8(x_24, sizeof(void*)*1, x_25);
x_26 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_26, 0, x_22);
lean_ctor_set(x_26, 1, x_23);
lean_ctor_set(x_26, 2, x_24);
x_27 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_27, 0, x_15);
lean_ctor_set(x_27, 1, x_21);
lean_ctor_set(x_27, 2, x_26);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_13);
lean_ctor_set(x_28, 1, x_27);
lean_inc(x_7);
x_29 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_29, 0, x_7);
lean_ctor_set(x_29, 1, x_11);
lean_ctor_set(x_29, 2, x_28);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_9);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_mk_string_unchecked(" := ", 4, 4);
x_32 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_32, 0, x_31);
lean_inc(x_7);
x_33 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_33, 0, x_7);
lean_ctor_set(x_33, 1, x_30);
lean_ctor_set(x_33, 2, x_32);
x_34 = lean_mk_string_unchecked("withoutPosition", 15, 15);
x_35 = l_Lean_Name_mkStr1(x_34);
x_36 = lean_mk_string_unchecked("tacticSeq", 9, 9);
x_37 = l_Lean_Name_mkStr1(x_36);
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_37);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_35);
lean_ctor_set(x_39, 1, x_38);
lean_inc(x_7);
x_40 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_40, 0, x_7);
lean_ctor_set(x_40, 1, x_33);
lean_ctor_set(x_40, 2, x_39);
x_41 = lean_mk_string_unchecked(")", 1, 1);
x_42 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_42, 0, x_41);
x_43 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_43, 0, x_7);
lean_ctor_set(x_43, 1, x_40);
lean_ctor_set(x_43, 2, x_42);
x_44 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_44, 0, x_1);
lean_ctor_set(x_44, 1, x_5);
lean_ctor_set(x_44, 2, x_43);
return x_44;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpPre() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_1 = lean_mk_string_unchecked("simpPre", 7, 7);
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Tactic", 6, 6);
lean_inc(x_1);
x_5 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_1);
x_6 = lean_mk_string_unchecked("↓", 3, 1);
x_7 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_5);
lean_ctor_set(x_8, 2, x_7);
return x_8;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpPost() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_1 = lean_mk_string_unchecked("simpPost", 8, 8);
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Tactic", 6, 6);
lean_inc(x_1);
x_5 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_1);
x_6 = lean_mk_string_unchecked("↑", 3, 1);
x_7 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_5);
lean_ctor_set(x_8, 2, x_7);
return x_8;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpLemma() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_1 = lean_mk_string_unchecked("simpLemma", 9, 9);
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Tactic", 6, 6);
lean_inc(x_1);
x_5 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_1);
x_6 = lean_mk_string_unchecked("andthen", 7, 7);
x_7 = l_Lean_Name_mkStr1(x_6);
x_8 = lean_mk_string_unchecked("optional", 8, 8);
x_9 = l_Lean_Name_mkStr1(x_8);
x_10 = lean_mk_string_unchecked("orelse", 6, 6);
x_11 = l_Lean_Name_mkStr1(x_10);
x_12 = l_Lean_Parser_Tactic_simpPre;
x_13 = l_Lean_Parser_Tactic_simpPost;
lean_inc(x_11);
x_14 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_12);
lean_ctor_set(x_14, 2, x_13);
lean_inc(x_9);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_9);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_mk_string_unchecked("patternIgnore", 13, 13);
x_17 = l_Lean_Name_mkStr1(x_16);
x_18 = lean_mk_string_unchecked("← ", 4, 2);
x_19 = lean_mk_string_unchecked("token", 5, 5);
lean_inc(x_18);
lean_inc(x_19);
x_20 = l_Lean_Name_mkStr2(x_19, x_18);
lean_inc(x_18);
x_21 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_21, 0, x_18);
x_22 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_22, 0, x_18);
lean_ctor_set(x_22, 1, x_20);
lean_ctor_set(x_22, 2, x_21);
x_23 = lean_mk_string_unchecked("<- ", 3, 3);
lean_inc(x_23);
x_24 = l_Lean_Name_mkStr2(x_19, x_23);
lean_inc(x_23);
x_25 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_25, 0, x_23);
x_26 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_24);
lean_ctor_set(x_26, 2, x_25);
x_27 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_27, 0, x_11);
lean_ctor_set(x_27, 1, x_22);
lean_ctor_set(x_27, 2, x_26);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_17);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_9);
lean_ctor_set(x_29, 1, x_28);
lean_inc(x_7);
x_30 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_30, 0, x_7);
lean_ctor_set(x_30, 1, x_15);
lean_ctor_set(x_30, 2, x_29);
x_31 = lean_mk_string_unchecked("term", 4, 4);
x_32 = l_Lean_Name_mkStr1(x_31);
x_33 = lean_unsigned_to_nat(0u);
x_34 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_35, 0, x_7);
lean_ctor_set(x_35, 1, x_30);
lean_ctor_set(x_35, 2, x_34);
x_36 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_36, 0, x_1);
lean_ctor_set(x_36, 1, x_5);
lean_ctor_set(x_36, 2, x_35);
return x_36;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpErase() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_1 = lean_mk_string_unchecked("simpErase", 9, 9);
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Tactic", 6, 6);
lean_inc(x_1);
x_5 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_1);
x_6 = lean_mk_string_unchecked("andthen", 7, 7);
x_7 = l_Lean_Name_mkStr1(x_6);
x_8 = lean_mk_string_unchecked("-", 1, 1);
x_9 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_mk_string_unchecked("term", 4, 4);
x_11 = l_Lean_Name_mkStr1(x_10);
x_12 = lean_unsigned_to_nat(1024u);
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_9);
lean_ctor_set(x_14, 2, x_13);
x_15 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_5);
lean_ctor_set(x_15, 2, x_14);
return x_15;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpStar() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_1 = lean_mk_string_unchecked("simpStar", 8, 8);
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Tactic", 6, 6);
lean_inc(x_1);
x_5 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_1);
x_6 = lean_mk_string_unchecked("*", 1, 1);
x_7 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_5);
lean_ctor_set(x_8, 2, x_7);
return x_8;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simp() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("simp", 4, 4);
lean_inc(x_4);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_10, 0, x_4);
x_11 = lean_unbox(x_9);
lean_ctor_set_uint8(x_10, sizeof(void*)*1, x_11);
x_12 = l_Lean_Parser_Tactic_optConfig;
lean_inc(x_8);
x_13 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_10);
lean_ctor_set(x_13, 2, x_12);
x_14 = lean_mk_string_unchecked("optional", 8, 8);
x_15 = l_Lean_Name_mkStr1(x_14);
x_16 = l_Lean_Parser_Tactic_discharger;
lean_inc(x_15);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
lean_inc(x_8);
x_18 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_18, 0, x_8);
lean_ctor_set(x_18, 1, x_13);
lean_ctor_set(x_18, 2, x_17);
x_19 = lean_mk_string_unchecked(" only", 5, 5);
x_20 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_unbox(x_9);
lean_ctor_set_uint8(x_20, sizeof(void*)*1, x_21);
lean_inc(x_15);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_15);
lean_ctor_set(x_22, 1, x_20);
lean_inc(x_8);
x_23 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_23, 0, x_8);
lean_ctor_set(x_23, 1, x_18);
lean_ctor_set(x_23, 2, x_22);
x_24 = lean_mk_string_unchecked(" [", 2, 2);
x_25 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_mk_string_unchecked("withoutPosition", 15, 15);
x_27 = l_Lean_Name_mkStr1(x_26);
x_28 = lean_mk_string_unchecked("orelse", 6, 6);
x_29 = l_Lean_Name_mkStr1(x_28);
x_30 = l_Lean_Parser_Tactic_simpStar;
x_31 = l_Lean_Parser_Tactic_simpErase;
x_32 = l_Lean_Parser_Tactic_simpLemma;
lean_inc(x_29);
x_33 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_33, 0, x_29);
lean_ctor_set(x_33, 1, x_31);
lean_ctor_set(x_33, 2, x_32);
x_34 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_34, 0, x_29);
lean_ctor_set(x_34, 1, x_30);
lean_ctor_set(x_34, 2, x_33);
x_35 = lean_mk_string_unchecked(",", 1, 1);
x_36 = lean_mk_string_unchecked(", ", 2, 2);
x_37 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = lean_box(1);
x_39 = lean_alloc_ctor(10, 3, 1);
lean_ctor_set(x_39, 0, x_34);
lean_ctor_set(x_39, 1, x_35);
lean_ctor_set(x_39, 2, x_37);
x_40 = lean_unbox(x_38);
lean_ctor_set_uint8(x_39, sizeof(void*)*3, x_40);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_27);
lean_ctor_set(x_41, 1, x_39);
lean_inc(x_8);
x_42 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_42, 0, x_8);
lean_ctor_set(x_42, 1, x_25);
lean_ctor_set(x_42, 2, x_41);
x_43 = lean_mk_string_unchecked("]", 1, 1);
x_44 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_44, 0, x_43);
lean_inc(x_8);
x_45 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_45, 0, x_8);
lean_ctor_set(x_45, 1, x_42);
lean_ctor_set(x_45, 2, x_44);
lean_inc(x_15);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_15);
lean_ctor_set(x_46, 1, x_45);
lean_inc(x_8);
x_47 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_47, 0, x_8);
lean_ctor_set(x_47, 1, x_23);
lean_ctor_set(x_47, 2, x_46);
x_48 = l_Lean_Parser_Tactic_location;
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_15);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_50, 0, x_8);
lean_ctor_set(x_50, 1, x_47);
lean_ctor_set(x_50, 2, x_49);
x_51 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_51, 0, x_5);
lean_ctor_set(x_51, 1, x_6);
lean_ctor_set(x_51, 2, x_50);
return x_51;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpAll() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("simpAll", 7, 7);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("simp_all", 8, 8);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_unbox(x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_12);
x_13 = l_Lean_Parser_Tactic_optConfig;
lean_inc(x_8);
x_14 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_14, 0, x_8);
lean_ctor_set(x_14, 1, x_11);
lean_ctor_set(x_14, 2, x_13);
x_15 = lean_mk_string_unchecked("optional", 8, 8);
x_16 = l_Lean_Name_mkStr1(x_15);
x_17 = l_Lean_Parser_Tactic_discharger;
lean_inc(x_16);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
lean_inc(x_8);
x_19 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_19, 0, x_8);
lean_ctor_set(x_19, 1, x_14);
lean_ctor_set(x_19, 2, x_18);
x_20 = lean_mk_string_unchecked(" only", 5, 5);
x_21 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_unbox(x_10);
lean_ctor_set_uint8(x_21, sizeof(void*)*1, x_22);
lean_inc(x_16);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_16);
lean_ctor_set(x_23, 1, x_21);
lean_inc(x_8);
x_24 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_24, 0, x_8);
lean_ctor_set(x_24, 1, x_19);
lean_ctor_set(x_24, 2, x_23);
x_25 = lean_mk_string_unchecked(" [", 2, 2);
x_26 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_mk_string_unchecked("withoutPosition", 15, 15);
x_28 = l_Lean_Name_mkStr1(x_27);
x_29 = lean_mk_string_unchecked("orelse", 6, 6);
x_30 = l_Lean_Name_mkStr1(x_29);
x_31 = l_Lean_Parser_Tactic_simpErase;
x_32 = l_Lean_Parser_Tactic_simpLemma;
x_33 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_31);
lean_ctor_set(x_33, 2, x_32);
x_34 = lean_mk_string_unchecked(",", 1, 1);
x_35 = lean_mk_string_unchecked(", ", 2, 2);
x_36 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_36, 0, x_35);
x_37 = lean_box(1);
x_38 = lean_alloc_ctor(10, 3, 1);
lean_ctor_set(x_38, 0, x_33);
lean_ctor_set(x_38, 1, x_34);
lean_ctor_set(x_38, 2, x_36);
x_39 = lean_unbox(x_37);
lean_ctor_set_uint8(x_38, sizeof(void*)*3, x_39);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_28);
lean_ctor_set(x_40, 1, x_38);
lean_inc(x_8);
x_41 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_41, 0, x_8);
lean_ctor_set(x_41, 1, x_26);
lean_ctor_set(x_41, 2, x_40);
x_42 = lean_mk_string_unchecked("]", 1, 1);
x_43 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_43, 0, x_42);
lean_inc(x_8);
x_44 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_44, 0, x_8);
lean_ctor_set(x_44, 1, x_41);
lean_ctor_set(x_44, 2, x_43);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_16);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_46, 0, x_8);
lean_ctor_set(x_46, 1, x_24);
lean_ctor_set(x_46, 2, x_45);
x_47 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_47, 0, x_5);
lean_ctor_set(x_47, 1, x_6);
lean_ctor_set(x_47, 2, x_46);
return x_47;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_dsimp() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("dsimp", 5, 5);
lean_inc(x_4);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_10, 0, x_4);
x_11 = lean_unbox(x_9);
lean_ctor_set_uint8(x_10, sizeof(void*)*1, x_11);
x_12 = l_Lean_Parser_Tactic_optConfig;
lean_inc(x_8);
x_13 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_10);
lean_ctor_set(x_13, 2, x_12);
x_14 = lean_mk_string_unchecked("optional", 8, 8);
x_15 = l_Lean_Name_mkStr1(x_14);
x_16 = l_Lean_Parser_Tactic_discharger;
lean_inc(x_15);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
lean_inc(x_8);
x_18 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_18, 0, x_8);
lean_ctor_set(x_18, 1, x_13);
lean_ctor_set(x_18, 2, x_17);
x_19 = lean_mk_string_unchecked(" only", 5, 5);
x_20 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_unbox(x_9);
lean_ctor_set_uint8(x_20, sizeof(void*)*1, x_21);
lean_inc(x_15);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_15);
lean_ctor_set(x_22, 1, x_20);
lean_inc(x_8);
x_23 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_23, 0, x_8);
lean_ctor_set(x_23, 1, x_18);
lean_ctor_set(x_23, 2, x_22);
x_24 = lean_mk_string_unchecked(" [", 2, 2);
x_25 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_mk_string_unchecked("withoutPosition", 15, 15);
x_27 = l_Lean_Name_mkStr1(x_26);
x_28 = lean_mk_string_unchecked("orelse", 6, 6);
x_29 = l_Lean_Name_mkStr1(x_28);
x_30 = l_Lean_Parser_Tactic_simpErase;
x_31 = l_Lean_Parser_Tactic_simpLemma;
x_32 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_30);
lean_ctor_set(x_32, 2, x_31);
x_33 = lean_mk_string_unchecked(",", 1, 1);
x_34 = lean_mk_string_unchecked(", ", 2, 2);
x_35 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_35, 0, x_34);
x_36 = lean_box(1);
x_37 = lean_alloc_ctor(10, 3, 1);
lean_ctor_set(x_37, 0, x_32);
lean_ctor_set(x_37, 1, x_33);
lean_ctor_set(x_37, 2, x_35);
x_38 = lean_unbox(x_36);
lean_ctor_set_uint8(x_37, sizeof(void*)*3, x_38);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_27);
lean_ctor_set(x_39, 1, x_37);
lean_inc(x_8);
x_40 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_40, 0, x_8);
lean_ctor_set(x_40, 1, x_25);
lean_ctor_set(x_40, 2, x_39);
x_41 = lean_mk_string_unchecked("]", 1, 1);
x_42 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_42, 0, x_41);
lean_inc(x_8);
x_43 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_43, 0, x_8);
lean_ctor_set(x_43, 1, x_40);
lean_ctor_set(x_43, 2, x_42);
lean_inc(x_15);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_15);
lean_ctor_set(x_44, 1, x_43);
lean_inc(x_8);
x_45 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_45, 0, x_8);
lean_ctor_set(x_45, 1, x_23);
lean_ctor_set(x_45, 2, x_44);
x_46 = l_Lean_Parser_Tactic_location;
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_15);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_48, 0, x_8);
lean_ctor_set(x_48, 1, x_45);
lean_ctor_set(x_48, 2, x_47);
x_49 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_49, 0, x_5);
lean_ctor_set(x_49, 1, x_6);
lean_ctor_set(x_49, 2, x_48);
return x_49;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpArg() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = lean_mk_string_unchecked("orelse", 6, 6);
x_2 = l_Lean_Name_mkStr1(x_1);
x_3 = l_Lean_Parser_Tactic_simpStar;
x_4 = l_Lean_Parser_Tactic_simpErase;
x_5 = l_Lean_Parser_Tactic_simpLemma;
lean_inc(x_2);
x_6 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_5);
x_7 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_3);
lean_ctor_set(x_7, 2, x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpArgs() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_1 = lean_mk_string_unchecked("simpArgs", 8, 8);
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Tactic", 6, 6);
lean_inc(x_1);
x_5 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_1);
x_6 = lean_mk_string_unchecked("andthen", 7, 7);
x_7 = l_Lean_Name_mkStr1(x_6);
x_8 = lean_mk_string_unchecked(" [", 2, 2);
x_9 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = l_Lean_Parser_Tactic_simpArg;
x_11 = lean_mk_string_unchecked(",", 1, 1);
x_12 = lean_mk_string_unchecked(", ", 2, 2);
x_13 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(10, 3, 1);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_11);
lean_ctor_set(x_15, 2, x_13);
x_16 = lean_unbox(x_14);
lean_ctor_set_uint8(x_15, sizeof(void*)*3, x_16);
lean_inc(x_7);
x_17 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_17, 0, x_7);
lean_ctor_set(x_17, 1, x_9);
lean_ctor_set(x_17, 2, x_15);
x_18 = lean_mk_string_unchecked("]", 1, 1);
x_19 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_20, 0, x_7);
lean_ctor_set(x_20, 1, x_17);
lean_ctor_set(x_20, 2, x_19);
x_21 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_21, 0, x_1);
lean_ctor_set(x_21, 1, x_5);
lean_ctor_set(x_21, 2, x_20);
return x_21;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_dsimpArg() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_mk_string_unchecked("orelse", 6, 6);
x_2 = l_Lean_Name_mkStr1(x_1);
x_3 = l_Lean_Parser_Tactic_simpErase;
x_4 = l_Lean_Parser_Tactic_simpLemma;
x_5 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_dsimpArgs() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_1 = lean_mk_string_unchecked("dsimpArgs", 9, 9);
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Tactic", 6, 6);
lean_inc(x_1);
x_5 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_1);
x_6 = lean_mk_string_unchecked("andthen", 7, 7);
x_7 = l_Lean_Name_mkStr1(x_6);
x_8 = lean_mk_string_unchecked(" [", 2, 2);
x_9 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = l_Lean_Parser_Tactic_dsimpArg;
x_11 = lean_mk_string_unchecked(",", 1, 1);
x_12 = lean_mk_string_unchecked(", ", 2, 2);
x_13 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(10, 3, 1);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_11);
lean_ctor_set(x_15, 2, x_13);
x_16 = lean_unbox(x_14);
lean_ctor_set_uint8(x_15, sizeof(void*)*3, x_16);
lean_inc(x_7);
x_17 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_17, 0, x_7);
lean_ctor_set(x_17, 1, x_9);
lean_ctor_set(x_17, 2, x_15);
x_18 = lean_mk_string_unchecked("]", 1, 1);
x_19 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_20, 0, x_7);
lean_ctor_set(x_20, 1, x_17);
lean_ctor_set(x_20, 2, x_19);
x_21 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_21, 0, x_1);
lean_ctor_set(x_21, 1, x_5);
lean_ctor_set(x_21, 2, x_20);
return x_21;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpTraceArgsRest() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_1 = lean_mk_string_unchecked("simpTraceArgsRest", 17, 17);
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Tactic", 6, 6);
lean_inc(x_1);
x_5 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_1);
x_6 = lean_mk_string_unchecked("andthen", 7, 7);
x_7 = l_Lean_Name_mkStr1(x_6);
x_8 = l_Lean_Parser_Tactic_optConfig;
x_9 = lean_mk_string_unchecked("optional", 8, 8);
x_10 = l_Lean_Name_mkStr1(x_9);
x_11 = l_Lean_Parser_Tactic_discharger;
lean_inc(x_10);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
lean_inc(x_7);
x_13 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_12);
x_14 = lean_mk_string_unchecked(" only", 5, 5);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_16, 0, x_14);
x_17 = lean_unbox(x_15);
lean_ctor_set_uint8(x_16, sizeof(void*)*1, x_17);
lean_inc(x_10);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_10);
lean_ctor_set(x_18, 1, x_16);
lean_inc(x_7);
x_19 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_19, 0, x_7);
lean_ctor_set(x_19, 1, x_13);
lean_ctor_set(x_19, 2, x_18);
x_20 = l_Lean_Parser_Tactic_simpArgs;
lean_inc(x_10);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_10);
lean_ctor_set(x_21, 1, x_20);
lean_inc(x_7);
x_22 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_22, 0, x_7);
lean_ctor_set(x_22, 1, x_19);
lean_ctor_set(x_22, 2, x_21);
x_23 = lean_mk_string_unchecked("ppSpace", 7, 7);
x_24 = l_Lean_Name_mkStr1(x_23);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = l_Lean_Parser_Tactic_location;
lean_inc(x_7);
x_27 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_27, 0, x_7);
lean_ctor_set(x_27, 1, x_25);
lean_ctor_set(x_27, 2, x_26);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_10);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_29, 0, x_7);
lean_ctor_set(x_29, 1, x_22);
lean_ctor_set(x_29, 2, x_28);
x_30 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_30, 0, x_1);
lean_ctor_set(x_30, 1, x_5);
lean_ctor_set(x_30, 2, x_29);
return x_30;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpTrace() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("simpTrace", 9, 9);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("simp\?", 5, 5);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_unbox(x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_12);
x_13 = lean_mk_string_unchecked("optional", 8, 8);
x_14 = l_Lean_Name_mkStr1(x_13);
x_15 = lean_mk_string_unchecked("!", 1, 1);
x_16 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
lean_inc(x_8);
x_18 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_18, 0, x_8);
lean_ctor_set(x_18, 1, x_11);
lean_ctor_set(x_18, 2, x_17);
x_19 = l_Lean_Parser_Tactic_simpTraceArgsRest;
x_20 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_20, 0, x_8);
lean_ctor_set(x_20, 1, x_18);
lean_ctor_set(x_20, 2, x_19);
x_21 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_21, 0, x_5);
lean_ctor_set(x_21, 1, x_6);
lean_ctor_set(x_21, 2, x_20);
return x_21;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSimp_x3f_x21__() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("tacticSimp\?!_", 13, 13);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("simp\?!", 6, 6);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_unbox(x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_12);
x_13 = l_Lean_Parser_Tactic_simpTraceArgsRest;
x_14 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_14, 0, x_8);
lean_ctor_set(x_14, 1, x_11);
lean_ctor_set(x_14, 2, x_13);
x_15 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_15, 0, x_5);
lean_ctor_set(x_15, 1, x_6);
lean_ctor_set(x_15, 2, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticSimp_x3f_x21____1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Tactic", 6, 6);
x_7 = lean_mk_string_unchecked("tacticSimp\?!_", 13, 13);
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
x_10 = lean_box(1);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_unsigned_to_nat(1u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
x_15 = l_Lean_Syntax_getArg(x_1, x_12);
lean_dec(x_1);
x_16 = lean_ctor_get(x_2, 5);
x_17 = lean_box(0);
x_18 = lean_unbox(x_17);
x_19 = l_Lean_SourceInfo_fromRef(x_16, x_18);
x_20 = lean_mk_string_unchecked("simpTrace", 9, 9);
x_21 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_20);
x_22 = l_Lean_SourceInfo_fromRef(x_15, x_9);
lean_dec(x_15);
x_23 = lean_mk_string_unchecked("simp\?", 5, 5);
x_24 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_mk_string_unchecked("null", 4, 4);
x_26 = l_Lean_Name_mkStr1(x_25);
x_27 = lean_mk_string_unchecked("!", 1, 1);
lean_inc(x_19);
x_28 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_28, 0, x_19);
lean_ctor_set(x_28, 1, x_27);
lean_inc(x_19);
x_29 = l_Lean_Syntax_node1(x_19, x_26, x_28);
x_30 = l_Lean_Syntax_node3(x_19, x_21, x_24, x_29, x_14);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_3);
return x_31;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticSimp_x3f_x21____1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticSimp_x3f_x21____1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpAllTraceArgsRest() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_1 = lean_mk_string_unchecked("simpAllTraceArgsRest", 20, 20);
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Tactic", 6, 6);
lean_inc(x_1);
x_5 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_1);
x_6 = lean_mk_string_unchecked("andthen", 7, 7);
x_7 = l_Lean_Name_mkStr1(x_6);
x_8 = l_Lean_Parser_Tactic_optConfig;
x_9 = lean_mk_string_unchecked("optional", 8, 8);
x_10 = l_Lean_Name_mkStr1(x_9);
x_11 = l_Lean_Parser_Tactic_discharger;
lean_inc(x_10);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
lean_inc(x_7);
x_13 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_12);
x_14 = lean_mk_string_unchecked(" only", 5, 5);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_16, 0, x_14);
x_17 = lean_unbox(x_15);
lean_ctor_set_uint8(x_16, sizeof(void*)*1, x_17);
lean_inc(x_10);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_10);
lean_ctor_set(x_18, 1, x_16);
lean_inc(x_7);
x_19 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_19, 0, x_7);
lean_ctor_set(x_19, 1, x_13);
lean_ctor_set(x_19, 2, x_18);
x_20 = l_Lean_Parser_Tactic_dsimpArgs;
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_10);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_22, 0, x_7);
lean_ctor_set(x_22, 1, x_19);
lean_ctor_set(x_22, 2, x_21);
x_23 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_23, 0, x_1);
lean_ctor_set(x_23, 1, x_5);
lean_ctor_set(x_23, 2, x_22);
return x_23;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpAllTrace() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("simpAllTrace", 12, 12);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("simp_all\?", 9, 9);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_unbox(x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_12);
x_13 = lean_mk_string_unchecked("optional", 8, 8);
x_14 = l_Lean_Name_mkStr1(x_13);
x_15 = lean_mk_string_unchecked("!", 1, 1);
x_16 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
lean_inc(x_8);
x_18 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_18, 0, x_8);
lean_ctor_set(x_18, 1, x_11);
lean_ctor_set(x_18, 2, x_17);
x_19 = l_Lean_Parser_Tactic_simpAllTraceArgsRest;
x_20 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_20, 0, x_8);
lean_ctor_set(x_20, 1, x_18);
lean_ctor_set(x_20, 2, x_19);
x_21 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_21, 0, x_5);
lean_ctor_set(x_21, 1, x_6);
lean_ctor_set(x_21, 2, x_20);
return x_21;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSimp__all_x3f_x21__() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("tacticSimp_all\?!_", 17, 17);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("simp_all\?!", 10, 10);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_unbox(x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_12);
x_13 = l_Lean_Parser_Tactic_simpAllTraceArgsRest;
x_14 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_14, 0, x_8);
lean_ctor_set(x_14, 1, x_11);
lean_ctor_set(x_14, 2, x_13);
x_15 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_15, 0, x_5);
lean_ctor_set(x_15, 1, x_6);
lean_ctor_set(x_15, 2, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticSimp__all_x3f_x21____1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Tactic", 6, 6);
x_7 = lean_mk_string_unchecked("tacticSimp_all\?!_", 17, 17);
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
x_10 = lean_box(1);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_unsigned_to_nat(1u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
x_15 = l_Lean_Syntax_getArg(x_1, x_12);
lean_dec(x_1);
x_16 = lean_ctor_get(x_2, 5);
x_17 = lean_box(0);
x_18 = lean_unbox(x_17);
x_19 = l_Lean_SourceInfo_fromRef(x_16, x_18);
x_20 = lean_mk_string_unchecked("simpAllTrace", 12, 12);
x_21 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_20);
x_22 = l_Lean_SourceInfo_fromRef(x_15, x_9);
lean_dec(x_15);
x_23 = lean_mk_string_unchecked("simp_all\?", 9, 9);
x_24 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_mk_string_unchecked("null", 4, 4);
x_26 = l_Lean_Name_mkStr1(x_25);
x_27 = lean_mk_string_unchecked("!", 1, 1);
lean_inc(x_19);
x_28 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_28, 0, x_19);
lean_ctor_set(x_28, 1, x_27);
lean_inc(x_19);
x_29 = l_Lean_Syntax_node1(x_19, x_26, x_28);
x_30 = l_Lean_Syntax_node3(x_19, x_21, x_24, x_29, x_14);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_3);
return x_31;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticSimp__all_x3f_x21____1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticSimp__all_x3f_x21____1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_dsimpTraceArgsRest() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_1 = lean_mk_string_unchecked("dsimpTraceArgsRest", 18, 18);
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Tactic", 6, 6);
lean_inc(x_1);
x_5 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_1);
x_6 = lean_mk_string_unchecked("andthen", 7, 7);
x_7 = l_Lean_Name_mkStr1(x_6);
x_8 = l_Lean_Parser_Tactic_optConfig;
x_9 = lean_mk_string_unchecked("optional", 8, 8);
x_10 = l_Lean_Name_mkStr1(x_9);
x_11 = lean_mk_string_unchecked(" only", 5, 5);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_13, 0, x_11);
x_14 = lean_unbox(x_12);
lean_ctor_set_uint8(x_13, sizeof(void*)*1, x_14);
lean_inc(x_10);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_13);
lean_inc(x_7);
x_16 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_16, 0, x_7);
lean_ctor_set(x_16, 1, x_8);
lean_ctor_set(x_16, 2, x_15);
x_17 = l_Lean_Parser_Tactic_dsimpArgs;
lean_inc(x_10);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_10);
lean_ctor_set(x_18, 1, x_17);
lean_inc(x_7);
x_19 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_19, 0, x_7);
lean_ctor_set(x_19, 1, x_16);
lean_ctor_set(x_19, 2, x_18);
x_20 = lean_mk_string_unchecked("ppSpace", 7, 7);
x_21 = l_Lean_Name_mkStr1(x_20);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = l_Lean_Parser_Tactic_location;
lean_inc(x_7);
x_24 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_24, 0, x_7);
lean_ctor_set(x_24, 1, x_22);
lean_ctor_set(x_24, 2, x_23);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_10);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_26, 0, x_7);
lean_ctor_set(x_26, 1, x_19);
lean_ctor_set(x_26, 2, x_25);
x_27 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_27, 0, x_1);
lean_ctor_set(x_27, 1, x_5);
lean_ctor_set(x_27, 2, x_26);
return x_27;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_dsimpTrace() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("dsimpTrace", 10, 10);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("dsimp\?", 6, 6);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_unbox(x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_12);
x_13 = lean_mk_string_unchecked("optional", 8, 8);
x_14 = l_Lean_Name_mkStr1(x_13);
x_15 = lean_mk_string_unchecked("!", 1, 1);
x_16 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
lean_inc(x_8);
x_18 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_18, 0, x_8);
lean_ctor_set(x_18, 1, x_11);
lean_ctor_set(x_18, 2, x_17);
x_19 = l_Lean_Parser_Tactic_dsimpTraceArgsRest;
x_20 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_20, 0, x_8);
lean_ctor_set(x_20, 1, x_18);
lean_ctor_set(x_20, 2, x_19);
x_21 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_21, 0, x_5);
lean_ctor_set(x_21, 1, x_6);
lean_ctor_set(x_21, 2, x_20);
return x_21;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticDsimp_x3f_x21__() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("tacticDsimp\?!_", 14, 14);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("dsimp\?!", 7, 7);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_unbox(x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_12);
x_13 = l_Lean_Parser_Tactic_dsimpTraceArgsRest;
x_14 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_14, 0, x_8);
lean_ctor_set(x_14, 1, x_11);
lean_ctor_set(x_14, 2, x_13);
x_15 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_15, 0, x_5);
lean_ctor_set(x_15, 1, x_6);
lean_ctor_set(x_15, 2, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticDsimp_x3f_x21____1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Tactic", 6, 6);
x_7 = lean_mk_string_unchecked("tacticDsimp\?!_", 14, 14);
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
x_10 = lean_box(1);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_unsigned_to_nat(1u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
x_15 = l_Lean_Syntax_getArg(x_1, x_12);
lean_dec(x_1);
x_16 = lean_ctor_get(x_2, 5);
x_17 = lean_box(0);
x_18 = lean_unbox(x_17);
x_19 = l_Lean_SourceInfo_fromRef(x_16, x_18);
x_20 = lean_mk_string_unchecked("dsimpTrace", 10, 10);
x_21 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_20);
x_22 = l_Lean_SourceInfo_fromRef(x_15, x_9);
lean_dec(x_15);
x_23 = lean_mk_string_unchecked("dsimp\?", 6, 6);
x_24 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_mk_string_unchecked("null", 4, 4);
x_26 = l_Lean_Name_mkStr1(x_25);
x_27 = lean_mk_string_unchecked("!", 1, 1);
lean_inc(x_19);
x_28 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_28, 0, x_19);
lean_ctor_set(x_28, 1, x_27);
lean_inc(x_19);
x_29 = l_Lean_Syntax_node1(x_19, x_26, x_28);
x_30 = l_Lean_Syntax_node3(x_19, x_21, x_24, x_29, x_14);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_3);
return x_31;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticDsimp_x3f_x21____1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticDsimp_x3f_x21____1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpaArgsRest() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_1 = lean_mk_string_unchecked("simpaArgsRest", 13, 13);
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Tactic", 6, 6);
lean_inc(x_1);
x_5 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_1);
x_6 = lean_mk_string_unchecked("andthen", 7, 7);
x_7 = l_Lean_Name_mkStr1(x_6);
x_8 = l_Lean_Parser_Tactic_optConfig;
x_9 = lean_mk_string_unchecked("optional", 8, 8);
x_10 = l_Lean_Name_mkStr1(x_9);
x_11 = l_Lean_Parser_Tactic_discharger;
lean_inc(x_10);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
lean_inc(x_7);
x_13 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_12);
x_14 = lean_mk_string_unchecked(" only ", 6, 6);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_16, 0, x_14);
x_17 = lean_unbox(x_15);
lean_ctor_set_uint8(x_16, sizeof(void*)*1, x_17);
lean_inc(x_10);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_10);
lean_ctor_set(x_18, 1, x_16);
lean_inc(x_7);
x_19 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_19, 0, x_7);
lean_ctor_set(x_19, 1, x_13);
lean_ctor_set(x_19, 2, x_18);
x_20 = l_Lean_Parser_Tactic_simpArgs;
lean_inc(x_10);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_10);
lean_ctor_set(x_21, 1, x_20);
lean_inc(x_7);
x_22 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_22, 0, x_7);
lean_ctor_set(x_22, 1, x_19);
lean_ctor_set(x_22, 2, x_21);
x_23 = lean_mk_string_unchecked(" using ", 7, 7);
x_24 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_mk_string_unchecked("term", 4, 4);
x_26 = l_Lean_Name_mkStr1(x_25);
x_27 = lean_unsigned_to_nat(0u);
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
lean_inc(x_7);
x_29 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_29, 0, x_7);
lean_ctor_set(x_29, 1, x_24);
lean_ctor_set(x_29, 2, x_28);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_10);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_31, 0, x_7);
lean_ctor_set(x_31, 1, x_22);
lean_ctor_set(x_31, 2, x_30);
x_32 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_32, 0, x_1);
lean_ctor_set(x_32, 1, x_5);
lean_ctor_set(x_32, 2, x_31);
return x_32;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpa() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("simpa", 5, 5);
lean_inc(x_4);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_10, 0, x_4);
x_11 = lean_unbox(x_9);
lean_ctor_set_uint8(x_10, sizeof(void*)*1, x_11);
x_12 = lean_mk_string_unchecked("optional", 8, 8);
x_13 = l_Lean_Name_mkStr1(x_12);
x_14 = lean_mk_string_unchecked("\?", 1, 1);
x_15 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_15, 0, x_14);
lean_inc(x_13);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
lean_inc(x_8);
x_17 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_17, 0, x_8);
lean_ctor_set(x_17, 1, x_10);
lean_ctor_set(x_17, 2, x_16);
x_18 = lean_mk_string_unchecked("!", 1, 1);
x_19 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_13);
lean_ctor_set(x_20, 1, x_19);
lean_inc(x_8);
x_21 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_21, 0, x_8);
lean_ctor_set(x_21, 1, x_17);
lean_ctor_set(x_21, 2, x_20);
x_22 = l_Lean_Parser_Tactic_simpaArgsRest;
x_23 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_23, 0, x_8);
lean_ctor_set(x_23, 1, x_21);
lean_ctor_set(x_23, 2, x_22);
x_24 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_24, 0, x_5);
lean_ctor_set(x_24, 1, x_6);
lean_ctor_set(x_24, 2, x_23);
return x_24;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSimpa_x21__() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("tacticSimpa!_", 13, 13);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("simpa!", 6, 6);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_unbox(x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_12);
x_13 = l_Lean_Parser_Tactic_simpaArgsRest;
x_14 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_14, 0, x_8);
lean_ctor_set(x_14, 1, x_11);
lean_ctor_set(x_14, 2, x_13);
x_15 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_15, 0, x_5);
lean_ctor_set(x_15, 1, x_6);
lean_ctor_set(x_15, 2, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticSimpa_x21____1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Tactic", 6, 6);
x_7 = lean_mk_string_unchecked("tacticSimpa!_", 13, 13);
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
x_10 = lean_box(1);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = l_Lean_Syntax_getArg(x_1, x_12);
lean_dec(x_1);
x_14 = lean_ctor_get(x_2, 5);
x_15 = lean_box(0);
x_16 = lean_unbox(x_15);
x_17 = l_Lean_SourceInfo_fromRef(x_14, x_16);
x_18 = lean_mk_string_unchecked("simpa", 5, 5);
lean_inc(x_18);
x_19 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_18);
lean_inc(x_17);
x_20 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_18);
x_21 = lean_mk_string_unchecked("null", 4, 4);
x_22 = l_Lean_Name_mkStr1(x_21);
x_23 = l_Array_mkArray0(lean_box(0));
lean_inc(x_22);
lean_inc(x_17);
x_24 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_24, 0, x_17);
lean_ctor_set(x_24, 1, x_22);
lean_ctor_set(x_24, 2, x_23);
x_25 = lean_mk_string_unchecked("!", 1, 1);
lean_inc(x_17);
x_26 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_26, 0, x_17);
lean_ctor_set(x_26, 1, x_25);
lean_inc(x_17);
x_27 = l_Lean_Syntax_node1(x_17, x_22, x_26);
x_28 = l_Lean_Syntax_node4(x_17, x_19, x_20, x_24, x_27, x_13);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_3);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticSimpa_x21____1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticSimpa_x21____1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSimpa_x3f__() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("tacticSimpa\?_", 13, 13);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("simpa\?", 6, 6);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_unbox(x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_12);
x_13 = l_Lean_Parser_Tactic_simpaArgsRest;
x_14 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_14, 0, x_8);
lean_ctor_set(x_14, 1, x_11);
lean_ctor_set(x_14, 2, x_13);
x_15 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_15, 0, x_5);
lean_ctor_set(x_15, 1, x_6);
lean_ctor_set(x_15, 2, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticSimpa_x3f____1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Tactic", 6, 6);
x_7 = lean_mk_string_unchecked("tacticSimpa\?_", 13, 13);
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
x_10 = lean_box(1);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = l_Lean_Syntax_getArg(x_1, x_12);
lean_dec(x_1);
x_14 = lean_ctor_get(x_2, 5);
x_15 = lean_box(0);
x_16 = lean_unbox(x_15);
x_17 = l_Lean_SourceInfo_fromRef(x_14, x_16);
x_18 = lean_mk_string_unchecked("simpa", 5, 5);
lean_inc(x_18);
x_19 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_18);
lean_inc(x_17);
x_20 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_18);
x_21 = lean_mk_string_unchecked("null", 4, 4);
x_22 = l_Lean_Name_mkStr1(x_21);
x_23 = lean_mk_string_unchecked("\?", 1, 1);
lean_inc(x_17);
x_24 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_24, 0, x_17);
lean_ctor_set(x_24, 1, x_23);
lean_inc(x_22);
lean_inc(x_17);
x_25 = l_Lean_Syntax_node1(x_17, x_22, x_24);
x_26 = l_Array_mkArray0(lean_box(0));
lean_inc(x_17);
x_27 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_27, 0, x_17);
lean_ctor_set(x_27, 1, x_22);
lean_ctor_set(x_27, 2, x_26);
x_28 = l_Lean_Syntax_node4(x_17, x_19, x_20, x_25, x_27, x_13);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_3);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticSimpa_x3f____1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticSimpa_x3f____1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSimpa_x3f_x21__() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("tacticSimpa\?!_", 14, 14);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("simpa\?!", 7, 7);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_unbox(x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_12);
x_13 = l_Lean_Parser_Tactic_simpaArgsRest;
x_14 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_14, 0, x_8);
lean_ctor_set(x_14, 1, x_11);
lean_ctor_set(x_14, 2, x_13);
x_15 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_15, 0, x_5);
lean_ctor_set(x_15, 1, x_6);
lean_ctor_set(x_15, 2, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticSimpa_x3f_x21____1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Tactic", 6, 6);
x_7 = lean_mk_string_unchecked("tacticSimpa\?!_", 14, 14);
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
x_10 = lean_box(1);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = l_Lean_Syntax_getArg(x_1, x_12);
lean_dec(x_1);
x_14 = lean_ctor_get(x_2, 5);
x_15 = lean_box(0);
x_16 = lean_unbox(x_15);
x_17 = l_Lean_SourceInfo_fromRef(x_14, x_16);
x_18 = lean_mk_string_unchecked("simpa", 5, 5);
lean_inc(x_18);
x_19 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_18);
lean_inc(x_17);
x_20 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_18);
x_21 = lean_mk_string_unchecked("null", 4, 4);
x_22 = l_Lean_Name_mkStr1(x_21);
x_23 = lean_mk_string_unchecked("\?", 1, 1);
lean_inc(x_17);
x_24 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_24, 0, x_17);
lean_ctor_set(x_24, 1, x_23);
lean_inc(x_22);
lean_inc(x_17);
x_25 = l_Lean_Syntax_node1(x_17, x_22, x_24);
x_26 = lean_mk_string_unchecked("!", 1, 1);
lean_inc(x_17);
x_27 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_27, 0, x_17);
lean_ctor_set(x_27, 1, x_26);
lean_inc(x_17);
x_28 = l_Lean_Syntax_node1(x_17, x_22, x_27);
x_29 = l_Lean_Syntax_node4(x_17, x_19, x_20, x_25, x_28, x_13);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_3);
return x_30;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticSimpa_x3f_x21____1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticSimpa_x3f_x21____1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_delta() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("delta", 5, 5);
lean_inc(x_4);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_10, 0, x_4);
x_11 = lean_unbox(x_9);
lean_ctor_set_uint8(x_10, sizeof(void*)*1, x_11);
x_12 = lean_mk_string_unchecked("many1", 5, 5);
x_13 = l_Lean_Name_mkStr1(x_12);
x_14 = lean_mk_string_unchecked("ppSpace", 7, 7);
x_15 = l_Lean_Name_mkStr1(x_14);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_mk_string_unchecked("colGt", 5, 5);
x_18 = l_Lean_Name_mkStr1(x_17);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
lean_inc(x_8);
x_20 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_20, 0, x_8);
lean_ctor_set(x_20, 1, x_16);
lean_ctor_set(x_20, 2, x_19);
x_21 = lean_mk_string_unchecked("ident", 5, 5);
x_22 = l_Lean_Name_mkStr1(x_21);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_22);
lean_inc(x_8);
x_24 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_24, 0, x_8);
lean_ctor_set(x_24, 1, x_20);
lean_ctor_set(x_24, 2, x_23);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_13);
lean_ctor_set(x_25, 1, x_24);
lean_inc(x_8);
x_26 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_26, 0, x_8);
lean_ctor_set(x_26, 1, x_10);
lean_ctor_set(x_26, 2, x_25);
x_27 = lean_mk_string_unchecked("optional", 8, 8);
x_28 = l_Lean_Name_mkStr1(x_27);
x_29 = l_Lean_Parser_Tactic_location;
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_31, 0, x_8);
lean_ctor_set(x_31, 1, x_26);
lean_ctor_set(x_31, 2, x_30);
x_32 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_32, 0, x_5);
lean_ctor_set(x_32, 1, x_6);
lean_ctor_set(x_32, 2, x_31);
return x_32;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_unfold() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("unfold", 6, 6);
lean_inc(x_4);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_10, 0, x_4);
x_11 = lean_unbox(x_9);
lean_ctor_set_uint8(x_10, sizeof(void*)*1, x_11);
x_12 = lean_mk_string_unchecked("many1", 5, 5);
x_13 = l_Lean_Name_mkStr1(x_12);
x_14 = lean_mk_string_unchecked("ppSpace", 7, 7);
x_15 = l_Lean_Name_mkStr1(x_14);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_mk_string_unchecked("colGt", 5, 5);
x_18 = l_Lean_Name_mkStr1(x_17);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
lean_inc(x_8);
x_20 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_20, 0, x_8);
lean_ctor_set(x_20, 1, x_16);
lean_ctor_set(x_20, 2, x_19);
x_21 = lean_mk_string_unchecked("ident", 5, 5);
x_22 = l_Lean_Name_mkStr1(x_21);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_22);
lean_inc(x_8);
x_24 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_24, 0, x_8);
lean_ctor_set(x_24, 1, x_20);
lean_ctor_set(x_24, 2, x_23);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_13);
lean_ctor_set(x_25, 1, x_24);
lean_inc(x_8);
x_26 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_26, 0, x_8);
lean_ctor_set(x_26, 1, x_10);
lean_ctor_set(x_26, 2, x_25);
x_27 = lean_mk_string_unchecked("optional", 8, 8);
x_28 = l_Lean_Name_mkStr1(x_27);
x_29 = l_Lean_Parser_Tactic_location;
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_31, 0, x_8);
lean_ctor_set(x_31, 1, x_26);
lean_ctor_set(x_31, 2, x_30);
x_32 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_32, 0, x_5);
lean_ctor_set(x_32, 1, x_6);
lean_ctor_set(x_32, 2, x_31);
return x_32;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticRefine__lift__() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("tacticRefine_lift_", 18, 18);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("refine_lift ", 12, 12);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_unbox(x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_12);
x_13 = lean_mk_string_unchecked("term", 4, 4);
x_14 = l_Lean_Name_mkStr1(x_13);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_17, 0, x_8);
lean_ctor_set(x_17, 1, x_11);
lean_ctor_set(x_17, 2, x_16);
x_18 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_18, 0, x_5);
lean_ctor_set(x_18, 1, x_6);
lean_ctor_set(x_18, 2, x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticRefine__lift____1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Tactic", 6, 6);
x_7 = lean_mk_string_unchecked("tacticRefine_lift_", 18, 18);
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
x_10 = lean_box(1);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = l_Lean_Syntax_getArg(x_1, x_12);
lean_dec(x_1);
x_14 = lean_ctor_get(x_2, 5);
x_15 = lean_box(0);
x_16 = lean_unbox(x_15);
x_17 = l_Lean_SourceInfo_fromRef(x_14, x_16);
x_18 = lean_mk_string_unchecked("focus", 5, 5);
lean_inc(x_18);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_19 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_18);
lean_inc(x_17);
x_20 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_18);
x_21 = lean_mk_string_unchecked("tacticSeq", 9, 9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_22 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_21);
x_23 = lean_mk_string_unchecked("tacticSeq1Indented", 18, 18);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_24 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_23);
x_25 = lean_mk_string_unchecked("null", 4, 4);
x_26 = l_Lean_Name_mkStr1(x_25);
x_27 = lean_mk_string_unchecked("paren", 5, 5);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_28 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_27);
x_29 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_17);
x_30 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_30, 0, x_17);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_mk_string_unchecked("refine", 6, 6);
lean_inc(x_31);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_32 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_31);
lean_inc(x_17);
x_33 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_33, 0, x_17);
lean_ctor_set(x_33, 1, x_31);
x_34 = lean_mk_string_unchecked("Term", 4, 4);
x_35 = lean_mk_string_unchecked("noImplicitLambda", 16, 16);
lean_inc(x_5);
lean_inc(x_4);
x_36 = l_Lean_Name_mkStr4(x_4, x_5, x_34, x_35);
x_37 = lean_mk_string_unchecked("no_implicit_lambda%", 19, 19);
lean_inc(x_17);
x_38 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_38, 0, x_17);
lean_ctor_set(x_38, 1, x_37);
lean_inc(x_17);
x_39 = l_Lean_Syntax_node2(x_17, x_36, x_38, x_13);
lean_inc(x_17);
x_40 = l_Lean_Syntax_node2(x_17, x_32, x_33, x_39);
x_41 = lean_mk_string_unchecked(";", 1, 1);
lean_inc(x_17);
x_42 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_42, 0, x_17);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_mk_string_unchecked("rotateRight", 11, 11);
x_44 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_43);
x_45 = lean_mk_string_unchecked("rotate_right", 12, 12);
lean_inc(x_17);
x_46 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_46, 0, x_17);
lean_ctor_set(x_46, 1, x_45);
x_47 = l_Array_mkArray0(lean_box(0));
lean_inc(x_26);
lean_inc(x_17);
x_48 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_48, 0, x_17);
lean_ctor_set(x_48, 1, x_26);
lean_ctor_set(x_48, 2, x_47);
lean_inc(x_17);
x_49 = l_Lean_Syntax_node2(x_17, x_44, x_46, x_48);
lean_inc(x_26);
lean_inc(x_17);
x_50 = l_Lean_Syntax_node3(x_17, x_26, x_40, x_42, x_49);
lean_inc(x_24);
lean_inc(x_17);
x_51 = l_Lean_Syntax_node1(x_17, x_24, x_50);
lean_inc(x_22);
lean_inc(x_17);
x_52 = l_Lean_Syntax_node1(x_17, x_22, x_51);
x_53 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_17);
x_54 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_54, 0, x_17);
lean_ctor_set(x_54, 1, x_53);
lean_inc(x_17);
x_55 = l_Lean_Syntax_node3(x_17, x_28, x_30, x_52, x_54);
lean_inc(x_17);
x_56 = l_Lean_Syntax_node1(x_17, x_26, x_55);
lean_inc(x_17);
x_57 = l_Lean_Syntax_node1(x_17, x_24, x_56);
lean_inc(x_17);
x_58 = l_Lean_Syntax_node1(x_17, x_22, x_57);
x_59 = l_Lean_Syntax_node2(x_17, x_19, x_20, x_58);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_3);
return x_60;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticRefine__lift____1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticRefine__lift____1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticHave__() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("tacticHave_", 11, 11);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("have ", 5, 5);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_unbox(x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_12);
x_13 = lean_mk_string_unchecked("haveDecl", 8, 8);
x_14 = l_Lean_Name_mkStr1(x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_16, 0, x_8);
lean_ctor_set(x_16, 1, x_11);
lean_ctor_set(x_16, 2, x_15);
x_17 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_17, 0, x_5);
lean_ctor_set(x_17, 1, x_6);
lean_ctor_set(x_17, 2, x_16);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticHave____1___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 5);
lean_inc(x_4);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticHave____1___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_box(0);
x_5 = lean_unbox(x_4);
x_6 = l_Lean_SourceInfo_fromRef(x_1, x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticHave____1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Tactic", 6, 6);
x_7 = lean_mk_string_unchecked("tacticHave_", 11, 11);
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = l_Lean_Syntax_getArg(x_1, x_12);
x_14 = lean_mk_string_unchecked("Term", 4, 4);
x_15 = lean_mk_string_unchecked("haveDecl", 8, 8);
lean_inc(x_14);
lean_inc(x_5);
lean_inc(x_4);
x_16 = l_Lean_Name_mkStr4(x_4, x_5, x_14, x_15);
lean_inc(x_13);
x_17 = l_Lean_Syntax_isOfKind(x_13, x_16);
if (x_17 == 0)
{
lean_dec(x_16);
lean_dec(x_1);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_18 = lean_box(1);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_3);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_20 = lean_ctor_get(x_2, 5);
lean_inc(x_20);
lean_dec(x_2);
x_21 = l_Lean_SourceInfo_fromRef(x_20, x_17);
lean_dec(x_20);
x_22 = lean_mk_string_unchecked("tacticRefine_lift_", 18, 18);
lean_inc(x_5);
lean_inc(x_4);
x_23 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_22);
x_24 = lean_mk_string_unchecked("refine_lift", 11, 11);
lean_inc(x_21);
x_25 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_25, 0, x_21);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_mk_string_unchecked("have", 4, 4);
lean_inc(x_26);
lean_inc(x_14);
lean_inc(x_5);
lean_inc(x_4);
x_27 = l_Lean_Name_mkStr4(x_4, x_5, x_14, x_26);
lean_inc(x_21);
x_28 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_28, 0, x_21);
lean_ctor_set(x_28, 1, x_26);
x_29 = lean_mk_string_unchecked(";", 1, 1);
lean_inc(x_21);
x_30 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_30, 0, x_21);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_mk_string_unchecked("syntheticHole", 13, 13);
x_32 = l_Lean_Name_mkStr4(x_4, x_5, x_14, x_31);
x_33 = lean_mk_string_unchecked("\?", 1, 1);
lean_inc(x_21);
x_34 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_34, 0, x_21);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_mk_string_unchecked("_", 1, 1);
lean_inc(x_21);
x_36 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_36, 0, x_21);
lean_ctor_set(x_36, 1, x_35);
lean_inc(x_21);
x_37 = l_Lean_Syntax_node2(x_21, x_32, x_34, x_36);
lean_inc(x_21);
x_38 = l_Lean_Syntax_node4(x_21, x_27, x_28, x_13, x_30, x_37);
x_39 = l_Lean_Syntax_node2(x_21, x_23, x_25, x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_3);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_41 = lean_unsigned_to_nat(0u);
x_42 = l_Lean_Syntax_getArg(x_13, x_41);
x_43 = lean_mk_string_unchecked("haveIdDecl", 10, 10);
lean_inc(x_14);
lean_inc(x_5);
lean_inc(x_4);
x_44 = l_Lean_Name_mkStr4(x_4, x_5, x_14, x_43);
lean_inc(x_42);
x_45 = l_Lean_Syntax_isOfKind(x_42, x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_44);
lean_dec(x_42);
lean_dec(x_16);
lean_dec(x_1);
x_46 = lean_ctor_get(x_2, 5);
lean_inc(x_46);
lean_dec(x_2);
x_47 = l_Lean_SourceInfo_fromRef(x_46, x_45);
lean_dec(x_46);
x_48 = lean_mk_string_unchecked("tacticRefine_lift_", 18, 18);
lean_inc(x_5);
lean_inc(x_4);
x_49 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_48);
x_50 = lean_mk_string_unchecked("refine_lift", 11, 11);
lean_inc(x_47);
x_51 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_51, 0, x_47);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_mk_string_unchecked("have", 4, 4);
lean_inc(x_52);
lean_inc(x_14);
lean_inc(x_5);
lean_inc(x_4);
x_53 = l_Lean_Name_mkStr4(x_4, x_5, x_14, x_52);
lean_inc(x_47);
x_54 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_54, 0, x_47);
lean_ctor_set(x_54, 1, x_52);
x_55 = lean_mk_string_unchecked(";", 1, 1);
lean_inc(x_47);
x_56 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_56, 0, x_47);
lean_ctor_set(x_56, 1, x_55);
x_57 = lean_mk_string_unchecked("syntheticHole", 13, 13);
x_58 = l_Lean_Name_mkStr4(x_4, x_5, x_14, x_57);
x_59 = lean_mk_string_unchecked("\?", 1, 1);
lean_inc(x_47);
x_60 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_60, 0, x_47);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_mk_string_unchecked("_", 1, 1);
lean_inc(x_47);
x_62 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_62, 0, x_47);
lean_ctor_set(x_62, 1, x_61);
lean_inc(x_47);
x_63 = l_Lean_Syntax_node2(x_47, x_58, x_60, x_62);
lean_inc(x_47);
x_64 = l_Lean_Syntax_node4(x_47, x_53, x_54, x_13, x_56, x_63);
x_65 = l_Lean_Syntax_node2(x_47, x_49, x_51, x_64);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_3);
return x_66;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_67 = l_Lean_Syntax_getArg(x_42, x_41);
x_68 = lean_mk_string_unchecked("haveId", 6, 6);
lean_inc(x_14);
lean_inc(x_5);
lean_inc(x_4);
x_69 = l_Lean_Name_mkStr4(x_4, x_5, x_14, x_68);
lean_inc(x_67);
x_70 = l_Lean_Syntax_isOfKind(x_67, x_69);
lean_dec(x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_67);
lean_dec(x_44);
lean_dec(x_42);
lean_dec(x_16);
lean_dec(x_1);
x_71 = lean_ctor_get(x_2, 5);
lean_inc(x_71);
lean_dec(x_2);
x_72 = l_Lean_SourceInfo_fromRef(x_71, x_70);
lean_dec(x_71);
x_73 = lean_mk_string_unchecked("tacticRefine_lift_", 18, 18);
lean_inc(x_5);
lean_inc(x_4);
x_74 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_73);
x_75 = lean_mk_string_unchecked("refine_lift", 11, 11);
lean_inc(x_72);
x_76 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_76, 0, x_72);
lean_ctor_set(x_76, 1, x_75);
x_77 = lean_mk_string_unchecked("have", 4, 4);
lean_inc(x_77);
lean_inc(x_14);
lean_inc(x_5);
lean_inc(x_4);
x_78 = l_Lean_Name_mkStr4(x_4, x_5, x_14, x_77);
lean_inc(x_72);
x_79 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_79, 0, x_72);
lean_ctor_set(x_79, 1, x_77);
x_80 = lean_mk_string_unchecked(";", 1, 1);
lean_inc(x_72);
x_81 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_81, 0, x_72);
lean_ctor_set(x_81, 1, x_80);
x_82 = lean_mk_string_unchecked("syntheticHole", 13, 13);
x_83 = l_Lean_Name_mkStr4(x_4, x_5, x_14, x_82);
x_84 = lean_mk_string_unchecked("\?", 1, 1);
lean_inc(x_72);
x_85 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_85, 0, x_72);
lean_ctor_set(x_85, 1, x_84);
x_86 = lean_mk_string_unchecked("_", 1, 1);
lean_inc(x_72);
x_87 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_87, 0, x_72);
lean_ctor_set(x_87, 1, x_86);
lean_inc(x_72);
x_88 = l_Lean_Syntax_node2(x_72, x_83, x_85, x_87);
lean_inc(x_72);
x_89 = l_Lean_Syntax_node4(x_72, x_78, x_79, x_13, x_81, x_88);
x_90 = l_Lean_Syntax_node2(x_72, x_74, x_76, x_89);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_3);
return x_91;
}
else
{
lean_object* x_92; lean_object* x_93; uint8_t x_94; 
x_92 = lean_unsigned_to_nat(2u);
x_93 = l_Lean_Syntax_getArg(x_42, x_92);
lean_inc(x_93);
x_94 = l_Lean_Syntax_matchesNull(x_93, x_12);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_93);
lean_dec(x_67);
lean_dec(x_44);
lean_dec(x_42);
lean_dec(x_16);
lean_dec(x_1);
x_95 = lean_ctor_get(x_2, 5);
lean_inc(x_95);
lean_dec(x_2);
x_96 = l_Lean_SourceInfo_fromRef(x_95, x_94);
lean_dec(x_95);
x_97 = lean_mk_string_unchecked("tacticRefine_lift_", 18, 18);
lean_inc(x_5);
lean_inc(x_4);
x_98 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_97);
x_99 = lean_mk_string_unchecked("refine_lift", 11, 11);
lean_inc(x_96);
x_100 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_100, 0, x_96);
lean_ctor_set(x_100, 1, x_99);
x_101 = lean_mk_string_unchecked("have", 4, 4);
lean_inc(x_101);
lean_inc(x_14);
lean_inc(x_5);
lean_inc(x_4);
x_102 = l_Lean_Name_mkStr4(x_4, x_5, x_14, x_101);
lean_inc(x_96);
x_103 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_103, 0, x_96);
lean_ctor_set(x_103, 1, x_101);
x_104 = lean_mk_string_unchecked(";", 1, 1);
lean_inc(x_96);
x_105 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_105, 0, x_96);
lean_ctor_set(x_105, 1, x_104);
x_106 = lean_mk_string_unchecked("syntheticHole", 13, 13);
x_107 = l_Lean_Name_mkStr4(x_4, x_5, x_14, x_106);
x_108 = lean_mk_string_unchecked("\?", 1, 1);
lean_inc(x_96);
x_109 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_109, 0, x_96);
lean_ctor_set(x_109, 1, x_108);
x_110 = lean_mk_string_unchecked("_", 1, 1);
lean_inc(x_96);
x_111 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_111, 0, x_96);
lean_ctor_set(x_111, 1, x_110);
lean_inc(x_96);
x_112 = l_Lean_Syntax_node2(x_96, x_107, x_109, x_111);
lean_inc(x_96);
x_113 = l_Lean_Syntax_node4(x_96, x_102, x_103, x_13, x_105, x_112);
x_114 = l_Lean_Syntax_node2(x_96, x_98, x_100, x_113);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_3);
return x_115;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; 
x_116 = l_Lean_Syntax_getArg(x_93, x_41);
lean_dec(x_93);
x_117 = lean_mk_string_unchecked("typeSpec", 8, 8);
lean_inc(x_14);
lean_inc(x_5);
lean_inc(x_4);
x_118 = l_Lean_Name_mkStr4(x_4, x_5, x_14, x_117);
lean_inc(x_116);
x_119 = l_Lean_Syntax_isOfKind(x_116, x_118);
if (x_119 == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
lean_dec(x_118);
lean_dec(x_116);
lean_dec(x_67);
lean_dec(x_44);
lean_dec(x_42);
lean_dec(x_16);
lean_dec(x_1);
x_120 = lean_ctor_get(x_2, 5);
lean_inc(x_120);
lean_dec(x_2);
x_121 = l_Lean_SourceInfo_fromRef(x_120, x_119);
lean_dec(x_120);
x_122 = lean_mk_string_unchecked("tacticRefine_lift_", 18, 18);
lean_inc(x_5);
lean_inc(x_4);
x_123 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_122);
x_124 = lean_mk_string_unchecked("refine_lift", 11, 11);
lean_inc(x_121);
x_125 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_125, 0, x_121);
lean_ctor_set(x_125, 1, x_124);
x_126 = lean_mk_string_unchecked("have", 4, 4);
lean_inc(x_126);
lean_inc(x_14);
lean_inc(x_5);
lean_inc(x_4);
x_127 = l_Lean_Name_mkStr4(x_4, x_5, x_14, x_126);
lean_inc(x_121);
x_128 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_128, 0, x_121);
lean_ctor_set(x_128, 1, x_126);
x_129 = lean_mk_string_unchecked(";", 1, 1);
lean_inc(x_121);
x_130 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_130, 0, x_121);
lean_ctor_set(x_130, 1, x_129);
x_131 = lean_mk_string_unchecked("syntheticHole", 13, 13);
x_132 = l_Lean_Name_mkStr4(x_4, x_5, x_14, x_131);
x_133 = lean_mk_string_unchecked("\?", 1, 1);
lean_inc(x_121);
x_134 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_134, 0, x_121);
lean_ctor_set(x_134, 1, x_133);
x_135 = lean_mk_string_unchecked("_", 1, 1);
lean_inc(x_121);
x_136 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_136, 0, x_121);
lean_ctor_set(x_136, 1, x_135);
lean_inc(x_121);
x_137 = l_Lean_Syntax_node2(x_121, x_132, x_134, x_136);
lean_inc(x_121);
x_138 = l_Lean_Syntax_node4(x_121, x_127, x_128, x_13, x_130, x_137);
x_139 = l_Lean_Syntax_node2(x_121, x_123, x_125, x_138);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_3);
return x_140;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; 
x_141 = lean_unsigned_to_nat(4u);
x_142 = l_Lean_Syntax_getArg(x_42, x_141);
x_143 = lean_mk_string_unchecked("byTactic", 8, 8);
lean_inc(x_14);
lean_inc(x_5);
lean_inc(x_4);
x_144 = l_Lean_Name_mkStr4(x_4, x_5, x_14, x_143);
lean_inc(x_142);
x_145 = l_Lean_Syntax_isOfKind(x_142, x_144);
lean_dec(x_144);
if (x_145 == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_dec(x_142);
lean_dec(x_118);
lean_dec(x_116);
lean_dec(x_67);
lean_dec(x_44);
lean_dec(x_42);
lean_dec(x_16);
lean_dec(x_1);
x_146 = lean_ctor_get(x_2, 5);
lean_inc(x_146);
lean_dec(x_2);
x_147 = l_Lean_SourceInfo_fromRef(x_146, x_145);
lean_dec(x_146);
x_148 = lean_mk_string_unchecked("tacticRefine_lift_", 18, 18);
lean_inc(x_5);
lean_inc(x_4);
x_149 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_148);
x_150 = lean_mk_string_unchecked("refine_lift", 11, 11);
lean_inc(x_147);
x_151 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_151, 0, x_147);
lean_ctor_set(x_151, 1, x_150);
x_152 = lean_mk_string_unchecked("have", 4, 4);
lean_inc(x_152);
lean_inc(x_14);
lean_inc(x_5);
lean_inc(x_4);
x_153 = l_Lean_Name_mkStr4(x_4, x_5, x_14, x_152);
lean_inc(x_147);
x_154 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_154, 0, x_147);
lean_ctor_set(x_154, 1, x_152);
x_155 = lean_mk_string_unchecked(";", 1, 1);
lean_inc(x_147);
x_156 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_156, 0, x_147);
lean_ctor_set(x_156, 1, x_155);
x_157 = lean_mk_string_unchecked("syntheticHole", 13, 13);
x_158 = l_Lean_Name_mkStr4(x_4, x_5, x_14, x_157);
x_159 = lean_mk_string_unchecked("\?", 1, 1);
lean_inc(x_147);
x_160 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_160, 0, x_147);
lean_ctor_set(x_160, 1, x_159);
x_161 = lean_mk_string_unchecked("_", 1, 1);
lean_inc(x_147);
x_162 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_162, 0, x_147);
lean_ctor_set(x_162, 1, x_161);
lean_inc(x_147);
x_163 = l_Lean_Syntax_node2(x_147, x_158, x_160, x_162);
lean_inc(x_147);
x_164 = l_Lean_Syntax_node4(x_147, x_153, x_154, x_13, x_156, x_163);
x_165 = l_Lean_Syntax_node2(x_147, x_149, x_151, x_164);
x_166 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_166, 0, x_165);
lean_ctor_set(x_166, 1, x_3);
return x_166;
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; 
x_167 = l_Lean_Syntax_getArg(x_142, x_12);
x_168 = lean_mk_string_unchecked("tacticSeq", 9, 9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_169 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_168);
lean_inc(x_167);
x_170 = l_Lean_Syntax_isOfKind(x_167, x_169);
if (x_170 == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
lean_dec(x_169);
lean_dec(x_167);
lean_dec(x_142);
lean_dec(x_118);
lean_dec(x_116);
lean_dec(x_67);
lean_dec(x_44);
lean_dec(x_42);
lean_dec(x_16);
lean_dec(x_1);
x_171 = lean_ctor_get(x_2, 5);
lean_inc(x_171);
lean_dec(x_2);
x_172 = l_Lean_SourceInfo_fromRef(x_171, x_170);
lean_dec(x_171);
x_173 = lean_mk_string_unchecked("tacticRefine_lift_", 18, 18);
lean_inc(x_5);
lean_inc(x_4);
x_174 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_173);
x_175 = lean_mk_string_unchecked("refine_lift", 11, 11);
lean_inc(x_172);
x_176 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_176, 0, x_172);
lean_ctor_set(x_176, 1, x_175);
x_177 = lean_mk_string_unchecked("have", 4, 4);
lean_inc(x_177);
lean_inc(x_14);
lean_inc(x_5);
lean_inc(x_4);
x_178 = l_Lean_Name_mkStr4(x_4, x_5, x_14, x_177);
lean_inc(x_172);
x_179 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_179, 0, x_172);
lean_ctor_set(x_179, 1, x_177);
x_180 = lean_mk_string_unchecked(";", 1, 1);
lean_inc(x_172);
x_181 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_181, 0, x_172);
lean_ctor_set(x_181, 1, x_180);
x_182 = lean_mk_string_unchecked("syntheticHole", 13, 13);
x_183 = l_Lean_Name_mkStr4(x_4, x_5, x_14, x_182);
x_184 = lean_mk_string_unchecked("\?", 1, 1);
lean_inc(x_172);
x_185 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_185, 0, x_172);
lean_ctor_set(x_185, 1, x_184);
x_186 = lean_mk_string_unchecked("_", 1, 1);
lean_inc(x_172);
x_187 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_187, 0, x_172);
lean_ctor_set(x_187, 1, x_186);
lean_inc(x_172);
x_188 = l_Lean_Syntax_node2(x_172, x_183, x_185, x_187);
lean_inc(x_172);
x_189 = l_Lean_Syntax_node4(x_172, x_178, x_179, x_13, x_181, x_188);
x_190 = l_Lean_Syntax_node2(x_172, x_174, x_176, x_189);
x_191 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_191, 0, x_190);
lean_ctor_set(x_191, 1, x_3);
return x_191;
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; uint8_t x_195; 
x_192 = l_Lean_Syntax_getArg(x_167, x_41);
lean_dec(x_167);
x_193 = lean_mk_string_unchecked("tacticSeq1Indented", 18, 18);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_194 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_193);
lean_inc(x_192);
x_195 = l_Lean_Syntax_isOfKind(x_192, x_194);
if (x_195 == 0)
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
lean_dec(x_194);
lean_dec(x_192);
lean_dec(x_169);
lean_dec(x_142);
lean_dec(x_118);
lean_dec(x_116);
lean_dec(x_67);
lean_dec(x_44);
lean_dec(x_42);
lean_dec(x_16);
lean_dec(x_1);
x_196 = lean_ctor_get(x_2, 5);
lean_inc(x_196);
lean_dec(x_2);
x_197 = l_Lean_SourceInfo_fromRef(x_196, x_195);
lean_dec(x_196);
x_198 = lean_mk_string_unchecked("tacticRefine_lift_", 18, 18);
lean_inc(x_5);
lean_inc(x_4);
x_199 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_198);
x_200 = lean_mk_string_unchecked("refine_lift", 11, 11);
lean_inc(x_197);
x_201 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_201, 0, x_197);
lean_ctor_set(x_201, 1, x_200);
x_202 = lean_mk_string_unchecked("have", 4, 4);
lean_inc(x_202);
lean_inc(x_14);
lean_inc(x_5);
lean_inc(x_4);
x_203 = l_Lean_Name_mkStr4(x_4, x_5, x_14, x_202);
lean_inc(x_197);
x_204 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_204, 0, x_197);
lean_ctor_set(x_204, 1, x_202);
x_205 = lean_mk_string_unchecked(";", 1, 1);
lean_inc(x_197);
x_206 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_206, 0, x_197);
lean_ctor_set(x_206, 1, x_205);
x_207 = lean_mk_string_unchecked("syntheticHole", 13, 13);
x_208 = l_Lean_Name_mkStr4(x_4, x_5, x_14, x_207);
x_209 = lean_mk_string_unchecked("\?", 1, 1);
lean_inc(x_197);
x_210 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_210, 0, x_197);
lean_ctor_set(x_210, 1, x_209);
x_211 = lean_mk_string_unchecked("_", 1, 1);
lean_inc(x_197);
x_212 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_212, 0, x_197);
lean_ctor_set(x_212, 1, x_211);
lean_inc(x_197);
x_213 = l_Lean_Syntax_node2(x_197, x_208, x_210, x_212);
lean_inc(x_197);
x_214 = l_Lean_Syntax_node4(x_197, x_203, x_204, x_13, x_206, x_213);
x_215 = l_Lean_Syntax_node2(x_197, x_199, x_201, x_214);
x_216 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_216, 0, x_215);
lean_ctor_set(x_216, 1, x_3);
return x_216;
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; uint8_t x_227; 
lean_dec(x_13);
x_217 = l_Lean_Syntax_getArg(x_142, x_41);
lean_dec(x_142);
x_218 = lean_ctor_get(x_2, 5);
lean_inc(x_218);
x_219 = l_Lean_replaceRef(x_217, x_218);
x_220 = lean_ctor_get(x_2, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_2, 1);
lean_inc(x_221);
x_222 = lean_ctor_get(x_2, 2);
lean_inc(x_222);
x_223 = lean_ctor_get(x_2, 3);
lean_inc(x_223);
x_224 = lean_ctor_get(x_2, 4);
lean_inc(x_224);
lean_inc(x_224);
lean_inc(x_223);
lean_inc(x_222);
lean_inc(x_221);
lean_inc(x_220);
x_225 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_225, 0, x_220);
lean_ctor_set(x_225, 1, x_221);
lean_ctor_set(x_225, 2, x_222);
lean_ctor_set(x_225, 3, x_223);
lean_ctor_set(x_225, 4, x_224);
lean_ctor_set(x_225, 5, x_219);
x_226 = l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticHave____1___lam__0(x_225, x_225, x_3);
x_227 = !lean_is_exclusive(x_226);
if (x_227 == 0)
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; uint8_t x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; uint8_t x_242; 
x_228 = lean_ctor_get(x_226, 0);
x_229 = lean_ctor_get(x_226, 1);
x_230 = l_Lean_Syntax_getArg(x_192, x_41);
lean_dec(x_192);
x_231 = l_Lean_Syntax_getArgs(x_230);
lean_dec(x_230);
x_232 = lean_box(0);
x_233 = lean_unbox(x_232);
x_234 = l_Lean_SourceInfo_fromRef(x_228, x_233);
lean_dec(x_228);
x_235 = lean_mk_string_unchecked("null", 4, 4);
x_236 = l_Lean_Name_mkStr1(x_235);
x_237 = l_Array_mkArray0(lean_box(0));
lean_inc(x_237);
x_238 = l_Array_appendCore___redArg(x_237, x_231);
lean_dec(x_231);
lean_inc(x_236);
lean_inc(x_234);
x_239 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_239, 0, x_234);
lean_ctor_set(x_239, 1, x_236);
lean_ctor_set(x_239, 2, x_238);
lean_inc(x_194);
lean_inc(x_234);
x_240 = l_Lean_Syntax_node1(x_234, x_194, x_239);
x_241 = l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticHave____1___lam__0(x_2, x_2, x_229);
x_242 = !lean_is_exclusive(x_241);
if (x_242 == 0)
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; uint8_t x_246; 
x_243 = lean_ctor_get(x_241, 0);
x_244 = lean_ctor_get(x_241, 1);
x_245 = l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticHave____1___lam__1(x_243, x_2, x_244);
lean_dec(x_2);
lean_dec(x_243);
x_246 = !lean_is_exclusive(x_245);
if (x_246 == 0)
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; uint8_t x_260; 
x_247 = lean_ctor_get(x_245, 0);
x_248 = lean_ctor_get(x_245, 1);
x_249 = lean_mk_string_unchecked("withAnnotateState", 17, 17);
x_250 = lean_mk_string_unchecked("with_annotate_state", 19, 19);
x_251 = lean_mk_string_unchecked("paren", 5, 5);
lean_inc(x_251);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_252 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_251);
x_253 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_253);
lean_inc(x_234);
lean_ctor_set_tag(x_245, 2);
lean_ctor_set(x_245, 1, x_253);
lean_ctor_set(x_245, 0, x_234);
lean_inc(x_169);
lean_inc(x_234);
x_254 = l_Lean_Syntax_node1(x_234, x_169, x_240);
x_255 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_255);
lean_inc(x_234);
lean_ctor_set_tag(x_241, 2);
lean_ctor_set(x_241, 1, x_255);
lean_ctor_set(x_241, 0, x_234);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_256 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_249);
lean_inc(x_234);
lean_ctor_set_tag(x_226, 2);
lean_ctor_set(x_226, 1, x_250);
lean_ctor_set(x_226, 0, x_234);
lean_inc(x_234);
x_257 = l_Lean_Syntax_node3(x_234, x_252, x_245, x_254, x_241);
x_258 = l_Lean_Syntax_node3(x_234, x_256, x_226, x_217, x_257);
x_259 = l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticHave____1___lam__0(x_225, x_225, x_248);
x_260 = !lean_is_exclusive(x_259);
if (x_260 == 0)
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; uint8_t x_264; 
x_261 = lean_ctor_get(x_259, 0);
x_262 = lean_ctor_get(x_259, 1);
x_263 = l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticHave____1___lam__1(x_261, x_225, x_262);
lean_dec(x_225);
lean_dec(x_261);
x_264 = !lean_is_exclusive(x_263);
if (x_264 == 0)
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; uint8_t x_284; 
x_265 = lean_ctor_get(x_263, 0);
x_266 = lean_ctor_get(x_263, 1);
lean_inc(x_236);
lean_inc(x_247);
x_267 = l_Lean_Syntax_node1(x_247, x_236, x_258);
x_268 = l_Lean_Syntax_getArg(x_1, x_41);
lean_dec(x_1);
x_269 = lean_mk_string_unchecked("caseArg", 7, 7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_270 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_269);
x_271 = lean_mk_string_unchecked("binderIdent", 11, 11);
lean_inc(x_4);
x_272 = l_Lean_Name_mkStr2(x_4, x_271);
x_273 = lean_mk_string_unchecked("body", 4, 4);
lean_inc(x_273);
x_274 = l_String_toSubstring_x27(x_273);
x_275 = l_Lean_Name_mkStr1(x_273);
lean_inc(x_222);
lean_inc(x_221);
x_276 = l_Lean_addMacroScope(x_221, x_275, x_222);
x_277 = lean_box(0);
lean_inc(x_276);
lean_inc(x_274);
lean_inc(x_265);
x_278 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_278, 0, x_265);
lean_ctor_set(x_278, 1, x_274);
lean_ctor_set(x_278, 2, x_276);
lean_ctor_set(x_278, 3, x_277);
lean_inc(x_265);
x_279 = l_Lean_Syntax_node1(x_265, x_272, x_278);
lean_inc(x_237);
lean_inc(x_236);
lean_inc(x_265);
x_280 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_280, 0, x_265);
lean_ctor_set(x_280, 1, x_236);
lean_ctor_set(x_280, 2, x_237);
x_281 = l_Lean_replaceRef(x_268, x_218);
lean_dec(x_218);
lean_dec(x_268);
x_282 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_282, 0, x_220);
lean_ctor_set(x_282, 1, x_221);
lean_ctor_set(x_282, 2, x_222);
lean_ctor_set(x_282, 3, x_223);
lean_ctor_set(x_282, 4, x_224);
lean_ctor_set(x_282, 5, x_281);
x_283 = l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticHave____1___lam__0(x_282, x_282, x_266);
x_284 = !lean_is_exclusive(x_283);
if (x_284 == 0)
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; uint8_t x_288; 
x_285 = lean_ctor_get(x_283, 0);
x_286 = lean_ctor_get(x_283, 1);
x_287 = l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticHave____1___lam__1(x_285, x_282, x_286);
lean_dec(x_282);
lean_dec(x_285);
x_288 = !lean_is_exclusive(x_287);
if (x_288 == 0)
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; 
x_289 = lean_ctor_get(x_287, 0);
x_290 = l_Lean_Syntax_getArg(x_42, x_12);
lean_dec(x_42);
lean_inc(x_194);
lean_inc(x_247);
x_291 = l_Lean_Syntax_node1(x_247, x_194, x_267);
x_292 = lean_mk_string_unchecked("case", 4, 4);
lean_inc(x_265);
x_293 = l_Lean_Syntax_node2(x_265, x_270, x_279, x_280);
x_294 = lean_mk_string_unchecked("=>", 2, 2);
x_295 = l_Lean_Syntax_getArgs(x_290);
lean_dec(x_290);
lean_inc(x_169);
x_296 = l_Lean_Syntax_node1(x_247, x_169, x_291);
lean_inc(x_292);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_297 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_292);
lean_inc(x_265);
lean_ctor_set_tag(x_283, 2);
lean_ctor_set(x_283, 1, x_292);
lean_ctor_set(x_283, 0, x_265);
lean_inc(x_236);
lean_inc(x_265);
x_298 = l_Lean_Syntax_node1(x_265, x_236, x_293);
lean_inc(x_265);
lean_ctor_set_tag(x_263, 2);
lean_ctor_set(x_263, 1, x_294);
x_299 = l_Lean_Syntax_getArg(x_116, x_12);
lean_dec(x_116);
x_300 = l_Lean_Syntax_node4(x_265, x_297, x_283, x_298, x_263, x_296);
x_301 = lean_mk_string_unchecked("focus", 5, 5);
lean_inc(x_301);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_302 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_301);
lean_inc(x_289);
lean_ctor_set_tag(x_259, 2);
lean_ctor_set(x_259, 1, x_301);
lean_ctor_set(x_259, 0, x_289);
x_303 = lean_mk_string_unchecked("refine", 6, 6);
lean_inc(x_303);
lean_inc(x_5);
lean_inc(x_4);
x_304 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_303);
lean_inc(x_289);
x_305 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_305, 0, x_289);
lean_ctor_set(x_305, 1, x_303);
x_306 = lean_mk_string_unchecked("noImplicitLambda", 16, 16);
lean_inc(x_14);
lean_inc(x_5);
lean_inc(x_4);
x_307 = l_Lean_Name_mkStr4(x_4, x_5, x_14, x_306);
x_308 = lean_mk_string_unchecked("no_implicit_lambda%", 19, 19);
lean_inc(x_289);
x_309 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_309, 0, x_289);
lean_ctor_set(x_309, 1, x_308);
lean_inc(x_14);
lean_inc(x_5);
lean_inc(x_4);
x_310 = l_Lean_Name_mkStr4(x_4, x_5, x_14, x_251);
lean_inc(x_289);
x_311 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_311, 0, x_289);
lean_ctor_set(x_311, 1, x_253);
x_312 = lean_mk_string_unchecked("have", 4, 4);
lean_inc(x_312);
lean_inc(x_14);
lean_inc(x_5);
lean_inc(x_4);
x_313 = l_Lean_Name_mkStr4(x_4, x_5, x_14, x_312);
lean_inc(x_289);
x_314 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_314, 0, x_289);
lean_ctor_set(x_314, 1, x_312);
lean_inc(x_237);
x_315 = l_Array_appendCore___redArg(x_237, x_295);
lean_dec(x_295);
lean_inc(x_236);
lean_inc(x_289);
x_316 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_316, 0, x_289);
lean_ctor_set(x_316, 1, x_236);
lean_ctor_set(x_316, 2, x_315);
x_317 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_289);
x_318 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_318, 0, x_289);
lean_ctor_set(x_318, 1, x_317);
lean_inc(x_289);
x_319 = l_Lean_Syntax_node2(x_289, x_118, x_318, x_299);
lean_inc(x_236);
lean_inc(x_289);
x_320 = l_Lean_Syntax_node1(x_289, x_236, x_319);
x_321 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_289);
x_322 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_322, 0, x_289);
lean_ctor_set(x_322, 1, x_321);
x_323 = lean_mk_string_unchecked("syntheticHole", 13, 13);
x_324 = l_Lean_Name_mkStr4(x_4, x_5, x_14, x_323);
x_325 = lean_mk_string_unchecked("\?", 1, 1);
lean_inc(x_289);
x_326 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_326, 0, x_289);
lean_ctor_set(x_326, 1, x_325);
lean_inc(x_289);
x_327 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_327, 0, x_289);
lean_ctor_set(x_327, 1, x_274);
lean_ctor_set(x_327, 2, x_276);
lean_ctor_set(x_327, 3, x_277);
lean_inc(x_326);
lean_inc(x_324);
lean_inc(x_289);
x_328 = l_Lean_Syntax_node2(x_289, x_324, x_326, x_327);
lean_inc(x_289);
x_329 = l_Lean_Syntax_node5(x_289, x_44, x_67, x_316, x_320, x_322, x_328);
lean_inc(x_289);
x_330 = l_Lean_Syntax_node1(x_289, x_16, x_329);
x_331 = lean_mk_string_unchecked(";", 1, 1);
lean_inc(x_289);
x_332 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_332, 0, x_289);
lean_ctor_set(x_332, 1, x_331);
x_333 = lean_mk_string_unchecked("_", 1, 1);
lean_inc(x_289);
x_334 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_334, 0, x_289);
lean_ctor_set(x_334, 1, x_333);
lean_inc(x_289);
x_335 = l_Lean_Syntax_node2(x_289, x_324, x_326, x_334);
lean_inc(x_289);
x_336 = l_Lean_Syntax_node4(x_289, x_313, x_314, x_330, x_332, x_335);
lean_inc(x_289);
x_337 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_337, 0, x_289);
lean_ctor_set(x_337, 1, x_255);
lean_inc(x_289);
x_338 = l_Lean_Syntax_node3(x_289, x_310, x_311, x_336, x_337);
lean_inc(x_289);
x_339 = l_Lean_Syntax_node2(x_289, x_307, x_309, x_338);
lean_inc(x_289);
x_340 = l_Lean_Syntax_node2(x_289, x_304, x_305, x_339);
lean_inc(x_236);
lean_inc(x_289);
x_341 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_341, 0, x_289);
lean_ctor_set(x_341, 1, x_236);
lean_ctor_set(x_341, 2, x_237);
lean_inc(x_289);
x_342 = l_Lean_Syntax_node3(x_289, x_236, x_340, x_341, x_300);
lean_inc(x_289);
x_343 = l_Lean_Syntax_node1(x_289, x_194, x_342);
lean_inc(x_289);
x_344 = l_Lean_Syntax_node1(x_289, x_169, x_343);
x_345 = l_Lean_Syntax_node2(x_289, x_302, x_259, x_344);
lean_ctor_set(x_287, 0, x_345);
return x_287;
}
else
{
lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; 
x_346 = lean_ctor_get(x_287, 0);
x_347 = lean_ctor_get(x_287, 1);
lean_inc(x_347);
lean_inc(x_346);
lean_dec(x_287);
x_348 = l_Lean_Syntax_getArg(x_42, x_12);
lean_dec(x_42);
lean_inc(x_194);
lean_inc(x_247);
x_349 = l_Lean_Syntax_node1(x_247, x_194, x_267);
x_350 = lean_mk_string_unchecked("case", 4, 4);
lean_inc(x_265);
x_351 = l_Lean_Syntax_node2(x_265, x_270, x_279, x_280);
x_352 = lean_mk_string_unchecked("=>", 2, 2);
x_353 = l_Lean_Syntax_getArgs(x_348);
lean_dec(x_348);
lean_inc(x_169);
x_354 = l_Lean_Syntax_node1(x_247, x_169, x_349);
lean_inc(x_350);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_355 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_350);
lean_inc(x_265);
lean_ctor_set_tag(x_283, 2);
lean_ctor_set(x_283, 1, x_350);
lean_ctor_set(x_283, 0, x_265);
lean_inc(x_236);
lean_inc(x_265);
x_356 = l_Lean_Syntax_node1(x_265, x_236, x_351);
lean_inc(x_265);
lean_ctor_set_tag(x_263, 2);
lean_ctor_set(x_263, 1, x_352);
x_357 = l_Lean_Syntax_getArg(x_116, x_12);
lean_dec(x_116);
x_358 = l_Lean_Syntax_node4(x_265, x_355, x_283, x_356, x_263, x_354);
x_359 = lean_mk_string_unchecked("focus", 5, 5);
lean_inc(x_359);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_360 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_359);
lean_inc(x_346);
lean_ctor_set_tag(x_259, 2);
lean_ctor_set(x_259, 1, x_359);
lean_ctor_set(x_259, 0, x_346);
x_361 = lean_mk_string_unchecked("refine", 6, 6);
lean_inc(x_361);
lean_inc(x_5);
lean_inc(x_4);
x_362 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_361);
lean_inc(x_346);
x_363 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_363, 0, x_346);
lean_ctor_set(x_363, 1, x_361);
x_364 = lean_mk_string_unchecked("noImplicitLambda", 16, 16);
lean_inc(x_14);
lean_inc(x_5);
lean_inc(x_4);
x_365 = l_Lean_Name_mkStr4(x_4, x_5, x_14, x_364);
x_366 = lean_mk_string_unchecked("no_implicit_lambda%", 19, 19);
lean_inc(x_346);
x_367 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_367, 0, x_346);
lean_ctor_set(x_367, 1, x_366);
lean_inc(x_14);
lean_inc(x_5);
lean_inc(x_4);
x_368 = l_Lean_Name_mkStr4(x_4, x_5, x_14, x_251);
lean_inc(x_346);
x_369 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_369, 0, x_346);
lean_ctor_set(x_369, 1, x_253);
x_370 = lean_mk_string_unchecked("have", 4, 4);
lean_inc(x_370);
lean_inc(x_14);
lean_inc(x_5);
lean_inc(x_4);
x_371 = l_Lean_Name_mkStr4(x_4, x_5, x_14, x_370);
lean_inc(x_346);
x_372 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_372, 0, x_346);
lean_ctor_set(x_372, 1, x_370);
lean_inc(x_237);
x_373 = l_Array_appendCore___redArg(x_237, x_353);
lean_dec(x_353);
lean_inc(x_236);
lean_inc(x_346);
x_374 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_374, 0, x_346);
lean_ctor_set(x_374, 1, x_236);
lean_ctor_set(x_374, 2, x_373);
x_375 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_346);
x_376 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_376, 0, x_346);
lean_ctor_set(x_376, 1, x_375);
lean_inc(x_346);
x_377 = l_Lean_Syntax_node2(x_346, x_118, x_376, x_357);
lean_inc(x_236);
lean_inc(x_346);
x_378 = l_Lean_Syntax_node1(x_346, x_236, x_377);
x_379 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_346);
x_380 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_380, 0, x_346);
lean_ctor_set(x_380, 1, x_379);
x_381 = lean_mk_string_unchecked("syntheticHole", 13, 13);
x_382 = l_Lean_Name_mkStr4(x_4, x_5, x_14, x_381);
x_383 = lean_mk_string_unchecked("\?", 1, 1);
lean_inc(x_346);
x_384 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_384, 0, x_346);
lean_ctor_set(x_384, 1, x_383);
lean_inc(x_346);
x_385 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_385, 0, x_346);
lean_ctor_set(x_385, 1, x_274);
lean_ctor_set(x_385, 2, x_276);
lean_ctor_set(x_385, 3, x_277);
lean_inc(x_384);
lean_inc(x_382);
lean_inc(x_346);
x_386 = l_Lean_Syntax_node2(x_346, x_382, x_384, x_385);
lean_inc(x_346);
x_387 = l_Lean_Syntax_node5(x_346, x_44, x_67, x_374, x_378, x_380, x_386);
lean_inc(x_346);
x_388 = l_Lean_Syntax_node1(x_346, x_16, x_387);
x_389 = lean_mk_string_unchecked(";", 1, 1);
lean_inc(x_346);
x_390 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_390, 0, x_346);
lean_ctor_set(x_390, 1, x_389);
x_391 = lean_mk_string_unchecked("_", 1, 1);
lean_inc(x_346);
x_392 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_392, 0, x_346);
lean_ctor_set(x_392, 1, x_391);
lean_inc(x_346);
x_393 = l_Lean_Syntax_node2(x_346, x_382, x_384, x_392);
lean_inc(x_346);
x_394 = l_Lean_Syntax_node4(x_346, x_371, x_372, x_388, x_390, x_393);
lean_inc(x_346);
x_395 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_395, 0, x_346);
lean_ctor_set(x_395, 1, x_255);
lean_inc(x_346);
x_396 = l_Lean_Syntax_node3(x_346, x_368, x_369, x_394, x_395);
lean_inc(x_346);
x_397 = l_Lean_Syntax_node2(x_346, x_365, x_367, x_396);
lean_inc(x_346);
x_398 = l_Lean_Syntax_node2(x_346, x_362, x_363, x_397);
lean_inc(x_236);
lean_inc(x_346);
x_399 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_399, 0, x_346);
lean_ctor_set(x_399, 1, x_236);
lean_ctor_set(x_399, 2, x_237);
lean_inc(x_346);
x_400 = l_Lean_Syntax_node3(x_346, x_236, x_398, x_399, x_358);
lean_inc(x_346);
x_401 = l_Lean_Syntax_node1(x_346, x_194, x_400);
lean_inc(x_346);
x_402 = l_Lean_Syntax_node1(x_346, x_169, x_401);
x_403 = l_Lean_Syntax_node2(x_346, x_360, x_259, x_402);
x_404 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_404, 0, x_403);
lean_ctor_set(x_404, 1, x_347);
return x_404;
}
}
else
{
lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; 
x_405 = lean_ctor_get(x_283, 0);
x_406 = lean_ctor_get(x_283, 1);
lean_inc(x_406);
lean_inc(x_405);
lean_dec(x_283);
x_407 = l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticHave____1___lam__1(x_405, x_282, x_406);
lean_dec(x_282);
lean_dec(x_405);
x_408 = lean_ctor_get(x_407, 0);
lean_inc(x_408);
x_409 = lean_ctor_get(x_407, 1);
lean_inc(x_409);
if (lean_is_exclusive(x_407)) {
 lean_ctor_release(x_407, 0);
 lean_ctor_release(x_407, 1);
 x_410 = x_407;
} else {
 lean_dec_ref(x_407);
 x_410 = lean_box(0);
}
x_411 = l_Lean_Syntax_getArg(x_42, x_12);
lean_dec(x_42);
lean_inc(x_194);
lean_inc(x_247);
x_412 = l_Lean_Syntax_node1(x_247, x_194, x_267);
x_413 = lean_mk_string_unchecked("case", 4, 4);
lean_inc(x_265);
x_414 = l_Lean_Syntax_node2(x_265, x_270, x_279, x_280);
x_415 = lean_mk_string_unchecked("=>", 2, 2);
x_416 = l_Lean_Syntax_getArgs(x_411);
lean_dec(x_411);
lean_inc(x_169);
x_417 = l_Lean_Syntax_node1(x_247, x_169, x_412);
lean_inc(x_413);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_418 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_413);
lean_inc(x_265);
x_419 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_419, 0, x_265);
lean_ctor_set(x_419, 1, x_413);
lean_inc(x_236);
lean_inc(x_265);
x_420 = l_Lean_Syntax_node1(x_265, x_236, x_414);
lean_inc(x_265);
lean_ctor_set_tag(x_263, 2);
lean_ctor_set(x_263, 1, x_415);
x_421 = l_Lean_Syntax_getArg(x_116, x_12);
lean_dec(x_116);
x_422 = l_Lean_Syntax_node4(x_265, x_418, x_419, x_420, x_263, x_417);
x_423 = lean_mk_string_unchecked("focus", 5, 5);
lean_inc(x_423);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_424 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_423);
lean_inc(x_408);
lean_ctor_set_tag(x_259, 2);
lean_ctor_set(x_259, 1, x_423);
lean_ctor_set(x_259, 0, x_408);
x_425 = lean_mk_string_unchecked("refine", 6, 6);
lean_inc(x_425);
lean_inc(x_5);
lean_inc(x_4);
x_426 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_425);
lean_inc(x_408);
x_427 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_427, 0, x_408);
lean_ctor_set(x_427, 1, x_425);
x_428 = lean_mk_string_unchecked("noImplicitLambda", 16, 16);
lean_inc(x_14);
lean_inc(x_5);
lean_inc(x_4);
x_429 = l_Lean_Name_mkStr4(x_4, x_5, x_14, x_428);
x_430 = lean_mk_string_unchecked("no_implicit_lambda%", 19, 19);
lean_inc(x_408);
x_431 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_431, 0, x_408);
lean_ctor_set(x_431, 1, x_430);
lean_inc(x_14);
lean_inc(x_5);
lean_inc(x_4);
x_432 = l_Lean_Name_mkStr4(x_4, x_5, x_14, x_251);
lean_inc(x_408);
x_433 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_433, 0, x_408);
lean_ctor_set(x_433, 1, x_253);
x_434 = lean_mk_string_unchecked("have", 4, 4);
lean_inc(x_434);
lean_inc(x_14);
lean_inc(x_5);
lean_inc(x_4);
x_435 = l_Lean_Name_mkStr4(x_4, x_5, x_14, x_434);
lean_inc(x_408);
x_436 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_436, 0, x_408);
lean_ctor_set(x_436, 1, x_434);
lean_inc(x_237);
x_437 = l_Array_appendCore___redArg(x_237, x_416);
lean_dec(x_416);
lean_inc(x_236);
lean_inc(x_408);
x_438 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_438, 0, x_408);
lean_ctor_set(x_438, 1, x_236);
lean_ctor_set(x_438, 2, x_437);
x_439 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_408);
x_440 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_440, 0, x_408);
lean_ctor_set(x_440, 1, x_439);
lean_inc(x_408);
x_441 = l_Lean_Syntax_node2(x_408, x_118, x_440, x_421);
lean_inc(x_236);
lean_inc(x_408);
x_442 = l_Lean_Syntax_node1(x_408, x_236, x_441);
x_443 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_408);
x_444 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_444, 0, x_408);
lean_ctor_set(x_444, 1, x_443);
x_445 = lean_mk_string_unchecked("syntheticHole", 13, 13);
x_446 = l_Lean_Name_mkStr4(x_4, x_5, x_14, x_445);
x_447 = lean_mk_string_unchecked("\?", 1, 1);
lean_inc(x_408);
x_448 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_448, 0, x_408);
lean_ctor_set(x_448, 1, x_447);
lean_inc(x_408);
x_449 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_449, 0, x_408);
lean_ctor_set(x_449, 1, x_274);
lean_ctor_set(x_449, 2, x_276);
lean_ctor_set(x_449, 3, x_277);
lean_inc(x_448);
lean_inc(x_446);
lean_inc(x_408);
x_450 = l_Lean_Syntax_node2(x_408, x_446, x_448, x_449);
lean_inc(x_408);
x_451 = l_Lean_Syntax_node5(x_408, x_44, x_67, x_438, x_442, x_444, x_450);
lean_inc(x_408);
x_452 = l_Lean_Syntax_node1(x_408, x_16, x_451);
x_453 = lean_mk_string_unchecked(";", 1, 1);
lean_inc(x_408);
x_454 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_454, 0, x_408);
lean_ctor_set(x_454, 1, x_453);
x_455 = lean_mk_string_unchecked("_", 1, 1);
lean_inc(x_408);
x_456 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_456, 0, x_408);
lean_ctor_set(x_456, 1, x_455);
lean_inc(x_408);
x_457 = l_Lean_Syntax_node2(x_408, x_446, x_448, x_456);
lean_inc(x_408);
x_458 = l_Lean_Syntax_node4(x_408, x_435, x_436, x_452, x_454, x_457);
lean_inc(x_408);
x_459 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_459, 0, x_408);
lean_ctor_set(x_459, 1, x_255);
lean_inc(x_408);
x_460 = l_Lean_Syntax_node3(x_408, x_432, x_433, x_458, x_459);
lean_inc(x_408);
x_461 = l_Lean_Syntax_node2(x_408, x_429, x_431, x_460);
lean_inc(x_408);
x_462 = l_Lean_Syntax_node2(x_408, x_426, x_427, x_461);
lean_inc(x_236);
lean_inc(x_408);
x_463 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_463, 0, x_408);
lean_ctor_set(x_463, 1, x_236);
lean_ctor_set(x_463, 2, x_237);
lean_inc(x_408);
x_464 = l_Lean_Syntax_node3(x_408, x_236, x_462, x_463, x_422);
lean_inc(x_408);
x_465 = l_Lean_Syntax_node1(x_408, x_194, x_464);
lean_inc(x_408);
x_466 = l_Lean_Syntax_node1(x_408, x_169, x_465);
x_467 = l_Lean_Syntax_node2(x_408, x_424, x_259, x_466);
if (lean_is_scalar(x_410)) {
 x_468 = lean_alloc_ctor(0, 2, 0);
} else {
 x_468 = x_410;
}
lean_ctor_set(x_468, 0, x_467);
lean_ctor_set(x_468, 1, x_409);
return x_468;
}
}
else
{
lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; 
x_469 = lean_ctor_get(x_263, 0);
x_470 = lean_ctor_get(x_263, 1);
lean_inc(x_470);
lean_inc(x_469);
lean_dec(x_263);
lean_inc(x_236);
lean_inc(x_247);
x_471 = l_Lean_Syntax_node1(x_247, x_236, x_258);
x_472 = l_Lean_Syntax_getArg(x_1, x_41);
lean_dec(x_1);
x_473 = lean_mk_string_unchecked("caseArg", 7, 7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_474 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_473);
x_475 = lean_mk_string_unchecked("binderIdent", 11, 11);
lean_inc(x_4);
x_476 = l_Lean_Name_mkStr2(x_4, x_475);
x_477 = lean_mk_string_unchecked("body", 4, 4);
lean_inc(x_477);
x_478 = l_String_toSubstring_x27(x_477);
x_479 = l_Lean_Name_mkStr1(x_477);
lean_inc(x_222);
lean_inc(x_221);
x_480 = l_Lean_addMacroScope(x_221, x_479, x_222);
x_481 = lean_box(0);
lean_inc(x_480);
lean_inc(x_478);
lean_inc(x_469);
x_482 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_482, 0, x_469);
lean_ctor_set(x_482, 1, x_478);
lean_ctor_set(x_482, 2, x_480);
lean_ctor_set(x_482, 3, x_481);
lean_inc(x_469);
x_483 = l_Lean_Syntax_node1(x_469, x_476, x_482);
lean_inc(x_237);
lean_inc(x_236);
lean_inc(x_469);
x_484 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_484, 0, x_469);
lean_ctor_set(x_484, 1, x_236);
lean_ctor_set(x_484, 2, x_237);
x_485 = l_Lean_replaceRef(x_472, x_218);
lean_dec(x_218);
lean_dec(x_472);
x_486 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_486, 0, x_220);
lean_ctor_set(x_486, 1, x_221);
lean_ctor_set(x_486, 2, x_222);
lean_ctor_set(x_486, 3, x_223);
lean_ctor_set(x_486, 4, x_224);
lean_ctor_set(x_486, 5, x_485);
x_487 = l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticHave____1___lam__0(x_486, x_486, x_470);
x_488 = lean_ctor_get(x_487, 0);
lean_inc(x_488);
x_489 = lean_ctor_get(x_487, 1);
lean_inc(x_489);
if (lean_is_exclusive(x_487)) {
 lean_ctor_release(x_487, 0);
 lean_ctor_release(x_487, 1);
 x_490 = x_487;
} else {
 lean_dec_ref(x_487);
 x_490 = lean_box(0);
}
x_491 = l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticHave____1___lam__1(x_488, x_486, x_489);
lean_dec(x_486);
lean_dec(x_488);
x_492 = lean_ctor_get(x_491, 0);
lean_inc(x_492);
x_493 = lean_ctor_get(x_491, 1);
lean_inc(x_493);
if (lean_is_exclusive(x_491)) {
 lean_ctor_release(x_491, 0);
 lean_ctor_release(x_491, 1);
 x_494 = x_491;
} else {
 lean_dec_ref(x_491);
 x_494 = lean_box(0);
}
x_495 = l_Lean_Syntax_getArg(x_42, x_12);
lean_dec(x_42);
lean_inc(x_194);
lean_inc(x_247);
x_496 = l_Lean_Syntax_node1(x_247, x_194, x_471);
x_497 = lean_mk_string_unchecked("case", 4, 4);
lean_inc(x_469);
x_498 = l_Lean_Syntax_node2(x_469, x_474, x_483, x_484);
x_499 = lean_mk_string_unchecked("=>", 2, 2);
x_500 = l_Lean_Syntax_getArgs(x_495);
lean_dec(x_495);
lean_inc(x_169);
x_501 = l_Lean_Syntax_node1(x_247, x_169, x_496);
lean_inc(x_497);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_502 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_497);
lean_inc(x_469);
if (lean_is_scalar(x_490)) {
 x_503 = lean_alloc_ctor(2, 2, 0);
} else {
 x_503 = x_490;
 lean_ctor_set_tag(x_503, 2);
}
lean_ctor_set(x_503, 0, x_469);
lean_ctor_set(x_503, 1, x_497);
lean_inc(x_236);
lean_inc(x_469);
x_504 = l_Lean_Syntax_node1(x_469, x_236, x_498);
lean_inc(x_469);
x_505 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_505, 0, x_469);
lean_ctor_set(x_505, 1, x_499);
x_506 = l_Lean_Syntax_getArg(x_116, x_12);
lean_dec(x_116);
x_507 = l_Lean_Syntax_node4(x_469, x_502, x_503, x_504, x_505, x_501);
x_508 = lean_mk_string_unchecked("focus", 5, 5);
lean_inc(x_508);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_509 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_508);
lean_inc(x_492);
lean_ctor_set_tag(x_259, 2);
lean_ctor_set(x_259, 1, x_508);
lean_ctor_set(x_259, 0, x_492);
x_510 = lean_mk_string_unchecked("refine", 6, 6);
lean_inc(x_510);
lean_inc(x_5);
lean_inc(x_4);
x_511 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_510);
lean_inc(x_492);
x_512 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_512, 0, x_492);
lean_ctor_set(x_512, 1, x_510);
x_513 = lean_mk_string_unchecked("noImplicitLambda", 16, 16);
lean_inc(x_14);
lean_inc(x_5);
lean_inc(x_4);
x_514 = l_Lean_Name_mkStr4(x_4, x_5, x_14, x_513);
x_515 = lean_mk_string_unchecked("no_implicit_lambda%", 19, 19);
lean_inc(x_492);
x_516 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_516, 0, x_492);
lean_ctor_set(x_516, 1, x_515);
lean_inc(x_14);
lean_inc(x_5);
lean_inc(x_4);
x_517 = l_Lean_Name_mkStr4(x_4, x_5, x_14, x_251);
lean_inc(x_492);
x_518 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_518, 0, x_492);
lean_ctor_set(x_518, 1, x_253);
x_519 = lean_mk_string_unchecked("have", 4, 4);
lean_inc(x_519);
lean_inc(x_14);
lean_inc(x_5);
lean_inc(x_4);
x_520 = l_Lean_Name_mkStr4(x_4, x_5, x_14, x_519);
lean_inc(x_492);
x_521 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_521, 0, x_492);
lean_ctor_set(x_521, 1, x_519);
lean_inc(x_237);
x_522 = l_Array_appendCore___redArg(x_237, x_500);
lean_dec(x_500);
lean_inc(x_236);
lean_inc(x_492);
x_523 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_523, 0, x_492);
lean_ctor_set(x_523, 1, x_236);
lean_ctor_set(x_523, 2, x_522);
x_524 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_492);
x_525 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_525, 0, x_492);
lean_ctor_set(x_525, 1, x_524);
lean_inc(x_492);
x_526 = l_Lean_Syntax_node2(x_492, x_118, x_525, x_506);
lean_inc(x_236);
lean_inc(x_492);
x_527 = l_Lean_Syntax_node1(x_492, x_236, x_526);
x_528 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_492);
x_529 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_529, 0, x_492);
lean_ctor_set(x_529, 1, x_528);
x_530 = lean_mk_string_unchecked("syntheticHole", 13, 13);
x_531 = l_Lean_Name_mkStr4(x_4, x_5, x_14, x_530);
x_532 = lean_mk_string_unchecked("\?", 1, 1);
lean_inc(x_492);
x_533 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_533, 0, x_492);
lean_ctor_set(x_533, 1, x_532);
lean_inc(x_492);
x_534 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_534, 0, x_492);
lean_ctor_set(x_534, 1, x_478);
lean_ctor_set(x_534, 2, x_480);
lean_ctor_set(x_534, 3, x_481);
lean_inc(x_533);
lean_inc(x_531);
lean_inc(x_492);
x_535 = l_Lean_Syntax_node2(x_492, x_531, x_533, x_534);
lean_inc(x_492);
x_536 = l_Lean_Syntax_node5(x_492, x_44, x_67, x_523, x_527, x_529, x_535);
lean_inc(x_492);
x_537 = l_Lean_Syntax_node1(x_492, x_16, x_536);
x_538 = lean_mk_string_unchecked(";", 1, 1);
lean_inc(x_492);
x_539 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_539, 0, x_492);
lean_ctor_set(x_539, 1, x_538);
x_540 = lean_mk_string_unchecked("_", 1, 1);
lean_inc(x_492);
x_541 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_541, 0, x_492);
lean_ctor_set(x_541, 1, x_540);
lean_inc(x_492);
x_542 = l_Lean_Syntax_node2(x_492, x_531, x_533, x_541);
lean_inc(x_492);
x_543 = l_Lean_Syntax_node4(x_492, x_520, x_521, x_537, x_539, x_542);
lean_inc(x_492);
x_544 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_544, 0, x_492);
lean_ctor_set(x_544, 1, x_255);
lean_inc(x_492);
x_545 = l_Lean_Syntax_node3(x_492, x_517, x_518, x_543, x_544);
lean_inc(x_492);
x_546 = l_Lean_Syntax_node2(x_492, x_514, x_516, x_545);
lean_inc(x_492);
x_547 = l_Lean_Syntax_node2(x_492, x_511, x_512, x_546);
lean_inc(x_236);
lean_inc(x_492);
x_548 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_548, 0, x_492);
lean_ctor_set(x_548, 1, x_236);
lean_ctor_set(x_548, 2, x_237);
lean_inc(x_492);
x_549 = l_Lean_Syntax_node3(x_492, x_236, x_547, x_548, x_507);
lean_inc(x_492);
x_550 = l_Lean_Syntax_node1(x_492, x_194, x_549);
lean_inc(x_492);
x_551 = l_Lean_Syntax_node1(x_492, x_169, x_550);
x_552 = l_Lean_Syntax_node2(x_492, x_509, x_259, x_551);
if (lean_is_scalar(x_494)) {
 x_553 = lean_alloc_ctor(0, 2, 0);
} else {
 x_553 = x_494;
}
lean_ctor_set(x_553, 0, x_552);
lean_ctor_set(x_553, 1, x_493);
return x_553;
}
}
else
{
lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; 
x_554 = lean_ctor_get(x_259, 0);
x_555 = lean_ctor_get(x_259, 1);
lean_inc(x_555);
lean_inc(x_554);
lean_dec(x_259);
x_556 = l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticHave____1___lam__1(x_554, x_225, x_555);
lean_dec(x_225);
lean_dec(x_554);
x_557 = lean_ctor_get(x_556, 0);
lean_inc(x_557);
x_558 = lean_ctor_get(x_556, 1);
lean_inc(x_558);
if (lean_is_exclusive(x_556)) {
 lean_ctor_release(x_556, 0);
 lean_ctor_release(x_556, 1);
 x_559 = x_556;
} else {
 lean_dec_ref(x_556);
 x_559 = lean_box(0);
}
lean_inc(x_236);
lean_inc(x_247);
x_560 = l_Lean_Syntax_node1(x_247, x_236, x_258);
x_561 = l_Lean_Syntax_getArg(x_1, x_41);
lean_dec(x_1);
x_562 = lean_mk_string_unchecked("caseArg", 7, 7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_563 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_562);
x_564 = lean_mk_string_unchecked("binderIdent", 11, 11);
lean_inc(x_4);
x_565 = l_Lean_Name_mkStr2(x_4, x_564);
x_566 = lean_mk_string_unchecked("body", 4, 4);
lean_inc(x_566);
x_567 = l_String_toSubstring_x27(x_566);
x_568 = l_Lean_Name_mkStr1(x_566);
lean_inc(x_222);
lean_inc(x_221);
x_569 = l_Lean_addMacroScope(x_221, x_568, x_222);
x_570 = lean_box(0);
lean_inc(x_569);
lean_inc(x_567);
lean_inc(x_557);
x_571 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_571, 0, x_557);
lean_ctor_set(x_571, 1, x_567);
lean_ctor_set(x_571, 2, x_569);
lean_ctor_set(x_571, 3, x_570);
lean_inc(x_557);
x_572 = l_Lean_Syntax_node1(x_557, x_565, x_571);
lean_inc(x_237);
lean_inc(x_236);
lean_inc(x_557);
x_573 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_573, 0, x_557);
lean_ctor_set(x_573, 1, x_236);
lean_ctor_set(x_573, 2, x_237);
x_574 = l_Lean_replaceRef(x_561, x_218);
lean_dec(x_218);
lean_dec(x_561);
x_575 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_575, 0, x_220);
lean_ctor_set(x_575, 1, x_221);
lean_ctor_set(x_575, 2, x_222);
lean_ctor_set(x_575, 3, x_223);
lean_ctor_set(x_575, 4, x_224);
lean_ctor_set(x_575, 5, x_574);
x_576 = l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticHave____1___lam__0(x_575, x_575, x_558);
x_577 = lean_ctor_get(x_576, 0);
lean_inc(x_577);
x_578 = lean_ctor_get(x_576, 1);
lean_inc(x_578);
if (lean_is_exclusive(x_576)) {
 lean_ctor_release(x_576, 0);
 lean_ctor_release(x_576, 1);
 x_579 = x_576;
} else {
 lean_dec_ref(x_576);
 x_579 = lean_box(0);
}
x_580 = l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticHave____1___lam__1(x_577, x_575, x_578);
lean_dec(x_575);
lean_dec(x_577);
x_581 = lean_ctor_get(x_580, 0);
lean_inc(x_581);
x_582 = lean_ctor_get(x_580, 1);
lean_inc(x_582);
if (lean_is_exclusive(x_580)) {
 lean_ctor_release(x_580, 0);
 lean_ctor_release(x_580, 1);
 x_583 = x_580;
} else {
 lean_dec_ref(x_580);
 x_583 = lean_box(0);
}
x_584 = l_Lean_Syntax_getArg(x_42, x_12);
lean_dec(x_42);
lean_inc(x_194);
lean_inc(x_247);
x_585 = l_Lean_Syntax_node1(x_247, x_194, x_560);
x_586 = lean_mk_string_unchecked("case", 4, 4);
lean_inc(x_557);
x_587 = l_Lean_Syntax_node2(x_557, x_563, x_572, x_573);
x_588 = lean_mk_string_unchecked("=>", 2, 2);
x_589 = l_Lean_Syntax_getArgs(x_584);
lean_dec(x_584);
lean_inc(x_169);
x_590 = l_Lean_Syntax_node1(x_247, x_169, x_585);
lean_inc(x_586);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_591 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_586);
lean_inc(x_557);
if (lean_is_scalar(x_579)) {
 x_592 = lean_alloc_ctor(2, 2, 0);
} else {
 x_592 = x_579;
 lean_ctor_set_tag(x_592, 2);
}
lean_ctor_set(x_592, 0, x_557);
lean_ctor_set(x_592, 1, x_586);
lean_inc(x_236);
lean_inc(x_557);
x_593 = l_Lean_Syntax_node1(x_557, x_236, x_587);
lean_inc(x_557);
if (lean_is_scalar(x_559)) {
 x_594 = lean_alloc_ctor(2, 2, 0);
} else {
 x_594 = x_559;
 lean_ctor_set_tag(x_594, 2);
}
lean_ctor_set(x_594, 0, x_557);
lean_ctor_set(x_594, 1, x_588);
x_595 = l_Lean_Syntax_getArg(x_116, x_12);
lean_dec(x_116);
x_596 = l_Lean_Syntax_node4(x_557, x_591, x_592, x_593, x_594, x_590);
x_597 = lean_mk_string_unchecked("focus", 5, 5);
lean_inc(x_597);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_598 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_597);
lean_inc(x_581);
x_599 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_599, 0, x_581);
lean_ctor_set(x_599, 1, x_597);
x_600 = lean_mk_string_unchecked("refine", 6, 6);
lean_inc(x_600);
lean_inc(x_5);
lean_inc(x_4);
x_601 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_600);
lean_inc(x_581);
x_602 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_602, 0, x_581);
lean_ctor_set(x_602, 1, x_600);
x_603 = lean_mk_string_unchecked("noImplicitLambda", 16, 16);
lean_inc(x_14);
lean_inc(x_5);
lean_inc(x_4);
x_604 = l_Lean_Name_mkStr4(x_4, x_5, x_14, x_603);
x_605 = lean_mk_string_unchecked("no_implicit_lambda%", 19, 19);
lean_inc(x_581);
x_606 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_606, 0, x_581);
lean_ctor_set(x_606, 1, x_605);
lean_inc(x_14);
lean_inc(x_5);
lean_inc(x_4);
x_607 = l_Lean_Name_mkStr4(x_4, x_5, x_14, x_251);
lean_inc(x_581);
x_608 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_608, 0, x_581);
lean_ctor_set(x_608, 1, x_253);
x_609 = lean_mk_string_unchecked("have", 4, 4);
lean_inc(x_609);
lean_inc(x_14);
lean_inc(x_5);
lean_inc(x_4);
x_610 = l_Lean_Name_mkStr4(x_4, x_5, x_14, x_609);
lean_inc(x_581);
x_611 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_611, 0, x_581);
lean_ctor_set(x_611, 1, x_609);
lean_inc(x_237);
x_612 = l_Array_appendCore___redArg(x_237, x_589);
lean_dec(x_589);
lean_inc(x_236);
lean_inc(x_581);
x_613 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_613, 0, x_581);
lean_ctor_set(x_613, 1, x_236);
lean_ctor_set(x_613, 2, x_612);
x_614 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_581);
x_615 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_615, 0, x_581);
lean_ctor_set(x_615, 1, x_614);
lean_inc(x_581);
x_616 = l_Lean_Syntax_node2(x_581, x_118, x_615, x_595);
lean_inc(x_236);
lean_inc(x_581);
x_617 = l_Lean_Syntax_node1(x_581, x_236, x_616);
x_618 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_581);
x_619 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_619, 0, x_581);
lean_ctor_set(x_619, 1, x_618);
x_620 = lean_mk_string_unchecked("syntheticHole", 13, 13);
x_621 = l_Lean_Name_mkStr4(x_4, x_5, x_14, x_620);
x_622 = lean_mk_string_unchecked("\?", 1, 1);
lean_inc(x_581);
x_623 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_623, 0, x_581);
lean_ctor_set(x_623, 1, x_622);
lean_inc(x_581);
x_624 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_624, 0, x_581);
lean_ctor_set(x_624, 1, x_567);
lean_ctor_set(x_624, 2, x_569);
lean_ctor_set(x_624, 3, x_570);
lean_inc(x_623);
lean_inc(x_621);
lean_inc(x_581);
x_625 = l_Lean_Syntax_node2(x_581, x_621, x_623, x_624);
lean_inc(x_581);
x_626 = l_Lean_Syntax_node5(x_581, x_44, x_67, x_613, x_617, x_619, x_625);
lean_inc(x_581);
x_627 = l_Lean_Syntax_node1(x_581, x_16, x_626);
x_628 = lean_mk_string_unchecked(";", 1, 1);
lean_inc(x_581);
x_629 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_629, 0, x_581);
lean_ctor_set(x_629, 1, x_628);
x_630 = lean_mk_string_unchecked("_", 1, 1);
lean_inc(x_581);
x_631 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_631, 0, x_581);
lean_ctor_set(x_631, 1, x_630);
lean_inc(x_581);
x_632 = l_Lean_Syntax_node2(x_581, x_621, x_623, x_631);
lean_inc(x_581);
x_633 = l_Lean_Syntax_node4(x_581, x_610, x_611, x_627, x_629, x_632);
lean_inc(x_581);
x_634 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_634, 0, x_581);
lean_ctor_set(x_634, 1, x_255);
lean_inc(x_581);
x_635 = l_Lean_Syntax_node3(x_581, x_607, x_608, x_633, x_634);
lean_inc(x_581);
x_636 = l_Lean_Syntax_node2(x_581, x_604, x_606, x_635);
lean_inc(x_581);
x_637 = l_Lean_Syntax_node2(x_581, x_601, x_602, x_636);
lean_inc(x_236);
lean_inc(x_581);
x_638 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_638, 0, x_581);
lean_ctor_set(x_638, 1, x_236);
lean_ctor_set(x_638, 2, x_237);
lean_inc(x_581);
x_639 = l_Lean_Syntax_node3(x_581, x_236, x_637, x_638, x_596);
lean_inc(x_581);
x_640 = l_Lean_Syntax_node1(x_581, x_194, x_639);
lean_inc(x_581);
x_641 = l_Lean_Syntax_node1(x_581, x_169, x_640);
x_642 = l_Lean_Syntax_node2(x_581, x_598, x_599, x_641);
if (lean_is_scalar(x_583)) {
 x_643 = lean_alloc_ctor(0, 2, 0);
} else {
 x_643 = x_583;
}
lean_ctor_set(x_643, 0, x_642);
lean_ctor_set(x_643, 1, x_582);
return x_643;
}
}
else
{
lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; 
x_644 = lean_ctor_get(x_245, 0);
x_645 = lean_ctor_get(x_245, 1);
lean_inc(x_645);
lean_inc(x_644);
lean_dec(x_245);
x_646 = lean_mk_string_unchecked("withAnnotateState", 17, 17);
x_647 = lean_mk_string_unchecked("with_annotate_state", 19, 19);
x_648 = lean_mk_string_unchecked("paren", 5, 5);
lean_inc(x_648);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_649 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_648);
x_650 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_650);
lean_inc(x_234);
x_651 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_651, 0, x_234);
lean_ctor_set(x_651, 1, x_650);
lean_inc(x_169);
lean_inc(x_234);
x_652 = l_Lean_Syntax_node1(x_234, x_169, x_240);
x_653 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_653);
lean_inc(x_234);
lean_ctor_set_tag(x_241, 2);
lean_ctor_set(x_241, 1, x_653);
lean_ctor_set(x_241, 0, x_234);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_654 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_646);
lean_inc(x_234);
lean_ctor_set_tag(x_226, 2);
lean_ctor_set(x_226, 1, x_647);
lean_ctor_set(x_226, 0, x_234);
lean_inc(x_234);
x_655 = l_Lean_Syntax_node3(x_234, x_649, x_651, x_652, x_241);
x_656 = l_Lean_Syntax_node3(x_234, x_654, x_226, x_217, x_655);
x_657 = l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticHave____1___lam__0(x_225, x_225, x_645);
x_658 = lean_ctor_get(x_657, 0);
lean_inc(x_658);
x_659 = lean_ctor_get(x_657, 1);
lean_inc(x_659);
if (lean_is_exclusive(x_657)) {
 lean_ctor_release(x_657, 0);
 lean_ctor_release(x_657, 1);
 x_660 = x_657;
} else {
 lean_dec_ref(x_657);
 x_660 = lean_box(0);
}
x_661 = l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticHave____1___lam__1(x_658, x_225, x_659);
lean_dec(x_225);
lean_dec(x_658);
x_662 = lean_ctor_get(x_661, 0);
lean_inc(x_662);
x_663 = lean_ctor_get(x_661, 1);
lean_inc(x_663);
if (lean_is_exclusive(x_661)) {
 lean_ctor_release(x_661, 0);
 lean_ctor_release(x_661, 1);
 x_664 = x_661;
} else {
 lean_dec_ref(x_661);
 x_664 = lean_box(0);
}
lean_inc(x_236);
lean_inc(x_644);
x_665 = l_Lean_Syntax_node1(x_644, x_236, x_656);
x_666 = l_Lean_Syntax_getArg(x_1, x_41);
lean_dec(x_1);
x_667 = lean_mk_string_unchecked("caseArg", 7, 7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_668 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_667);
x_669 = lean_mk_string_unchecked("binderIdent", 11, 11);
lean_inc(x_4);
x_670 = l_Lean_Name_mkStr2(x_4, x_669);
x_671 = lean_mk_string_unchecked("body", 4, 4);
lean_inc(x_671);
x_672 = l_String_toSubstring_x27(x_671);
x_673 = l_Lean_Name_mkStr1(x_671);
lean_inc(x_222);
lean_inc(x_221);
x_674 = l_Lean_addMacroScope(x_221, x_673, x_222);
x_675 = lean_box(0);
lean_inc(x_674);
lean_inc(x_672);
lean_inc(x_662);
x_676 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_676, 0, x_662);
lean_ctor_set(x_676, 1, x_672);
lean_ctor_set(x_676, 2, x_674);
lean_ctor_set(x_676, 3, x_675);
lean_inc(x_662);
x_677 = l_Lean_Syntax_node1(x_662, x_670, x_676);
lean_inc(x_237);
lean_inc(x_236);
lean_inc(x_662);
x_678 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_678, 0, x_662);
lean_ctor_set(x_678, 1, x_236);
lean_ctor_set(x_678, 2, x_237);
x_679 = l_Lean_replaceRef(x_666, x_218);
lean_dec(x_218);
lean_dec(x_666);
x_680 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_680, 0, x_220);
lean_ctor_set(x_680, 1, x_221);
lean_ctor_set(x_680, 2, x_222);
lean_ctor_set(x_680, 3, x_223);
lean_ctor_set(x_680, 4, x_224);
lean_ctor_set(x_680, 5, x_679);
x_681 = l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticHave____1___lam__0(x_680, x_680, x_663);
x_682 = lean_ctor_get(x_681, 0);
lean_inc(x_682);
x_683 = lean_ctor_get(x_681, 1);
lean_inc(x_683);
if (lean_is_exclusive(x_681)) {
 lean_ctor_release(x_681, 0);
 lean_ctor_release(x_681, 1);
 x_684 = x_681;
} else {
 lean_dec_ref(x_681);
 x_684 = lean_box(0);
}
x_685 = l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticHave____1___lam__1(x_682, x_680, x_683);
lean_dec(x_680);
lean_dec(x_682);
x_686 = lean_ctor_get(x_685, 0);
lean_inc(x_686);
x_687 = lean_ctor_get(x_685, 1);
lean_inc(x_687);
if (lean_is_exclusive(x_685)) {
 lean_ctor_release(x_685, 0);
 lean_ctor_release(x_685, 1);
 x_688 = x_685;
} else {
 lean_dec_ref(x_685);
 x_688 = lean_box(0);
}
x_689 = l_Lean_Syntax_getArg(x_42, x_12);
lean_dec(x_42);
lean_inc(x_194);
lean_inc(x_644);
x_690 = l_Lean_Syntax_node1(x_644, x_194, x_665);
x_691 = lean_mk_string_unchecked("case", 4, 4);
lean_inc(x_662);
x_692 = l_Lean_Syntax_node2(x_662, x_668, x_677, x_678);
x_693 = lean_mk_string_unchecked("=>", 2, 2);
x_694 = l_Lean_Syntax_getArgs(x_689);
lean_dec(x_689);
lean_inc(x_169);
x_695 = l_Lean_Syntax_node1(x_644, x_169, x_690);
lean_inc(x_691);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_696 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_691);
lean_inc(x_662);
if (lean_is_scalar(x_684)) {
 x_697 = lean_alloc_ctor(2, 2, 0);
} else {
 x_697 = x_684;
 lean_ctor_set_tag(x_697, 2);
}
lean_ctor_set(x_697, 0, x_662);
lean_ctor_set(x_697, 1, x_691);
lean_inc(x_236);
lean_inc(x_662);
x_698 = l_Lean_Syntax_node1(x_662, x_236, x_692);
lean_inc(x_662);
if (lean_is_scalar(x_664)) {
 x_699 = lean_alloc_ctor(2, 2, 0);
} else {
 x_699 = x_664;
 lean_ctor_set_tag(x_699, 2);
}
lean_ctor_set(x_699, 0, x_662);
lean_ctor_set(x_699, 1, x_693);
x_700 = l_Lean_Syntax_getArg(x_116, x_12);
lean_dec(x_116);
x_701 = l_Lean_Syntax_node4(x_662, x_696, x_697, x_698, x_699, x_695);
x_702 = lean_mk_string_unchecked("focus", 5, 5);
lean_inc(x_702);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_703 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_702);
lean_inc(x_686);
if (lean_is_scalar(x_660)) {
 x_704 = lean_alloc_ctor(2, 2, 0);
} else {
 x_704 = x_660;
 lean_ctor_set_tag(x_704, 2);
}
lean_ctor_set(x_704, 0, x_686);
lean_ctor_set(x_704, 1, x_702);
x_705 = lean_mk_string_unchecked("refine", 6, 6);
lean_inc(x_705);
lean_inc(x_5);
lean_inc(x_4);
x_706 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_705);
lean_inc(x_686);
x_707 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_707, 0, x_686);
lean_ctor_set(x_707, 1, x_705);
x_708 = lean_mk_string_unchecked("noImplicitLambda", 16, 16);
lean_inc(x_14);
lean_inc(x_5);
lean_inc(x_4);
x_709 = l_Lean_Name_mkStr4(x_4, x_5, x_14, x_708);
x_710 = lean_mk_string_unchecked("no_implicit_lambda%", 19, 19);
lean_inc(x_686);
x_711 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_711, 0, x_686);
lean_ctor_set(x_711, 1, x_710);
lean_inc(x_14);
lean_inc(x_5);
lean_inc(x_4);
x_712 = l_Lean_Name_mkStr4(x_4, x_5, x_14, x_648);
lean_inc(x_686);
x_713 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_713, 0, x_686);
lean_ctor_set(x_713, 1, x_650);
x_714 = lean_mk_string_unchecked("have", 4, 4);
lean_inc(x_714);
lean_inc(x_14);
lean_inc(x_5);
lean_inc(x_4);
x_715 = l_Lean_Name_mkStr4(x_4, x_5, x_14, x_714);
lean_inc(x_686);
x_716 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_716, 0, x_686);
lean_ctor_set(x_716, 1, x_714);
lean_inc(x_237);
x_717 = l_Array_appendCore___redArg(x_237, x_694);
lean_dec(x_694);
lean_inc(x_236);
lean_inc(x_686);
x_718 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_718, 0, x_686);
lean_ctor_set(x_718, 1, x_236);
lean_ctor_set(x_718, 2, x_717);
x_719 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_686);
x_720 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_720, 0, x_686);
lean_ctor_set(x_720, 1, x_719);
lean_inc(x_686);
x_721 = l_Lean_Syntax_node2(x_686, x_118, x_720, x_700);
lean_inc(x_236);
lean_inc(x_686);
x_722 = l_Lean_Syntax_node1(x_686, x_236, x_721);
x_723 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_686);
x_724 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_724, 0, x_686);
lean_ctor_set(x_724, 1, x_723);
x_725 = lean_mk_string_unchecked("syntheticHole", 13, 13);
x_726 = l_Lean_Name_mkStr4(x_4, x_5, x_14, x_725);
x_727 = lean_mk_string_unchecked("\?", 1, 1);
lean_inc(x_686);
x_728 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_728, 0, x_686);
lean_ctor_set(x_728, 1, x_727);
lean_inc(x_686);
x_729 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_729, 0, x_686);
lean_ctor_set(x_729, 1, x_672);
lean_ctor_set(x_729, 2, x_674);
lean_ctor_set(x_729, 3, x_675);
lean_inc(x_728);
lean_inc(x_726);
lean_inc(x_686);
x_730 = l_Lean_Syntax_node2(x_686, x_726, x_728, x_729);
lean_inc(x_686);
x_731 = l_Lean_Syntax_node5(x_686, x_44, x_67, x_718, x_722, x_724, x_730);
lean_inc(x_686);
x_732 = l_Lean_Syntax_node1(x_686, x_16, x_731);
x_733 = lean_mk_string_unchecked(";", 1, 1);
lean_inc(x_686);
x_734 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_734, 0, x_686);
lean_ctor_set(x_734, 1, x_733);
x_735 = lean_mk_string_unchecked("_", 1, 1);
lean_inc(x_686);
x_736 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_736, 0, x_686);
lean_ctor_set(x_736, 1, x_735);
lean_inc(x_686);
x_737 = l_Lean_Syntax_node2(x_686, x_726, x_728, x_736);
lean_inc(x_686);
x_738 = l_Lean_Syntax_node4(x_686, x_715, x_716, x_732, x_734, x_737);
lean_inc(x_686);
x_739 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_739, 0, x_686);
lean_ctor_set(x_739, 1, x_653);
lean_inc(x_686);
x_740 = l_Lean_Syntax_node3(x_686, x_712, x_713, x_738, x_739);
lean_inc(x_686);
x_741 = l_Lean_Syntax_node2(x_686, x_709, x_711, x_740);
lean_inc(x_686);
x_742 = l_Lean_Syntax_node2(x_686, x_706, x_707, x_741);
lean_inc(x_236);
lean_inc(x_686);
x_743 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_743, 0, x_686);
lean_ctor_set(x_743, 1, x_236);
lean_ctor_set(x_743, 2, x_237);
lean_inc(x_686);
x_744 = l_Lean_Syntax_node3(x_686, x_236, x_742, x_743, x_701);
lean_inc(x_686);
x_745 = l_Lean_Syntax_node1(x_686, x_194, x_744);
lean_inc(x_686);
x_746 = l_Lean_Syntax_node1(x_686, x_169, x_745);
x_747 = l_Lean_Syntax_node2(x_686, x_703, x_704, x_746);
if (lean_is_scalar(x_688)) {
 x_748 = lean_alloc_ctor(0, 2, 0);
} else {
 x_748 = x_688;
}
lean_ctor_set(x_748, 0, x_747);
lean_ctor_set(x_748, 1, x_687);
return x_748;
}
}
else
{
lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; lean_object* x_783; lean_object* x_784; lean_object* x_785; lean_object* x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; lean_object* x_795; lean_object* x_796; lean_object* x_797; lean_object* x_798; lean_object* x_799; lean_object* x_800; lean_object* x_801; lean_object* x_802; lean_object* x_803; lean_object* x_804; lean_object* x_805; lean_object* x_806; lean_object* x_807; lean_object* x_808; lean_object* x_809; lean_object* x_810; lean_object* x_811; lean_object* x_812; lean_object* x_813; lean_object* x_814; lean_object* x_815; lean_object* x_816; lean_object* x_817; lean_object* x_818; lean_object* x_819; lean_object* x_820; lean_object* x_821; lean_object* x_822; lean_object* x_823; lean_object* x_824; lean_object* x_825; lean_object* x_826; lean_object* x_827; lean_object* x_828; lean_object* x_829; lean_object* x_830; lean_object* x_831; lean_object* x_832; lean_object* x_833; lean_object* x_834; lean_object* x_835; lean_object* x_836; lean_object* x_837; lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; lean_object* x_844; lean_object* x_845; lean_object* x_846; lean_object* x_847; lean_object* x_848; lean_object* x_849; lean_object* x_850; lean_object* x_851; lean_object* x_852; lean_object* x_853; lean_object* x_854; lean_object* x_855; lean_object* x_856; lean_object* x_857; lean_object* x_858; 
x_749 = lean_ctor_get(x_241, 0);
x_750 = lean_ctor_get(x_241, 1);
lean_inc(x_750);
lean_inc(x_749);
lean_dec(x_241);
x_751 = l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticHave____1___lam__1(x_749, x_2, x_750);
lean_dec(x_2);
lean_dec(x_749);
x_752 = lean_ctor_get(x_751, 0);
lean_inc(x_752);
x_753 = lean_ctor_get(x_751, 1);
lean_inc(x_753);
if (lean_is_exclusive(x_751)) {
 lean_ctor_release(x_751, 0);
 lean_ctor_release(x_751, 1);
 x_754 = x_751;
} else {
 lean_dec_ref(x_751);
 x_754 = lean_box(0);
}
x_755 = lean_mk_string_unchecked("withAnnotateState", 17, 17);
x_756 = lean_mk_string_unchecked("with_annotate_state", 19, 19);
x_757 = lean_mk_string_unchecked("paren", 5, 5);
lean_inc(x_757);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_758 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_757);
x_759 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_759);
lean_inc(x_234);
if (lean_is_scalar(x_754)) {
 x_760 = lean_alloc_ctor(2, 2, 0);
} else {
 x_760 = x_754;
 lean_ctor_set_tag(x_760, 2);
}
lean_ctor_set(x_760, 0, x_234);
lean_ctor_set(x_760, 1, x_759);
lean_inc(x_169);
lean_inc(x_234);
x_761 = l_Lean_Syntax_node1(x_234, x_169, x_240);
x_762 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_762);
lean_inc(x_234);
x_763 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_763, 0, x_234);
lean_ctor_set(x_763, 1, x_762);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_764 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_755);
lean_inc(x_234);
lean_ctor_set_tag(x_226, 2);
lean_ctor_set(x_226, 1, x_756);
lean_ctor_set(x_226, 0, x_234);
lean_inc(x_234);
x_765 = l_Lean_Syntax_node3(x_234, x_758, x_760, x_761, x_763);
x_766 = l_Lean_Syntax_node3(x_234, x_764, x_226, x_217, x_765);
x_767 = l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticHave____1___lam__0(x_225, x_225, x_753);
x_768 = lean_ctor_get(x_767, 0);
lean_inc(x_768);
x_769 = lean_ctor_get(x_767, 1);
lean_inc(x_769);
if (lean_is_exclusive(x_767)) {
 lean_ctor_release(x_767, 0);
 lean_ctor_release(x_767, 1);
 x_770 = x_767;
} else {
 lean_dec_ref(x_767);
 x_770 = lean_box(0);
}
x_771 = l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticHave____1___lam__1(x_768, x_225, x_769);
lean_dec(x_225);
lean_dec(x_768);
x_772 = lean_ctor_get(x_771, 0);
lean_inc(x_772);
x_773 = lean_ctor_get(x_771, 1);
lean_inc(x_773);
if (lean_is_exclusive(x_771)) {
 lean_ctor_release(x_771, 0);
 lean_ctor_release(x_771, 1);
 x_774 = x_771;
} else {
 lean_dec_ref(x_771);
 x_774 = lean_box(0);
}
lean_inc(x_236);
lean_inc(x_752);
x_775 = l_Lean_Syntax_node1(x_752, x_236, x_766);
x_776 = l_Lean_Syntax_getArg(x_1, x_41);
lean_dec(x_1);
x_777 = lean_mk_string_unchecked("caseArg", 7, 7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_778 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_777);
x_779 = lean_mk_string_unchecked("binderIdent", 11, 11);
lean_inc(x_4);
x_780 = l_Lean_Name_mkStr2(x_4, x_779);
x_781 = lean_mk_string_unchecked("body", 4, 4);
lean_inc(x_781);
x_782 = l_String_toSubstring_x27(x_781);
x_783 = l_Lean_Name_mkStr1(x_781);
lean_inc(x_222);
lean_inc(x_221);
x_784 = l_Lean_addMacroScope(x_221, x_783, x_222);
x_785 = lean_box(0);
lean_inc(x_784);
lean_inc(x_782);
lean_inc(x_772);
x_786 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_786, 0, x_772);
lean_ctor_set(x_786, 1, x_782);
lean_ctor_set(x_786, 2, x_784);
lean_ctor_set(x_786, 3, x_785);
lean_inc(x_772);
x_787 = l_Lean_Syntax_node1(x_772, x_780, x_786);
lean_inc(x_237);
lean_inc(x_236);
lean_inc(x_772);
x_788 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_788, 0, x_772);
lean_ctor_set(x_788, 1, x_236);
lean_ctor_set(x_788, 2, x_237);
x_789 = l_Lean_replaceRef(x_776, x_218);
lean_dec(x_218);
lean_dec(x_776);
x_790 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_790, 0, x_220);
lean_ctor_set(x_790, 1, x_221);
lean_ctor_set(x_790, 2, x_222);
lean_ctor_set(x_790, 3, x_223);
lean_ctor_set(x_790, 4, x_224);
lean_ctor_set(x_790, 5, x_789);
x_791 = l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticHave____1___lam__0(x_790, x_790, x_773);
x_792 = lean_ctor_get(x_791, 0);
lean_inc(x_792);
x_793 = lean_ctor_get(x_791, 1);
lean_inc(x_793);
if (lean_is_exclusive(x_791)) {
 lean_ctor_release(x_791, 0);
 lean_ctor_release(x_791, 1);
 x_794 = x_791;
} else {
 lean_dec_ref(x_791);
 x_794 = lean_box(0);
}
x_795 = l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticHave____1___lam__1(x_792, x_790, x_793);
lean_dec(x_790);
lean_dec(x_792);
x_796 = lean_ctor_get(x_795, 0);
lean_inc(x_796);
x_797 = lean_ctor_get(x_795, 1);
lean_inc(x_797);
if (lean_is_exclusive(x_795)) {
 lean_ctor_release(x_795, 0);
 lean_ctor_release(x_795, 1);
 x_798 = x_795;
} else {
 lean_dec_ref(x_795);
 x_798 = lean_box(0);
}
x_799 = l_Lean_Syntax_getArg(x_42, x_12);
lean_dec(x_42);
lean_inc(x_194);
lean_inc(x_752);
x_800 = l_Lean_Syntax_node1(x_752, x_194, x_775);
x_801 = lean_mk_string_unchecked("case", 4, 4);
lean_inc(x_772);
x_802 = l_Lean_Syntax_node2(x_772, x_778, x_787, x_788);
x_803 = lean_mk_string_unchecked("=>", 2, 2);
x_804 = l_Lean_Syntax_getArgs(x_799);
lean_dec(x_799);
lean_inc(x_169);
x_805 = l_Lean_Syntax_node1(x_752, x_169, x_800);
lean_inc(x_801);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_806 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_801);
lean_inc(x_772);
if (lean_is_scalar(x_794)) {
 x_807 = lean_alloc_ctor(2, 2, 0);
} else {
 x_807 = x_794;
 lean_ctor_set_tag(x_807, 2);
}
lean_ctor_set(x_807, 0, x_772);
lean_ctor_set(x_807, 1, x_801);
lean_inc(x_236);
lean_inc(x_772);
x_808 = l_Lean_Syntax_node1(x_772, x_236, x_802);
lean_inc(x_772);
if (lean_is_scalar(x_774)) {
 x_809 = lean_alloc_ctor(2, 2, 0);
} else {
 x_809 = x_774;
 lean_ctor_set_tag(x_809, 2);
}
lean_ctor_set(x_809, 0, x_772);
lean_ctor_set(x_809, 1, x_803);
x_810 = l_Lean_Syntax_getArg(x_116, x_12);
lean_dec(x_116);
x_811 = l_Lean_Syntax_node4(x_772, x_806, x_807, x_808, x_809, x_805);
x_812 = lean_mk_string_unchecked("focus", 5, 5);
lean_inc(x_812);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_813 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_812);
lean_inc(x_796);
if (lean_is_scalar(x_770)) {
 x_814 = lean_alloc_ctor(2, 2, 0);
} else {
 x_814 = x_770;
 lean_ctor_set_tag(x_814, 2);
}
lean_ctor_set(x_814, 0, x_796);
lean_ctor_set(x_814, 1, x_812);
x_815 = lean_mk_string_unchecked("refine", 6, 6);
lean_inc(x_815);
lean_inc(x_5);
lean_inc(x_4);
x_816 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_815);
lean_inc(x_796);
x_817 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_817, 0, x_796);
lean_ctor_set(x_817, 1, x_815);
x_818 = lean_mk_string_unchecked("noImplicitLambda", 16, 16);
lean_inc(x_14);
lean_inc(x_5);
lean_inc(x_4);
x_819 = l_Lean_Name_mkStr4(x_4, x_5, x_14, x_818);
x_820 = lean_mk_string_unchecked("no_implicit_lambda%", 19, 19);
lean_inc(x_796);
x_821 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_821, 0, x_796);
lean_ctor_set(x_821, 1, x_820);
lean_inc(x_14);
lean_inc(x_5);
lean_inc(x_4);
x_822 = l_Lean_Name_mkStr4(x_4, x_5, x_14, x_757);
lean_inc(x_796);
x_823 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_823, 0, x_796);
lean_ctor_set(x_823, 1, x_759);
x_824 = lean_mk_string_unchecked("have", 4, 4);
lean_inc(x_824);
lean_inc(x_14);
lean_inc(x_5);
lean_inc(x_4);
x_825 = l_Lean_Name_mkStr4(x_4, x_5, x_14, x_824);
lean_inc(x_796);
x_826 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_826, 0, x_796);
lean_ctor_set(x_826, 1, x_824);
lean_inc(x_237);
x_827 = l_Array_appendCore___redArg(x_237, x_804);
lean_dec(x_804);
lean_inc(x_236);
lean_inc(x_796);
x_828 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_828, 0, x_796);
lean_ctor_set(x_828, 1, x_236);
lean_ctor_set(x_828, 2, x_827);
x_829 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_796);
x_830 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_830, 0, x_796);
lean_ctor_set(x_830, 1, x_829);
lean_inc(x_796);
x_831 = l_Lean_Syntax_node2(x_796, x_118, x_830, x_810);
lean_inc(x_236);
lean_inc(x_796);
x_832 = l_Lean_Syntax_node1(x_796, x_236, x_831);
x_833 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_796);
x_834 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_834, 0, x_796);
lean_ctor_set(x_834, 1, x_833);
x_835 = lean_mk_string_unchecked("syntheticHole", 13, 13);
x_836 = l_Lean_Name_mkStr4(x_4, x_5, x_14, x_835);
x_837 = lean_mk_string_unchecked("\?", 1, 1);
lean_inc(x_796);
x_838 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_838, 0, x_796);
lean_ctor_set(x_838, 1, x_837);
lean_inc(x_796);
x_839 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_839, 0, x_796);
lean_ctor_set(x_839, 1, x_782);
lean_ctor_set(x_839, 2, x_784);
lean_ctor_set(x_839, 3, x_785);
lean_inc(x_838);
lean_inc(x_836);
lean_inc(x_796);
x_840 = l_Lean_Syntax_node2(x_796, x_836, x_838, x_839);
lean_inc(x_796);
x_841 = l_Lean_Syntax_node5(x_796, x_44, x_67, x_828, x_832, x_834, x_840);
lean_inc(x_796);
x_842 = l_Lean_Syntax_node1(x_796, x_16, x_841);
x_843 = lean_mk_string_unchecked(";", 1, 1);
lean_inc(x_796);
x_844 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_844, 0, x_796);
lean_ctor_set(x_844, 1, x_843);
x_845 = lean_mk_string_unchecked("_", 1, 1);
lean_inc(x_796);
x_846 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_846, 0, x_796);
lean_ctor_set(x_846, 1, x_845);
lean_inc(x_796);
x_847 = l_Lean_Syntax_node2(x_796, x_836, x_838, x_846);
lean_inc(x_796);
x_848 = l_Lean_Syntax_node4(x_796, x_825, x_826, x_842, x_844, x_847);
lean_inc(x_796);
x_849 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_849, 0, x_796);
lean_ctor_set(x_849, 1, x_762);
lean_inc(x_796);
x_850 = l_Lean_Syntax_node3(x_796, x_822, x_823, x_848, x_849);
lean_inc(x_796);
x_851 = l_Lean_Syntax_node2(x_796, x_819, x_821, x_850);
lean_inc(x_796);
x_852 = l_Lean_Syntax_node2(x_796, x_816, x_817, x_851);
lean_inc(x_236);
lean_inc(x_796);
x_853 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_853, 0, x_796);
lean_ctor_set(x_853, 1, x_236);
lean_ctor_set(x_853, 2, x_237);
lean_inc(x_796);
x_854 = l_Lean_Syntax_node3(x_796, x_236, x_852, x_853, x_811);
lean_inc(x_796);
x_855 = l_Lean_Syntax_node1(x_796, x_194, x_854);
lean_inc(x_796);
x_856 = l_Lean_Syntax_node1(x_796, x_169, x_855);
x_857 = l_Lean_Syntax_node2(x_796, x_813, x_814, x_856);
if (lean_is_scalar(x_798)) {
 x_858 = lean_alloc_ctor(0, 2, 0);
} else {
 x_858 = x_798;
}
lean_ctor_set(x_858, 0, x_857);
lean_ctor_set(x_858, 1, x_797);
return x_858;
}
}
else
{
lean_object* x_859; lean_object* x_860; lean_object* x_861; lean_object* x_862; lean_object* x_863; uint8_t x_864; lean_object* x_865; lean_object* x_866; lean_object* x_867; lean_object* x_868; lean_object* x_869; lean_object* x_870; lean_object* x_871; lean_object* x_872; lean_object* x_873; lean_object* x_874; lean_object* x_875; lean_object* x_876; lean_object* x_877; lean_object* x_878; lean_object* x_879; lean_object* x_880; lean_object* x_881; lean_object* x_882; lean_object* x_883; lean_object* x_884; lean_object* x_885; lean_object* x_886; lean_object* x_887; lean_object* x_888; lean_object* x_889; lean_object* x_890; lean_object* x_891; lean_object* x_892; lean_object* x_893; lean_object* x_894; lean_object* x_895; lean_object* x_896; lean_object* x_897; lean_object* x_898; lean_object* x_899; lean_object* x_900; lean_object* x_901; lean_object* x_902; lean_object* x_903; lean_object* x_904; lean_object* x_905; lean_object* x_906; lean_object* x_907; lean_object* x_908; lean_object* x_909; lean_object* x_910; lean_object* x_911; lean_object* x_912; lean_object* x_913; lean_object* x_914; lean_object* x_915; lean_object* x_916; lean_object* x_917; lean_object* x_918; lean_object* x_919; lean_object* x_920; lean_object* x_921; lean_object* x_922; lean_object* x_923; lean_object* x_924; lean_object* x_925; lean_object* x_926; lean_object* x_927; lean_object* x_928; lean_object* x_929; lean_object* x_930; lean_object* x_931; lean_object* x_932; lean_object* x_933; lean_object* x_934; lean_object* x_935; lean_object* x_936; lean_object* x_937; lean_object* x_938; lean_object* x_939; lean_object* x_940; lean_object* x_941; lean_object* x_942; lean_object* x_943; lean_object* x_944; lean_object* x_945; lean_object* x_946; lean_object* x_947; lean_object* x_948; lean_object* x_949; lean_object* x_950; lean_object* x_951; lean_object* x_952; lean_object* x_953; lean_object* x_954; lean_object* x_955; lean_object* x_956; lean_object* x_957; lean_object* x_958; lean_object* x_959; lean_object* x_960; lean_object* x_961; lean_object* x_962; lean_object* x_963; lean_object* x_964; lean_object* x_965; lean_object* x_966; lean_object* x_967; lean_object* x_968; lean_object* x_969; lean_object* x_970; lean_object* x_971; lean_object* x_972; lean_object* x_973; lean_object* x_974; lean_object* x_975; lean_object* x_976; lean_object* x_977; lean_object* x_978; lean_object* x_979; lean_object* x_980; lean_object* x_981; lean_object* x_982; lean_object* x_983; lean_object* x_984; 
x_859 = lean_ctor_get(x_226, 0);
x_860 = lean_ctor_get(x_226, 1);
lean_inc(x_860);
lean_inc(x_859);
lean_dec(x_226);
x_861 = l_Lean_Syntax_getArg(x_192, x_41);
lean_dec(x_192);
x_862 = l_Lean_Syntax_getArgs(x_861);
lean_dec(x_861);
x_863 = lean_box(0);
x_864 = lean_unbox(x_863);
x_865 = l_Lean_SourceInfo_fromRef(x_859, x_864);
lean_dec(x_859);
x_866 = lean_mk_string_unchecked("null", 4, 4);
x_867 = l_Lean_Name_mkStr1(x_866);
x_868 = l_Array_mkArray0(lean_box(0));
lean_inc(x_868);
x_869 = l_Array_appendCore___redArg(x_868, x_862);
lean_dec(x_862);
lean_inc(x_867);
lean_inc(x_865);
x_870 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_870, 0, x_865);
lean_ctor_set(x_870, 1, x_867);
lean_ctor_set(x_870, 2, x_869);
lean_inc(x_194);
lean_inc(x_865);
x_871 = l_Lean_Syntax_node1(x_865, x_194, x_870);
x_872 = l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticHave____1___lam__0(x_2, x_2, x_860);
x_873 = lean_ctor_get(x_872, 0);
lean_inc(x_873);
x_874 = lean_ctor_get(x_872, 1);
lean_inc(x_874);
if (lean_is_exclusive(x_872)) {
 lean_ctor_release(x_872, 0);
 lean_ctor_release(x_872, 1);
 x_875 = x_872;
} else {
 lean_dec_ref(x_872);
 x_875 = lean_box(0);
}
x_876 = l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticHave____1___lam__1(x_873, x_2, x_874);
lean_dec(x_2);
lean_dec(x_873);
x_877 = lean_ctor_get(x_876, 0);
lean_inc(x_877);
x_878 = lean_ctor_get(x_876, 1);
lean_inc(x_878);
if (lean_is_exclusive(x_876)) {
 lean_ctor_release(x_876, 0);
 lean_ctor_release(x_876, 1);
 x_879 = x_876;
} else {
 lean_dec_ref(x_876);
 x_879 = lean_box(0);
}
x_880 = lean_mk_string_unchecked("withAnnotateState", 17, 17);
x_881 = lean_mk_string_unchecked("with_annotate_state", 19, 19);
x_882 = lean_mk_string_unchecked("paren", 5, 5);
lean_inc(x_882);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_883 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_882);
x_884 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_884);
lean_inc(x_865);
if (lean_is_scalar(x_879)) {
 x_885 = lean_alloc_ctor(2, 2, 0);
} else {
 x_885 = x_879;
 lean_ctor_set_tag(x_885, 2);
}
lean_ctor_set(x_885, 0, x_865);
lean_ctor_set(x_885, 1, x_884);
lean_inc(x_169);
lean_inc(x_865);
x_886 = l_Lean_Syntax_node1(x_865, x_169, x_871);
x_887 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_887);
lean_inc(x_865);
if (lean_is_scalar(x_875)) {
 x_888 = lean_alloc_ctor(2, 2, 0);
} else {
 x_888 = x_875;
 lean_ctor_set_tag(x_888, 2);
}
lean_ctor_set(x_888, 0, x_865);
lean_ctor_set(x_888, 1, x_887);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_889 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_880);
lean_inc(x_865);
x_890 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_890, 0, x_865);
lean_ctor_set(x_890, 1, x_881);
lean_inc(x_865);
x_891 = l_Lean_Syntax_node3(x_865, x_883, x_885, x_886, x_888);
x_892 = l_Lean_Syntax_node3(x_865, x_889, x_890, x_217, x_891);
x_893 = l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticHave____1___lam__0(x_225, x_225, x_878);
x_894 = lean_ctor_get(x_893, 0);
lean_inc(x_894);
x_895 = lean_ctor_get(x_893, 1);
lean_inc(x_895);
if (lean_is_exclusive(x_893)) {
 lean_ctor_release(x_893, 0);
 lean_ctor_release(x_893, 1);
 x_896 = x_893;
} else {
 lean_dec_ref(x_893);
 x_896 = lean_box(0);
}
x_897 = l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticHave____1___lam__1(x_894, x_225, x_895);
lean_dec(x_225);
lean_dec(x_894);
x_898 = lean_ctor_get(x_897, 0);
lean_inc(x_898);
x_899 = lean_ctor_get(x_897, 1);
lean_inc(x_899);
if (lean_is_exclusive(x_897)) {
 lean_ctor_release(x_897, 0);
 lean_ctor_release(x_897, 1);
 x_900 = x_897;
} else {
 lean_dec_ref(x_897);
 x_900 = lean_box(0);
}
lean_inc(x_867);
lean_inc(x_877);
x_901 = l_Lean_Syntax_node1(x_877, x_867, x_892);
x_902 = l_Lean_Syntax_getArg(x_1, x_41);
lean_dec(x_1);
x_903 = lean_mk_string_unchecked("caseArg", 7, 7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_904 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_903);
x_905 = lean_mk_string_unchecked("binderIdent", 11, 11);
lean_inc(x_4);
x_906 = l_Lean_Name_mkStr2(x_4, x_905);
x_907 = lean_mk_string_unchecked("body", 4, 4);
lean_inc(x_907);
x_908 = l_String_toSubstring_x27(x_907);
x_909 = l_Lean_Name_mkStr1(x_907);
lean_inc(x_222);
lean_inc(x_221);
x_910 = l_Lean_addMacroScope(x_221, x_909, x_222);
x_911 = lean_box(0);
lean_inc(x_910);
lean_inc(x_908);
lean_inc(x_898);
x_912 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_912, 0, x_898);
lean_ctor_set(x_912, 1, x_908);
lean_ctor_set(x_912, 2, x_910);
lean_ctor_set(x_912, 3, x_911);
lean_inc(x_898);
x_913 = l_Lean_Syntax_node1(x_898, x_906, x_912);
lean_inc(x_868);
lean_inc(x_867);
lean_inc(x_898);
x_914 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_914, 0, x_898);
lean_ctor_set(x_914, 1, x_867);
lean_ctor_set(x_914, 2, x_868);
x_915 = l_Lean_replaceRef(x_902, x_218);
lean_dec(x_218);
lean_dec(x_902);
x_916 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_916, 0, x_220);
lean_ctor_set(x_916, 1, x_221);
lean_ctor_set(x_916, 2, x_222);
lean_ctor_set(x_916, 3, x_223);
lean_ctor_set(x_916, 4, x_224);
lean_ctor_set(x_916, 5, x_915);
x_917 = l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticHave____1___lam__0(x_916, x_916, x_899);
x_918 = lean_ctor_get(x_917, 0);
lean_inc(x_918);
x_919 = lean_ctor_get(x_917, 1);
lean_inc(x_919);
if (lean_is_exclusive(x_917)) {
 lean_ctor_release(x_917, 0);
 lean_ctor_release(x_917, 1);
 x_920 = x_917;
} else {
 lean_dec_ref(x_917);
 x_920 = lean_box(0);
}
x_921 = l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticHave____1___lam__1(x_918, x_916, x_919);
lean_dec(x_916);
lean_dec(x_918);
x_922 = lean_ctor_get(x_921, 0);
lean_inc(x_922);
x_923 = lean_ctor_get(x_921, 1);
lean_inc(x_923);
if (lean_is_exclusive(x_921)) {
 lean_ctor_release(x_921, 0);
 lean_ctor_release(x_921, 1);
 x_924 = x_921;
} else {
 lean_dec_ref(x_921);
 x_924 = lean_box(0);
}
x_925 = l_Lean_Syntax_getArg(x_42, x_12);
lean_dec(x_42);
lean_inc(x_194);
lean_inc(x_877);
x_926 = l_Lean_Syntax_node1(x_877, x_194, x_901);
x_927 = lean_mk_string_unchecked("case", 4, 4);
lean_inc(x_898);
x_928 = l_Lean_Syntax_node2(x_898, x_904, x_913, x_914);
x_929 = lean_mk_string_unchecked("=>", 2, 2);
x_930 = l_Lean_Syntax_getArgs(x_925);
lean_dec(x_925);
lean_inc(x_169);
x_931 = l_Lean_Syntax_node1(x_877, x_169, x_926);
lean_inc(x_927);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_932 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_927);
lean_inc(x_898);
if (lean_is_scalar(x_920)) {
 x_933 = lean_alloc_ctor(2, 2, 0);
} else {
 x_933 = x_920;
 lean_ctor_set_tag(x_933, 2);
}
lean_ctor_set(x_933, 0, x_898);
lean_ctor_set(x_933, 1, x_927);
lean_inc(x_867);
lean_inc(x_898);
x_934 = l_Lean_Syntax_node1(x_898, x_867, x_928);
lean_inc(x_898);
if (lean_is_scalar(x_900)) {
 x_935 = lean_alloc_ctor(2, 2, 0);
} else {
 x_935 = x_900;
 lean_ctor_set_tag(x_935, 2);
}
lean_ctor_set(x_935, 0, x_898);
lean_ctor_set(x_935, 1, x_929);
x_936 = l_Lean_Syntax_getArg(x_116, x_12);
lean_dec(x_116);
x_937 = l_Lean_Syntax_node4(x_898, x_932, x_933, x_934, x_935, x_931);
x_938 = lean_mk_string_unchecked("focus", 5, 5);
lean_inc(x_938);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_939 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_938);
lean_inc(x_922);
if (lean_is_scalar(x_896)) {
 x_940 = lean_alloc_ctor(2, 2, 0);
} else {
 x_940 = x_896;
 lean_ctor_set_tag(x_940, 2);
}
lean_ctor_set(x_940, 0, x_922);
lean_ctor_set(x_940, 1, x_938);
x_941 = lean_mk_string_unchecked("refine", 6, 6);
lean_inc(x_941);
lean_inc(x_5);
lean_inc(x_4);
x_942 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_941);
lean_inc(x_922);
x_943 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_943, 0, x_922);
lean_ctor_set(x_943, 1, x_941);
x_944 = lean_mk_string_unchecked("noImplicitLambda", 16, 16);
lean_inc(x_14);
lean_inc(x_5);
lean_inc(x_4);
x_945 = l_Lean_Name_mkStr4(x_4, x_5, x_14, x_944);
x_946 = lean_mk_string_unchecked("no_implicit_lambda%", 19, 19);
lean_inc(x_922);
x_947 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_947, 0, x_922);
lean_ctor_set(x_947, 1, x_946);
lean_inc(x_14);
lean_inc(x_5);
lean_inc(x_4);
x_948 = l_Lean_Name_mkStr4(x_4, x_5, x_14, x_882);
lean_inc(x_922);
x_949 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_949, 0, x_922);
lean_ctor_set(x_949, 1, x_884);
x_950 = lean_mk_string_unchecked("have", 4, 4);
lean_inc(x_950);
lean_inc(x_14);
lean_inc(x_5);
lean_inc(x_4);
x_951 = l_Lean_Name_mkStr4(x_4, x_5, x_14, x_950);
lean_inc(x_922);
x_952 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_952, 0, x_922);
lean_ctor_set(x_952, 1, x_950);
lean_inc(x_868);
x_953 = l_Array_appendCore___redArg(x_868, x_930);
lean_dec(x_930);
lean_inc(x_867);
lean_inc(x_922);
x_954 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_954, 0, x_922);
lean_ctor_set(x_954, 1, x_867);
lean_ctor_set(x_954, 2, x_953);
x_955 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_922);
x_956 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_956, 0, x_922);
lean_ctor_set(x_956, 1, x_955);
lean_inc(x_922);
x_957 = l_Lean_Syntax_node2(x_922, x_118, x_956, x_936);
lean_inc(x_867);
lean_inc(x_922);
x_958 = l_Lean_Syntax_node1(x_922, x_867, x_957);
x_959 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_922);
x_960 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_960, 0, x_922);
lean_ctor_set(x_960, 1, x_959);
x_961 = lean_mk_string_unchecked("syntheticHole", 13, 13);
x_962 = l_Lean_Name_mkStr4(x_4, x_5, x_14, x_961);
x_963 = lean_mk_string_unchecked("\?", 1, 1);
lean_inc(x_922);
x_964 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_964, 0, x_922);
lean_ctor_set(x_964, 1, x_963);
lean_inc(x_922);
x_965 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_965, 0, x_922);
lean_ctor_set(x_965, 1, x_908);
lean_ctor_set(x_965, 2, x_910);
lean_ctor_set(x_965, 3, x_911);
lean_inc(x_964);
lean_inc(x_962);
lean_inc(x_922);
x_966 = l_Lean_Syntax_node2(x_922, x_962, x_964, x_965);
lean_inc(x_922);
x_967 = l_Lean_Syntax_node5(x_922, x_44, x_67, x_954, x_958, x_960, x_966);
lean_inc(x_922);
x_968 = l_Lean_Syntax_node1(x_922, x_16, x_967);
x_969 = lean_mk_string_unchecked(";", 1, 1);
lean_inc(x_922);
x_970 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_970, 0, x_922);
lean_ctor_set(x_970, 1, x_969);
x_971 = lean_mk_string_unchecked("_", 1, 1);
lean_inc(x_922);
x_972 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_972, 0, x_922);
lean_ctor_set(x_972, 1, x_971);
lean_inc(x_922);
x_973 = l_Lean_Syntax_node2(x_922, x_962, x_964, x_972);
lean_inc(x_922);
x_974 = l_Lean_Syntax_node4(x_922, x_951, x_952, x_968, x_970, x_973);
lean_inc(x_922);
x_975 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_975, 0, x_922);
lean_ctor_set(x_975, 1, x_887);
lean_inc(x_922);
x_976 = l_Lean_Syntax_node3(x_922, x_948, x_949, x_974, x_975);
lean_inc(x_922);
x_977 = l_Lean_Syntax_node2(x_922, x_945, x_947, x_976);
lean_inc(x_922);
x_978 = l_Lean_Syntax_node2(x_922, x_942, x_943, x_977);
lean_inc(x_867);
lean_inc(x_922);
x_979 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_979, 0, x_922);
lean_ctor_set(x_979, 1, x_867);
lean_ctor_set(x_979, 2, x_868);
lean_inc(x_922);
x_980 = l_Lean_Syntax_node3(x_922, x_867, x_978, x_979, x_937);
lean_inc(x_922);
x_981 = l_Lean_Syntax_node1(x_922, x_194, x_980);
lean_inc(x_922);
x_982 = l_Lean_Syntax_node1(x_922, x_169, x_981);
x_983 = l_Lean_Syntax_node2(x_922, x_939, x_940, x_982);
if (lean_is_scalar(x_924)) {
 x_984 = lean_alloc_ctor(0, 2, 0);
} else {
 x_984 = x_924;
}
lean_ctor_set(x_984, 0, x_983);
lean_ctor_set(x_984, 1, x_923);
return x_984;
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
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticHave____1___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticHave____1___lam__0(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticHave____1___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticHave____1___lam__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSuffices__() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("tacticSuffices_", 15, 15);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("suffices ", 9, 9);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_unbox(x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_12);
x_13 = lean_mk_string_unchecked("sufficesDecl", 12, 12);
x_14 = l_Lean_Name_mkStr1(x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_16, 0, x_8);
lean_ctor_set(x_16, 1, x_11);
lean_ctor_set(x_16, 2, x_15);
x_17 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_17, 0, x_5);
lean_ctor_set(x_17, 1, x_6);
lean_ctor_set(x_17, 2, x_16);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticSuffices____1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Tactic", 6, 6);
x_7 = lean_mk_string_unchecked("tacticSuffices_", 15, 15);
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
x_10 = lean_box(1);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = l_Lean_Syntax_getArg(x_1, x_12);
lean_dec(x_1);
x_14 = lean_mk_string_unchecked("Term", 4, 4);
x_15 = lean_ctor_get(x_2, 5);
x_16 = lean_box(0);
x_17 = lean_unbox(x_16);
x_18 = l_Lean_SourceInfo_fromRef(x_15, x_17);
x_19 = lean_mk_string_unchecked("tacticRefine_lift_", 18, 18);
lean_inc(x_5);
lean_inc(x_4);
x_20 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_19);
x_21 = lean_mk_string_unchecked("refine_lift", 11, 11);
lean_inc(x_18);
x_22 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_22, 0, x_18);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_mk_string_unchecked("suffices", 8, 8);
lean_inc(x_23);
lean_inc(x_14);
lean_inc(x_5);
lean_inc(x_4);
x_24 = l_Lean_Name_mkStr4(x_4, x_5, x_14, x_23);
lean_inc(x_18);
x_25 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_25, 0, x_18);
lean_ctor_set(x_25, 1, x_23);
x_26 = lean_mk_string_unchecked(";", 1, 1);
lean_inc(x_18);
x_27 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_27, 0, x_18);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_mk_string_unchecked("syntheticHole", 13, 13);
x_29 = l_Lean_Name_mkStr4(x_4, x_5, x_14, x_28);
x_30 = lean_mk_string_unchecked("\?", 1, 1);
lean_inc(x_18);
x_31 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_31, 0, x_18);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_mk_string_unchecked("_", 1, 1);
lean_inc(x_18);
x_33 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_33, 0, x_18);
lean_ctor_set(x_33, 1, x_32);
lean_inc(x_18);
x_34 = l_Lean_Syntax_node2(x_18, x_29, x_31, x_33);
lean_inc(x_18);
x_35 = l_Lean_Syntax_node4(x_18, x_24, x_25, x_13, x_27, x_34);
x_36 = l_Lean_Syntax_node2(x_18, x_20, x_22, x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_3);
return x_37;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticSuffices____1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticSuffices____1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticLet__() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("tacticLet_", 10, 10);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("let ", 4, 4);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_unbox(x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_12);
x_13 = lean_mk_string_unchecked("letDecl", 7, 7);
x_14 = l_Lean_Name_mkStr1(x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_16, 0, x_8);
lean_ctor_set(x_16, 1, x_11);
lean_ctor_set(x_16, 2, x_15);
x_17 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_17, 0, x_5);
lean_ctor_set(x_17, 1, x_6);
lean_ctor_set(x_17, 2, x_16);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticLet____1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Tactic", 6, 6);
x_7 = lean_mk_string_unchecked("tacticLet_", 10, 10);
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
x_10 = lean_box(1);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = l_Lean_Syntax_getArg(x_1, x_12);
lean_dec(x_1);
x_14 = lean_mk_string_unchecked("Term", 4, 4);
x_15 = lean_ctor_get(x_2, 5);
x_16 = lean_box(0);
x_17 = lean_unbox(x_16);
x_18 = l_Lean_SourceInfo_fromRef(x_15, x_17);
x_19 = lean_mk_string_unchecked("tacticRefine_lift_", 18, 18);
lean_inc(x_5);
lean_inc(x_4);
x_20 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_19);
x_21 = lean_mk_string_unchecked("refine_lift", 11, 11);
lean_inc(x_18);
x_22 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_22, 0, x_18);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_mk_string_unchecked("let", 3, 3);
lean_inc(x_23);
lean_inc(x_14);
lean_inc(x_5);
lean_inc(x_4);
x_24 = l_Lean_Name_mkStr4(x_4, x_5, x_14, x_23);
lean_inc(x_18);
x_25 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_25, 0, x_18);
lean_ctor_set(x_25, 1, x_23);
x_26 = lean_mk_string_unchecked(";", 1, 1);
lean_inc(x_18);
x_27 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_27, 0, x_18);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_mk_string_unchecked("syntheticHole", 13, 13);
x_29 = l_Lean_Name_mkStr4(x_4, x_5, x_14, x_28);
x_30 = lean_mk_string_unchecked("\?", 1, 1);
lean_inc(x_18);
x_31 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_31, 0, x_18);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_mk_string_unchecked("_", 1, 1);
lean_inc(x_18);
x_33 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_33, 0, x_18);
lean_ctor_set(x_33, 1, x_32);
lean_inc(x_18);
x_34 = l_Lean_Syntax_node2(x_18, x_29, x_31, x_33);
lean_inc(x_18);
x_35 = l_Lean_Syntax_node4(x_18, x_24, x_25, x_13, x_27, x_34);
x_36 = l_Lean_Syntax_node2(x_18, x_20, x_22, x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_3);
return x_37;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticLet____1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticLet____1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticShow__() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("tacticShow_", 11, 11);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("show ", 5, 5);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_unbox(x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_12);
x_13 = lean_mk_string_unchecked("term", 4, 4);
x_14 = l_Lean_Name_mkStr1(x_13);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_17, 0, x_8);
lean_ctor_set(x_17, 1, x_11);
lean_ctor_set(x_17, 2, x_16);
x_18 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_18, 0, x_5);
lean_ctor_set(x_18, 1, x_6);
lean_ctor_set(x_18, 2, x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticShow____1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Tactic", 6, 6);
x_7 = lean_mk_string_unchecked("tacticShow_", 11, 11);
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
x_10 = lean_box(1);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = l_Lean_Syntax_getArg(x_1, x_12);
lean_dec(x_1);
x_14 = lean_ctor_get(x_2, 5);
x_15 = lean_box(0);
x_16 = lean_unbox(x_15);
x_17 = l_Lean_SourceInfo_fromRef(x_14, x_16);
x_18 = lean_mk_string_unchecked("tacticRefine_lift_", 18, 18);
lean_inc(x_5);
lean_inc(x_4);
x_19 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_18);
x_20 = lean_mk_string_unchecked("refine_lift", 11, 11);
lean_inc(x_17);
x_21 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_21, 0, x_17);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_mk_string_unchecked("Term", 4, 4);
x_23 = lean_mk_string_unchecked("show", 4, 4);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_5);
lean_inc(x_4);
x_24 = l_Lean_Name_mkStr4(x_4, x_5, x_22, x_23);
lean_inc(x_17);
x_25 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_25, 0, x_17);
lean_ctor_set(x_25, 1, x_23);
x_26 = lean_mk_string_unchecked("fromTerm", 8, 8);
lean_inc(x_22);
lean_inc(x_5);
lean_inc(x_4);
x_27 = l_Lean_Name_mkStr4(x_4, x_5, x_22, x_26);
x_28 = lean_mk_string_unchecked("from", 4, 4);
lean_inc(x_17);
x_29 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_29, 0, x_17);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_mk_string_unchecked("syntheticHole", 13, 13);
x_31 = l_Lean_Name_mkStr4(x_4, x_5, x_22, x_30);
x_32 = lean_mk_string_unchecked("\?", 1, 1);
lean_inc(x_17);
x_33 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_33, 0, x_17);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_mk_string_unchecked("_", 1, 1);
lean_inc(x_17);
x_35 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_35, 0, x_17);
lean_ctor_set(x_35, 1, x_34);
lean_inc(x_17);
x_36 = l_Lean_Syntax_node2(x_17, x_31, x_33, x_35);
lean_inc(x_17);
x_37 = l_Lean_Syntax_node2(x_17, x_27, x_29, x_36);
lean_inc(x_17);
x_38 = l_Lean_Syntax_node3(x_17, x_24, x_25, x_13, x_37);
x_39 = l_Lean_Syntax_node2(x_17, x_19, x_21, x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_3);
return x_40;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticShow____1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticShow____1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_letrec() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("letrec", 6, 6);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("withPosition", 12, 12);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("andthen", 7, 7);
x_10 = l_Lean_Name_mkStr1(x_9);
x_11 = lean_mk_string_unchecked("atomic", 6, 6);
x_12 = l_Lean_Name_mkStr1(x_11);
x_13 = lean_mk_string_unchecked("let ", 4, 4);
x_14 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_mk_string_unchecked("rec ", 4, 4);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_17, 0, x_15);
x_18 = lean_unbox(x_16);
lean_ctor_set_uint8(x_17, sizeof(void*)*1, x_18);
lean_inc(x_10);
x_19 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_19, 0, x_10);
lean_ctor_set(x_19, 1, x_14);
lean_ctor_set(x_19, 2, x_17);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_12);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_mk_string_unchecked("letRecDecls", 11, 11);
x_22 = l_Lean_Name_mkStr1(x_21);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_24, 0, x_10);
lean_ctor_set(x_24, 1, x_20);
lean_ctor_set(x_24, 2, x_23);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_8);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_26, 0, x_5);
lean_ctor_set(x_26, 1, x_6);
lean_ctor_set(x_26, 2, x_25);
return x_26;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__letrec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Tactic", 6, 6);
x_7 = lean_mk_string_unchecked("letrec", 6, 6);
lean_inc(x_7);
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
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_10 = lean_box(1);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_12 = lean_unsigned_to_nat(2u);
x_13 = l_Lean_Syntax_getArg(x_1, x_12);
lean_dec(x_1);
x_14 = lean_mk_string_unchecked("Term", 4, 4);
x_15 = lean_ctor_get(x_2, 5);
x_16 = lean_box(0);
x_17 = lean_unbox(x_16);
x_18 = l_Lean_SourceInfo_fromRef(x_15, x_17);
x_19 = lean_mk_string_unchecked("tacticRefine_lift_", 18, 18);
lean_inc(x_5);
lean_inc(x_4);
x_20 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_19);
x_21 = lean_mk_string_unchecked("refine_lift", 11, 11);
lean_inc(x_18);
x_22 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_22, 0, x_18);
lean_ctor_set(x_22, 1, x_21);
lean_inc(x_14);
lean_inc(x_5);
lean_inc(x_4);
x_23 = l_Lean_Name_mkStr4(x_4, x_5, x_14, x_7);
x_24 = lean_mk_string_unchecked("group", 5, 5);
x_25 = l_Lean_Name_mkStr1(x_24);
x_26 = lean_mk_string_unchecked("let", 3, 3);
lean_inc(x_18);
x_27 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_27, 0, x_18);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_mk_string_unchecked("rec", 3, 3);
lean_inc(x_18);
x_29 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_29, 0, x_18);
lean_ctor_set(x_29, 1, x_28);
lean_inc(x_18);
x_30 = l_Lean_Syntax_node2(x_18, x_25, x_27, x_29);
x_31 = lean_mk_string_unchecked(";", 1, 1);
lean_inc(x_18);
x_32 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_32, 0, x_18);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_mk_string_unchecked("syntheticHole", 13, 13);
x_34 = l_Lean_Name_mkStr4(x_4, x_5, x_14, x_33);
x_35 = lean_mk_string_unchecked("\?", 1, 1);
lean_inc(x_18);
x_36 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_36, 0, x_18);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_mk_string_unchecked("_", 1, 1);
lean_inc(x_18);
x_38 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_38, 0, x_18);
lean_ctor_set(x_38, 1, x_37);
lean_inc(x_18);
x_39 = l_Lean_Syntax_node2(x_18, x_34, x_36, x_38);
lean_inc(x_18);
x_40 = l_Lean_Syntax_node4(x_18, x_23, x_30, x_13, x_32, x_39);
x_41 = l_Lean_Syntax_node2(x_18, x_20, x_22, x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_3);
return x_42;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__letrec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__letrec__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticRefine__lift_x27__() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("tacticRefine_lift'_", 19, 19);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("refine_lift' ", 13, 13);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_unbox(x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_12);
x_13 = lean_mk_string_unchecked("term", 4, 4);
x_14 = l_Lean_Name_mkStr1(x_13);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_17, 0, x_8);
lean_ctor_set(x_17, 1, x_11);
lean_ctor_set(x_17, 2, x_16);
x_18 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_18, 0, x_5);
lean_ctor_set(x_18, 1, x_6);
lean_ctor_set(x_18, 2, x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticRefine__lift_x27____1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Tactic", 6, 6);
x_7 = lean_mk_string_unchecked("tacticRefine_lift'_", 19, 19);
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
x_10 = lean_box(1);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = l_Lean_Syntax_getArg(x_1, x_12);
lean_dec(x_1);
x_14 = lean_ctor_get(x_2, 5);
x_15 = lean_box(0);
x_16 = lean_unbox(x_15);
x_17 = l_Lean_SourceInfo_fromRef(x_14, x_16);
x_18 = lean_mk_string_unchecked("focus", 5, 5);
lean_inc(x_18);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_19 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_18);
lean_inc(x_17);
x_20 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_18);
x_21 = lean_mk_string_unchecked("tacticSeq", 9, 9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_22 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_21);
x_23 = lean_mk_string_unchecked("tacticSeq1Indented", 18, 18);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_24 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_23);
x_25 = lean_mk_string_unchecked("null", 4, 4);
x_26 = l_Lean_Name_mkStr1(x_25);
x_27 = lean_mk_string_unchecked("paren", 5, 5);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_28 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_27);
x_29 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_17);
x_30 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_30, 0, x_17);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_mk_string_unchecked("refine'", 7, 7);
lean_inc(x_31);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_32 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_31);
lean_inc(x_17);
x_33 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_33, 0, x_17);
lean_ctor_set(x_33, 1, x_31);
x_34 = lean_mk_string_unchecked("Term", 4, 4);
x_35 = lean_mk_string_unchecked("noImplicitLambda", 16, 16);
lean_inc(x_5);
lean_inc(x_4);
x_36 = l_Lean_Name_mkStr4(x_4, x_5, x_34, x_35);
x_37 = lean_mk_string_unchecked("no_implicit_lambda%", 19, 19);
lean_inc(x_17);
x_38 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_38, 0, x_17);
lean_ctor_set(x_38, 1, x_37);
lean_inc(x_17);
x_39 = l_Lean_Syntax_node2(x_17, x_36, x_38, x_13);
lean_inc(x_17);
x_40 = l_Lean_Syntax_node2(x_17, x_32, x_33, x_39);
x_41 = lean_mk_string_unchecked(";", 1, 1);
lean_inc(x_17);
x_42 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_42, 0, x_17);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_mk_string_unchecked("rotateRight", 11, 11);
x_44 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_43);
x_45 = lean_mk_string_unchecked("rotate_right", 12, 12);
lean_inc(x_17);
x_46 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_46, 0, x_17);
lean_ctor_set(x_46, 1, x_45);
x_47 = l_Array_mkArray0(lean_box(0));
lean_inc(x_26);
lean_inc(x_17);
x_48 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_48, 0, x_17);
lean_ctor_set(x_48, 1, x_26);
lean_ctor_set(x_48, 2, x_47);
lean_inc(x_17);
x_49 = l_Lean_Syntax_node2(x_17, x_44, x_46, x_48);
lean_inc(x_26);
lean_inc(x_17);
x_50 = l_Lean_Syntax_node3(x_17, x_26, x_40, x_42, x_49);
lean_inc(x_24);
lean_inc(x_17);
x_51 = l_Lean_Syntax_node1(x_17, x_24, x_50);
lean_inc(x_22);
lean_inc(x_17);
x_52 = l_Lean_Syntax_node1(x_17, x_22, x_51);
x_53 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_17);
x_54 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_54, 0, x_17);
lean_ctor_set(x_54, 1, x_53);
lean_inc(x_17);
x_55 = l_Lean_Syntax_node3(x_17, x_28, x_30, x_52, x_54);
lean_inc(x_17);
x_56 = l_Lean_Syntax_node1(x_17, x_26, x_55);
lean_inc(x_17);
x_57 = l_Lean_Syntax_node1(x_17, x_24, x_56);
lean_inc(x_17);
x_58 = l_Lean_Syntax_node1(x_17, x_22, x_57);
x_59 = l_Lean_Syntax_node2(x_17, x_19, x_20, x_58);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_3);
return x_60;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticRefine__lift_x27____1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticRefine__lift_x27____1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticHave_x27__() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("tacticHave'_", 12, 12);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("have' ", 6, 6);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_unbox(x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_12);
x_13 = lean_mk_string_unchecked("haveDecl", 8, 8);
x_14 = l_Lean_Name_mkStr1(x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_16, 0, x_8);
lean_ctor_set(x_16, 1, x_11);
lean_ctor_set(x_16, 2, x_15);
x_17 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_17, 0, x_5);
lean_ctor_set(x_17, 1, x_6);
lean_ctor_set(x_17, 2, x_16);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticHave_x27____1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Tactic", 6, 6);
x_7 = lean_mk_string_unchecked("tacticHave'_", 12, 12);
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
x_10 = lean_box(1);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = l_Lean_Syntax_getArg(x_1, x_12);
lean_dec(x_1);
x_14 = lean_mk_string_unchecked("Term", 4, 4);
x_15 = lean_ctor_get(x_2, 5);
x_16 = lean_box(0);
x_17 = lean_unbox(x_16);
x_18 = l_Lean_SourceInfo_fromRef(x_15, x_17);
x_19 = lean_mk_string_unchecked("tacticRefine_lift'_", 19, 19);
lean_inc(x_5);
lean_inc(x_4);
x_20 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_19);
x_21 = lean_mk_string_unchecked("refine_lift'", 12, 12);
lean_inc(x_18);
x_22 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_22, 0, x_18);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_mk_string_unchecked("have", 4, 4);
lean_inc(x_23);
lean_inc(x_14);
lean_inc(x_5);
lean_inc(x_4);
x_24 = l_Lean_Name_mkStr4(x_4, x_5, x_14, x_23);
lean_inc(x_18);
x_25 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_25, 0, x_18);
lean_ctor_set(x_25, 1, x_23);
x_26 = lean_mk_string_unchecked(";", 1, 1);
lean_inc(x_18);
x_27 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_27, 0, x_18);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_mk_string_unchecked("syntheticHole", 13, 13);
x_29 = l_Lean_Name_mkStr4(x_4, x_5, x_14, x_28);
x_30 = lean_mk_string_unchecked("\?", 1, 1);
lean_inc(x_18);
x_31 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_31, 0, x_18);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_mk_string_unchecked("_", 1, 1);
lean_inc(x_18);
x_33 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_33, 0, x_18);
lean_ctor_set(x_33, 1, x_32);
lean_inc(x_18);
x_34 = l_Lean_Syntax_node2(x_18, x_29, x_31, x_33);
lean_inc(x_18);
x_35 = l_Lean_Syntax_node4(x_18, x_24, x_25, x_13, x_27, x_34);
x_36 = l_Lean_Syntax_node2(x_18, x_20, x_22, x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_3);
return x_37;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticHave_x27____1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticHave_x27____1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticHave_x27___x3a_x3d__() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("tacticHave'_:=_", 15, 15);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("have'", 5, 5);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_unbox(x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_12);
x_13 = lean_mk_string_unchecked("ident", 5, 5);
x_14 = l_Lean_Name_mkStr1(x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
lean_inc(x_8);
x_16 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_16, 0, x_8);
lean_ctor_set(x_16, 1, x_11);
lean_ctor_set(x_16, 2, x_15);
x_17 = lean_mk_string_unchecked(" := ", 4, 4);
x_18 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_18, 0, x_17);
lean_inc(x_8);
x_19 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_19, 0, x_8);
lean_ctor_set(x_19, 1, x_16);
lean_ctor_set(x_19, 2, x_18);
x_20 = lean_mk_string_unchecked("term", 4, 4);
x_21 = l_Lean_Name_mkStr1(x_20);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_24, 0, x_8);
lean_ctor_set(x_24, 1, x_19);
lean_ctor_set(x_24, 2, x_23);
x_25 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_25, 0, x_5);
lean_ctor_set(x_25, 1, x_6);
lean_ctor_set(x_25, 2, x_24);
return x_25;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticHave_x27___x3a_x3d____1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Tactic", 6, 6);
x_7 = lean_mk_string_unchecked("tacticHave'_:=_", 15, 15);
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
x_10 = lean_box(1);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = l_Lean_Syntax_getArg(x_1, x_12);
x_14 = lean_unsigned_to_nat(3u);
x_15 = l_Lean_Syntax_getArg(x_1, x_14);
lean_dec(x_1);
x_16 = lean_ctor_get(x_2, 5);
x_17 = lean_box(0);
x_18 = lean_unbox(x_17);
x_19 = l_Lean_SourceInfo_fromRef(x_16, x_18);
x_20 = lean_mk_string_unchecked("tacticHave'_", 12, 12);
lean_inc(x_5);
lean_inc(x_4);
x_21 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_20);
x_22 = lean_mk_string_unchecked("have'", 5, 5);
lean_inc(x_19);
x_23 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_23, 0, x_19);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_mk_string_unchecked("Term", 4, 4);
x_25 = lean_mk_string_unchecked("haveDecl", 8, 8);
lean_inc(x_24);
lean_inc(x_5);
lean_inc(x_4);
x_26 = l_Lean_Name_mkStr4(x_4, x_5, x_24, x_25);
x_27 = lean_mk_string_unchecked("haveIdDecl", 10, 10);
lean_inc(x_24);
lean_inc(x_5);
lean_inc(x_4);
x_28 = l_Lean_Name_mkStr4(x_4, x_5, x_24, x_27);
x_29 = lean_mk_string_unchecked("haveId", 6, 6);
lean_inc(x_24);
lean_inc(x_5);
lean_inc(x_4);
x_30 = l_Lean_Name_mkStr4(x_4, x_5, x_24, x_29);
lean_inc(x_19);
x_31 = l_Lean_Syntax_node1(x_19, x_30, x_13);
x_32 = lean_mk_string_unchecked("null", 4, 4);
x_33 = l_Lean_Name_mkStr1(x_32);
x_34 = l_Array_mkArray0(lean_box(0));
lean_inc(x_33);
lean_inc(x_19);
x_35 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_35, 0, x_19);
lean_ctor_set(x_35, 1, x_33);
lean_ctor_set(x_35, 2, x_34);
x_36 = lean_mk_string_unchecked("typeSpec", 8, 8);
lean_inc(x_24);
lean_inc(x_5);
lean_inc(x_4);
x_37 = l_Lean_Name_mkStr4(x_4, x_5, x_24, x_36);
x_38 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_19);
x_39 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_39, 0, x_19);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_mk_string_unchecked("hole", 4, 4);
x_41 = l_Lean_Name_mkStr4(x_4, x_5, x_24, x_40);
x_42 = lean_mk_string_unchecked("_", 1, 1);
lean_inc(x_19);
x_43 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_43, 0, x_19);
lean_ctor_set(x_43, 1, x_42);
lean_inc(x_19);
x_44 = l_Lean_Syntax_node1(x_19, x_41, x_43);
lean_inc(x_19);
x_45 = l_Lean_Syntax_node2(x_19, x_37, x_39, x_44);
lean_inc(x_19);
x_46 = l_Lean_Syntax_node1(x_19, x_33, x_45);
x_47 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_19);
x_48 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_48, 0, x_19);
lean_ctor_set(x_48, 1, x_47);
lean_inc(x_19);
x_49 = l_Lean_Syntax_node5(x_19, x_28, x_31, x_35, x_46, x_48, x_15);
lean_inc(x_19);
x_50 = l_Lean_Syntax_node1(x_19, x_26, x_49);
x_51 = l_Lean_Syntax_node2(x_19, x_21, x_23, x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_3);
return x_52;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticHave_x27___x3a_x3d____1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticHave_x27___x3a_x3d____1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticLet_x27__() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("tacticLet'_", 11, 11);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("let' ", 5, 5);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_unbox(x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_12);
x_13 = lean_mk_string_unchecked("letDecl", 7, 7);
x_14 = l_Lean_Name_mkStr1(x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_16, 0, x_8);
lean_ctor_set(x_16, 1, x_11);
lean_ctor_set(x_16, 2, x_15);
x_17 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_17, 0, x_5);
lean_ctor_set(x_17, 1, x_6);
lean_ctor_set(x_17, 2, x_16);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticLet_x27____1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Tactic", 6, 6);
x_7 = lean_mk_string_unchecked("tacticLet'_", 11, 11);
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
x_10 = lean_box(1);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = l_Lean_Syntax_getArg(x_1, x_12);
lean_dec(x_1);
x_14 = lean_mk_string_unchecked("Term", 4, 4);
x_15 = lean_ctor_get(x_2, 5);
x_16 = lean_box(0);
x_17 = lean_unbox(x_16);
x_18 = l_Lean_SourceInfo_fromRef(x_15, x_17);
x_19 = lean_mk_string_unchecked("tacticRefine_lift'_", 19, 19);
lean_inc(x_5);
lean_inc(x_4);
x_20 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_19);
x_21 = lean_mk_string_unchecked("refine_lift'", 12, 12);
lean_inc(x_18);
x_22 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_22, 0, x_18);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_mk_string_unchecked("let", 3, 3);
lean_inc(x_23);
lean_inc(x_14);
lean_inc(x_5);
lean_inc(x_4);
x_24 = l_Lean_Name_mkStr4(x_4, x_5, x_14, x_23);
lean_inc(x_18);
x_25 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_25, 0, x_18);
lean_ctor_set(x_25, 1, x_23);
x_26 = lean_mk_string_unchecked(";", 1, 1);
lean_inc(x_18);
x_27 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_27, 0, x_18);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_mk_string_unchecked("syntheticHole", 13, 13);
x_29 = l_Lean_Name_mkStr4(x_4, x_5, x_14, x_28);
x_30 = lean_mk_string_unchecked("\?", 1, 1);
lean_inc(x_18);
x_31 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_31, 0, x_18);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_mk_string_unchecked("_", 1, 1);
lean_inc(x_18);
x_33 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_33, 0, x_18);
lean_ctor_set(x_33, 1, x_32);
lean_inc(x_18);
x_34 = l_Lean_Syntax_node2(x_18, x_29, x_31, x_33);
lean_inc(x_18);
x_35 = l_Lean_Syntax_node4(x_18, x_24, x_25, x_13, x_27, x_34);
x_36 = l_Lean_Syntax_node2(x_18, x_20, x_22, x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_3);
return x_37;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticLet_x27____1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticLet_x27____1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_inductionAltLHS() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_1 = lean_mk_string_unchecked("inductionAltLHS", 15, 15);
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Tactic", 6, 6);
lean_inc(x_1);
x_5 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_1);
x_6 = lean_mk_string_unchecked("withPosition", 12, 12);
x_7 = l_Lean_Name_mkStr1(x_6);
x_8 = lean_mk_string_unchecked("andthen", 7, 7);
x_9 = l_Lean_Name_mkStr1(x_8);
x_10 = lean_mk_string_unchecked("| ", 2, 2);
x_11 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_mk_string_unchecked("orelse", 6, 6);
x_13 = l_Lean_Name_mkStr1(x_12);
x_14 = lean_mk_string_unchecked("group", 5, 5);
x_15 = l_Lean_Name_mkStr1(x_14);
x_16 = lean_mk_string_unchecked("optional", 8, 8);
x_17 = l_Lean_Name_mkStr1(x_16);
x_18 = lean_mk_string_unchecked("@", 1, 1);
x_19 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_mk_string_unchecked("ident", 5, 5);
x_22 = l_Lean_Name_mkStr1(x_21);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_22);
lean_inc(x_23);
lean_inc(x_9);
x_24 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_24, 0, x_9);
lean_ctor_set(x_24, 1, x_20);
lean_ctor_set(x_24, 2, x_23);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_15);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_mk_string_unchecked("hole", 4, 4);
x_27 = l_Lean_Name_mkStr1(x_26);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
lean_inc(x_28);
lean_inc(x_13);
x_29 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_29, 0, x_13);
lean_ctor_set(x_29, 1, x_25);
lean_ctor_set(x_29, 2, x_28);
lean_inc(x_9);
x_30 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_30, 0, x_9);
lean_ctor_set(x_30, 1, x_11);
lean_ctor_set(x_30, 2, x_29);
x_31 = lean_mk_string_unchecked("many", 4, 4);
x_32 = l_Lean_Name_mkStr1(x_31);
x_33 = lean_mk_string_unchecked("colGt", 5, 5);
x_34 = l_Lean_Name_mkStr1(x_33);
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_34);
x_36 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_36, 0, x_13);
lean_ctor_set(x_36, 1, x_23);
lean_ctor_set(x_36, 2, x_28);
lean_inc(x_9);
x_37 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_37, 0, x_9);
lean_ctor_set(x_37, 1, x_35);
lean_ctor_set(x_37, 2, x_36);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_32);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_39, 0, x_9);
lean_ctor_set(x_39, 1, x_30);
lean_ctor_set(x_39, 2, x_38);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_7);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_41, 0, x_1);
lean_ctor_set(x_41, 1, x_5);
lean_ctor_set(x_41, 2, x_40);
return x_41;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_inductionAlt() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_1 = lean_mk_string_unchecked("inductionAlt", 12, 12);
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Tactic", 6, 6);
lean_inc(x_1);
x_5 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_1);
x_6 = lean_mk_string_unchecked("andthen", 7, 7);
x_7 = l_Lean_Name_mkStr1(x_6);
x_8 = lean_mk_string_unchecked("ppDedent", 8, 8);
x_9 = l_Lean_Name_mkStr1(x_8);
x_10 = lean_mk_string_unchecked("ppLine", 6, 6);
x_11 = l_Lean_Name_mkStr1(x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_mk_string_unchecked("many1", 5, 5);
x_15 = l_Lean_Name_mkStr1(x_14);
x_16 = l_Lean_Parser_Tactic_inductionAltLHS;
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
lean_inc(x_7);
x_18 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_18, 0, x_7);
lean_ctor_set(x_18, 1, x_13);
lean_ctor_set(x_18, 2, x_17);
x_19 = lean_mk_string_unchecked("optional", 8, 8);
x_20 = l_Lean_Name_mkStr1(x_19);
x_21 = lean_mk_string_unchecked(" => ", 4, 4);
x_22 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_mk_string_unchecked("orelse", 6, 6);
x_24 = l_Lean_Name_mkStr1(x_23);
x_25 = lean_mk_string_unchecked("hole", 4, 4);
x_26 = l_Lean_Name_mkStr1(x_25);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_mk_string_unchecked("syntheticHole", 13, 13);
x_29 = l_Lean_Name_mkStr1(x_28);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_mk_string_unchecked("tacticSeq", 9, 9);
x_32 = l_Lean_Name_mkStr1(x_31);
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_32);
lean_inc(x_24);
x_34 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_34, 0, x_24);
lean_ctor_set(x_34, 1, x_30);
lean_ctor_set(x_34, 2, x_33);
x_35 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_35, 0, x_24);
lean_ctor_set(x_35, 1, x_27);
lean_ctor_set(x_35, 2, x_34);
lean_inc(x_7);
x_36 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_36, 0, x_7);
lean_ctor_set(x_36, 1, x_22);
lean_ctor_set(x_36, 2, x_35);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_20);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_38, 0, x_7);
lean_ctor_set(x_38, 1, x_18);
lean_ctor_set(x_38, 2, x_37);
x_39 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_39, 0, x_1);
lean_ctor_set(x_39, 1, x_5);
lean_ctor_set(x_39, 2, x_38);
return x_39;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_inductionAlts() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_1 = lean_mk_string_unchecked("inductionAlts", 13, 13);
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Tactic", 6, 6);
lean_inc(x_1);
x_5 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_1);
x_6 = lean_mk_string_unchecked("andthen", 7, 7);
x_7 = l_Lean_Name_mkStr1(x_6);
x_8 = lean_mk_string_unchecked(" with", 5, 5);
x_9 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_mk_string_unchecked("optional", 8, 8);
x_11 = l_Lean_Name_mkStr1(x_10);
x_12 = lean_mk_string_unchecked("ppSpace", 7, 7);
x_13 = l_Lean_Name_mkStr1(x_12);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_mk_string_unchecked("colGt", 5, 5);
x_16 = l_Lean_Name_mkStr1(x_15);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
lean_inc(x_7);
x_18 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_18, 0, x_7);
lean_ctor_set(x_18, 1, x_14);
lean_ctor_set(x_18, 2, x_17);
x_19 = lean_mk_string_unchecked("tactic", 6, 6);
x_20 = l_Lean_Name_mkStr1(x_19);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
lean_inc(x_7);
x_23 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_23, 0, x_7);
lean_ctor_set(x_23, 1, x_18);
lean_ctor_set(x_23, 2, x_22);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_11);
lean_ctor_set(x_24, 1, x_23);
lean_inc(x_7);
x_25 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_25, 0, x_7);
lean_ctor_set(x_25, 1, x_9);
lean_ctor_set(x_25, 2, x_24);
x_26 = lean_mk_string_unchecked("withPosition", 12, 12);
x_27 = l_Lean_Name_mkStr1(x_26);
x_28 = lean_mk_string_unchecked("many", 4, 4);
x_29 = l_Lean_Name_mkStr1(x_28);
x_30 = lean_mk_string_unchecked("colGe", 5, 5);
x_31 = l_Lean_Name_mkStr1(x_30);
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = l_Lean_Parser_Tactic_inductionAlt;
lean_inc(x_7);
x_34 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_34, 0, x_7);
lean_ctor_set(x_34, 1, x_32);
lean_ctor_set(x_34, 2, x_33);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_29);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_27);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_37, 0, x_7);
lean_ctor_set(x_37, 1, x_25);
lean_ctor_set(x_37, 2, x_36);
x_38 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_38, 0, x_1);
lean_ctor_set(x_38, 1, x_5);
lean_ctor_set(x_38, 2, x_37);
return x_38;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_elimTarget() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_1 = lean_mk_string_unchecked("elimTarget", 10, 10);
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Tactic", 6, 6);
lean_inc(x_1);
x_5 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_1);
x_6 = lean_mk_string_unchecked("andthen", 7, 7);
x_7 = l_Lean_Name_mkStr1(x_6);
x_8 = lean_mk_string_unchecked("optional", 8, 8);
x_9 = l_Lean_Name_mkStr1(x_8);
x_10 = lean_mk_string_unchecked("atomic", 6, 6);
x_11 = l_Lean_Name_mkStr1(x_10);
x_12 = l_Lean_binderIdent;
x_13 = lean_mk_string_unchecked(" : ", 3, 3);
x_14 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_14, 0, x_13);
lean_inc(x_7);
x_15 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_12);
lean_ctor_set(x_15, 2, x_14);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_9);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_mk_string_unchecked("term", 4, 4);
x_19 = l_Lean_Name_mkStr1(x_18);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_22, 0, x_7);
lean_ctor_set(x_22, 1, x_17);
lean_ctor_set(x_22, 2, x_21);
x_23 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_23, 0, x_1);
lean_ctor_set(x_23, 1, x_5);
lean_ctor_set(x_23, 2, x_22);
return x_23;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_induction() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("induction", 9, 9);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("induction ", 10, 10);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_unbox(x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_12);
x_13 = l_Lean_Parser_Tactic_elimTarget;
x_14 = lean_mk_string_unchecked(",", 1, 1);
x_15 = lean_mk_string_unchecked(", ", 2, 2);
x_16 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(11, 3, 1);
lean_ctor_set(x_17, 0, x_13);
lean_ctor_set(x_17, 1, x_14);
lean_ctor_set(x_17, 2, x_16);
x_18 = lean_unbox(x_10);
lean_ctor_set_uint8(x_17, sizeof(void*)*3, x_18);
lean_inc(x_8);
x_19 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_19, 0, x_8);
lean_ctor_set(x_19, 1, x_11);
lean_ctor_set(x_19, 2, x_17);
x_20 = lean_mk_string_unchecked("optional", 8, 8);
x_21 = l_Lean_Name_mkStr1(x_20);
x_22 = lean_mk_string_unchecked(" using ", 7, 7);
x_23 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_mk_string_unchecked("term", 4, 4);
x_25 = l_Lean_Name_mkStr1(x_24);
x_26 = lean_unsigned_to_nat(0u);
lean_inc(x_25);
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
lean_inc(x_8);
x_28 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_28, 0, x_8);
lean_ctor_set(x_28, 1, x_23);
lean_ctor_set(x_28, 2, x_27);
lean_inc(x_21);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_21);
lean_ctor_set(x_29, 1, x_28);
lean_inc(x_8);
x_30 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_30, 0, x_8);
lean_ctor_set(x_30, 1, x_19);
lean_ctor_set(x_30, 2, x_29);
x_31 = lean_mk_string_unchecked(" generalizing", 13, 13);
x_32 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = lean_mk_string_unchecked("many1", 5, 5);
x_34 = l_Lean_Name_mkStr1(x_33);
x_35 = lean_mk_string_unchecked("ppSpace", 7, 7);
x_36 = l_Lean_Name_mkStr1(x_35);
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = lean_mk_string_unchecked("colGt", 5, 5);
x_39 = l_Lean_Name_mkStr1(x_38);
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_39);
lean_inc(x_8);
x_41 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_41, 0, x_8);
lean_ctor_set(x_41, 1, x_37);
lean_ctor_set(x_41, 2, x_40);
x_42 = lean_unsigned_to_nat(1024u);
x_43 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_43, 0, x_25);
lean_ctor_set(x_43, 1, x_42);
lean_inc(x_8);
x_44 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_44, 0, x_8);
lean_ctor_set(x_44, 1, x_41);
lean_ctor_set(x_44, 2, x_43);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_34);
lean_ctor_set(x_45, 1, x_44);
lean_inc(x_8);
x_46 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_46, 0, x_8);
lean_ctor_set(x_46, 1, x_32);
lean_ctor_set(x_46, 2, x_45);
lean_inc(x_21);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_21);
lean_ctor_set(x_47, 1, x_46);
lean_inc(x_8);
x_48 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_48, 0, x_8);
lean_ctor_set(x_48, 1, x_30);
lean_ctor_set(x_48, 2, x_47);
x_49 = l_Lean_Parser_Tactic_inductionAlts;
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_21);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_51, 0, x_8);
lean_ctor_set(x_51, 1, x_48);
lean_ctor_set(x_51, 2, x_50);
x_52 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_52, 0, x_5);
lean_ctor_set(x_52, 1, x_6);
lean_ctor_set(x_52, 2, x_51);
return x_52;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_generalizeArg() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_1 = lean_mk_string_unchecked("generalizeArg", 13, 13);
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Tactic", 6, 6);
lean_inc(x_1);
x_5 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_1);
x_6 = lean_mk_string_unchecked("andthen", 7, 7);
x_7 = l_Lean_Name_mkStr1(x_6);
x_8 = lean_mk_string_unchecked("optional", 8, 8);
x_9 = l_Lean_Name_mkStr1(x_8);
x_10 = lean_mk_string_unchecked("atomic", 6, 6);
x_11 = l_Lean_Name_mkStr1(x_10);
x_12 = lean_mk_string_unchecked("ident", 5, 5);
x_13 = l_Lean_Name_mkStr1(x_12);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_mk_string_unchecked(" : ", 3, 3);
x_16 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_16, 0, x_15);
lean_inc(x_14);
lean_inc(x_7);
x_17 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_17, 0, x_7);
lean_ctor_set(x_17, 1, x_14);
lean_ctor_set(x_17, 2, x_16);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_9);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_mk_string_unchecked("term", 4, 4);
x_21 = l_Lean_Name_mkStr1(x_20);
x_22 = lean_unsigned_to_nat(51u);
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
lean_inc(x_7);
x_24 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_24, 0, x_7);
lean_ctor_set(x_24, 1, x_19);
lean_ctor_set(x_24, 2, x_23);
x_25 = lean_mk_string_unchecked(" = ", 3, 3);
x_26 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_26, 0, x_25);
lean_inc(x_7);
x_27 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_27, 0, x_7);
lean_ctor_set(x_27, 1, x_24);
lean_ctor_set(x_27, 2, x_26);
x_28 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_28, 0, x_7);
lean_ctor_set(x_28, 1, x_27);
lean_ctor_set(x_28, 2, x_14);
x_29 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_29, 0, x_1);
lean_ctor_set(x_29, 1, x_5);
lean_ctor_set(x_29, 2, x_28);
return x_29;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_generalize() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("generalize", 10, 10);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("generalize ", 11, 11);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_unbox(x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_12);
x_13 = l_Lean_Parser_Tactic_generalizeArg;
x_14 = lean_mk_string_unchecked(",", 1, 1);
x_15 = lean_mk_string_unchecked(", ", 2, 2);
x_16 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(11, 3, 1);
lean_ctor_set(x_17, 0, x_13);
lean_ctor_set(x_17, 1, x_14);
lean_ctor_set(x_17, 2, x_16);
x_18 = lean_unbox(x_10);
lean_ctor_set_uint8(x_17, sizeof(void*)*3, x_18);
lean_inc(x_8);
x_19 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_19, 0, x_8);
lean_ctor_set(x_19, 1, x_11);
lean_ctor_set(x_19, 2, x_17);
x_20 = lean_mk_string_unchecked("optional", 8, 8);
x_21 = l_Lean_Name_mkStr1(x_20);
x_22 = l_Lean_Parser_Tactic_location;
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_24, 0, x_8);
lean_ctor_set(x_24, 1, x_19);
lean_ctor_set(x_24, 2, x_23);
x_25 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_25, 0, x_5);
lean_ctor_set(x_25, 1, x_6);
lean_ctor_set(x_25, 2, x_24);
return x_25;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_cases() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("cases", 5, 5);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("cases ", 6, 6);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_unbox(x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_12);
x_13 = l_Lean_Parser_Tactic_elimTarget;
x_14 = lean_mk_string_unchecked(",", 1, 1);
x_15 = lean_mk_string_unchecked(", ", 2, 2);
x_16 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(11, 3, 1);
lean_ctor_set(x_17, 0, x_13);
lean_ctor_set(x_17, 1, x_14);
lean_ctor_set(x_17, 2, x_16);
x_18 = lean_unbox(x_10);
lean_ctor_set_uint8(x_17, sizeof(void*)*3, x_18);
lean_inc(x_8);
x_19 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_19, 0, x_8);
lean_ctor_set(x_19, 1, x_11);
lean_ctor_set(x_19, 2, x_17);
x_20 = lean_mk_string_unchecked("optional", 8, 8);
x_21 = l_Lean_Name_mkStr1(x_20);
x_22 = lean_mk_string_unchecked(" using ", 7, 7);
x_23 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_mk_string_unchecked("term", 4, 4);
x_25 = l_Lean_Name_mkStr1(x_24);
x_26 = lean_unsigned_to_nat(0u);
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
lean_inc(x_8);
x_28 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_28, 0, x_8);
lean_ctor_set(x_28, 1, x_23);
lean_ctor_set(x_28, 2, x_27);
lean_inc(x_21);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_21);
lean_ctor_set(x_29, 1, x_28);
lean_inc(x_8);
x_30 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_30, 0, x_8);
lean_ctor_set(x_30, 1, x_19);
lean_ctor_set(x_30, 2, x_29);
x_31 = l_Lean_Parser_Tactic_inductionAlts;
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_21);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_33, 0, x_8);
lean_ctor_set(x_33, 1, x_30);
lean_ctor_set(x_33, 2, x_32);
x_34 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_34, 0, x_5);
lean_ctor_set(x_34, 1, x_6);
lean_ctor_set(x_34, 2, x_33);
return x_34;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_funInduction() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("funInduction", 12, 12);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("fun_induction ", 14, 14);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_unbox(x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_12);
x_13 = lean_mk_string_unchecked("term", 4, 4);
x_14 = l_Lean_Name_mkStr1(x_13);
x_15 = lean_unsigned_to_nat(0u);
lean_inc(x_14);
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
lean_inc(x_8);
x_17 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_17, 0, x_8);
lean_ctor_set(x_17, 1, x_11);
lean_ctor_set(x_17, 2, x_16);
x_18 = lean_mk_string_unchecked("optional", 8, 8);
x_19 = l_Lean_Name_mkStr1(x_18);
x_20 = lean_mk_string_unchecked(" generalizing", 13, 13);
x_21 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_mk_string_unchecked("many1", 5, 5);
x_23 = l_Lean_Name_mkStr1(x_22);
x_24 = lean_mk_string_unchecked("ppSpace", 7, 7);
x_25 = l_Lean_Name_mkStr1(x_24);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_mk_string_unchecked("colGt", 5, 5);
x_28 = l_Lean_Name_mkStr1(x_27);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_28);
lean_inc(x_8);
x_30 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_30, 0, x_8);
lean_ctor_set(x_30, 1, x_26);
lean_ctor_set(x_30, 2, x_29);
x_31 = lean_unsigned_to_nat(1024u);
x_32 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_32, 0, x_14);
lean_ctor_set(x_32, 1, x_31);
lean_inc(x_8);
x_33 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_33, 0, x_8);
lean_ctor_set(x_33, 1, x_30);
lean_ctor_set(x_33, 2, x_32);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_23);
lean_ctor_set(x_34, 1, x_33);
lean_inc(x_8);
x_35 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_35, 0, x_8);
lean_ctor_set(x_35, 1, x_21);
lean_ctor_set(x_35, 2, x_34);
lean_inc(x_19);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_19);
lean_ctor_set(x_36, 1, x_35);
lean_inc(x_8);
x_37 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_37, 0, x_8);
lean_ctor_set(x_37, 1, x_17);
lean_ctor_set(x_37, 2, x_36);
x_38 = l_Lean_Parser_Tactic_inductionAlts;
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_19);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_40, 0, x_8);
lean_ctor_set(x_40, 1, x_37);
lean_ctor_set(x_40, 2, x_39);
x_41 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_41, 0, x_5);
lean_ctor_set(x_41, 1, x_6);
lean_ctor_set(x_41, 2, x_40);
return x_41;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_funCases() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("funCases", 8, 8);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("fun_cases ", 10, 10);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_unbox(x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_12);
x_13 = lean_mk_string_unchecked("term", 4, 4);
x_14 = l_Lean_Name_mkStr1(x_13);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
lean_inc(x_8);
x_17 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_17, 0, x_8);
lean_ctor_set(x_17, 1, x_11);
lean_ctor_set(x_17, 2, x_16);
x_18 = lean_mk_string_unchecked("optional", 8, 8);
x_19 = l_Lean_Name_mkStr1(x_18);
x_20 = l_Lean_Parser_Tactic_inductionAlts;
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_22, 0, x_8);
lean_ctor_set(x_22, 1, x_17);
lean_ctor_set(x_22, 2, x_21);
x_23 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_23, 0, x_5);
lean_ctor_set(x_23, 1, x_6);
lean_ctor_set(x_23, 2, x_22);
return x_23;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_renameI() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("renameI", 7, 7);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("rename_i", 8, 8);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_unbox(x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_12);
x_13 = lean_mk_string_unchecked("many1", 5, 5);
x_14 = l_Lean_Name_mkStr1(x_13);
x_15 = lean_mk_string_unchecked("ppSpace", 7, 7);
x_16 = l_Lean_Name_mkStr1(x_15);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_mk_string_unchecked("colGt", 5, 5);
x_19 = l_Lean_Name_mkStr1(x_18);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
lean_inc(x_8);
x_21 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_21, 0, x_8);
lean_ctor_set(x_21, 1, x_17);
lean_ctor_set(x_21, 2, x_20);
x_22 = l_Lean_binderIdent;
lean_inc(x_8);
x_23 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_23, 0, x_8);
lean_ctor_set(x_23, 1, x_21);
lean_ctor_set(x_23, 2, x_22);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_14);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_25, 0, x_8);
lean_ctor_set(x_25, 1, x_11);
lean_ctor_set(x_25, 2, x_24);
x_26 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_26, 0, x_5);
lean_ctor_set(x_26, 1, x_6);
lean_ctor_set(x_26, 2, x_25);
return x_26;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticRepeat__() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("tacticRepeat_", 13, 13);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("repeat ", 7, 7);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_unbox(x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_12);
x_13 = lean_mk_string_unchecked("tacticSeq", 9, 9);
x_14 = l_Lean_Name_mkStr1(x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_16, 0, x_8);
lean_ctor_set(x_16, 1, x_11);
lean_ctor_set(x_16, 2, x_15);
x_17 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_17, 0, x_5);
lean_ctor_set(x_17, 1, x_6);
lean_ctor_set(x_17, 2, x_16);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticRepeat____1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Tactic", 6, 6);
x_7 = lean_mk_string_unchecked("tacticRepeat_", 13, 13);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_8 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_7);
lean_inc(x_1);
x_9 = l_Lean_Syntax_isOfKind(x_1, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_10 = lean_box(1);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = l_Lean_Syntax_getArg(x_1, x_12);
lean_dec(x_1);
x_14 = lean_mk_string_unchecked("tacticSeq", 9, 9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_15 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_14);
x_16 = lean_ctor_get(x_2, 5);
x_17 = lean_box(0);
x_18 = lean_unbox(x_17);
x_19 = l_Lean_SourceInfo_fromRef(x_16, x_18);
x_20 = lean_mk_string_unchecked("first", 5, 5);
lean_inc(x_20);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_21 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_20);
lean_inc(x_19);
x_22 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_20);
x_23 = lean_mk_string_unchecked("null", 4, 4);
x_24 = l_Lean_Name_mkStr1(x_23);
x_25 = lean_mk_string_unchecked("group", 5, 5);
x_26 = l_Lean_Name_mkStr1(x_25);
x_27 = lean_mk_string_unchecked("|", 1, 1);
lean_inc(x_19);
x_28 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_28, 0, x_19);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_mk_string_unchecked("tacticSeq1Indented", 18, 18);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_30 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_29);
x_31 = lean_mk_string_unchecked("paren", 5, 5);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_32 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_31);
x_33 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_19);
x_34 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_34, 0, x_19);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_19);
x_36 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_36, 0, x_19);
lean_ctor_set(x_36, 1, x_35);
lean_inc(x_13);
lean_inc(x_19);
x_37 = l_Lean_Syntax_node3(x_19, x_32, x_34, x_13, x_36);
x_38 = lean_mk_string_unchecked(";", 1, 1);
lean_inc(x_19);
x_39 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_39, 0, x_19);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_mk_string_unchecked("repeat", 6, 6);
lean_inc(x_19);
x_41 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_41, 0, x_19);
lean_ctor_set(x_41, 1, x_40);
lean_inc(x_19);
x_42 = l_Lean_Syntax_node2(x_19, x_8, x_41, x_13);
lean_inc(x_24);
lean_inc(x_19);
x_43 = l_Lean_Syntax_node3(x_19, x_24, x_37, x_39, x_42);
lean_inc(x_30);
lean_inc(x_19);
x_44 = l_Lean_Syntax_node1(x_19, x_30, x_43);
lean_inc(x_15);
lean_inc(x_19);
x_45 = l_Lean_Syntax_node1(x_19, x_15, x_44);
lean_inc(x_28);
lean_inc(x_26);
lean_inc(x_19);
x_46 = l_Lean_Syntax_node2(x_19, x_26, x_28, x_45);
x_47 = lean_mk_string_unchecked("skip", 4, 4);
lean_inc(x_47);
x_48 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_47);
lean_inc(x_19);
x_49 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_49, 0, x_19);
lean_ctor_set(x_49, 1, x_47);
lean_inc(x_19);
x_50 = l_Lean_Syntax_node1(x_19, x_48, x_49);
lean_inc(x_24);
lean_inc(x_19);
x_51 = l_Lean_Syntax_node1(x_19, x_24, x_50);
lean_inc(x_19);
x_52 = l_Lean_Syntax_node1(x_19, x_30, x_51);
lean_inc(x_19);
x_53 = l_Lean_Syntax_node1(x_19, x_15, x_52);
lean_inc(x_19);
x_54 = l_Lean_Syntax_node2(x_19, x_26, x_28, x_53);
lean_inc(x_19);
x_55 = l_Lean_Syntax_node2(x_19, x_24, x_46, x_54);
x_56 = l_Lean_Syntax_node2(x_19, x_21, x_22, x_55);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_3);
return x_57;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticRepeat____1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticRepeat____1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_repeat_x27() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("repeat'", 7, 7);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("repeat' ", 8, 8);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_unbox(x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_12);
x_13 = lean_mk_string_unchecked("tacticSeq", 9, 9);
x_14 = l_Lean_Name_mkStr1(x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_16, 0, x_8);
lean_ctor_set(x_16, 1, x_11);
lean_ctor_set(x_16, 2, x_15);
x_17 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_17, 0, x_5);
lean_ctor_set(x_17, 1, x_6);
lean_ctor_set(x_17, 2, x_16);
return x_17;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_repeat1_x27() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("repeat1'", 8, 8);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("repeat1' ", 9, 9);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_unbox(x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_12);
x_13 = lean_mk_string_unchecked("tacticSeq", 9, 9);
x_14 = l_Lean_Name_mkStr1(x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_16, 0, x_8);
lean_ctor_set(x_16, 1, x_11);
lean_ctor_set(x_16, 2, x_15);
x_17 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_17, 0, x_5);
lean_ctor_set(x_17, 1, x_6);
lean_ctor_set(x_17, 2, x_16);
return x_17;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticTrivial() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("tacticTrivial", 13, 13);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1024u);
x_7 = lean_mk_string_unchecked("trivial", 7, 7);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_9, 0, x_7);
x_10 = lean_unbox(x_8);
lean_ctor_set_uint8(x_9, sizeof(void*)*1, x_10);
x_11 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_6);
lean_ctor_set(x_11, 2, x_9);
return x_11;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_classical() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("classical", 9, 9);
lean_inc(x_4);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_10, 0, x_4);
x_11 = lean_unbox(x_9);
lean_ctor_set_uint8(x_10, sizeof(void*)*1, x_11);
x_12 = lean_mk_string_unchecked("ppDedent", 8, 8);
x_13 = l_Lean_Name_mkStr1(x_12);
x_14 = lean_mk_string_unchecked("tacticSeq", 9, 9);
x_15 = l_Lean_Name_mkStr1(x_14);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_13);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_18, 0, x_8);
lean_ctor_set(x_18, 1, x_10);
lean_ctor_set(x_18, 2, x_17);
x_19 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_19, 0, x_5);
lean_ctor_set(x_19, 1, x_6);
lean_ctor_set(x_19, 2, x_18);
return x_19;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_split() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("split", 5, 5);
lean_inc(x_4);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_10, 0, x_4);
x_11 = lean_unbox(x_9);
lean_ctor_set_uint8(x_10, sizeof(void*)*1, x_11);
x_12 = lean_mk_string_unchecked("optional", 8, 8);
x_13 = l_Lean_Name_mkStr1(x_12);
x_14 = lean_mk_string_unchecked("ppSpace", 7, 7);
x_15 = l_Lean_Name_mkStr1(x_14);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_mk_string_unchecked("colGt", 5, 5);
x_18 = l_Lean_Name_mkStr1(x_17);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
lean_inc(x_8);
x_20 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_20, 0, x_8);
lean_ctor_set(x_20, 1, x_16);
lean_ctor_set(x_20, 2, x_19);
x_21 = lean_mk_string_unchecked("term", 4, 4);
x_22 = l_Lean_Name_mkStr1(x_21);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
lean_inc(x_8);
x_25 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_25, 0, x_8);
lean_ctor_set(x_25, 1, x_20);
lean_ctor_set(x_25, 2, x_24);
lean_inc(x_13);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_13);
lean_ctor_set(x_26, 1, x_25);
lean_inc(x_8);
x_27 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_27, 0, x_8);
lean_ctor_set(x_27, 1, x_10);
lean_ctor_set(x_27, 2, x_26);
x_28 = l_Lean_Parser_Tactic_location;
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_13);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_30, 0, x_8);
lean_ctor_set(x_30, 1, x_27);
lean_ctor_set(x_30, 2, x_29);
x_31 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_31, 0, x_5);
lean_ctor_set(x_31, 1, x_6);
lean_ctor_set(x_31, 2, x_30);
return x_31;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_dbgTrace() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("dbgTrace", 8, 8);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("dbg_trace ", 10, 10);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_unbox(x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_12);
x_13 = lean_mk_string_unchecked("str", 3, 3);
x_14 = l_Lean_Name_mkStr1(x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_16, 0, x_8);
lean_ctor_set(x_16, 1, x_11);
lean_ctor_set(x_16, 2, x_15);
x_17 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_17, 0, x_5);
lean_ctor_set(x_17, 1, x_6);
lean_ctor_set(x_17, 2, x_16);
return x_17;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticStop__() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("tacticStop_", 11, 11);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("stop", 4, 4);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_unbox(x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_12);
x_13 = lean_mk_string_unchecked("group", 5, 5);
x_14 = l_Lean_Name_mkStr1(x_13);
x_15 = lean_mk_string_unchecked("tacticSeq", 9, 9);
x_16 = l_Lean_Name_mkStr1(x_15);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_14);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_19, 0, x_8);
lean_ctor_set(x_19, 1, x_11);
lean_ctor_set(x_19, 2, x_18);
x_20 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_20, 0, x_5);
lean_ctor_set(x_20, 1, x_6);
lean_ctor_set(x_20, 2, x_19);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticStop____1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Tactic", 6, 6);
x_7 = lean_mk_string_unchecked("tacticStop_", 11, 11);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_8 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_7);
x_9 = l_Lean_Syntax_isOfKind(x_1, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_10 = lean_box(1);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_12 = lean_mk_string_unchecked("tacticSeq", 9, 9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_13 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_12);
x_14 = lean_ctor_get(x_2, 5);
x_15 = lean_box(0);
x_16 = lean_unbox(x_15);
x_17 = l_Lean_SourceInfo_fromRef(x_14, x_16);
x_18 = lean_mk_string_unchecked("tacticRepeat_", 13, 13);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_19 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_18);
x_20 = lean_mk_string_unchecked("repeat", 6, 6);
lean_inc(x_17);
x_21 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_21, 0, x_17);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_mk_string_unchecked("tacticSeq1Indented", 18, 18);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_23 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_22);
x_24 = lean_mk_string_unchecked("null", 4, 4);
x_25 = l_Lean_Name_mkStr1(x_24);
x_26 = lean_mk_string_unchecked("tacticSorry", 11, 11);
x_27 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_26);
x_28 = lean_mk_string_unchecked("sorry", 5, 5);
lean_inc(x_17);
x_29 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_29, 0, x_17);
lean_ctor_set(x_29, 1, x_28);
lean_inc(x_17);
x_30 = l_Lean_Syntax_node1(x_17, x_27, x_29);
lean_inc(x_17);
x_31 = l_Lean_Syntax_node1(x_17, x_25, x_30);
lean_inc(x_17);
x_32 = l_Lean_Syntax_node1(x_17, x_23, x_31);
lean_inc(x_17);
x_33 = l_Lean_Syntax_node1(x_17, x_13, x_32);
x_34 = l_Lean_Syntax_node2(x_17, x_19, x_21, x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_3);
return x_35;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticStop____1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticStop____1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_specialize() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("specialize", 10, 10);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("specialize ", 11, 11);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_unbox(x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_12);
x_13 = lean_mk_string_unchecked("term", 4, 4);
x_14 = l_Lean_Name_mkStr1(x_13);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_17, 0, x_8);
lean_ctor_set(x_17, 1, x_11);
lean_ctor_set(x_17, 2, x_16);
x_18 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_18, 0, x_5);
lean_ctor_set(x_18, 1, x_6);
lean_ctor_set(x_18, 2, x_17);
return x_18;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticUnhygienic__() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("tacticUnhygienic_", 17, 17);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("unhygienic ", 11, 11);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_unbox(x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_12);
x_13 = lean_mk_string_unchecked("tacticSeq", 9, 9);
x_14 = l_Lean_Name_mkStr1(x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_16, 0, x_8);
lean_ctor_set(x_16, 1, x_11);
lean_ctor_set(x_16, 2, x_15);
x_17 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_17, 0, x_5);
lean_ctor_set(x_17, 1, x_6);
lean_ctor_set(x_17, 2, x_16);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticUnhygienic____1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Tactic", 6, 6);
x_7 = lean_mk_string_unchecked("tacticUnhygienic_", 17, 17);
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = l_Lean_Syntax_getArg(x_1, x_12);
lean_dec(x_1);
x_14 = lean_ctor_get(x_2, 5);
lean_inc(x_14);
x_15 = lean_box(0);
x_16 = lean_unbox(x_15);
x_17 = l_Lean_SourceInfo_fromRef(x_14, x_16);
lean_dec(x_14);
x_18 = lean_ctor_get(x_2, 2);
lean_inc(x_18);
x_19 = lean_ctor_get(x_2, 1);
lean_inc(x_19);
lean_dec(x_2);
x_20 = lean_mk_string_unchecked("tactic", 6, 6);
x_21 = lean_mk_string_unchecked("set_option", 10, 10);
lean_inc(x_21);
x_22 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_21);
lean_inc(x_17);
x_23 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_23, 0, x_17);
lean_ctor_set(x_23, 1, x_21);
x_24 = lean_mk_string_unchecked("tactic.hygienic", 15, 15);
x_25 = l_String_toSubstring_x27(x_24);
x_26 = lean_mk_string_unchecked("hygienic", 8, 8);
x_27 = l_Lean_Name_mkStr2(x_20, x_26);
x_28 = l_Lean_addMacroScope(x_19, x_27, x_18);
x_29 = lean_box(0);
lean_inc(x_17);
x_30 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_30, 0, x_17);
lean_ctor_set(x_30, 1, x_25);
lean_ctor_set(x_30, 2, x_28);
lean_ctor_set(x_30, 3, x_29);
x_31 = lean_mk_string_unchecked("null", 4, 4);
x_32 = l_Lean_Name_mkStr1(x_31);
x_33 = l_Array_mkArray0(lean_box(0));
lean_inc(x_17);
x_34 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_34, 0, x_17);
lean_ctor_set(x_34, 1, x_32);
lean_ctor_set(x_34, 2, x_33);
x_35 = lean_mk_string_unchecked("false", 5, 5);
lean_inc(x_17);
x_36 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_36, 0, x_17);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_mk_string_unchecked("in", 2, 2);
lean_inc(x_17);
x_38 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_38, 0, x_17);
lean_ctor_set(x_38, 1, x_37);
x_39 = l_Lean_Syntax_node6(x_17, x_22, x_23, x_30, x_34, x_36, x_38, x_13);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_3);
return x_40;
}
}
}
static lean_object* _init_l_Lean_Parser_Tactic_sleep() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("sleep", 5, 5);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("sleep ", 6, 6);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_unbox(x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_12);
x_13 = lean_mk_string_unchecked("num", 3, 3);
x_14 = l_Lean_Name_mkStr1(x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_16, 0, x_8);
lean_ctor_set(x_16, 1, x_11);
lean_ctor_set(x_16, 2, x_15);
x_17 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_17, 0, x_5);
lean_ctor_set(x_17, 1, x_6);
lean_ctor_set(x_17, 2, x_16);
return x_17;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticExists___x2c_x2c() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("tacticExists_,,", 15, 15);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("exists ", 7, 7);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_unbox(x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_12);
x_13 = lean_mk_string_unchecked("term", 4, 4);
x_14 = l_Lean_Name_mkStr1(x_13);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_mk_string_unchecked(",", 1, 1);
x_18 = lean_mk_string_unchecked(", ", 2, 2);
x_19 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_alloc_ctor(11, 3, 1);
lean_ctor_set(x_20, 0, x_16);
lean_ctor_set(x_20, 1, x_17);
lean_ctor_set(x_20, 2, x_19);
x_21 = lean_unbox(x_10);
lean_ctor_set_uint8(x_20, sizeof(void*)*3, x_21);
x_22 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_22, 0, x_8);
lean_ctor_set(x_22, 1, x_11);
lean_ctor_set(x_22, 2, x_20);
x_23 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_23, 0, x_5);
lean_ctor_set(x_23, 1, x_6);
lean_ctor_set(x_23, 2, x_22);
return x_23;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticExists___x2c_x2c__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Tactic", 6, 6);
x_7 = lean_mk_string_unchecked("tacticExists_,,", 15, 15);
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
x_10 = lean_box(1);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = l_Lean_Syntax_getArg(x_1, x_12);
lean_dec(x_1);
x_14 = lean_mk_string_unchecked(",", 1, 1);
x_15 = l_Lean_Syntax_getArgs(x_13);
lean_dec(x_13);
x_16 = lean_ctor_get(x_2, 5);
x_17 = lean_box(0);
x_18 = lean_unbox(x_17);
x_19 = l_Lean_SourceInfo_fromRef(x_16, x_18);
x_20 = lean_mk_string_unchecked("paren", 5, 5);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_21 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_20);
x_22 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_19);
x_23 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_23, 0, x_19);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_mk_string_unchecked("tacticSeq", 9, 9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_25 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_24);
x_26 = lean_mk_string_unchecked("tacticSeq1Indented", 18, 18);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_27 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_26);
x_28 = lean_mk_string_unchecked("null", 4, 4);
x_29 = l_Lean_Name_mkStr1(x_28);
x_30 = lean_mk_string_unchecked("refine", 6, 6);
lean_inc(x_30);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_31 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_30);
lean_inc(x_19);
x_32 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_32, 0, x_19);
lean_ctor_set(x_32, 1, x_30);
x_33 = lean_mk_string_unchecked("Term", 4, 4);
x_34 = lean_mk_string_unchecked("anonymousCtor", 13, 13);
lean_inc(x_33);
lean_inc(x_5);
lean_inc(x_4);
x_35 = l_Lean_Name_mkStr4(x_4, x_5, x_33, x_34);
x_36 = lean_mk_string_unchecked("⟨", 3, 1);
lean_inc(x_19);
x_37 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_37, 0, x_19);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_Array_mkArray0(lean_box(0));
x_39 = l_Array_appendCore___redArg(x_38, x_15);
lean_dec(x_15);
lean_inc(x_19);
x_40 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_40, 0, x_19);
lean_ctor_set(x_40, 1, x_14);
x_41 = lean_array_push(x_39, x_40);
x_42 = lean_mk_string_unchecked("syntheticHole", 13, 13);
lean_inc(x_5);
lean_inc(x_4);
x_43 = l_Lean_Name_mkStr4(x_4, x_5, x_33, x_42);
x_44 = lean_mk_string_unchecked("\?", 1, 1);
lean_inc(x_19);
x_45 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_45, 0, x_19);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_mk_string_unchecked("_", 1, 1);
lean_inc(x_19);
x_47 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_47, 0, x_19);
lean_ctor_set(x_47, 1, x_46);
lean_inc(x_19);
x_48 = l_Lean_Syntax_node2(x_19, x_43, x_45, x_47);
x_49 = lean_array_push(x_41, x_48);
lean_inc(x_29);
lean_inc(x_19);
x_50 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_50, 0, x_19);
lean_ctor_set(x_50, 1, x_29);
lean_ctor_set(x_50, 2, x_49);
x_51 = lean_mk_string_unchecked("⟩", 3, 1);
lean_inc(x_19);
x_52 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_52, 0, x_19);
lean_ctor_set(x_52, 1, x_51);
lean_inc(x_19);
x_53 = l_Lean_Syntax_node3(x_19, x_35, x_37, x_50, x_52);
lean_inc(x_19);
x_54 = l_Lean_Syntax_node2(x_19, x_31, x_32, x_53);
x_55 = lean_mk_string_unchecked(";", 1, 1);
lean_inc(x_19);
x_56 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_56, 0, x_19);
lean_ctor_set(x_56, 1, x_55);
x_57 = lean_mk_string_unchecked("tacticTry_", 10, 10);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_58 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_57);
x_59 = lean_mk_string_unchecked("try", 3, 3);
lean_inc(x_19);
x_60 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_60, 0, x_19);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_mk_string_unchecked("tacticTrivial", 13, 13);
x_62 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_61);
x_63 = lean_mk_string_unchecked("trivial", 7, 7);
lean_inc(x_19);
x_64 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_64, 0, x_19);
lean_ctor_set(x_64, 1, x_63);
lean_inc(x_19);
x_65 = l_Lean_Syntax_node1(x_19, x_62, x_64);
lean_inc(x_29);
lean_inc(x_19);
x_66 = l_Lean_Syntax_node1(x_19, x_29, x_65);
lean_inc(x_27);
lean_inc(x_19);
x_67 = l_Lean_Syntax_node1(x_19, x_27, x_66);
lean_inc(x_25);
lean_inc(x_19);
x_68 = l_Lean_Syntax_node1(x_19, x_25, x_67);
lean_inc(x_19);
x_69 = l_Lean_Syntax_node2(x_19, x_58, x_60, x_68);
lean_inc(x_19);
x_70 = l_Lean_Syntax_node3(x_19, x_29, x_54, x_56, x_69);
lean_inc(x_19);
x_71 = l_Lean_Syntax_node1(x_19, x_27, x_70);
lean_inc(x_19);
x_72 = l_Lean_Syntax_node1(x_19, x_25, x_71);
x_73 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_19);
x_74 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_74, 0, x_19);
lean_ctor_set(x_74, 1, x_73);
x_75 = l_Lean_Syntax_node3(x_19, x_21, x_23, x_72, x_74);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_3);
return x_76;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticExists___x2c_x2c__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticExists___x2c_x2c__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_congr() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("congr", 5, 5);
lean_inc(x_4);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_10, 0, x_4);
x_11 = lean_unbox(x_9);
lean_ctor_set_uint8(x_10, sizeof(void*)*1, x_11);
x_12 = lean_mk_string_unchecked("optional", 8, 8);
x_13 = l_Lean_Name_mkStr1(x_12);
x_14 = lean_mk_string_unchecked("ppSpace", 7, 7);
x_15 = l_Lean_Name_mkStr1(x_14);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_mk_string_unchecked("num", 3, 3);
x_18 = l_Lean_Name_mkStr1(x_17);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
lean_inc(x_8);
x_20 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_20, 0, x_8);
lean_ctor_set(x_20, 1, x_16);
lean_ctor_set(x_20, 2, x_19);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_13);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_22, 0, x_8);
lean_ctor_set(x_22, 1, x_10);
lean_ctor_set(x_22, 2, x_21);
x_23 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_23, 0, x_5);
lean_ctor_set(x_23, 1, x_6);
lean_ctor_set(x_23, 2, x_22);
return x_23;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacDepIfThenElse() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("tacDepIfThenElse", 16, 16);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("ppRealGroup", 11, 11);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("andthen", 7, 7);
x_10 = l_Lean_Name_mkStr1(x_9);
x_11 = lean_mk_string_unchecked("ppRealFill", 10, 10);
x_12 = l_Lean_Name_mkStr1(x_11);
x_13 = lean_mk_string_unchecked("ppIndent", 8, 8);
x_14 = l_Lean_Name_mkStr1(x_13);
x_15 = lean_mk_string_unchecked("if ", 3, 3);
x_16 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = l_Lean_binderIdent;
lean_inc(x_10);
x_18 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_18, 0, x_10);
lean_ctor_set(x_18, 1, x_16);
lean_ctor_set(x_18, 2, x_17);
x_19 = lean_mk_string_unchecked(" : ", 3, 3);
x_20 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_20, 0, x_19);
lean_inc(x_10);
x_21 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_21, 0, x_10);
lean_ctor_set(x_21, 1, x_18);
lean_ctor_set(x_21, 2, x_20);
x_22 = lean_mk_string_unchecked("term", 4, 4);
x_23 = l_Lean_Name_mkStr1(x_22);
x_24 = lean_unsigned_to_nat(0u);
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
lean_inc(x_10);
x_26 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_26, 0, x_10);
lean_ctor_set(x_26, 1, x_21);
lean_ctor_set(x_26, 2, x_25);
x_27 = lean_mk_string_unchecked(" then", 5, 5);
x_28 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_28, 0, x_27);
lean_inc(x_10);
x_29 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_29, 0, x_10);
lean_ctor_set(x_29, 1, x_26);
lean_ctor_set(x_29, 2, x_28);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_14);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_mk_string_unchecked("ppSpace", 7, 7);
x_32 = l_Lean_Name_mkStr1(x_31);
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_32);
lean_inc(x_33);
lean_inc(x_10);
x_34 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_34, 0, x_10);
lean_ctor_set(x_34, 1, x_30);
lean_ctor_set(x_34, 2, x_33);
x_35 = lean_mk_string_unchecked("matchRhsTacticSeq", 17, 17);
x_36 = l_Lean_Name_mkStr1(x_35);
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_36);
lean_inc(x_37);
lean_inc(x_10);
x_38 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_38, 0, x_10);
lean_ctor_set(x_38, 1, x_34);
lean_ctor_set(x_38, 2, x_37);
lean_inc(x_12);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_12);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_mk_string_unchecked("ppDedent", 8, 8);
x_41 = l_Lean_Name_mkStr1(x_40);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_33);
lean_inc(x_10);
x_43 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_43, 0, x_10);
lean_ctor_set(x_43, 1, x_39);
lean_ctor_set(x_43, 2, x_42);
x_44 = lean_mk_string_unchecked("else ", 5, 5);
x_45 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_45, 0, x_44);
lean_inc(x_10);
x_46 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_46, 0, x_10);
lean_ctor_set(x_46, 1, x_45);
lean_ctor_set(x_46, 2, x_37);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_12);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_48, 0, x_10);
lean_ctor_set(x_48, 1, x_43);
lean_ctor_set(x_48, 2, x_47);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_8);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_50, 0, x_5);
lean_ctor_set(x_50, 1, x_6);
lean_ctor_set(x_50, 2, x_49);
return x_50;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacIfThenElse() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("tacIfThenElse", 13, 13);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("ppRealGroup", 11, 11);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("andthen", 7, 7);
x_10 = l_Lean_Name_mkStr1(x_9);
x_11 = lean_mk_string_unchecked("ppRealFill", 10, 10);
x_12 = l_Lean_Name_mkStr1(x_11);
x_13 = lean_mk_string_unchecked("ppIndent", 8, 8);
x_14 = l_Lean_Name_mkStr1(x_13);
x_15 = lean_mk_string_unchecked("if ", 3, 3);
x_16 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_mk_string_unchecked("term", 4, 4);
x_18 = l_Lean_Name_mkStr1(x_17);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
lean_inc(x_10);
x_21 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_21, 0, x_10);
lean_ctor_set(x_21, 1, x_16);
lean_ctor_set(x_21, 2, x_20);
x_22 = lean_mk_string_unchecked(" then", 5, 5);
x_23 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_23, 0, x_22);
lean_inc(x_10);
x_24 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_24, 0, x_10);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 2, x_23);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_14);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_mk_string_unchecked("ppSpace", 7, 7);
x_27 = l_Lean_Name_mkStr1(x_26);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
lean_inc(x_28);
lean_inc(x_10);
x_29 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_29, 0, x_10);
lean_ctor_set(x_29, 1, x_25);
lean_ctor_set(x_29, 2, x_28);
x_30 = lean_mk_string_unchecked("matchRhsTacticSeq", 17, 17);
x_31 = l_Lean_Name_mkStr1(x_30);
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_31);
lean_inc(x_32);
lean_inc(x_10);
x_33 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_33, 0, x_10);
lean_ctor_set(x_33, 1, x_29);
lean_ctor_set(x_33, 2, x_32);
lean_inc(x_12);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_12);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_mk_string_unchecked("ppDedent", 8, 8);
x_36 = l_Lean_Name_mkStr1(x_35);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_28);
lean_inc(x_10);
x_38 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_38, 0, x_10);
lean_ctor_set(x_38, 1, x_34);
lean_ctor_set(x_38, 2, x_37);
x_39 = lean_mk_string_unchecked("else ", 5, 5);
x_40 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_40, 0, x_39);
lean_inc(x_10);
x_41 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_41, 0, x_10);
lean_ctor_set(x_41, 1, x_40);
lean_ctor_set(x_41, 2, x_32);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_12);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_43, 0, x_10);
lean_ctor_set(x_43, 1, x_38);
lean_ctor_set(x_43, 2, x_42);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_8);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_45, 0, x_5);
lean_ctor_set(x_45, 1, x_6);
lean_ctor_set(x_45, 2, x_44);
return x_45;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticNofun() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("tacticNofun", 11, 11);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1024u);
x_7 = lean_mk_string_unchecked("nofun", 5, 5);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_9, 0, x_7);
x_10 = lean_unbox(x_8);
lean_ctor_set_uint8(x_9, sizeof(void*)*1, x_10);
x_11 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_6);
lean_ctor_set(x_11, 2, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticNofun__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Tactic", 6, 6);
x_7 = lean_mk_string_unchecked("tacticNofun", 11, 11);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_8 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_7);
x_9 = l_Lean_Syntax_isOfKind(x_1, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_10 = lean_box(1);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_12 = lean_ctor_get(x_2, 5);
x_13 = lean_box(0);
x_14 = lean_unbox(x_13);
x_15 = l_Lean_SourceInfo_fromRef(x_12, x_14);
x_16 = lean_mk_string_unchecked("exact", 5, 5);
lean_inc(x_16);
lean_inc(x_5);
lean_inc(x_4);
x_17 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_16);
lean_inc(x_15);
x_18 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_16);
x_19 = lean_mk_string_unchecked("Term", 4, 4);
x_20 = lean_mk_string_unchecked("nofun", 5, 5);
lean_inc(x_20);
x_21 = l_Lean_Name_mkStr4(x_4, x_5, x_19, x_20);
lean_inc(x_15);
x_22 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_22, 0, x_15);
lean_ctor_set(x_22, 1, x_20);
lean_inc(x_15);
x_23 = l_Lean_Syntax_node1(x_15, x_21, x_22);
x_24 = l_Lean_Syntax_node2(x_15, x_17, x_18, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_3);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticNofun__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticNofun__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticNomatch___x2c_x2c() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("tacticNomatch_,,", 16, 16);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("nomatch ", 8, 8);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_unbox(x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_12);
x_13 = lean_mk_string_unchecked("term", 4, 4);
x_14 = l_Lean_Name_mkStr1(x_13);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_mk_string_unchecked(",", 1, 1);
x_18 = lean_mk_string_unchecked(", ", 2, 2);
x_19 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_alloc_ctor(11, 3, 1);
lean_ctor_set(x_20, 0, x_16);
lean_ctor_set(x_20, 1, x_17);
lean_ctor_set(x_20, 2, x_19);
x_21 = lean_unbox(x_10);
lean_ctor_set_uint8(x_20, sizeof(void*)*3, x_21);
x_22 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_22, 0, x_8);
lean_ctor_set(x_22, 1, x_11);
lean_ctor_set(x_22, 2, x_20);
x_23 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_23, 0, x_5);
lean_ctor_set(x_23, 1, x_6);
lean_ctor_set(x_23, 2, x_22);
return x_23;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticNomatch___x2c_x2c__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Tactic", 6, 6);
x_7 = lean_mk_string_unchecked("tacticNomatch_,,", 16, 16);
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
x_10 = lean_box(1);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = l_Lean_Syntax_getArg(x_1, x_12);
lean_dec(x_1);
x_14 = l_Lean_Syntax_getArgs(x_13);
lean_dec(x_13);
x_15 = lean_ctor_get(x_2, 5);
x_16 = lean_box(0);
x_17 = lean_unbox(x_16);
x_18 = l_Lean_SourceInfo_fromRef(x_15, x_17);
x_19 = lean_mk_string_unchecked("exact", 5, 5);
lean_inc(x_19);
lean_inc(x_5);
lean_inc(x_4);
x_20 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_19);
lean_inc(x_18);
x_21 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_mk_string_unchecked("Term", 4, 4);
x_23 = lean_mk_string_unchecked("nomatch", 7, 7);
lean_inc(x_23);
x_24 = l_Lean_Name_mkStr4(x_4, x_5, x_22, x_23);
lean_inc(x_18);
x_25 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_25, 0, x_18);
lean_ctor_set(x_25, 1, x_23);
x_26 = lean_mk_string_unchecked("null", 4, 4);
x_27 = l_Lean_Name_mkStr1(x_26);
x_28 = l_Array_mkArray0(lean_box(0));
x_29 = l_Array_appendCore___redArg(x_28, x_14);
lean_dec(x_14);
lean_inc(x_18);
x_30 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_30, 0, x_18);
lean_ctor_set(x_30, 1, x_27);
lean_ctor_set(x_30, 2, x_29);
lean_inc(x_18);
x_31 = l_Lean_Syntax_node2(x_18, x_24, x_25, x_30);
x_32 = l_Lean_Syntax_node2(x_18, x_20, x_21, x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_3);
return x_33;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticNomatch___x2c_x2c__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticNomatch___x2c_x2c__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_replace() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("replace", 7, 7);
lean_inc(x_4);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_10, 0, x_4);
x_11 = lean_unbox(x_9);
lean_ctor_set_uint8(x_10, sizeof(void*)*1, x_11);
x_12 = lean_mk_string_unchecked("haveDecl", 8, 8);
x_13 = l_Lean_Name_mkStr1(x_12);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_10);
lean_ctor_set(x_15, 2, x_14);
x_16 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_16, 0, x_5);
lean_ctor_set(x_16, 1, x_6);
lean_ctor_set(x_16, 2, x_15);
return x_16;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticAnd__intros() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("tacticAnd_intros", 16, 16);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1024u);
x_7 = lean_mk_string_unchecked("and_intros", 10, 10);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_9, 0, x_7);
x_10 = lean_unbox(x_8);
lean_ctor_set_uint8(x_9, sizeof(void*)*1, x_10);
x_11 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_6);
lean_ctor_set(x_11, 2, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticAnd__intros__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Tactic", 6, 6);
x_7 = lean_mk_string_unchecked("tacticAnd_intros", 16, 16);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_8 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_7);
x_9 = l_Lean_Syntax_isOfKind(x_1, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_10 = lean_box(1);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_12 = lean_ctor_get(x_2, 5);
lean_inc(x_12);
x_13 = lean_box(0);
x_14 = lean_unbox(x_13);
x_15 = l_Lean_SourceInfo_fromRef(x_12, x_14);
lean_dec(x_12);
x_16 = lean_ctor_get(x_2, 2);
lean_inc(x_16);
x_17 = lean_ctor_get(x_2, 1);
lean_inc(x_17);
lean_dec(x_2);
x_18 = lean_mk_string_unchecked("repeat'", 7, 7);
lean_inc(x_18);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_19 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_18);
lean_inc(x_15);
x_20 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_20, 0, x_15);
lean_ctor_set(x_20, 1, x_18);
x_21 = lean_mk_string_unchecked("tacticSeq", 9, 9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_22 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_21);
x_23 = lean_mk_string_unchecked("tacticSeq1Indented", 18, 18);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_24 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_23);
x_25 = lean_mk_string_unchecked("null", 4, 4);
x_26 = l_Lean_Name_mkStr1(x_25);
x_27 = lean_mk_string_unchecked("refine", 6, 6);
lean_inc(x_27);
lean_inc(x_5);
lean_inc(x_4);
x_28 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_27);
lean_inc(x_15);
x_29 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_29, 0, x_15);
lean_ctor_set(x_29, 1, x_27);
x_30 = lean_mk_string_unchecked("Term", 4, 4);
x_31 = lean_mk_string_unchecked("app", 3, 3);
lean_inc(x_30);
lean_inc(x_5);
lean_inc(x_4);
x_32 = l_Lean_Name_mkStr4(x_4, x_5, x_30, x_31);
x_33 = lean_mk_string_unchecked("And.intro", 9, 9);
x_34 = l_String_toSubstring_x27(x_33);
x_35 = lean_mk_string_unchecked("And", 3, 3);
x_36 = lean_mk_string_unchecked("intro", 5, 5);
x_37 = l_Lean_Name_mkStr2(x_35, x_36);
lean_inc(x_37);
x_38 = l_Lean_addMacroScope(x_17, x_37, x_16);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
lean_inc(x_15);
x_43 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_43, 0, x_15);
lean_ctor_set(x_43, 1, x_34);
lean_ctor_set(x_43, 2, x_38);
lean_ctor_set(x_43, 3, x_42);
x_44 = lean_mk_string_unchecked("syntheticHole", 13, 13);
x_45 = l_Lean_Name_mkStr4(x_4, x_5, x_30, x_44);
x_46 = lean_mk_string_unchecked("\?", 1, 1);
lean_inc(x_15);
x_47 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_47, 0, x_15);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_mk_string_unchecked("_", 1, 1);
lean_inc(x_15);
x_49 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_49, 0, x_15);
lean_ctor_set(x_49, 1, x_48);
lean_inc(x_15);
x_50 = l_Lean_Syntax_node2(x_15, x_45, x_47, x_49);
lean_inc(x_50);
lean_inc(x_26);
lean_inc(x_15);
x_51 = l_Lean_Syntax_node2(x_15, x_26, x_50, x_50);
lean_inc(x_15);
x_52 = l_Lean_Syntax_node2(x_15, x_32, x_43, x_51);
lean_inc(x_15);
x_53 = l_Lean_Syntax_node2(x_15, x_28, x_29, x_52);
lean_inc(x_15);
x_54 = l_Lean_Syntax_node1(x_15, x_26, x_53);
lean_inc(x_15);
x_55 = l_Lean_Syntax_node1(x_15, x_24, x_54);
lean_inc(x_15);
x_56 = l_Lean_Syntax_node1(x_15, x_22, x_55);
x_57 = l_Lean_Syntax_node2(x_15, x_19, x_20, x_56);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_3);
return x_58;
}
}
}
static lean_object* _init_l_Lean_Parser_Tactic_substEqs() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("substEqs", 8, 8);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1024u);
x_7 = lean_mk_string_unchecked("subst_eqs", 9, 9);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_9, 0, x_7);
x_10 = lean_unbox(x_8);
lean_ctor_set_uint8(x_9, sizeof(void*)*1, x_10);
x_11 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_6);
lean_ctor_set(x_11, 2, x_9);
return x_11;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_runTac() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("runTac", 6, 6);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("run_tac ", 8, 8);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_unbox(x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_12);
x_13 = lean_mk_string_unchecked("doSeq", 5, 5);
x_14 = l_Lean_Name_mkStr1(x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_16, 0, x_8);
lean_ctor_set(x_16, 1, x_11);
lean_ctor_set(x_16, 2, x_15);
x_17 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_17, 0, x_5);
lean_ctor_set(x_17, 1, x_6);
lean_ctor_set(x_17, 2, x_16);
return x_17;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticHaveI__() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("tacticHaveI_", 12, 12);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("haveI", 5, 5);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_unbox(x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_12);
x_13 = lean_mk_string_unchecked("haveDecl", 8, 8);
x_14 = l_Lean_Name_mkStr1(x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_16, 0, x_8);
lean_ctor_set(x_16, 1, x_11);
lean_ctor_set(x_16, 2, x_15);
x_17 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_17, 0, x_5);
lean_ctor_set(x_17, 1, x_6);
lean_ctor_set(x_17, 2, x_16);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticHaveI____1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Tactic", 6, 6);
x_7 = lean_mk_string_unchecked("tacticHaveI_", 12, 12);
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
x_10 = lean_box(1);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = l_Lean_Syntax_getArg(x_1, x_12);
lean_dec(x_1);
x_14 = lean_mk_string_unchecked("Term", 4, 4);
x_15 = lean_ctor_get(x_2, 5);
x_16 = lean_box(0);
x_17 = lean_unbox(x_16);
x_18 = l_Lean_SourceInfo_fromRef(x_15, x_17);
x_19 = lean_mk_string_unchecked("tacticRefine_lift_", 18, 18);
lean_inc(x_5);
lean_inc(x_4);
x_20 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_19);
x_21 = lean_mk_string_unchecked("refine_lift", 11, 11);
lean_inc(x_18);
x_22 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_22, 0, x_18);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_mk_string_unchecked("haveI", 5, 5);
lean_inc(x_23);
lean_inc(x_14);
lean_inc(x_5);
lean_inc(x_4);
x_24 = l_Lean_Name_mkStr4(x_4, x_5, x_14, x_23);
lean_inc(x_18);
x_25 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_25, 0, x_18);
lean_ctor_set(x_25, 1, x_23);
x_26 = lean_mk_string_unchecked(";", 1, 1);
lean_inc(x_18);
x_27 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_27, 0, x_18);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_mk_string_unchecked("syntheticHole", 13, 13);
x_29 = l_Lean_Name_mkStr4(x_4, x_5, x_14, x_28);
x_30 = lean_mk_string_unchecked("\?", 1, 1);
lean_inc(x_18);
x_31 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_31, 0, x_18);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_mk_string_unchecked("_", 1, 1);
lean_inc(x_18);
x_33 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_33, 0, x_18);
lean_ctor_set(x_33, 1, x_32);
lean_inc(x_18);
x_34 = l_Lean_Syntax_node2(x_18, x_29, x_31, x_33);
lean_inc(x_18);
x_35 = l_Lean_Syntax_node4(x_18, x_24, x_25, x_13, x_27, x_34);
x_36 = l_Lean_Syntax_node2(x_18, x_20, x_22, x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_3);
return x_37;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticHaveI____1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticHaveI____1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticLetI__() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("tacticLetI_", 11, 11);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("letI", 4, 4);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_unbox(x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_12);
x_13 = lean_mk_string_unchecked("haveDecl", 8, 8);
x_14 = l_Lean_Name_mkStr1(x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_16, 0, x_8);
lean_ctor_set(x_16, 1, x_11);
lean_ctor_set(x_16, 2, x_15);
x_17 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_17, 0, x_5);
lean_ctor_set(x_17, 1, x_6);
lean_ctor_set(x_17, 2, x_16);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticLetI____1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Tactic", 6, 6);
x_7 = lean_mk_string_unchecked("tacticLetI_", 11, 11);
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
x_10 = lean_box(1);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = l_Lean_Syntax_getArg(x_1, x_12);
lean_dec(x_1);
x_14 = lean_mk_string_unchecked("Term", 4, 4);
x_15 = lean_ctor_get(x_2, 5);
x_16 = lean_box(0);
x_17 = lean_unbox(x_16);
x_18 = l_Lean_SourceInfo_fromRef(x_15, x_17);
x_19 = lean_mk_string_unchecked("tacticRefine_lift_", 18, 18);
lean_inc(x_5);
lean_inc(x_4);
x_20 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_19);
x_21 = lean_mk_string_unchecked("refine_lift", 11, 11);
lean_inc(x_18);
x_22 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_22, 0, x_18);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_mk_string_unchecked("letI", 4, 4);
lean_inc(x_23);
lean_inc(x_14);
lean_inc(x_5);
lean_inc(x_4);
x_24 = l_Lean_Name_mkStr4(x_4, x_5, x_14, x_23);
lean_inc(x_18);
x_25 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_25, 0, x_18);
lean_ctor_set(x_25, 1, x_23);
x_26 = lean_mk_string_unchecked(";", 1, 1);
lean_inc(x_18);
x_27 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_27, 0, x_18);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_mk_string_unchecked("syntheticHole", 13, 13);
x_29 = l_Lean_Name_mkStr4(x_4, x_5, x_14, x_28);
x_30 = lean_mk_string_unchecked("\?", 1, 1);
lean_inc(x_18);
x_31 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_31, 0, x_18);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_mk_string_unchecked("_", 1, 1);
lean_inc(x_18);
x_33 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_33, 0, x_18);
lean_ctor_set(x_33, 1, x_32);
lean_inc(x_18);
x_34 = l_Lean_Syntax_node2(x_18, x_29, x_31, x_33);
lean_inc(x_18);
x_35 = l_Lean_Syntax_node4(x_18, x_24, x_25, x_13, x_27, x_34);
x_36 = l_Lean_Syntax_node2(x_18, x_20, x_22, x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_3);
return x_37;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticLetI____1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticLetI____1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_decide() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("decide", 6, 6);
lean_inc(x_4);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_10, 0, x_4);
x_11 = lean_unbox(x_9);
lean_ctor_set_uint8(x_10, sizeof(void*)*1, x_11);
x_12 = l_Lean_Parser_Tactic_optConfig;
x_13 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_10);
lean_ctor_set(x_13, 2, x_12);
x_14 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_14, 0, x_5);
lean_ctor_set(x_14, 1, x_6);
lean_ctor_set(x_14, 2, x_13);
return x_14;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_nativeDecide() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("nativeDecide", 12, 12);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("native_decide", 13, 13);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_unbox(x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_12);
x_13 = l_Lean_Parser_Tactic_optConfig;
x_14 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_14, 0, x_8);
lean_ctor_set(x_14, 1, x_11);
lean_ctor_set(x_14, 2, x_13);
x_15 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_15, 0, x_5);
lean_ctor_set(x_15, 1, x_6);
lean_ctor_set(x_15, 2, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticTrivial__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Tactic", 6, 6);
x_7 = lean_mk_string_unchecked("tacticTrivial", 13, 13);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_8 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_7);
x_9 = l_Lean_Syntax_isOfKind(x_1, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_10 = lean_box(1);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_2, 5);
x_13 = lean_box(0);
x_14 = lean_unbox(x_13);
x_15 = l_Lean_SourceInfo_fromRef(x_12, x_14);
x_16 = lean_mk_string_unchecked("assumption", 10, 10);
lean_inc(x_16);
x_17 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_16);
lean_inc(x_15);
x_18 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_16);
x_19 = l_Lean_Syntax_node1(x_15, x_17, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_3);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticTrivial__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticTrivial__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticTrivial__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Tactic", 6, 6);
x_7 = lean_mk_string_unchecked("tacticTrivial", 13, 13);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_8 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_7);
x_9 = l_Lean_Syntax_isOfKind(x_1, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_10 = lean_box(1);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_12 = lean_ctor_get(x_2, 5);
x_13 = lean_box(0);
x_14 = lean_unbox(x_13);
x_15 = l_Lean_SourceInfo_fromRef(x_12, x_14);
x_16 = lean_mk_string_unchecked("tacticRfl", 9, 9);
x_17 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_16);
x_18 = lean_mk_string_unchecked("rfl", 3, 3);
lean_inc(x_15);
x_19 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_19, 0, x_15);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_Syntax_node1(x_15, x_17, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_3);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticTrivial__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticTrivial__2(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticTrivial__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Tactic", 6, 6);
x_7 = lean_mk_string_unchecked("tacticTrivial", 13, 13);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_8 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_7);
x_9 = l_Lean_Syntax_isOfKind(x_1, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_10 = lean_box(1);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_2, 5);
x_13 = lean_box(0);
x_14 = lean_unbox(x_13);
x_15 = l_Lean_SourceInfo_fromRef(x_12, x_14);
x_16 = lean_mk_string_unchecked("contradiction", 13, 13);
lean_inc(x_16);
x_17 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_16);
lean_inc(x_15);
x_18 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_16);
x_19 = l_Lean_Syntax_node1(x_15, x_17, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_3);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticTrivial__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticTrivial__3(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticTrivial__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Tactic", 6, 6);
x_7 = lean_mk_string_unchecked("tacticTrivial", 13, 13);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_8 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_7);
x_9 = l_Lean_Syntax_isOfKind(x_1, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_10 = lean_box(1);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_12 = lean_ctor_get(x_2, 5);
x_13 = lean_box(0);
x_14 = lean_unbox(x_13);
x_15 = l_Lean_SourceInfo_fromRef(x_12, x_14);
x_16 = lean_mk_string_unchecked("decide", 6, 6);
lean_inc(x_16);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_17 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_16);
lean_inc(x_15);
x_18 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_16);
x_19 = lean_mk_string_unchecked("optConfig", 9, 9);
x_20 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_19);
x_21 = lean_mk_string_unchecked("null", 4, 4);
x_22 = l_Lean_Name_mkStr1(x_21);
x_23 = l_Array_mkArray0(lean_box(0));
lean_inc(x_15);
x_24 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_24, 0, x_15);
lean_ctor_set(x_24, 1, x_22);
lean_ctor_set(x_24, 2, x_23);
lean_inc(x_15);
x_25 = l_Lean_Syntax_node1(x_15, x_20, x_24);
x_26 = l_Lean_Syntax_node2(x_15, x_17, x_18, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_3);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticTrivial__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticTrivial__4(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticTrivial__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Tactic", 6, 6);
x_7 = lean_mk_string_unchecked("tacticTrivial", 13, 13);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_8 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_7);
x_9 = l_Lean_Syntax_isOfKind(x_1, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_10 = lean_box(1);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_12 = lean_ctor_get(x_2, 5);
lean_inc(x_12);
x_13 = lean_box(0);
x_14 = lean_unbox(x_13);
x_15 = l_Lean_SourceInfo_fromRef(x_12, x_14);
lean_dec(x_12);
x_16 = lean_ctor_get(x_2, 2);
lean_inc(x_16);
x_17 = lean_ctor_get(x_2, 1);
lean_inc(x_17);
lean_dec(x_2);
x_18 = lean_mk_string_unchecked("apply", 5, 5);
lean_inc(x_18);
x_19 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_18);
lean_inc(x_15);
x_20 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_20, 0, x_15);
lean_ctor_set(x_20, 1, x_18);
x_21 = lean_mk_string_unchecked("True.intro", 10, 10);
x_22 = l_String_toSubstring_x27(x_21);
x_23 = lean_mk_string_unchecked("True", 4, 4);
x_24 = lean_mk_string_unchecked("intro", 5, 5);
x_25 = l_Lean_Name_mkStr2(x_23, x_24);
lean_inc(x_25);
x_26 = l_Lean_addMacroScope(x_17, x_25, x_16);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
lean_inc(x_15);
x_31 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_31, 0, x_15);
lean_ctor_set(x_31, 1, x_22);
lean_ctor_set(x_31, 2, x_26);
lean_ctor_set(x_31, 3, x_30);
x_32 = l_Lean_Syntax_node2(x_15, x_19, x_20, x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_3);
return x_33;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticTrivial__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Tactic", 6, 6);
x_7 = lean_mk_string_unchecked("tacticTrivial", 13, 13);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_8 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_7);
x_9 = l_Lean_Syntax_isOfKind(x_1, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_10 = lean_box(1);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_12 = lean_ctor_get(x_2, 5);
lean_inc(x_12);
x_13 = lean_box(0);
x_14 = lean_unbox(x_13);
x_15 = l_Lean_SourceInfo_fromRef(x_12, x_14);
lean_dec(x_12);
x_16 = lean_ctor_get(x_2, 2);
lean_inc(x_16);
x_17 = lean_ctor_get(x_2, 1);
lean_inc(x_17);
lean_dec(x_2);
x_18 = lean_mk_string_unchecked("tactic_<;>_", 11, 11);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_19 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_18);
x_20 = lean_mk_string_unchecked("apply", 5, 5);
lean_inc(x_20);
x_21 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_20);
lean_inc(x_15);
x_22 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_22, 0, x_15);
lean_ctor_set(x_22, 1, x_20);
x_23 = lean_mk_string_unchecked("And.intro", 9, 9);
x_24 = l_String_toSubstring_x27(x_23);
x_25 = lean_mk_string_unchecked("And", 3, 3);
x_26 = lean_mk_string_unchecked("intro", 5, 5);
x_27 = l_Lean_Name_mkStr2(x_25, x_26);
lean_inc(x_27);
x_28 = l_Lean_addMacroScope(x_17, x_27, x_16);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_27);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
lean_inc(x_15);
x_33 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_33, 0, x_15);
lean_ctor_set(x_33, 1, x_24);
lean_ctor_set(x_33, 2, x_28);
lean_ctor_set(x_33, 3, x_32);
lean_inc(x_15);
x_34 = l_Lean_Syntax_node2(x_15, x_21, x_22, x_33);
x_35 = lean_mk_string_unchecked("<;>", 3, 3);
lean_inc(x_15);
x_36 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_36, 0, x_15);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_mk_string_unchecked("trivial", 7, 7);
lean_inc(x_15);
x_38 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_38, 0, x_15);
lean_ctor_set(x_38, 1, x_37);
lean_inc(x_15);
x_39 = l_Lean_Syntax_node1(x_15, x_8, x_38);
x_40 = l_Lean_Syntax_node3(x_15, x_19, x_34, x_36, x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_3);
return x_41;
}
}
}
static lean_object* _init_l_Lean_Parser_Tactic_omega() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("omega", 5, 5);
lean_inc(x_4);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_10, 0, x_4);
x_11 = lean_unbox(x_9);
lean_ctor_set_uint8(x_10, sizeof(void*)*1, x_11);
x_12 = l_Lean_Parser_Tactic_optConfig;
x_13 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_10);
lean_ctor_set(x_13, 2, x_12);
x_14 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_14, 0, x_5);
lean_ctor_set(x_14, 1, x_6);
lean_ctor_set(x_14, 2, x_13);
return x_14;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticBv__omega() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("tacticBv_omega", 14, 14);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1024u);
x_7 = lean_mk_string_unchecked("bv_omega", 8, 8);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_9, 0, x_7);
x_10 = lean_unbox(x_8);
lean_ctor_set_uint8(x_9, sizeof(void*)*1, x_10);
x_11 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_6);
lean_ctor_set(x_11, 2, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticBv__omega__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Tactic", 6, 6);
x_7 = lean_mk_string_unchecked("tacticBv_omega", 14, 14);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_8 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_7);
x_9 = l_Lean_Syntax_isOfKind(x_1, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_10 = lean_box(1);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_12 = lean_ctor_get(x_2, 5);
lean_inc(x_12);
x_13 = lean_box(0);
x_14 = lean_unbox(x_13);
x_15 = l_Lean_SourceInfo_fromRef(x_12, x_14);
lean_dec(x_12);
x_16 = lean_ctor_get(x_2, 2);
lean_inc(x_16);
x_17 = lean_ctor_get(x_2, 1);
lean_inc(x_17);
lean_dec(x_2);
x_18 = lean_mk_string_unchecked("tactic_<;>_", 11, 11);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_19 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_18);
x_20 = lean_mk_string_unchecked("paren", 5, 5);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_21 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_20);
x_22 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_15);
x_23 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_23, 0, x_15);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_mk_string_unchecked("tacticSeq", 9, 9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_25 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_24);
x_26 = lean_mk_string_unchecked("tacticSeq1Indented", 18, 18);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_27 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_26);
x_28 = lean_mk_string_unchecked("null", 4, 4);
x_29 = l_Lean_Name_mkStr1(x_28);
x_30 = lean_mk_string_unchecked("tacticTry_", 10, 10);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_31 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_30);
x_32 = lean_mk_string_unchecked("try", 3, 3);
lean_inc(x_15);
x_33 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_33, 0, x_15);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_mk_string_unchecked("simp", 4, 4);
lean_inc(x_34);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_35 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_34);
lean_inc(x_15);
x_36 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_36, 0, x_15);
lean_ctor_set(x_36, 1, x_34);
x_37 = lean_mk_string_unchecked("optConfig", 9, 9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_38 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_37);
x_39 = lean_mk_string_unchecked("configItem", 10, 10);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_40 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_39);
x_41 = lean_mk_string_unchecked("negConfigItem", 13, 13);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_42 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_41);
x_43 = lean_mk_string_unchecked("-", 1, 1);
lean_inc(x_15);
x_44 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_44, 0, x_15);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_mk_string_unchecked("implicitDefEqProofs", 19, 19);
lean_inc(x_45);
x_46 = l_String_toSubstring_x27(x_45);
x_47 = l_Lean_Name_mkStr1(x_45);
lean_inc(x_16);
lean_inc(x_17);
x_48 = l_Lean_addMacroScope(x_17, x_47, x_16);
x_49 = lean_box(0);
lean_inc(x_15);
x_50 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_50, 0, x_15);
lean_ctor_set(x_50, 1, x_46);
lean_ctor_set(x_50, 2, x_48);
lean_ctor_set(x_50, 3, x_49);
lean_inc(x_15);
x_51 = l_Lean_Syntax_node2(x_15, x_42, x_44, x_50);
lean_inc(x_15);
x_52 = l_Lean_Syntax_node1(x_15, x_40, x_51);
lean_inc(x_29);
lean_inc(x_15);
x_53 = l_Lean_Syntax_node1(x_15, x_29, x_52);
lean_inc(x_38);
lean_inc(x_15);
x_54 = l_Lean_Syntax_node1(x_15, x_38, x_53);
x_55 = l_Array_mkArray0(lean_box(0));
lean_inc(x_29);
lean_inc(x_15);
x_56 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_56, 0, x_15);
lean_ctor_set(x_56, 1, x_29);
lean_ctor_set(x_56, 2, x_55);
x_57 = lean_mk_string_unchecked("only", 4, 4);
lean_inc(x_15);
x_58 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_58, 0, x_15);
lean_ctor_set(x_58, 1, x_57);
lean_inc(x_29);
lean_inc(x_15);
x_59 = l_Lean_Syntax_node1(x_15, x_29, x_58);
x_60 = lean_mk_string_unchecked("[", 1, 1);
lean_inc(x_15);
x_61 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_61, 0, x_15);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_mk_string_unchecked("simpLemma", 9, 9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_63 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_62);
x_64 = lean_mk_string_unchecked("bitvec_to_nat", 13, 13);
lean_inc(x_64);
x_65 = l_String_toSubstring_x27(x_64);
x_66 = l_Lean_Name_mkStr1(x_64);
x_67 = l_Lean_addMacroScope(x_17, x_66, x_16);
lean_inc(x_15);
x_68 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_68, 0, x_15);
lean_ctor_set(x_68, 1, x_65);
lean_ctor_set(x_68, 2, x_67);
lean_ctor_set(x_68, 3, x_49);
lean_inc_n(x_56, 2);
lean_inc(x_15);
x_69 = l_Lean_Syntax_node3(x_15, x_63, x_56, x_56, x_68);
lean_inc(x_29);
lean_inc(x_15);
x_70 = l_Lean_Syntax_node1(x_15, x_29, x_69);
x_71 = lean_mk_string_unchecked("]", 1, 1);
lean_inc(x_15);
x_72 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_72, 0, x_15);
lean_ctor_set(x_72, 1, x_71);
lean_inc(x_29);
lean_inc(x_15);
x_73 = l_Lean_Syntax_node3(x_15, x_29, x_61, x_70, x_72);
x_74 = lean_mk_string_unchecked("location", 8, 8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_75 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_74);
x_76 = lean_mk_string_unchecked("at", 2, 2);
lean_inc(x_15);
x_77 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_77, 0, x_15);
lean_ctor_set(x_77, 1, x_76);
x_78 = lean_mk_string_unchecked("locationWildcard", 16, 16);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_79 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_78);
x_80 = lean_mk_string_unchecked("*", 1, 1);
lean_inc(x_15);
x_81 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_81, 0, x_15);
lean_ctor_set(x_81, 1, x_80);
lean_inc(x_15);
x_82 = l_Lean_Syntax_node1(x_15, x_79, x_81);
lean_inc(x_15);
x_83 = l_Lean_Syntax_node2(x_15, x_75, x_77, x_82);
lean_inc(x_29);
lean_inc(x_15);
x_84 = l_Lean_Syntax_node1(x_15, x_29, x_83);
lean_inc(x_56);
lean_inc(x_15);
x_85 = l_Lean_Syntax_node6(x_15, x_35, x_36, x_54, x_56, x_59, x_73, x_84);
lean_inc(x_29);
lean_inc(x_15);
x_86 = l_Lean_Syntax_node1(x_15, x_29, x_85);
lean_inc(x_27);
lean_inc(x_15);
x_87 = l_Lean_Syntax_node1(x_15, x_27, x_86);
lean_inc(x_25);
lean_inc(x_15);
x_88 = l_Lean_Syntax_node1(x_15, x_25, x_87);
lean_inc(x_15);
x_89 = l_Lean_Syntax_node2(x_15, x_31, x_33, x_88);
lean_inc(x_15);
x_90 = l_Lean_Syntax_node1(x_15, x_29, x_89);
lean_inc(x_15);
x_91 = l_Lean_Syntax_node1(x_15, x_27, x_90);
lean_inc(x_15);
x_92 = l_Lean_Syntax_node1(x_15, x_25, x_91);
x_93 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_15);
x_94 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_94, 0, x_15);
lean_ctor_set(x_94, 1, x_93);
lean_inc(x_15);
x_95 = l_Lean_Syntax_node3(x_15, x_21, x_23, x_92, x_94);
x_96 = lean_mk_string_unchecked("<;>", 3, 3);
lean_inc(x_15);
x_97 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_97, 0, x_15);
lean_ctor_set(x_97, 1, x_96);
x_98 = lean_mk_string_unchecked("omega", 5, 5);
lean_inc(x_98);
x_99 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_98);
lean_inc(x_15);
x_100 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_100, 0, x_15);
lean_ctor_set(x_100, 1, x_98);
lean_inc(x_15);
x_101 = l_Lean_Syntax_node1(x_15, x_38, x_56);
lean_inc(x_15);
x_102 = l_Lean_Syntax_node2(x_15, x_99, x_100, x_101);
x_103 = l_Lean_Syntax_node3(x_15, x_19, x_95, x_97, x_102);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_3);
return x_104;
}
}
}
static lean_object* _init_l_Lean_Parser_Tactic_acNf0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("acNf0", 5, 5);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("ac_nf0", 6, 6);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_unbox(x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_12);
x_13 = lean_mk_string_unchecked("optional", 8, 8);
x_14 = l_Lean_Name_mkStr1(x_13);
x_15 = l_Lean_Parser_Tactic_location;
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_17, 0, x_8);
lean_ctor_set(x_17, 1, x_11);
lean_ctor_set(x_17, 2, x_16);
x_18 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_18, 0, x_5);
lean_ctor_set(x_18, 1, x_6);
lean_ctor_set(x_18, 2, x_17);
return x_18;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_normCast0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("normCast0", 9, 9);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("norm_cast0", 10, 10);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_unbox(x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_12);
x_13 = l_Lean_Parser_Tactic_optConfig;
lean_inc(x_8);
x_14 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_14, 0, x_8);
lean_ctor_set(x_14, 1, x_11);
lean_ctor_set(x_14, 2, x_13);
x_15 = lean_mk_string_unchecked("optional", 8, 8);
x_16 = l_Lean_Name_mkStr1(x_15);
x_17 = l_Lean_Parser_Tactic_location;
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_19, 0, x_8);
lean_ctor_set(x_19, 1, x_14);
lean_ctor_set(x_19, 2, x_18);
x_20 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_20, 0, x_5);
lean_ctor_set(x_20, 1, x_6);
lean_ctor_set(x_20, 2, x_19);
return x_20;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticAssumption__mod__cast__() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("tacticAssumption_mod_cast_", 26, 26);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("assumption_mod_cast", 19, 19);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_unbox(x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_12);
x_13 = l_Lean_Parser_Tactic_optConfig;
x_14 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_14, 0, x_8);
lean_ctor_set(x_14, 1, x_11);
lean_ctor_set(x_14, 2, x_13);
x_15 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_15, 0, x_5);
lean_ctor_set(x_15, 1, x_6);
lean_ctor_set(x_15, 2, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticAssumption__mod__cast____1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Tactic", 6, 6);
x_7 = lean_mk_string_unchecked("tacticAssumption_mod_cast_", 26, 26);
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
x_10 = lean_box(1);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = l_Lean_Syntax_getArg(x_1, x_12);
lean_dec(x_1);
x_14 = lean_ctor_get(x_2, 5);
x_15 = lean_box(0);
x_16 = lean_unbox(x_15);
x_17 = l_Lean_SourceInfo_fromRef(x_14, x_16);
x_18 = lean_mk_string_unchecked("tactic_<;>_", 11, 11);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_19 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_18);
x_20 = lean_mk_string_unchecked("normCast0", 9, 9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_21 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_20);
x_22 = lean_mk_string_unchecked("norm_cast0", 10, 10);
lean_inc(x_17);
x_23 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_23, 0, x_17);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_mk_string_unchecked("null", 4, 4);
x_25 = l_Lean_Name_mkStr1(x_24);
x_26 = lean_mk_string_unchecked("location", 8, 8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_27 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_26);
x_28 = lean_mk_string_unchecked("at", 2, 2);
lean_inc(x_17);
x_29 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_29, 0, x_17);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_mk_string_unchecked("locationWildcard", 16, 16);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_31 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_30);
x_32 = lean_mk_string_unchecked("*", 1, 1);
lean_inc(x_17);
x_33 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_33, 0, x_17);
lean_ctor_set(x_33, 1, x_32);
lean_inc(x_17);
x_34 = l_Lean_Syntax_node1(x_17, x_31, x_33);
lean_inc(x_17);
x_35 = l_Lean_Syntax_node2(x_17, x_27, x_29, x_34);
lean_inc(x_17);
x_36 = l_Lean_Syntax_node1(x_17, x_25, x_35);
lean_inc(x_17);
x_37 = l_Lean_Syntax_node3(x_17, x_21, x_23, x_13, x_36);
x_38 = lean_mk_string_unchecked("<;>", 3, 3);
lean_inc(x_17);
x_39 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_39, 0, x_17);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_mk_string_unchecked("assumption", 10, 10);
lean_inc(x_40);
x_41 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_40);
lean_inc(x_17);
x_42 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_42, 0, x_17);
lean_ctor_set(x_42, 1, x_40);
lean_inc(x_17);
x_43 = l_Lean_Syntax_node1(x_17, x_41, x_42);
x_44 = l_Lean_Syntax_node3(x_17, x_19, x_37, x_39, x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_3);
return x_45;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticAssumption__mod__cast____1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticAssumption__mod__cast____1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticNorm__cast____() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("tacticNorm_cast__", 17, 17);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("norm_cast", 9, 9);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_unbox(x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_12);
x_13 = l_Lean_Parser_Tactic_optConfig;
lean_inc(x_8);
x_14 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_14, 0, x_8);
lean_ctor_set(x_14, 1, x_11);
lean_ctor_set(x_14, 2, x_13);
x_15 = lean_mk_string_unchecked("optional", 8, 8);
x_16 = l_Lean_Name_mkStr1(x_15);
x_17 = l_Lean_Parser_Tactic_location;
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_19, 0, x_8);
lean_ctor_set(x_19, 1, x_14);
lean_ctor_set(x_19, 2, x_18);
x_20 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_20, 0, x_5);
lean_ctor_set(x_20, 1, x_6);
lean_ctor_set(x_20, 2, x_19);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticNorm__cast______1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Tactic", 6, 6);
x_7 = lean_mk_string_unchecked("tacticNorm_cast__", 17, 17);
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
x_10 = lean_box(1);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_46; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = l_Lean_Syntax_getArg(x_1, x_12);
x_64 = lean_unsigned_to_nat(2u);
x_65 = l_Lean_Syntax_getArg(x_1, x_64);
lean_dec(x_1);
x_66 = l_Lean_Syntax_getOptional_x3f(x_65);
lean_dec(x_65);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; 
x_67 = lean_box(0);
x_46 = x_67;
goto block_63;
}
else
{
uint8_t x_68; 
x_68 = !lean_is_exclusive(x_66);
if (x_68 == 0)
{
x_46 = x_66;
goto block_63;
}
else
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_66, 0);
lean_inc(x_69);
lean_dec(x_66);
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_69);
x_46 = x_70;
goto block_63;
}
}
block_45:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_21 = l_Array_appendCore___redArg(x_14, x_20);
lean_dec(x_20);
lean_inc(x_16);
lean_inc(x_15);
x_22 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_22, 0, x_15);
lean_ctor_set(x_22, 1, x_16);
lean_ctor_set(x_22, 2, x_21);
lean_inc(x_15);
x_23 = l_Lean_Syntax_node3(x_15, x_19, x_17, x_13, x_22);
x_24 = lean_mk_string_unchecked("<;>", 3, 3);
lean_inc(x_15);
x_25 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_25, 0, x_15);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_mk_string_unchecked("tacticTry_", 10, 10);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_27 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_26);
x_28 = lean_mk_string_unchecked("try", 3, 3);
lean_inc(x_15);
x_29 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_29, 0, x_15);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_mk_string_unchecked("tacticSeq", 9, 9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_31 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_30);
x_32 = lean_mk_string_unchecked("tacticSeq1Indented", 18, 18);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_33 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_32);
x_34 = lean_mk_string_unchecked("tacticTrivial", 13, 13);
x_35 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_34);
x_36 = lean_mk_string_unchecked("trivial", 7, 7);
lean_inc(x_15);
x_37 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_37, 0, x_15);
lean_ctor_set(x_37, 1, x_36);
lean_inc(x_15);
x_38 = l_Lean_Syntax_node1(x_15, x_35, x_37);
lean_inc(x_15);
x_39 = l_Lean_Syntax_node1(x_15, x_16, x_38);
lean_inc(x_15);
x_40 = l_Lean_Syntax_node1(x_15, x_33, x_39);
lean_inc(x_15);
x_41 = l_Lean_Syntax_node1(x_15, x_31, x_40);
lean_inc(x_15);
x_42 = l_Lean_Syntax_node2(x_15, x_27, x_29, x_41);
x_43 = l_Lean_Syntax_node3(x_15, x_18, x_23, x_25, x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_3);
return x_44;
}
block_63:
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_47 = lean_ctor_get(x_2, 5);
x_48 = lean_box(0);
x_49 = lean_unbox(x_48);
x_50 = l_Lean_SourceInfo_fromRef(x_47, x_49);
x_51 = lean_mk_string_unchecked("tactic_<;>_", 11, 11);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_52 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_51);
x_53 = lean_mk_string_unchecked("normCast0", 9, 9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_54 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_53);
x_55 = lean_mk_string_unchecked("norm_cast0", 10, 10);
lean_inc(x_50);
x_56 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_56, 0, x_50);
lean_ctor_set(x_56, 1, x_55);
x_57 = lean_mk_string_unchecked("null", 4, 4);
x_58 = l_Lean_Name_mkStr1(x_57);
x_59 = l_Array_mkArray0(lean_box(0));
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_60; 
x_60 = l_Array_empty(lean_box(0));
x_14 = x_59;
x_15 = x_50;
x_16 = x_58;
x_17 = x_56;
x_18 = x_52;
x_19 = x_54;
x_20 = x_60;
goto block_45;
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_46, 0);
lean_inc(x_61);
lean_dec(x_46);
x_62 = l_Array_mkArray1___redArg(x_61);
x_14 = x_59;
x_15 = x_50;
x_16 = x_58;
x_17 = x_56;
x_18 = x_52;
x_19 = x_54;
x_20 = x_62;
goto block_45;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticNorm__cast______1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticNorm__cast______1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_pushCast() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("pushCast", 8, 8);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("push_cast", 9, 9);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_unbox(x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_12);
x_13 = l_Lean_Parser_Tactic_optConfig;
lean_inc(x_8);
x_14 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_14, 0, x_8);
lean_ctor_set(x_14, 1, x_11);
lean_ctor_set(x_14, 2, x_13);
x_15 = lean_mk_string_unchecked("optional", 8, 8);
x_16 = l_Lean_Name_mkStr1(x_15);
x_17 = l_Lean_Parser_Tactic_discharger;
lean_inc(x_16);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
lean_inc(x_8);
x_19 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_19, 0, x_8);
lean_ctor_set(x_19, 1, x_14);
lean_ctor_set(x_19, 2, x_18);
x_20 = lean_mk_string_unchecked(" only", 5, 5);
x_21 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_unbox(x_10);
lean_ctor_set_uint8(x_21, sizeof(void*)*1, x_22);
lean_inc(x_16);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_16);
lean_ctor_set(x_23, 1, x_21);
lean_inc(x_8);
x_24 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_24, 0, x_8);
lean_ctor_set(x_24, 1, x_19);
lean_ctor_set(x_24, 2, x_23);
x_25 = lean_mk_string_unchecked(" [", 2, 2);
x_26 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_mk_string_unchecked("orelse", 6, 6);
x_28 = l_Lean_Name_mkStr1(x_27);
x_29 = l_Lean_Parser_Tactic_simpStar;
x_30 = l_Lean_Parser_Tactic_simpErase;
x_31 = l_Lean_Parser_Tactic_simpLemma;
lean_inc(x_28);
x_32 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_32, 0, x_28);
lean_ctor_set(x_32, 1, x_30);
lean_ctor_set(x_32, 2, x_31);
x_33 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_33, 0, x_28);
lean_ctor_set(x_33, 1, x_29);
lean_ctor_set(x_33, 2, x_32);
x_34 = lean_mk_string_unchecked(",", 1, 1);
x_35 = lean_mk_string_unchecked(", ", 2, 2);
x_36 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_36, 0, x_35);
x_37 = lean_alloc_ctor(10, 3, 1);
lean_ctor_set(x_37, 0, x_33);
lean_ctor_set(x_37, 1, x_34);
lean_ctor_set(x_37, 2, x_36);
x_38 = lean_unbox(x_10);
lean_ctor_set_uint8(x_37, sizeof(void*)*3, x_38);
lean_inc(x_8);
x_39 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_39, 0, x_8);
lean_ctor_set(x_39, 1, x_26);
lean_ctor_set(x_39, 2, x_37);
x_40 = lean_mk_string_unchecked("]", 1, 1);
x_41 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_41, 0, x_40);
lean_inc(x_8);
x_42 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_42, 0, x_8);
lean_ctor_set(x_42, 1, x_39);
lean_ctor_set(x_42, 2, x_41);
lean_inc(x_16);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_16);
lean_ctor_set(x_43, 1, x_42);
lean_inc(x_8);
x_44 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_44, 0, x_8);
lean_ctor_set(x_44, 1, x_24);
lean_ctor_set(x_44, 2, x_43);
x_45 = l_Lean_Parser_Tactic_location;
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_16);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_47, 0, x_8);
lean_ctor_set(x_47, 1, x_44);
lean_ctor_set(x_47, 2, x_46);
x_48 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_48, 0, x_5);
lean_ctor_set(x_48, 1, x_6);
lean_ctor_set(x_48, 2, x_47);
return x_48;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_normCastAddElim() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("normCastAddElim", 15, 15);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("norm_cast_add_elim", 18, 18);
x_10 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_mk_string_unchecked("ident", 5, 5);
x_12 = l_Lean_Name_mkStr1(x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_14, 0, x_8);
lean_ctor_set(x_14, 1, x_10);
lean_ctor_set(x_14, 2, x_13);
x_15 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_15, 0, x_5);
lean_ctor_set(x_15, 1, x_6);
lean_ctor_set(x_15, 2, x_14);
return x_15;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticAc__nf__() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("tacticAc_nf_", 12, 12);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("ac_nf", 5, 5);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_unbox(x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_12);
x_13 = lean_mk_string_unchecked("optional", 8, 8);
x_14 = l_Lean_Name_mkStr1(x_13);
x_15 = l_Lean_Parser_Tactic_location;
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_17, 0, x_8);
lean_ctor_set(x_17, 1, x_11);
lean_ctor_set(x_17, 2, x_16);
x_18 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_18, 0, x_5);
lean_ctor_set(x_18, 1, x_6);
lean_ctor_set(x_18, 2, x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticAc__nf____1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_39; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Tactic", 6, 6);
x_57 = lean_mk_string_unchecked("tacticAc_nf_", 12, 12);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_58 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_57);
lean_inc(x_1);
x_59 = l_Lean_Syntax_isOfKind(x_1, x_58);
lean_dec(x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_60 = lean_box(1);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_3);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_unsigned_to_nat(1u);
x_63 = l_Lean_Syntax_getArg(x_1, x_62);
lean_dec(x_1);
x_64 = l_Lean_Syntax_getOptional_x3f(x_63);
lean_dec(x_63);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; 
x_65 = lean_box(0);
x_39 = x_65;
goto block_56;
}
else
{
uint8_t x_66; 
x_66 = !lean_is_exclusive(x_64);
if (x_66 == 0)
{
x_39 = x_64;
goto block_56;
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_64, 0);
lean_inc(x_67);
lean_dec(x_64);
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_67);
x_39 = x_68;
goto block_56;
}
}
}
block_38:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_14 = l_Array_appendCore___redArg(x_8, x_13);
lean_dec(x_13);
lean_inc(x_10);
lean_inc(x_11);
x_15 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_10);
lean_ctor_set(x_15, 2, x_14);
lean_inc(x_11);
x_16 = l_Lean_Syntax_node2(x_11, x_9, x_7, x_15);
x_17 = lean_mk_string_unchecked("<;>", 3, 3);
lean_inc(x_11);
x_18 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_mk_string_unchecked("tacticTry_", 10, 10);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_20 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_19);
x_21 = lean_mk_string_unchecked("try", 3, 3);
lean_inc(x_11);
x_22 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_22, 0, x_11);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_mk_string_unchecked("tacticSeq", 9, 9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_24 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_23);
x_25 = lean_mk_string_unchecked("tacticSeq1Indented", 18, 18);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_26 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_25);
x_27 = lean_mk_string_unchecked("tacticTrivial", 13, 13);
x_28 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_27);
x_29 = lean_mk_string_unchecked("trivial", 7, 7);
lean_inc(x_11);
x_30 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_30, 0, x_11);
lean_ctor_set(x_30, 1, x_29);
lean_inc(x_11);
x_31 = l_Lean_Syntax_node1(x_11, x_28, x_30);
lean_inc(x_11);
x_32 = l_Lean_Syntax_node1(x_11, x_10, x_31);
lean_inc(x_11);
x_33 = l_Lean_Syntax_node1(x_11, x_26, x_32);
lean_inc(x_11);
x_34 = l_Lean_Syntax_node1(x_11, x_24, x_33);
lean_inc(x_11);
x_35 = l_Lean_Syntax_node2(x_11, x_20, x_22, x_34);
x_36 = l_Lean_Syntax_node3(x_11, x_12, x_16, x_18, x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_3);
return x_37;
}
block_56:
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_40 = lean_ctor_get(x_2, 5);
x_41 = lean_box(0);
x_42 = lean_unbox(x_41);
x_43 = l_Lean_SourceInfo_fromRef(x_40, x_42);
x_44 = lean_mk_string_unchecked("tactic_<;>_", 11, 11);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_45 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_44);
x_46 = lean_mk_string_unchecked("acNf0", 5, 5);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_47 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_46);
x_48 = lean_mk_string_unchecked("ac_nf0", 6, 6);
lean_inc(x_43);
x_49 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_49, 0, x_43);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_mk_string_unchecked("null", 4, 4);
x_51 = l_Lean_Name_mkStr1(x_50);
x_52 = l_Array_mkArray0(lean_box(0));
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_53; 
x_53 = l_Array_empty(lean_box(0));
x_7 = x_49;
x_8 = x_52;
x_9 = x_47;
x_10 = x_51;
x_11 = x_43;
x_12 = x_45;
x_13 = x_53;
goto block_38;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_39, 0);
lean_inc(x_54);
lean_dec(x_39);
x_55 = l_Array_mkArray1___redArg(x_54);
x_7 = x_49;
x_8 = x_52;
x_9 = x_47;
x_10 = x_51;
x_11 = x_43;
x_12 = x_45;
x_13 = x_55;
goto block_38;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticAc__nf____1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__tacticAc__nf____1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_symm() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("symm", 4, 4);
lean_inc(x_4);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_10, 0, x_4);
x_11 = lean_unbox(x_9);
lean_ctor_set_uint8(x_10, sizeof(void*)*1, x_11);
x_12 = lean_mk_string_unchecked("optional", 8, 8);
x_13 = l_Lean_Name_mkStr1(x_12);
x_14 = l_Lean_Parser_Tactic_location;
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_16, 0, x_8);
lean_ctor_set(x_16, 1, x_10);
lean_ctor_set(x_16, 2, x_15);
x_17 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_17, 0, x_5);
lean_ctor_set(x_17, 1, x_6);
lean_ctor_set(x_17, 2, x_16);
return x_17;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_symmSaturate() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("symmSaturate", 12, 12);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1024u);
x_7 = lean_mk_string_unchecked("symm_saturate", 13, 13);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_9, 0, x_7);
x_10 = lean_unbox(x_8);
lean_ctor_set_uint8(x_9, sizeof(void*)*1, x_10);
x_11 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_6);
lean_ctor_set(x_11, 2, x_9);
return x_11;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_SolveByElim_erase() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_1 = lean_mk_string_unchecked("erase", 5, 5);
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Tactic", 6, 6);
x_5 = lean_mk_string_unchecked("SolveByElim", 11, 11);
lean_inc(x_1);
x_6 = l_Lean_Name_mkStr5(x_2, x_3, x_4, x_5, x_1);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("-", 1, 1);
x_10 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_mk_string_unchecked("term", 4, 4);
x_12 = l_Lean_Name_mkStr1(x_11);
x_13 = lean_unsigned_to_nat(1024u);
x_14 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_10);
lean_ctor_set(x_15, 2, x_14);
x_16 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_6);
lean_ctor_set(x_16, 2, x_15);
return x_16;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_SolveByElim_star() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_1 = lean_mk_string_unchecked("star", 4, 4);
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Tactic", 6, 6);
x_5 = lean_mk_string_unchecked("SolveByElim", 11, 11);
lean_inc(x_1);
x_6 = l_Lean_Name_mkStr5(x_2, x_3, x_4, x_5, x_1);
x_7 = lean_mk_string_unchecked("*", 1, 1);
x_8 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_6);
lean_ctor_set(x_9, 2, x_8);
return x_9;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_SolveByElim_arg() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_1 = lean_mk_string_unchecked("arg", 3, 3);
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Tactic", 6, 6);
x_5 = lean_mk_string_unchecked("SolveByElim", 11, 11);
lean_inc(x_1);
x_6 = l_Lean_Name_mkStr5(x_2, x_3, x_4, x_5, x_1);
x_7 = lean_mk_string_unchecked("orelse", 6, 6);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = l_Lean_Parser_Tactic_SolveByElim_star;
x_10 = l_Lean_Parser_Tactic_SolveByElim_erase;
x_11 = lean_mk_string_unchecked("term", 4, 4);
x_12 = l_Lean_Name_mkStr1(x_11);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
lean_inc(x_8);
x_15 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_10);
lean_ctor_set(x_15, 2, x_14);
x_16 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_16, 0, x_8);
lean_ctor_set(x_16, 1, x_9);
lean_ctor_set(x_16, 2, x_15);
x_17 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_6);
lean_ctor_set(x_17, 2, x_16);
return x_17;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_SolveByElim_args() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_1 = lean_mk_string_unchecked("args", 4, 4);
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Tactic", 6, 6);
x_5 = lean_mk_string_unchecked("SolveByElim", 11, 11);
lean_inc(x_1);
x_6 = l_Lean_Name_mkStr5(x_2, x_3, x_4, x_5, x_1);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked(" [", 2, 2);
x_10 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = l_Lean_Parser_Tactic_SolveByElim_arg;
x_12 = lean_mk_string_unchecked(",", 1, 1);
x_13 = lean_mk_string_unchecked(", ", 2, 2);
x_14 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(10, 3, 1);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_12);
lean_ctor_set(x_16, 2, x_14);
x_17 = lean_unbox(x_15);
lean_ctor_set_uint8(x_16, sizeof(void*)*3, x_17);
lean_inc(x_8);
x_18 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_18, 0, x_8);
lean_ctor_set(x_18, 1, x_10);
lean_ctor_set(x_18, 2, x_16);
x_19 = lean_mk_string_unchecked("]", 1, 1);
x_20 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_21, 0, x_8);
lean_ctor_set(x_21, 1, x_18);
lean_ctor_set(x_21, 2, x_20);
x_22 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_22, 0, x_1);
lean_ctor_set(x_22, 1, x_6);
lean_ctor_set(x_22, 2, x_21);
return x_22;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_SolveByElim_using__() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_1 = lean_mk_string_unchecked("using_", 6, 6);
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Tactic", 6, 6);
x_5 = lean_mk_string_unchecked("SolveByElim", 11, 11);
lean_inc(x_1);
x_6 = l_Lean_Name_mkStr5(x_2, x_3, x_4, x_5, x_1);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked(" using ", 7, 7);
x_10 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_mk_string_unchecked("ident", 5, 5);
x_12 = l_Lean_Name_mkStr1(x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_mk_string_unchecked(",", 1, 1);
x_15 = lean_mk_string_unchecked(", ", 2, 2);
x_16 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(10, 3, 1);
lean_ctor_set(x_18, 0, x_13);
lean_ctor_set(x_18, 1, x_14);
lean_ctor_set(x_18, 2, x_16);
x_19 = lean_unbox(x_17);
lean_ctor_set_uint8(x_18, sizeof(void*)*3, x_19);
x_20 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_20, 0, x_8);
lean_ctor_set(x_20, 1, x_10);
lean_ctor_set(x_20, 2, x_18);
x_21 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_21, 0, x_1);
lean_ctor_set(x_21, 1, x_6);
lean_ctor_set(x_21, 2, x_20);
return x_21;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_solveByElim() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("solveByElim", 11, 11);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("solve_by_elim", 13, 13);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_unbox(x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_12);
x_13 = lean_mk_string_unchecked("optional", 8, 8);
x_14 = l_Lean_Name_mkStr1(x_13);
x_15 = lean_mk_string_unchecked("*", 1, 1);
x_16 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_16, 0, x_15);
lean_inc(x_14);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
lean_inc(x_8);
x_18 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_18, 0, x_8);
lean_ctor_set(x_18, 1, x_11);
lean_ctor_set(x_18, 2, x_17);
x_19 = l_Lean_Parser_Tactic_optConfig;
lean_inc(x_8);
x_20 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_20, 0, x_8);
lean_ctor_set(x_20, 1, x_18);
lean_ctor_set(x_20, 2, x_19);
x_21 = lean_mk_string_unchecked(" only", 5, 5);
x_22 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_unbox(x_10);
lean_ctor_set_uint8(x_22, sizeof(void*)*1, x_23);
lean_inc(x_14);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_14);
lean_ctor_set(x_24, 1, x_22);
lean_inc(x_8);
x_25 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_25, 0, x_8);
lean_ctor_set(x_25, 1, x_20);
lean_ctor_set(x_25, 2, x_24);
x_26 = l_Lean_Parser_Tactic_SolveByElim_args;
lean_inc(x_14);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_14);
lean_ctor_set(x_27, 1, x_26);
lean_inc(x_8);
x_28 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_28, 0, x_8);
lean_ctor_set(x_28, 1, x_25);
lean_ctor_set(x_28, 2, x_27);
x_29 = l_Lean_Parser_Tactic_SolveByElim_using__;
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_14);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_31, 0, x_8);
lean_ctor_set(x_31, 1, x_28);
lean_ctor_set(x_31, 2, x_30);
x_32 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_32, 0, x_5);
lean_ctor_set(x_32, 1, x_6);
lean_ctor_set(x_32, 2, x_31);
return x_32;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_applyAssumption() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("applyAssumption", 15, 15);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("apply_assumption", 16, 16);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_unbox(x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_12);
x_13 = l_Lean_Parser_Tactic_optConfig;
lean_inc(x_8);
x_14 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_14, 0, x_8);
lean_ctor_set(x_14, 1, x_11);
lean_ctor_set(x_14, 2, x_13);
x_15 = lean_mk_string_unchecked("optional", 8, 8);
x_16 = l_Lean_Name_mkStr1(x_15);
x_17 = lean_mk_string_unchecked(" only", 5, 5);
x_18 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_unbox(x_10);
lean_ctor_set_uint8(x_18, sizeof(void*)*1, x_19);
lean_inc(x_16);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_16);
lean_ctor_set(x_20, 1, x_18);
lean_inc(x_8);
x_21 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_21, 0, x_8);
lean_ctor_set(x_21, 1, x_14);
lean_ctor_set(x_21, 2, x_20);
x_22 = l_Lean_Parser_Tactic_SolveByElim_args;
lean_inc(x_16);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_16);
lean_ctor_set(x_23, 1, x_22);
lean_inc(x_8);
x_24 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_24, 0, x_8);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 2, x_23);
x_25 = l_Lean_Parser_Tactic_SolveByElim_using__;
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_16);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_27, 0, x_8);
lean_ctor_set(x_27, 1, x_24);
lean_ctor_set(x_27, 2, x_26);
x_28 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_28, 0, x_5);
lean_ctor_set(x_28, 1, x_6);
lean_ctor_set(x_28, 2, x_27);
return x_28;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_applyRules() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("applyRules", 10, 10);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("apply_rules", 11, 11);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_unbox(x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_12);
x_13 = l_Lean_Parser_Tactic_optConfig;
lean_inc(x_8);
x_14 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_14, 0, x_8);
lean_ctor_set(x_14, 1, x_11);
lean_ctor_set(x_14, 2, x_13);
x_15 = lean_mk_string_unchecked("optional", 8, 8);
x_16 = l_Lean_Name_mkStr1(x_15);
x_17 = lean_mk_string_unchecked(" only", 5, 5);
x_18 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_unbox(x_10);
lean_ctor_set_uint8(x_18, sizeof(void*)*1, x_19);
lean_inc(x_16);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_16);
lean_ctor_set(x_20, 1, x_18);
lean_inc(x_8);
x_21 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_21, 0, x_8);
lean_ctor_set(x_21, 1, x_14);
lean_ctor_set(x_21, 2, x_20);
x_22 = l_Lean_Parser_Tactic_SolveByElim_args;
lean_inc(x_16);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_16);
lean_ctor_set(x_23, 1, x_22);
lean_inc(x_8);
x_24 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_24, 0, x_8);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 2, x_23);
x_25 = l_Lean_Parser_Tactic_SolveByElim_using__;
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_16);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_27, 0, x_8);
lean_ctor_set(x_27, 1, x_24);
lean_ctor_set(x_27, 2, x_26);
x_28 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_28, 0, x_5);
lean_ctor_set(x_28, 1, x_6);
lean_ctor_set(x_28, 2, x_27);
return x_28;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_exact_x3f() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("exact\?", 6, 6);
lean_inc(x_4);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_10, 0, x_4);
x_11 = lean_unbox(x_9);
lean_ctor_set_uint8(x_10, sizeof(void*)*1, x_11);
x_12 = lean_mk_string_unchecked("optional", 8, 8);
x_13 = l_Lean_Name_mkStr1(x_12);
x_14 = lean_mk_string_unchecked(" using ", 7, 7);
x_15 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_mk_string_unchecked("colGt", 5, 5);
x_17 = l_Lean_Name_mkStr1(x_16);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_mk_string_unchecked("ident", 5, 5);
x_20 = l_Lean_Name_mkStr1(x_19);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
lean_inc(x_8);
x_22 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_22, 0, x_8);
lean_ctor_set(x_22, 1, x_18);
lean_ctor_set(x_22, 2, x_21);
x_23 = lean_mk_string_unchecked(",", 1, 1);
x_24 = lean_mk_string_unchecked(", ", 2, 2);
x_25 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_alloc_ctor(11, 3, 1);
lean_ctor_set(x_26, 0, x_22);
lean_ctor_set(x_26, 1, x_23);
lean_ctor_set(x_26, 2, x_25);
x_27 = lean_unbox(x_9);
lean_ctor_set_uint8(x_26, sizeof(void*)*3, x_27);
lean_inc(x_8);
x_28 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_28, 0, x_8);
lean_ctor_set(x_28, 1, x_15);
lean_ctor_set(x_28, 2, x_26);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_13);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_30, 0, x_8);
lean_ctor_set(x_30, 1, x_10);
lean_ctor_set(x_30, 2, x_29);
x_31 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_31, 0, x_5);
lean_ctor_set(x_31, 1, x_6);
lean_ctor_set(x_31, 2, x_30);
return x_31;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_apply_x3f() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("apply\?", 6, 6);
lean_inc(x_4);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_10, 0, x_4);
x_11 = lean_unbox(x_9);
lean_ctor_set_uint8(x_10, sizeof(void*)*1, x_11);
x_12 = lean_mk_string_unchecked("optional", 8, 8);
x_13 = l_Lean_Name_mkStr1(x_12);
x_14 = lean_mk_string_unchecked(" using ", 7, 7);
x_15 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_mk_string_unchecked("colGt", 5, 5);
x_17 = l_Lean_Name_mkStr1(x_16);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_mk_string_unchecked("term", 4, 4);
x_20 = l_Lean_Name_mkStr1(x_19);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
lean_inc(x_8);
x_23 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_23, 0, x_8);
lean_ctor_set(x_23, 1, x_18);
lean_ctor_set(x_23, 2, x_22);
x_24 = lean_mk_string_unchecked(",", 1, 1);
x_25 = lean_mk_string_unchecked(", ", 2, 2);
x_26 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_alloc_ctor(11, 3, 1);
lean_ctor_set(x_27, 0, x_23);
lean_ctor_set(x_27, 1, x_24);
lean_ctor_set(x_27, 2, x_26);
x_28 = lean_unbox(x_9);
lean_ctor_set_uint8(x_27, sizeof(void*)*3, x_28);
lean_inc(x_8);
x_29 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_29, 0, x_8);
lean_ctor_set(x_29, 1, x_15);
lean_ctor_set(x_29, 2, x_27);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_13);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_31, 0, x_8);
lean_ctor_set(x_31, 1, x_10);
lean_ctor_set(x_31, 2, x_30);
x_32 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_32, 0, x_5);
lean_ctor_set(x_32, 1, x_6);
lean_ctor_set(x_32, 2, x_31);
return x_32;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rewrites__forbidden() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_1 = lean_mk_string_unchecked("rewrites_forbidden", 18, 18);
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Tactic", 6, 6);
lean_inc(x_1);
x_5 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_1);
x_6 = lean_mk_string_unchecked("andthen", 7, 7);
x_7 = l_Lean_Name_mkStr1(x_6);
x_8 = lean_mk_string_unchecked(" [", 2, 2);
x_9 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_mk_string_unchecked("group", 5, 5);
x_11 = l_Lean_Name_mkStr1(x_10);
x_12 = lean_mk_string_unchecked("-", 1, 1);
x_13 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_mk_string_unchecked("ident", 5, 5);
x_15 = l_Lean_Name_mkStr1(x_14);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
lean_inc(x_7);
x_17 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_17, 0, x_7);
lean_ctor_set(x_17, 1, x_13);
lean_ctor_set(x_17, 2, x_16);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_mk_string_unchecked(",", 1, 1);
x_20 = lean_mk_string_unchecked(", ", 2, 2);
x_21 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_box(1);
x_23 = lean_alloc_ctor(10, 3, 1);
lean_ctor_set(x_23, 0, x_18);
lean_ctor_set(x_23, 1, x_19);
lean_ctor_set(x_23, 2, x_21);
x_24 = lean_unbox(x_22);
lean_ctor_set_uint8(x_23, sizeof(void*)*3, x_24);
lean_inc(x_7);
x_25 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_25, 0, x_7);
lean_ctor_set(x_25, 1, x_9);
lean_ctor_set(x_25, 2, x_23);
x_26 = lean_mk_string_unchecked("]", 1, 1);
x_27 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_28, 0, x_7);
lean_ctor_set(x_28, 1, x_25);
lean_ctor_set(x_28, 2, x_27);
x_29 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_29, 0, x_1);
lean_ctor_set(x_29, 1, x_5);
lean_ctor_set(x_29, 2, x_28);
return x_29;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rewrites_x3f() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("rewrites\?", 9, 9);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("rw\?", 3, 3);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_unbox(x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_12);
x_13 = lean_mk_string_unchecked("optional", 8, 8);
x_14 = l_Lean_Name_mkStr1(x_13);
x_15 = lean_mk_string_unchecked("ppSpace", 7, 7);
x_16 = l_Lean_Name_mkStr1(x_15);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = l_Lean_Parser_Tactic_location;
lean_inc(x_8);
x_19 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_19, 0, x_8);
lean_ctor_set(x_19, 1, x_17);
lean_ctor_set(x_19, 2, x_18);
lean_inc(x_14);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_14);
lean_ctor_set(x_20, 1, x_19);
lean_inc(x_8);
x_21 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_21, 0, x_8);
lean_ctor_set(x_21, 1, x_11);
lean_ctor_set(x_21, 2, x_20);
x_22 = l_Lean_Parser_Tactic_rewrites__forbidden;
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_14);
lean_ctor_set(x_23, 1, x_22);
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
static lean_object* _init_l_Lean_Parser_Tactic_showTerm() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("showTerm", 8, 8);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("show_term ", 10, 10);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_unbox(x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_12);
x_13 = lean_mk_string_unchecked("tacticSeq", 9, 9);
x_14 = l_Lean_Name_mkStr1(x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_16, 0, x_8);
lean_ctor_set(x_16, 1, x_11);
lean_ctor_set(x_16, 2, x_15);
x_17 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_17, 0, x_5);
lean_ctor_set(x_17, 1, x_6);
lean_ctor_set(x_17, 2, x_16);
return x_17;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_showTermElab() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("showTermElab", 12, 12);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("show_term ", 10, 10);
x_10 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_mk_string_unchecked("term", 4, 4);
x_12 = l_Lean_Name_mkStr1(x_11);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_10);
lean_ctor_set(x_15, 2, x_14);
x_16 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_16, 0, x_5);
lean_ctor_set(x_16, 1, x_6);
lean_ctor_set(x_16, 2, x_15);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__showTermElab__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Tactic", 6, 6);
x_7 = lean_mk_string_unchecked("showTermElab", 12, 12);
lean_inc(x_5);
lean_inc(x_4);
x_8 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_7);
lean_inc(x_1);
x_9 = l_Lean_Syntax_isOfKind(x_1, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_10 = lean_box(1);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_unsigned_to_nat(1u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
x_15 = l_Lean_Syntax_getArg(x_1, x_12);
lean_dec(x_1);
x_16 = lean_ctor_get(x_2, 5);
x_17 = lean_box(0);
x_18 = lean_unbox(x_17);
x_19 = l_Lean_SourceInfo_fromRef(x_16, x_18);
x_20 = lean_mk_string_unchecked("Term", 4, 4);
x_21 = lean_mk_string_unchecked("noImplicitLambda", 16, 16);
lean_inc(x_20);
lean_inc(x_5);
lean_inc(x_4);
x_22 = l_Lean_Name_mkStr4(x_4, x_5, x_20, x_21);
x_23 = lean_mk_string_unchecked("no_implicit_lambda%", 19, 19);
lean_inc(x_19);
x_24 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_24, 0, x_19);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_mk_string_unchecked("paren", 5, 5);
lean_inc(x_20);
lean_inc(x_5);
lean_inc(x_4);
x_26 = l_Lean_Name_mkStr4(x_4, x_5, x_20, x_25);
x_27 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_19);
x_28 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_28, 0, x_19);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_mk_string_unchecked("showTermElabImpl", 16, 16);
x_30 = l_Lean_Name_mkStr4(x_4, x_5, x_20, x_29);
x_31 = l_Lean_SourceInfo_fromRef(x_15, x_9);
lean_dec(x_15);
x_32 = lean_mk_string_unchecked("show_term_elab", 14, 14);
x_33 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
lean_inc(x_19);
x_34 = l_Lean_Syntax_node2(x_19, x_30, x_33, x_14);
x_35 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_19);
x_36 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_36, 0, x_19);
lean_ctor_set(x_36, 1, x_35);
lean_inc(x_19);
x_37 = l_Lean_Syntax_node3(x_19, x_26, x_28, x_34, x_36);
x_38 = l_Lean_Syntax_node2(x_19, x_22, x_24, x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_3);
return x_39;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__showTermElab__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__showTermElab__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_by_x3f() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("by\?", 3, 3);
lean_inc(x_4);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_9, 0, x_4);
x_10 = lean_mk_string_unchecked("tacticSeq", 9, 9);
x_11 = l_Lean_Name_mkStr1(x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_9);
lean_ctor_set(x_13, 2, x_12);
x_14 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_14, 0, x_5);
lean_ctor_set(x_14, 1, x_6);
lean_ctor_set(x_14, 2, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__by_x3f__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Tactic", 6, 6);
x_7 = lean_mk_string_unchecked("by\?", 3, 3);
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
x_10 = lean_box(1);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_unsigned_to_nat(1u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
x_15 = l_Lean_Syntax_getArg(x_1, x_12);
lean_dec(x_1);
x_16 = lean_ctor_get(x_2, 5);
x_17 = lean_box(0);
x_18 = lean_unbox(x_17);
x_19 = l_Lean_SourceInfo_fromRef(x_16, x_18);
x_20 = lean_mk_string_unchecked("showTermElab", 12, 12);
lean_inc(x_5);
lean_inc(x_4);
x_21 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_20);
x_22 = l_Lean_SourceInfo_fromRef(x_15, x_9);
lean_dec(x_15);
x_23 = lean_mk_string_unchecked("show_term", 9, 9);
lean_inc(x_22);
x_24 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_mk_string_unchecked("Term", 4, 4);
x_26 = lean_mk_string_unchecked("byTactic", 8, 8);
x_27 = l_Lean_Name_mkStr4(x_4, x_5, x_25, x_26);
x_28 = lean_mk_string_unchecked("by", 2, 2);
x_29 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_29, 0, x_22);
lean_ctor_set(x_29, 1, x_28);
lean_inc(x_19);
x_30 = l_Lean_Syntax_node2(x_19, x_27, x_29, x_14);
x_31 = l_Lean_Syntax_node2(x_19, x_21, x_24, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_3);
return x_32;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__by_x3f__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__by_x3f__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_exposeNames() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("exposeNames", 11, 11);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1024u);
x_7 = lean_mk_string_unchecked("expose_names", 12, 12);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_9, 0, x_7);
x_10 = lean_unbox(x_8);
lean_ctor_set_uint8(x_9, sizeof(void*)*1, x_10);
x_11 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_6);
lean_ctor_set(x_11, 2, x_9);
return x_11;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_suggestPremises() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("suggestPremises", 15, 15);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1024u);
x_7 = lean_mk_string_unchecked("suggest_premises", 16, 16);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_9, 0, x_7);
x_10 = lean_unbox(x_8);
lean_ctor_set_uint8(x_9, sizeof(void*)*1, x_10);
x_11 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_6);
lean_ctor_set(x_11, 2, x_9);
return x_11;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_bvDecideMacro() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("bvDecideMacro", 13, 13);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("bv_decide", 9, 9);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_unbox(x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_12);
x_13 = lean_mk_string_unchecked("group", 5, 5);
x_14 = l_Lean_Name_mkStr1(x_13);
x_15 = l_Lean_Parser_Tactic_optConfig;
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_17, 0, x_8);
lean_ctor_set(x_17, 1, x_11);
lean_ctor_set(x_17, 2, x_16);
x_18 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_18, 0, x_5);
lean_ctor_set(x_18, 1, x_6);
lean_ctor_set(x_18, 2, x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__bvDecideMacro__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Tactic", 6, 6);
x_7 = lean_mk_string_unchecked("bvDecideMacro", 13, 13);
x_8 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_7);
x_9 = l_Lean_Syntax_isOfKind(x_1, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(1);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_mk_string_unchecked("to use `bv_decide`, please include `import Std.Tactic.BVDecide`", 63, 63);
x_13 = l_Lean_Macro_throwError___redArg(x_12, x_2, x_3);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
return x_13;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_13);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__bvDecideMacro__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__bvDecideMacro__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_bvTraceMacro() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("bvTraceMacro", 12, 12);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("bv_decide\?", 10, 10);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_unbox(x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_12);
x_13 = lean_mk_string_unchecked("group", 5, 5);
x_14 = l_Lean_Name_mkStr1(x_13);
x_15 = l_Lean_Parser_Tactic_optConfig;
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_17, 0, x_8);
lean_ctor_set(x_17, 1, x_11);
lean_ctor_set(x_17, 2, x_16);
x_18 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_18, 0, x_5);
lean_ctor_set(x_18, 1, x_6);
lean_ctor_set(x_18, 2, x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__bvTraceMacro__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Tactic", 6, 6);
x_7 = lean_mk_string_unchecked("bvTraceMacro", 12, 12);
x_8 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_7);
x_9 = l_Lean_Syntax_isOfKind(x_1, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(1);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_mk_string_unchecked("to use `bv_decide\?`, please include `import Std.Tactic.BVDecide`", 64, 64);
x_13 = l_Lean_Macro_throwError___redArg(x_12, x_2, x_3);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
return x_13;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_13);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__bvTraceMacro__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__bvTraceMacro__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_bvNormalizeMacro() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("bvNormalizeMacro", 16, 16);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("bv_normalize", 12, 12);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_unbox(x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_12);
x_13 = lean_mk_string_unchecked("group", 5, 5);
x_14 = l_Lean_Name_mkStr1(x_13);
x_15 = l_Lean_Parser_Tactic_optConfig;
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_17, 0, x_8);
lean_ctor_set(x_17, 1, x_11);
lean_ctor_set(x_17, 2, x_16);
x_18 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_18, 0, x_5);
lean_ctor_set(x_18, 1, x_6);
lean_ctor_set(x_18, 2, x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__bvNormalizeMacro__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Tactic", 6, 6);
x_7 = lean_mk_string_unchecked("bvNormalizeMacro", 16, 16);
x_8 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_7);
x_9 = l_Lean_Syntax_isOfKind(x_1, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(1);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_mk_string_unchecked("to use `bv_normalize`, please include `import Std.Tactic.BVDecide`", 66, 66);
x_13 = l_Lean_Macro_throwError___redArg(x_12, x_2, x_3);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
return x_13;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_13);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__bvNormalizeMacro__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_Tactic___aux__Init__Tactics______macroRules__Lean__Parser__Tactic__bvNormalizeMacro__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Attr_simp() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Attr", 4, 4);
x_4 = lean_mk_string_unchecked("simp", 4, 4);
lean_inc(x_4);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_10, 0, x_4);
x_11 = lean_unbox(x_9);
lean_ctor_set_uint8(x_10, sizeof(void*)*1, x_11);
x_12 = lean_mk_string_unchecked("optional", 8, 8);
x_13 = l_Lean_Name_mkStr1(x_12);
x_14 = lean_mk_string_unchecked("orelse", 6, 6);
x_15 = l_Lean_Name_mkStr1(x_14);
x_16 = l_Lean_Parser_Tactic_simpPre;
x_17 = l_Lean_Parser_Tactic_simpPost;
lean_inc(x_15);
x_18 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_16);
lean_ctor_set(x_18, 2, x_17);
lean_inc(x_13);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set(x_19, 1, x_18);
lean_inc(x_8);
x_20 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_20, 0, x_8);
lean_ctor_set(x_20, 1, x_10);
lean_ctor_set(x_20, 2, x_19);
x_21 = lean_mk_string_unchecked("patternIgnore", 13, 13);
x_22 = l_Lean_Name_mkStr1(x_21);
x_23 = lean_mk_string_unchecked("← ", 4, 2);
x_24 = lean_mk_string_unchecked("token", 5, 5);
lean_inc(x_23);
lean_inc(x_24);
x_25 = l_Lean_Name_mkStr2(x_24, x_23);
lean_inc(x_23);
x_26 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_26, 0, x_23);
x_27 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_27, 0, x_23);
lean_ctor_set(x_27, 1, x_25);
lean_ctor_set(x_27, 2, x_26);
x_28 = lean_mk_string_unchecked("<- ", 3, 3);
lean_inc(x_28);
x_29 = l_Lean_Name_mkStr2(x_24, x_28);
lean_inc(x_28);
x_30 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_30, 0, x_28);
x_31 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_29);
lean_ctor_set(x_31, 2, x_30);
x_32 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_32, 0, x_15);
lean_ctor_set(x_32, 1, x_27);
lean_ctor_set(x_32, 2, x_31);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_22);
lean_ctor_set(x_33, 1, x_32);
lean_inc(x_13);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_13);
lean_ctor_set(x_34, 1, x_33);
lean_inc(x_8);
x_35 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_35, 0, x_8);
lean_ctor_set(x_35, 1, x_20);
lean_ctor_set(x_35, 2, x_34);
x_36 = lean_mk_string_unchecked("ppSpace", 7, 7);
x_37 = l_Lean_Name_mkStr1(x_36);
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_37);
x_39 = lean_mk_string_unchecked("prio", 4, 4);
x_40 = l_Lean_Name_mkStr1(x_39);
x_41 = lean_unsigned_to_nat(0u);
x_42 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
lean_inc(x_8);
x_43 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_43, 0, x_8);
lean_ctor_set(x_43, 1, x_38);
lean_ctor_set(x_43, 2, x_42);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_13);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_45, 0, x_8);
lean_ctor_set(x_45, 1, x_35);
lean_ctor_set(x_45, 2, x_44);
x_46 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_46, 0, x_5);
lean_ctor_set(x_46, 1, x_6);
lean_ctor_set(x_46, 2, x_45);
return x_46;
}
}
static lean_object* _init_l_Lean_Parser_Attr_wf__preprocess() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Attr", 4, 4);
x_4 = lean_mk_string_unchecked("wf_preprocess", 13, 13);
lean_inc(x_4);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_10, 0, x_4);
x_11 = lean_unbox(x_9);
lean_ctor_set_uint8(x_10, sizeof(void*)*1, x_11);
x_12 = lean_mk_string_unchecked("optional", 8, 8);
x_13 = l_Lean_Name_mkStr1(x_12);
x_14 = lean_mk_string_unchecked("orelse", 6, 6);
x_15 = l_Lean_Name_mkStr1(x_14);
x_16 = l_Lean_Parser_Tactic_simpPre;
x_17 = l_Lean_Parser_Tactic_simpPost;
lean_inc(x_15);
x_18 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_16);
lean_ctor_set(x_18, 2, x_17);
lean_inc(x_13);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set(x_19, 1, x_18);
lean_inc(x_8);
x_20 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_20, 0, x_8);
lean_ctor_set(x_20, 1, x_10);
lean_ctor_set(x_20, 2, x_19);
x_21 = lean_mk_string_unchecked("patternIgnore", 13, 13);
x_22 = l_Lean_Name_mkStr1(x_21);
x_23 = lean_mk_string_unchecked("← ", 4, 2);
x_24 = lean_mk_string_unchecked("token", 5, 5);
lean_inc(x_23);
lean_inc(x_24);
x_25 = l_Lean_Name_mkStr2(x_24, x_23);
lean_inc(x_23);
x_26 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_26, 0, x_23);
x_27 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_27, 0, x_23);
lean_ctor_set(x_27, 1, x_25);
lean_ctor_set(x_27, 2, x_26);
x_28 = lean_mk_string_unchecked("<- ", 3, 3);
lean_inc(x_28);
x_29 = l_Lean_Name_mkStr2(x_24, x_28);
lean_inc(x_28);
x_30 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_30, 0, x_28);
x_31 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_29);
lean_ctor_set(x_31, 2, x_30);
x_32 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_32, 0, x_15);
lean_ctor_set(x_32, 1, x_27);
lean_ctor_set(x_32, 2, x_31);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_22);
lean_ctor_set(x_33, 1, x_32);
lean_inc(x_13);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_13);
lean_ctor_set(x_34, 1, x_33);
lean_inc(x_8);
x_35 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_35, 0, x_8);
lean_ctor_set(x_35, 1, x_20);
lean_ctor_set(x_35, 2, x_34);
x_36 = lean_mk_string_unchecked("ppSpace", 7, 7);
x_37 = l_Lean_Name_mkStr1(x_36);
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_37);
x_39 = lean_mk_string_unchecked("prio", 4, 4);
x_40 = l_Lean_Name_mkStr1(x_39);
x_41 = lean_unsigned_to_nat(0u);
x_42 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
lean_inc(x_8);
x_43 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_43, 0, x_8);
lean_ctor_set(x_43, 1, x_38);
lean_ctor_set(x_43, 2, x_42);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_13);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_45, 0, x_8);
lean_ctor_set(x_45, 1, x_35);
lean_ctor_set(x_45, 2, x_44);
x_46 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_46, 0, x_5);
lean_ctor_set(x_46, 1, x_6);
lean_ctor_set(x_46, 2, x_45);
return x_46;
}
}
static lean_object* _init_l_Lean_Parser_Attr_normCastLabel() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_1 = lean_mk_string_unchecked("normCastLabel", 13, 13);
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Attr", 4, 4);
lean_inc(x_1);
x_5 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_1);
x_6 = lean_mk_string_unchecked("orelse", 6, 6);
x_7 = l_Lean_Name_mkStr1(x_6);
x_8 = lean_mk_string_unchecked("elim", 4, 4);
x_9 = lean_mk_string_unchecked("token", 5, 5);
lean_inc(x_8);
lean_inc(x_9);
x_10 = l_Lean_Name_mkStr2(x_9, x_8);
x_11 = lean_box(0);
lean_inc(x_8);
x_12 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_12, 0, x_8);
x_13 = lean_unbox(x_11);
lean_ctor_set_uint8(x_12, sizeof(void*)*1, x_13);
x_14 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_14, 0, x_8);
lean_ctor_set(x_14, 1, x_10);
lean_ctor_set(x_14, 2, x_12);
x_15 = lean_mk_string_unchecked("move", 4, 4);
lean_inc(x_15);
lean_inc(x_9);
x_16 = l_Lean_Name_mkStr2(x_9, x_15);
lean_inc(x_15);
x_17 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_17, 0, x_15);
x_18 = lean_unbox(x_11);
lean_ctor_set_uint8(x_17, sizeof(void*)*1, x_18);
x_19 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_19, 0, x_15);
lean_ctor_set(x_19, 1, x_16);
lean_ctor_set(x_19, 2, x_17);
x_20 = lean_mk_string_unchecked("squash", 6, 6);
lean_inc(x_20);
x_21 = l_Lean_Name_mkStr2(x_9, x_20);
lean_inc(x_20);
x_22 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_22, 0, x_20);
x_23 = lean_unbox(x_11);
lean_ctor_set_uint8(x_22, sizeof(void*)*1, x_23);
x_24 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 2, x_22);
lean_inc(x_7);
x_25 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_25, 0, x_7);
lean_ctor_set(x_25, 1, x_19);
lean_ctor_set(x_25, 2, x_24);
x_26 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_26, 0, x_7);
lean_ctor_set(x_26, 1, x_14);
lean_ctor_set(x_26, 2, x_25);
x_27 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_27, 0, x_1);
lean_ctor_set(x_27, 1, x_5);
lean_ctor_set(x_27, 2, x_26);
return x_27;
}
}
static lean_object* _init_l_Lean_Parser_Attr_norm__cast() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Attr", 4, 4);
x_4 = lean_mk_string_unchecked("norm_cast", 9, 9);
lean_inc(x_4);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_10, 0, x_4);
x_11 = lean_unbox(x_9);
lean_ctor_set_uint8(x_10, sizeof(void*)*1, x_11);
x_12 = lean_mk_string_unchecked("optional", 8, 8);
x_13 = l_Lean_Name_mkStr1(x_12);
x_14 = lean_mk_string_unchecked("ppSpace", 7, 7);
x_15 = l_Lean_Name_mkStr1(x_14);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = l_Lean_Parser_Attr_normCastLabel;
lean_inc(x_16);
lean_inc(x_8);
x_18 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_18, 0, x_8);
lean_ctor_set(x_18, 1, x_16);
lean_ctor_set(x_18, 2, x_17);
lean_inc(x_13);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set(x_19, 1, x_18);
lean_inc(x_8);
x_20 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_20, 0, x_8);
lean_ctor_set(x_20, 1, x_10);
lean_ctor_set(x_20, 2, x_19);
x_21 = lean_mk_string_unchecked("num", 3, 3);
x_22 = l_Lean_Name_mkStr1(x_21);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_22);
lean_inc(x_8);
x_24 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_24, 0, x_8);
lean_ctor_set(x_24, 1, x_16);
lean_ctor_set(x_24, 2, x_23);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_13);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_26, 0, x_8);
lean_ctor_set(x_26, 1, x_20);
lean_ctor_set(x_26, 2, x_25);
x_27 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_27, 0, x_5);
lean_ctor_set(x_27, 1, x_6);
lean_ctor_set(x_27, 2, x_26);
return x_27;
}
}
static lean_object* _init_l_term_u2039___u203a() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_1 = lean_mk_string_unchecked("term‹_›", 11, 7);
x_2 = l_Lean_Name_mkStr1(x_1);
x_3 = lean_unsigned_to_nat(1024u);
x_4 = lean_mk_string_unchecked("andthen", 7, 7);
x_5 = l_Lean_Name_mkStr1(x_4);
x_6 = lean_mk_string_unchecked("‹", 3, 1);
x_7 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_mk_string_unchecked("withoutPosition", 15, 15);
x_9 = l_Lean_Name_mkStr1(x_8);
x_10 = lean_mk_string_unchecked("term", 4, 4);
x_11 = l_Lean_Name_mkStr1(x_10);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_9);
lean_ctor_set(x_14, 1, x_13);
lean_inc(x_5);
x_15 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_15, 0, x_5);
lean_ctor_set(x_15, 1, x_7);
lean_ctor_set(x_15, 2, x_14);
x_16 = lean_mk_string_unchecked("›", 3, 1);
x_17 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_18, 0, x_5);
lean_ctor_set(x_18, 1, x_15);
lean_ctor_set(x_18, 2, x_17);
x_19 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_19, 0, x_2);
lean_ctor_set(x_19, 1, x_3);
lean_ctor_set(x_19, 2, x_18);
return x_19;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Tactics______macroRules__term_u2039___u203a__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_mk_string_unchecked("term‹_›", 11, 7);
x_5 = l_Lean_Name_mkStr1(x_4);
lean_inc(x_1);
x_6 = l_Lean_Syntax_isOfKind(x_1, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_1);
x_7 = lean_box(1);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = l_Lean_Syntax_getArg(x_1, x_9);
lean_dec(x_1);
x_11 = lean_ctor_get(x_2, 5);
x_12 = lean_box(0);
x_13 = lean_unbox(x_12);
x_14 = l_Lean_SourceInfo_fromRef(x_11, x_13);
x_15 = lean_mk_string_unchecked("Lean", 4, 4);
x_16 = lean_mk_string_unchecked("Parser", 6, 6);
x_17 = lean_mk_string_unchecked("Term", 4, 4);
x_18 = lean_mk_string_unchecked("typeAscription", 14, 14);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_19 = l_Lean_Name_mkStr4(x_15, x_16, x_17, x_18);
x_20 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_14);
x_21 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_21, 0, x_14);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_mk_string_unchecked("byTactic", 8, 8);
lean_inc(x_16);
lean_inc(x_15);
x_23 = l_Lean_Name_mkStr4(x_15, x_16, x_17, x_22);
x_24 = lean_mk_string_unchecked("by", 2, 2);
lean_inc(x_14);
x_25 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_25, 0, x_14);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_mk_string_unchecked("Tactic", 6, 6);
x_27 = lean_mk_string_unchecked("tacticSeq", 9, 9);
lean_inc(x_26);
lean_inc(x_16);
lean_inc(x_15);
x_28 = l_Lean_Name_mkStr4(x_15, x_16, x_26, x_27);
x_29 = lean_mk_string_unchecked("tacticSeq1Indented", 18, 18);
lean_inc(x_26);
lean_inc(x_16);
lean_inc(x_15);
x_30 = l_Lean_Name_mkStr4(x_15, x_16, x_26, x_29);
x_31 = lean_mk_string_unchecked("null", 4, 4);
x_32 = l_Lean_Name_mkStr1(x_31);
x_33 = lean_mk_string_unchecked("assumption", 10, 10);
lean_inc(x_33);
x_34 = l_Lean_Name_mkStr4(x_15, x_16, x_26, x_33);
lean_inc(x_14);
x_35 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_35, 0, x_14);
lean_ctor_set(x_35, 1, x_33);
lean_inc(x_14);
x_36 = l_Lean_Syntax_node1(x_14, x_34, x_35);
lean_inc(x_32);
lean_inc(x_14);
x_37 = l_Lean_Syntax_node1(x_14, x_32, x_36);
lean_inc(x_14);
x_38 = l_Lean_Syntax_node1(x_14, x_30, x_37);
lean_inc(x_14);
x_39 = l_Lean_Syntax_node1(x_14, x_28, x_38);
lean_inc(x_14);
x_40 = l_Lean_Syntax_node2(x_14, x_23, x_25, x_39);
x_41 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_14);
x_42 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_42, 0, x_14);
lean_ctor_set(x_42, 1, x_41);
lean_inc(x_14);
x_43 = l_Lean_Syntax_node1(x_14, x_32, x_10);
x_44 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_14);
x_45 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_45, 0, x_14);
lean_ctor_set(x_45, 1, x_44);
x_46 = l_Lean_Syntax_node5(x_14, x_19, x_21, x_40, x_42, x_43, x_45);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_3);
return x_47;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Tactics______macroRules__term_u2039___u203a__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___aux__Init__Tactics______macroRules__term_u2039___u203a__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_tacticGet__elem__tactic__trivial() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_1 = lean_mk_string_unchecked("tacticGet_elem_tactic_trivial", 29, 29);
x_2 = l_Lean_Name_mkStr1(x_1);
x_3 = lean_unsigned_to_nat(1024u);
x_4 = lean_mk_string_unchecked("get_elem_tactic_trivial", 23, 23);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_6, 0, x_4);
x_7 = lean_unbox(x_5);
lean_ctor_set_uint8(x_6, sizeof(void*)*1, x_7);
x_8 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_3);
lean_ctor_set(x_8, 2, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Tactics______macroRules__tacticGet__elem__tactic__trivial__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_mk_string_unchecked("tacticGet_elem_tactic_trivial", 29, 29);
x_5 = l_Lean_Name_mkStr1(x_4);
x_6 = l_Lean_Syntax_isOfKind(x_1, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(1);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_9 = lean_ctor_get(x_2, 5);
x_10 = lean_box(0);
x_11 = lean_unbox(x_10);
x_12 = l_Lean_SourceInfo_fromRef(x_9, x_11);
x_13 = lean_mk_string_unchecked("Lean", 4, 4);
x_14 = lean_mk_string_unchecked("Parser", 6, 6);
x_15 = lean_mk_string_unchecked("Tactic", 6, 6);
x_16 = lean_mk_string_unchecked("omega", 5, 5);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_17 = l_Lean_Name_mkStr4(x_13, x_14, x_15, x_16);
lean_inc(x_12);
x_18 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_18, 0, x_12);
lean_ctor_set(x_18, 1, x_16);
x_19 = lean_mk_string_unchecked("optConfig", 9, 9);
x_20 = l_Lean_Name_mkStr4(x_13, x_14, x_15, x_19);
x_21 = lean_mk_string_unchecked("null", 4, 4);
x_22 = l_Lean_Name_mkStr1(x_21);
x_23 = l_Array_mkArray0(lean_box(0));
lean_inc(x_12);
x_24 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_24, 0, x_12);
lean_ctor_set(x_24, 1, x_22);
lean_ctor_set(x_24, 2, x_23);
lean_inc(x_12);
x_25 = l_Lean_Syntax_node1(x_12, x_20, x_24);
x_26 = l_Lean_Syntax_node2(x_12, x_17, x_18, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_3);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Tactics______macroRules__tacticGet__elem__tactic__trivial__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___aux__Init__Tactics______macroRules__tacticGet__elem__tactic__trivial__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Tactics______macroRules__tacticGet__elem__tactic__trivial__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_mk_string_unchecked("tacticGet_elem_tactic_trivial", 29, 29);
x_5 = l_Lean_Name_mkStr1(x_4);
x_6 = l_Lean_Syntax_isOfKind(x_1, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
x_7 = lean_box(1);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_9 = lean_ctor_get(x_2, 5);
lean_inc(x_9);
x_10 = lean_box(0);
x_11 = lean_unbox(x_10);
x_12 = l_Lean_SourceInfo_fromRef(x_9, x_11);
lean_dec(x_9);
x_13 = lean_ctor_get(x_2, 2);
lean_inc(x_13);
x_14 = lean_ctor_get(x_2, 1);
lean_inc(x_14);
lean_dec(x_2);
x_15 = lean_mk_string_unchecked("Lean", 4, 4);
x_16 = lean_mk_string_unchecked("Parser", 6, 6);
x_17 = lean_mk_string_unchecked("Tactic", 6, 6);
x_18 = lean_mk_string_unchecked("seq1", 4, 4);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_19 = l_Lean_Name_mkStr4(x_15, x_16, x_17, x_18);
x_20 = lean_mk_string_unchecked("null", 4, 4);
x_21 = l_Lean_Name_mkStr1(x_20);
x_22 = lean_mk_string_unchecked("simp", 4, 4);
lean_inc(x_22);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_23 = l_Lean_Name_mkStr4(x_15, x_16, x_17, x_22);
lean_inc(x_12);
x_24 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_24, 0, x_12);
lean_ctor_set(x_24, 1, x_22);
x_25 = lean_mk_string_unchecked("optConfig", 9, 9);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_26 = l_Lean_Name_mkStr4(x_15, x_16, x_17, x_25);
x_27 = lean_mk_string_unchecked("configItem", 10, 10);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_28 = l_Lean_Name_mkStr4(x_15, x_16, x_17, x_27);
x_29 = lean_mk_string_unchecked("posConfigItem", 13, 13);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_30 = l_Lean_Name_mkStr4(x_15, x_16, x_17, x_29);
x_31 = lean_mk_string_unchecked("+", 1, 1);
lean_inc(x_12);
x_32 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_32, 0, x_12);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_mk_string_unchecked("arith", 5, 5);
lean_inc(x_33);
x_34 = l_String_toSubstring_x27(x_33);
x_35 = l_Lean_Name_mkStr1(x_33);
x_36 = l_Lean_addMacroScope(x_14, x_35, x_13);
x_37 = lean_box(0);
lean_inc(x_12);
x_38 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_38, 0, x_12);
lean_ctor_set(x_38, 1, x_34);
lean_ctor_set(x_38, 2, x_36);
lean_ctor_set(x_38, 3, x_37);
lean_inc(x_12);
x_39 = l_Lean_Syntax_node2(x_12, x_30, x_32, x_38);
lean_inc(x_12);
x_40 = l_Lean_Syntax_node1(x_12, x_28, x_39);
lean_inc(x_21);
lean_inc(x_12);
x_41 = l_Lean_Syntax_node1(x_12, x_21, x_40);
lean_inc(x_12);
x_42 = l_Lean_Syntax_node1(x_12, x_26, x_41);
x_43 = l_Array_mkArray0(lean_box(0));
lean_inc(x_21);
lean_inc(x_12);
x_44 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_44, 0, x_12);
lean_ctor_set(x_44, 1, x_21);
lean_ctor_set(x_44, 2, x_43);
lean_inc_n(x_44, 3);
lean_inc(x_12);
x_45 = l_Lean_Syntax_node6(x_12, x_23, x_24, x_42, x_44, x_44, x_44, x_44);
x_46 = lean_mk_string_unchecked(";", 1, 1);
lean_inc(x_12);
x_47 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_47, 0, x_12);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_mk_string_unchecked("done", 4, 4);
lean_inc(x_48);
x_49 = l_Lean_Name_mkStr4(x_15, x_16, x_17, x_48);
lean_inc(x_12);
x_50 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_50, 0, x_12);
lean_ctor_set(x_50, 1, x_48);
lean_inc(x_12);
x_51 = l_Lean_Syntax_node1(x_12, x_49, x_50);
lean_inc(x_12);
x_52 = l_Lean_Syntax_node3(x_12, x_21, x_45, x_47, x_51);
x_53 = l_Lean_Syntax_node1(x_12, x_19, x_52);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_3);
return x_54;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Tactics______macroRules__tacticGet__elem__tactic__trivial__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_mk_string_unchecked("tacticGet_elem_tactic_trivial", 29, 29);
x_5 = l_Lean_Name_mkStr1(x_4);
x_6 = l_Lean_Syntax_isOfKind(x_1, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(1);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_9 = lean_ctor_get(x_2, 5);
x_10 = lean_box(0);
x_11 = lean_unbox(x_10);
x_12 = l_Lean_SourceInfo_fromRef(x_9, x_11);
x_13 = lean_mk_string_unchecked("Lean", 4, 4);
x_14 = lean_mk_string_unchecked("Parser", 6, 6);
x_15 = lean_mk_string_unchecked("Tactic", 6, 6);
x_16 = lean_mk_string_unchecked("tacticTrivial", 13, 13);
x_17 = l_Lean_Name_mkStr4(x_13, x_14, x_15, x_16);
x_18 = lean_mk_string_unchecked("trivial", 7, 7);
lean_inc(x_12);
x_19 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_Syntax_node1(x_12, x_17, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_3);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Tactics______macroRules__tacticGet__elem__tactic__trivial__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___aux__Init__Tactics______macroRules__tacticGet__elem__tactic__trivial__3(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_tacticGet__elem__tactic() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_1 = lean_mk_string_unchecked("tacticGet_elem_tactic", 21, 21);
x_2 = l_Lean_Name_mkStr1(x_1);
x_3 = lean_unsigned_to_nat(1024u);
x_4 = lean_mk_string_unchecked("get_elem_tactic", 15, 15);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_6, 0, x_4);
x_7 = lean_unbox(x_5);
lean_ctor_set_uint8(x_6, sizeof(void*)*1, x_7);
x_8 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_3);
lean_ctor_set(x_8, 2, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Tactics______macroRules__tacticGet__elem__tactic__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_mk_string_unchecked("tacticGet_elem_tactic", 21, 21);
x_5 = l_Lean_Name_mkStr1(x_4);
x_6 = l_Lean_Syntax_isOfKind(x_1, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(1);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_9 = lean_ctor_get(x_2, 5);
x_10 = lean_box(0);
x_11 = lean_unbox(x_10);
x_12 = l_Lean_SourceInfo_fromRef(x_9, x_11);
x_13 = lean_mk_string_unchecked("Lean", 4, 4);
x_14 = lean_mk_string_unchecked("Parser", 6, 6);
x_15 = lean_mk_string_unchecked("Tactic", 6, 6);
x_16 = lean_mk_string_unchecked("first", 5, 5);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_17 = l_Lean_Name_mkStr4(x_13, x_14, x_15, x_16);
lean_inc(x_12);
x_18 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_18, 0, x_12);
lean_ctor_set(x_18, 1, x_16);
x_19 = lean_mk_string_unchecked("null", 4, 4);
x_20 = l_Lean_Name_mkStr1(x_19);
x_21 = lean_mk_string_unchecked("group", 5, 5);
x_22 = l_Lean_Name_mkStr1(x_21);
x_23 = lean_mk_string_unchecked("|", 1, 1);
lean_inc(x_12);
x_24 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_24, 0, x_12);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_mk_string_unchecked("tacticSeq", 9, 9);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_26 = l_Lean_Name_mkStr4(x_13, x_14, x_15, x_25);
x_27 = lean_mk_string_unchecked("tacticSeq1Indented", 18, 18);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_28 = l_Lean_Name_mkStr4(x_13, x_14, x_15, x_27);
x_29 = lean_mk_string_unchecked("done", 4, 4);
lean_inc(x_29);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_30 = l_Lean_Name_mkStr4(x_13, x_14, x_15, x_29);
lean_inc(x_12);
x_31 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_31, 0, x_12);
lean_ctor_set(x_31, 1, x_29);
lean_inc(x_12);
x_32 = l_Lean_Syntax_node1(x_12, x_30, x_31);
lean_inc(x_20);
lean_inc(x_12);
x_33 = l_Lean_Syntax_node1(x_12, x_20, x_32);
lean_inc(x_28);
lean_inc(x_12);
x_34 = l_Lean_Syntax_node1(x_12, x_28, x_33);
lean_inc(x_26);
lean_inc(x_12);
x_35 = l_Lean_Syntax_node1(x_12, x_26, x_34);
lean_inc(x_24);
lean_inc(x_22);
lean_inc(x_12);
x_36 = l_Lean_Syntax_node2(x_12, x_22, x_24, x_35);
x_37 = lean_mk_string_unchecked("assumption", 10, 10);
lean_inc(x_37);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_38 = l_Lean_Name_mkStr4(x_13, x_14, x_15, x_37);
lean_inc(x_12);
x_39 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_39, 0, x_12);
lean_ctor_set(x_39, 1, x_37);
lean_inc(x_12);
x_40 = l_Lean_Syntax_node1(x_12, x_38, x_39);
lean_inc(x_20);
lean_inc(x_12);
x_41 = l_Lean_Syntax_node1(x_12, x_20, x_40);
lean_inc(x_28);
lean_inc(x_12);
x_42 = l_Lean_Syntax_node1(x_12, x_28, x_41);
lean_inc(x_26);
lean_inc(x_12);
x_43 = l_Lean_Syntax_node1(x_12, x_26, x_42);
lean_inc(x_24);
lean_inc(x_22);
lean_inc(x_12);
x_44 = l_Lean_Syntax_node2(x_12, x_22, x_24, x_43);
x_45 = lean_mk_string_unchecked("tacticGet_elem_tactic_trivial", 29, 29);
x_46 = l_Lean_Name_mkStr1(x_45);
x_47 = lean_mk_string_unchecked("get_elem_tactic_trivial", 23, 23);
lean_inc(x_12);
x_48 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_48, 0, x_12);
lean_ctor_set(x_48, 1, x_47);
lean_inc(x_12);
x_49 = l_Lean_Syntax_node1(x_12, x_46, x_48);
lean_inc(x_20);
lean_inc(x_12);
x_50 = l_Lean_Syntax_node1(x_12, x_20, x_49);
lean_inc(x_28);
lean_inc(x_12);
x_51 = l_Lean_Syntax_node1(x_12, x_28, x_50);
lean_inc(x_26);
lean_inc(x_12);
x_52 = l_Lean_Syntax_node1(x_12, x_26, x_51);
lean_inc(x_24);
lean_inc(x_22);
lean_inc(x_12);
x_53 = l_Lean_Syntax_node2(x_12, x_22, x_24, x_52);
x_54 = lean_mk_string_unchecked("fail", 4, 4);
lean_inc(x_54);
x_55 = l_Lean_Name_mkStr4(x_13, x_14, x_15, x_54);
lean_inc(x_12);
x_56 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_56, 0, x_12);
lean_ctor_set(x_56, 1, x_54);
x_57 = lean_mk_string_unchecked("str", 3, 3);
x_58 = l_Lean_Name_mkStr1(x_57);
x_59 = lean_mk_string_unchecked("\"failed to prove index is valid, possible solutions:\n  - Use `have`-expressions to prove the index is valid\n  - Use `a[i]!` notation instead, runtime check is performed, and 'Panic' error message is produced if index is not valid\n  - Use `a[i]\?` notation instead, result is an `Option` type\n  - Use `a[i]'h` notation instead, where `h` is a proof that index is valid\"", 367, 367);
lean_inc(x_12);
x_60 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_60, 0, x_12);
lean_ctor_set(x_60, 1, x_59);
lean_inc(x_12);
x_61 = l_Lean_Syntax_node1(x_12, x_58, x_60);
lean_inc(x_20);
lean_inc(x_12);
x_62 = l_Lean_Syntax_node1(x_12, x_20, x_61);
lean_inc(x_12);
x_63 = l_Lean_Syntax_node2(x_12, x_55, x_56, x_62);
lean_inc(x_20);
lean_inc(x_12);
x_64 = l_Lean_Syntax_node1(x_12, x_20, x_63);
lean_inc(x_12);
x_65 = l_Lean_Syntax_node1(x_12, x_28, x_64);
lean_inc(x_12);
x_66 = l_Lean_Syntax_node1(x_12, x_26, x_65);
lean_inc(x_12);
x_67 = l_Lean_Syntax_node2(x_12, x_22, x_24, x_66);
lean_inc(x_12);
x_68 = l_Lean_Syntax_node4(x_12, x_20, x_36, x_44, x_53, x_67);
x_69 = l_Lean_Syntax_node2(x_12, x_17, x_18, x_68);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_3);
return x_70;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Tactics______macroRules__tacticGet__elem__tactic__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___aux__Init__Tactics______macroRules__tacticGet__elem__tactic__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Syntax_exact_x3f() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Syntax", 6, 6);
x_4 = lean_mk_string_unchecked("exact\?", 6, 6);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1024u);
x_7 = lean_mk_string_unchecked("exact\?%", 7, 7);
x_8 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_6);
lean_ctor_set(x_9, 2, x_8);
return x_9;
}
}
lean_object* initialize_Init_Notation(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Tactics(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Notation(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Tactic_as__aux__lemma = _init_l_Lean_Parser_Tactic_as__aux__lemma();
lean_mark_persistent(l_Lean_Parser_Tactic_as__aux__lemma);
l_Lean_Parser_Tactic_withAnnotateState = _init_l_Lean_Parser_Tactic_withAnnotateState();
lean_mark_persistent(l_Lean_Parser_Tactic_withAnnotateState);
l_Lean_Parser_Tactic_intro = _init_l_Lean_Parser_Tactic_intro();
lean_mark_persistent(l_Lean_Parser_Tactic_intro);
l_Lean_Parser_Tactic_intros = _init_l_Lean_Parser_Tactic_intros();
lean_mark_persistent(l_Lean_Parser_Tactic_intros);
l_Lean_Parser_Tactic_rename = _init_l_Lean_Parser_Tactic_rename();
lean_mark_persistent(l_Lean_Parser_Tactic_rename);
l_Lean_Parser_Tactic_revert = _init_l_Lean_Parser_Tactic_revert();
lean_mark_persistent(l_Lean_Parser_Tactic_revert);
l_Lean_Parser_Tactic_clear = _init_l_Lean_Parser_Tactic_clear();
lean_mark_persistent(l_Lean_Parser_Tactic_clear);
l_Lean_Parser_Tactic_subst = _init_l_Lean_Parser_Tactic_subst();
lean_mark_persistent(l_Lean_Parser_Tactic_subst);
l_Lean_Parser_Tactic_substVars = _init_l_Lean_Parser_Tactic_substVars();
lean_mark_persistent(l_Lean_Parser_Tactic_substVars);
l_Lean_Parser_Tactic_assumption = _init_l_Lean_Parser_Tactic_assumption();
lean_mark_persistent(l_Lean_Parser_Tactic_assumption);
l_Lean_Parser_Tactic_contradiction = _init_l_Lean_Parser_Tactic_contradiction();
lean_mark_persistent(l_Lean_Parser_Tactic_contradiction);
l_Lean_Parser_Tactic_falseOrByContra = _init_l_Lean_Parser_Tactic_falseOrByContra();
lean_mark_persistent(l_Lean_Parser_Tactic_falseOrByContra);
l_Lean_Parser_Tactic_apply = _init_l_Lean_Parser_Tactic_apply();
lean_mark_persistent(l_Lean_Parser_Tactic_apply);
l_Lean_Parser_Tactic_exact = _init_l_Lean_Parser_Tactic_exact();
lean_mark_persistent(l_Lean_Parser_Tactic_exact);
l_Lean_Parser_Tactic_refine = _init_l_Lean_Parser_Tactic_refine();
lean_mark_persistent(l_Lean_Parser_Tactic_refine);
l_Lean_Parser_Tactic_refine_x27 = _init_l_Lean_Parser_Tactic_refine_x27();
lean_mark_persistent(l_Lean_Parser_Tactic_refine_x27);
l_Lean_Parser_Tactic_tacticExfalso = _init_l_Lean_Parser_Tactic_tacticExfalso();
lean_mark_persistent(l_Lean_Parser_Tactic_tacticExfalso);
l_Lean_Parser_Tactic_constructor = _init_l_Lean_Parser_Tactic_constructor();
lean_mark_persistent(l_Lean_Parser_Tactic_constructor);
l_Lean_Parser_Tactic_left = _init_l_Lean_Parser_Tactic_left();
lean_mark_persistent(l_Lean_Parser_Tactic_left);
l_Lean_Parser_Tactic_right = _init_l_Lean_Parser_Tactic_right();
lean_mark_persistent(l_Lean_Parser_Tactic_right);
l_Lean_Parser_Tactic_case = _init_l_Lean_Parser_Tactic_case();
lean_mark_persistent(l_Lean_Parser_Tactic_case);
l_Lean_Parser_Tactic_case_x27 = _init_l_Lean_Parser_Tactic_case_x27();
lean_mark_persistent(l_Lean_Parser_Tactic_case_x27);
l_Lean_Parser_Tactic_tacticNext___x3d_x3e__ = _init_l_Lean_Parser_Tactic_tacticNext___x3d_x3e__();
lean_mark_persistent(l_Lean_Parser_Tactic_tacticNext___x3d_x3e__);
l_Lean_Parser_Tactic_allGoals = _init_l_Lean_Parser_Tactic_allGoals();
lean_mark_persistent(l_Lean_Parser_Tactic_allGoals);
l_Lean_Parser_Tactic_anyGoals = _init_l_Lean_Parser_Tactic_anyGoals();
lean_mark_persistent(l_Lean_Parser_Tactic_anyGoals);
l_Lean_Parser_Tactic_focus = _init_l_Lean_Parser_Tactic_focus();
lean_mark_persistent(l_Lean_Parser_Tactic_focus);
l_Lean_Parser_Tactic_skip = _init_l_Lean_Parser_Tactic_skip();
lean_mark_persistent(l_Lean_Parser_Tactic_skip);
l_Lean_Parser_Tactic_done = _init_l_Lean_Parser_Tactic_done();
lean_mark_persistent(l_Lean_Parser_Tactic_done);
l_Lean_Parser_Tactic_traceState = _init_l_Lean_Parser_Tactic_traceState();
lean_mark_persistent(l_Lean_Parser_Tactic_traceState);
l_Lean_Parser_Tactic_traceMessage = _init_l_Lean_Parser_Tactic_traceMessage();
lean_mark_persistent(l_Lean_Parser_Tactic_traceMessage);
l_Lean_Parser_Tactic_failIfSuccess = _init_l_Lean_Parser_Tactic_failIfSuccess();
lean_mark_persistent(l_Lean_Parser_Tactic_failIfSuccess);
l_Lean_Parser_Tactic_paren = _init_l_Lean_Parser_Tactic_paren();
lean_mark_persistent(l_Lean_Parser_Tactic_paren);
l_Lean_Parser_Tactic_withReducible = _init_l_Lean_Parser_Tactic_withReducible();
lean_mark_persistent(l_Lean_Parser_Tactic_withReducible);
l_Lean_Parser_Tactic_withReducibleAndInstances = _init_l_Lean_Parser_Tactic_withReducibleAndInstances();
lean_mark_persistent(l_Lean_Parser_Tactic_withReducibleAndInstances);
l_Lean_Parser_Tactic_withUnfoldingAll = _init_l_Lean_Parser_Tactic_withUnfoldingAll();
lean_mark_persistent(l_Lean_Parser_Tactic_withUnfoldingAll);
l_Lean_Parser_Tactic_first = _init_l_Lean_Parser_Tactic_first();
lean_mark_persistent(l_Lean_Parser_Tactic_first);
l_Lean_Parser_Tactic_rotateLeft = _init_l_Lean_Parser_Tactic_rotateLeft();
lean_mark_persistent(l_Lean_Parser_Tactic_rotateLeft);
l_Lean_Parser_Tactic_rotateRight = _init_l_Lean_Parser_Tactic_rotateRight();
lean_mark_persistent(l_Lean_Parser_Tactic_rotateRight);
l_Lean_Parser_Tactic_tacticTry__ = _init_l_Lean_Parser_Tactic_tacticTry__();
lean_mark_persistent(l_Lean_Parser_Tactic_tacticTry__);
l_Lean_Parser_Tactic_tactic___x3c_x3b_x3e__ = _init_l_Lean_Parser_Tactic_tactic___x3c_x3b_x3e__();
lean_mark_persistent(l_Lean_Parser_Tactic_tactic___x3c_x3b_x3e__);
l_Lean_Parser_Tactic_fail = _init_l_Lean_Parser_Tactic_fail();
lean_mark_persistent(l_Lean_Parser_Tactic_fail);
l_Lean_Parser_Tactic_eqRefl = _init_l_Lean_Parser_Tactic_eqRefl();
lean_mark_persistent(l_Lean_Parser_Tactic_eqRefl);
l_Lean_Parser_Tactic_tacticRfl = _init_l_Lean_Parser_Tactic_tacticRfl();
lean_mark_persistent(l_Lean_Parser_Tactic_tacticRfl);
l_Lean_Parser_Tactic_applyRfl = _init_l_Lean_Parser_Tactic_applyRfl();
lean_mark_persistent(l_Lean_Parser_Tactic_applyRfl);
l_Lean_Parser_Tactic_tacticRfl_x27 = _init_l_Lean_Parser_Tactic_tacticRfl_x27();
lean_mark_persistent(l_Lean_Parser_Tactic_tacticRfl_x27);
l_Lean_Parser_Tactic_acRfl = _init_l_Lean_Parser_Tactic_acRfl();
lean_mark_persistent(l_Lean_Parser_Tactic_acRfl);
l_Lean_Parser_Tactic_tacticSorry = _init_l_Lean_Parser_Tactic_tacticSorry();
lean_mark_persistent(l_Lean_Parser_Tactic_tacticSorry);
l_Lean_Parser_Tactic_tacticAdmit = _init_l_Lean_Parser_Tactic_tacticAdmit();
lean_mark_persistent(l_Lean_Parser_Tactic_tacticAdmit);
l_Lean_Parser_Tactic_tacticInfer__instance = _init_l_Lean_Parser_Tactic_tacticInfer__instance();
lean_mark_persistent(l_Lean_Parser_Tactic_tacticInfer__instance);
l_Lean_Parser_Tactic_posConfigItem = _init_l_Lean_Parser_Tactic_posConfigItem();
lean_mark_persistent(l_Lean_Parser_Tactic_posConfigItem);
l_Lean_Parser_Tactic_negConfigItem = _init_l_Lean_Parser_Tactic_negConfigItem();
lean_mark_persistent(l_Lean_Parser_Tactic_negConfigItem);
l_Lean_Parser_Tactic_valConfigItem = _init_l_Lean_Parser_Tactic_valConfigItem();
lean_mark_persistent(l_Lean_Parser_Tactic_valConfigItem);
l_Lean_Parser_Tactic_configItem = _init_l_Lean_Parser_Tactic_configItem();
lean_mark_persistent(l_Lean_Parser_Tactic_configItem);
l_Lean_Parser_Tactic_optConfig = _init_l_Lean_Parser_Tactic_optConfig();
lean_mark_persistent(l_Lean_Parser_Tactic_optConfig);
l_Lean_Parser_Tactic_config = _init_l_Lean_Parser_Tactic_config();
lean_mark_persistent(l_Lean_Parser_Tactic_config);
l_Lean_Parser_Tactic_locationWildcard = _init_l_Lean_Parser_Tactic_locationWildcard();
lean_mark_persistent(l_Lean_Parser_Tactic_locationWildcard);
l_Lean_Parser_Tactic_locationType = _init_l_Lean_Parser_Tactic_locationType();
lean_mark_persistent(l_Lean_Parser_Tactic_locationType);
l_Lean_Parser_Tactic_locationHyp = _init_l_Lean_Parser_Tactic_locationHyp();
lean_mark_persistent(l_Lean_Parser_Tactic_locationHyp);
l_Lean_Parser_Tactic_location = _init_l_Lean_Parser_Tactic_location();
lean_mark_persistent(l_Lean_Parser_Tactic_location);
l_Lean_Parser_Tactic_change = _init_l_Lean_Parser_Tactic_change();
lean_mark_persistent(l_Lean_Parser_Tactic_change);
l_Lean_Parser_Tactic_changeWith = _init_l_Lean_Parser_Tactic_changeWith();
lean_mark_persistent(l_Lean_Parser_Tactic_changeWith);
l_Lean_Parser_Tactic_extractLets = _init_l_Lean_Parser_Tactic_extractLets();
lean_mark_persistent(l_Lean_Parser_Tactic_extractLets);
l_Lean_Parser_Tactic_liftLets = _init_l_Lean_Parser_Tactic_liftLets();
lean_mark_persistent(l_Lean_Parser_Tactic_liftLets);
l_Lean_Parser_Tactic_rwRule = _init_l_Lean_Parser_Tactic_rwRule();
lean_mark_persistent(l_Lean_Parser_Tactic_rwRule);
l_Lean_Parser_Tactic_rwRuleSeq = _init_l_Lean_Parser_Tactic_rwRuleSeq();
lean_mark_persistent(l_Lean_Parser_Tactic_rwRuleSeq);
l_Lean_Parser_Tactic_rewriteSeq = _init_l_Lean_Parser_Tactic_rewriteSeq();
lean_mark_persistent(l_Lean_Parser_Tactic_rewriteSeq);
l_Lean_Parser_Tactic_rwSeq = _init_l_Lean_Parser_Tactic_rwSeq();
lean_mark_persistent(l_Lean_Parser_Tactic_rwSeq);
l_Lean_Parser_Tactic_tacticRwa____ = _init_l_Lean_Parser_Tactic_tacticRwa____();
lean_mark_persistent(l_Lean_Parser_Tactic_tacticRwa____);
l_Lean_Parser_Tactic_injection = _init_l_Lean_Parser_Tactic_injection();
lean_mark_persistent(l_Lean_Parser_Tactic_injection);
l_Lean_Parser_Tactic_injections = _init_l_Lean_Parser_Tactic_injections();
lean_mark_persistent(l_Lean_Parser_Tactic_injections);
l_Lean_Parser_Tactic_discharger = _init_l_Lean_Parser_Tactic_discharger();
lean_mark_persistent(l_Lean_Parser_Tactic_discharger);
l_Lean_Parser_Tactic_simpPre = _init_l_Lean_Parser_Tactic_simpPre();
lean_mark_persistent(l_Lean_Parser_Tactic_simpPre);
l_Lean_Parser_Tactic_simpPost = _init_l_Lean_Parser_Tactic_simpPost();
lean_mark_persistent(l_Lean_Parser_Tactic_simpPost);
l_Lean_Parser_Tactic_simpLemma = _init_l_Lean_Parser_Tactic_simpLemma();
lean_mark_persistent(l_Lean_Parser_Tactic_simpLemma);
l_Lean_Parser_Tactic_simpErase = _init_l_Lean_Parser_Tactic_simpErase();
lean_mark_persistent(l_Lean_Parser_Tactic_simpErase);
l_Lean_Parser_Tactic_simpStar = _init_l_Lean_Parser_Tactic_simpStar();
lean_mark_persistent(l_Lean_Parser_Tactic_simpStar);
l_Lean_Parser_Tactic_simp = _init_l_Lean_Parser_Tactic_simp();
lean_mark_persistent(l_Lean_Parser_Tactic_simp);
l_Lean_Parser_Tactic_simpAll = _init_l_Lean_Parser_Tactic_simpAll();
lean_mark_persistent(l_Lean_Parser_Tactic_simpAll);
l_Lean_Parser_Tactic_dsimp = _init_l_Lean_Parser_Tactic_dsimp();
lean_mark_persistent(l_Lean_Parser_Tactic_dsimp);
l_Lean_Parser_Tactic_simpArg = _init_l_Lean_Parser_Tactic_simpArg();
lean_mark_persistent(l_Lean_Parser_Tactic_simpArg);
l_Lean_Parser_Tactic_simpArgs = _init_l_Lean_Parser_Tactic_simpArgs();
lean_mark_persistent(l_Lean_Parser_Tactic_simpArgs);
l_Lean_Parser_Tactic_dsimpArg = _init_l_Lean_Parser_Tactic_dsimpArg();
lean_mark_persistent(l_Lean_Parser_Tactic_dsimpArg);
l_Lean_Parser_Tactic_dsimpArgs = _init_l_Lean_Parser_Tactic_dsimpArgs();
lean_mark_persistent(l_Lean_Parser_Tactic_dsimpArgs);
l_Lean_Parser_Tactic_simpTraceArgsRest = _init_l_Lean_Parser_Tactic_simpTraceArgsRest();
lean_mark_persistent(l_Lean_Parser_Tactic_simpTraceArgsRest);
l_Lean_Parser_Tactic_simpTrace = _init_l_Lean_Parser_Tactic_simpTrace();
lean_mark_persistent(l_Lean_Parser_Tactic_simpTrace);
l_Lean_Parser_Tactic_tacticSimp_x3f_x21__ = _init_l_Lean_Parser_Tactic_tacticSimp_x3f_x21__();
lean_mark_persistent(l_Lean_Parser_Tactic_tacticSimp_x3f_x21__);
l_Lean_Parser_Tactic_simpAllTraceArgsRest = _init_l_Lean_Parser_Tactic_simpAllTraceArgsRest();
lean_mark_persistent(l_Lean_Parser_Tactic_simpAllTraceArgsRest);
l_Lean_Parser_Tactic_simpAllTrace = _init_l_Lean_Parser_Tactic_simpAllTrace();
lean_mark_persistent(l_Lean_Parser_Tactic_simpAllTrace);
l_Lean_Parser_Tactic_tacticSimp__all_x3f_x21__ = _init_l_Lean_Parser_Tactic_tacticSimp__all_x3f_x21__();
lean_mark_persistent(l_Lean_Parser_Tactic_tacticSimp__all_x3f_x21__);
l_Lean_Parser_Tactic_dsimpTraceArgsRest = _init_l_Lean_Parser_Tactic_dsimpTraceArgsRest();
lean_mark_persistent(l_Lean_Parser_Tactic_dsimpTraceArgsRest);
l_Lean_Parser_Tactic_dsimpTrace = _init_l_Lean_Parser_Tactic_dsimpTrace();
lean_mark_persistent(l_Lean_Parser_Tactic_dsimpTrace);
l_Lean_Parser_Tactic_tacticDsimp_x3f_x21__ = _init_l_Lean_Parser_Tactic_tacticDsimp_x3f_x21__();
lean_mark_persistent(l_Lean_Parser_Tactic_tacticDsimp_x3f_x21__);
l_Lean_Parser_Tactic_simpaArgsRest = _init_l_Lean_Parser_Tactic_simpaArgsRest();
lean_mark_persistent(l_Lean_Parser_Tactic_simpaArgsRest);
l_Lean_Parser_Tactic_simpa = _init_l_Lean_Parser_Tactic_simpa();
lean_mark_persistent(l_Lean_Parser_Tactic_simpa);
l_Lean_Parser_Tactic_tacticSimpa_x21__ = _init_l_Lean_Parser_Tactic_tacticSimpa_x21__();
lean_mark_persistent(l_Lean_Parser_Tactic_tacticSimpa_x21__);
l_Lean_Parser_Tactic_tacticSimpa_x3f__ = _init_l_Lean_Parser_Tactic_tacticSimpa_x3f__();
lean_mark_persistent(l_Lean_Parser_Tactic_tacticSimpa_x3f__);
l_Lean_Parser_Tactic_tacticSimpa_x3f_x21__ = _init_l_Lean_Parser_Tactic_tacticSimpa_x3f_x21__();
lean_mark_persistent(l_Lean_Parser_Tactic_tacticSimpa_x3f_x21__);
l_Lean_Parser_Tactic_delta = _init_l_Lean_Parser_Tactic_delta();
lean_mark_persistent(l_Lean_Parser_Tactic_delta);
l_Lean_Parser_Tactic_unfold = _init_l_Lean_Parser_Tactic_unfold();
lean_mark_persistent(l_Lean_Parser_Tactic_unfold);
l_Lean_Parser_Tactic_tacticRefine__lift__ = _init_l_Lean_Parser_Tactic_tacticRefine__lift__();
lean_mark_persistent(l_Lean_Parser_Tactic_tacticRefine__lift__);
l_Lean_Parser_Tactic_tacticHave__ = _init_l_Lean_Parser_Tactic_tacticHave__();
lean_mark_persistent(l_Lean_Parser_Tactic_tacticHave__);
l_Lean_Parser_Tactic_tacticSuffices__ = _init_l_Lean_Parser_Tactic_tacticSuffices__();
lean_mark_persistent(l_Lean_Parser_Tactic_tacticSuffices__);
l_Lean_Parser_Tactic_tacticLet__ = _init_l_Lean_Parser_Tactic_tacticLet__();
lean_mark_persistent(l_Lean_Parser_Tactic_tacticLet__);
l_Lean_Parser_Tactic_tacticShow__ = _init_l_Lean_Parser_Tactic_tacticShow__();
lean_mark_persistent(l_Lean_Parser_Tactic_tacticShow__);
l_Lean_Parser_Tactic_letrec = _init_l_Lean_Parser_Tactic_letrec();
lean_mark_persistent(l_Lean_Parser_Tactic_letrec);
l_Lean_Parser_Tactic_tacticRefine__lift_x27__ = _init_l_Lean_Parser_Tactic_tacticRefine__lift_x27__();
lean_mark_persistent(l_Lean_Parser_Tactic_tacticRefine__lift_x27__);
l_Lean_Parser_Tactic_tacticHave_x27__ = _init_l_Lean_Parser_Tactic_tacticHave_x27__();
lean_mark_persistent(l_Lean_Parser_Tactic_tacticHave_x27__);
l_Lean_Parser_Tactic_tacticHave_x27___x3a_x3d__ = _init_l_Lean_Parser_Tactic_tacticHave_x27___x3a_x3d__();
lean_mark_persistent(l_Lean_Parser_Tactic_tacticHave_x27___x3a_x3d__);
l_Lean_Parser_Tactic_tacticLet_x27__ = _init_l_Lean_Parser_Tactic_tacticLet_x27__();
lean_mark_persistent(l_Lean_Parser_Tactic_tacticLet_x27__);
l_Lean_Parser_Tactic_inductionAltLHS = _init_l_Lean_Parser_Tactic_inductionAltLHS();
lean_mark_persistent(l_Lean_Parser_Tactic_inductionAltLHS);
l_Lean_Parser_Tactic_inductionAlt = _init_l_Lean_Parser_Tactic_inductionAlt();
lean_mark_persistent(l_Lean_Parser_Tactic_inductionAlt);
l_Lean_Parser_Tactic_inductionAlts = _init_l_Lean_Parser_Tactic_inductionAlts();
lean_mark_persistent(l_Lean_Parser_Tactic_inductionAlts);
l_Lean_Parser_Tactic_elimTarget = _init_l_Lean_Parser_Tactic_elimTarget();
lean_mark_persistent(l_Lean_Parser_Tactic_elimTarget);
l_Lean_Parser_Tactic_induction = _init_l_Lean_Parser_Tactic_induction();
lean_mark_persistent(l_Lean_Parser_Tactic_induction);
l_Lean_Parser_Tactic_generalizeArg = _init_l_Lean_Parser_Tactic_generalizeArg();
lean_mark_persistent(l_Lean_Parser_Tactic_generalizeArg);
l_Lean_Parser_Tactic_generalize = _init_l_Lean_Parser_Tactic_generalize();
lean_mark_persistent(l_Lean_Parser_Tactic_generalize);
l_Lean_Parser_Tactic_cases = _init_l_Lean_Parser_Tactic_cases();
lean_mark_persistent(l_Lean_Parser_Tactic_cases);
l_Lean_Parser_Tactic_funInduction = _init_l_Lean_Parser_Tactic_funInduction();
lean_mark_persistent(l_Lean_Parser_Tactic_funInduction);
l_Lean_Parser_Tactic_funCases = _init_l_Lean_Parser_Tactic_funCases();
lean_mark_persistent(l_Lean_Parser_Tactic_funCases);
l_Lean_Parser_Tactic_renameI = _init_l_Lean_Parser_Tactic_renameI();
lean_mark_persistent(l_Lean_Parser_Tactic_renameI);
l_Lean_Parser_Tactic_tacticRepeat__ = _init_l_Lean_Parser_Tactic_tacticRepeat__();
lean_mark_persistent(l_Lean_Parser_Tactic_tacticRepeat__);
l_Lean_Parser_Tactic_repeat_x27 = _init_l_Lean_Parser_Tactic_repeat_x27();
lean_mark_persistent(l_Lean_Parser_Tactic_repeat_x27);
l_Lean_Parser_Tactic_repeat1_x27 = _init_l_Lean_Parser_Tactic_repeat1_x27();
lean_mark_persistent(l_Lean_Parser_Tactic_repeat1_x27);
l_Lean_Parser_Tactic_tacticTrivial = _init_l_Lean_Parser_Tactic_tacticTrivial();
lean_mark_persistent(l_Lean_Parser_Tactic_tacticTrivial);
l_Lean_Parser_Tactic_classical = _init_l_Lean_Parser_Tactic_classical();
lean_mark_persistent(l_Lean_Parser_Tactic_classical);
l_Lean_Parser_Tactic_split = _init_l_Lean_Parser_Tactic_split();
lean_mark_persistent(l_Lean_Parser_Tactic_split);
l_Lean_Parser_Tactic_dbgTrace = _init_l_Lean_Parser_Tactic_dbgTrace();
lean_mark_persistent(l_Lean_Parser_Tactic_dbgTrace);
l_Lean_Parser_Tactic_tacticStop__ = _init_l_Lean_Parser_Tactic_tacticStop__();
lean_mark_persistent(l_Lean_Parser_Tactic_tacticStop__);
l_Lean_Parser_Tactic_specialize = _init_l_Lean_Parser_Tactic_specialize();
lean_mark_persistent(l_Lean_Parser_Tactic_specialize);
l_Lean_Parser_Tactic_tacticUnhygienic__ = _init_l_Lean_Parser_Tactic_tacticUnhygienic__();
lean_mark_persistent(l_Lean_Parser_Tactic_tacticUnhygienic__);
l_Lean_Parser_Tactic_sleep = _init_l_Lean_Parser_Tactic_sleep();
lean_mark_persistent(l_Lean_Parser_Tactic_sleep);
l_Lean_Parser_Tactic_tacticExists___x2c_x2c = _init_l_Lean_Parser_Tactic_tacticExists___x2c_x2c();
lean_mark_persistent(l_Lean_Parser_Tactic_tacticExists___x2c_x2c);
l_Lean_Parser_Tactic_congr = _init_l_Lean_Parser_Tactic_congr();
lean_mark_persistent(l_Lean_Parser_Tactic_congr);
l_Lean_Parser_Tactic_tacDepIfThenElse = _init_l_Lean_Parser_Tactic_tacDepIfThenElse();
lean_mark_persistent(l_Lean_Parser_Tactic_tacDepIfThenElse);
l_Lean_Parser_Tactic_tacIfThenElse = _init_l_Lean_Parser_Tactic_tacIfThenElse();
lean_mark_persistent(l_Lean_Parser_Tactic_tacIfThenElse);
l_Lean_Parser_Tactic_tacticNofun = _init_l_Lean_Parser_Tactic_tacticNofun();
lean_mark_persistent(l_Lean_Parser_Tactic_tacticNofun);
l_Lean_Parser_Tactic_tacticNomatch___x2c_x2c = _init_l_Lean_Parser_Tactic_tacticNomatch___x2c_x2c();
lean_mark_persistent(l_Lean_Parser_Tactic_tacticNomatch___x2c_x2c);
l_Lean_Parser_Tactic_replace = _init_l_Lean_Parser_Tactic_replace();
lean_mark_persistent(l_Lean_Parser_Tactic_replace);
l_Lean_Parser_Tactic_tacticAnd__intros = _init_l_Lean_Parser_Tactic_tacticAnd__intros();
lean_mark_persistent(l_Lean_Parser_Tactic_tacticAnd__intros);
l_Lean_Parser_Tactic_substEqs = _init_l_Lean_Parser_Tactic_substEqs();
lean_mark_persistent(l_Lean_Parser_Tactic_substEqs);
l_Lean_Parser_Tactic_runTac = _init_l_Lean_Parser_Tactic_runTac();
lean_mark_persistent(l_Lean_Parser_Tactic_runTac);
l_Lean_Parser_Tactic_tacticHaveI__ = _init_l_Lean_Parser_Tactic_tacticHaveI__();
lean_mark_persistent(l_Lean_Parser_Tactic_tacticHaveI__);
l_Lean_Parser_Tactic_tacticLetI__ = _init_l_Lean_Parser_Tactic_tacticLetI__();
lean_mark_persistent(l_Lean_Parser_Tactic_tacticLetI__);
l_Lean_Parser_Tactic_decide = _init_l_Lean_Parser_Tactic_decide();
lean_mark_persistent(l_Lean_Parser_Tactic_decide);
l_Lean_Parser_Tactic_nativeDecide = _init_l_Lean_Parser_Tactic_nativeDecide();
lean_mark_persistent(l_Lean_Parser_Tactic_nativeDecide);
l_Lean_Parser_Tactic_omega = _init_l_Lean_Parser_Tactic_omega();
lean_mark_persistent(l_Lean_Parser_Tactic_omega);
l_Lean_Parser_Tactic_tacticBv__omega = _init_l_Lean_Parser_Tactic_tacticBv__omega();
lean_mark_persistent(l_Lean_Parser_Tactic_tacticBv__omega);
l_Lean_Parser_Tactic_acNf0 = _init_l_Lean_Parser_Tactic_acNf0();
lean_mark_persistent(l_Lean_Parser_Tactic_acNf0);
l_Lean_Parser_Tactic_normCast0 = _init_l_Lean_Parser_Tactic_normCast0();
lean_mark_persistent(l_Lean_Parser_Tactic_normCast0);
l_Lean_Parser_Tactic_tacticAssumption__mod__cast__ = _init_l_Lean_Parser_Tactic_tacticAssumption__mod__cast__();
lean_mark_persistent(l_Lean_Parser_Tactic_tacticAssumption__mod__cast__);
l_Lean_Parser_Tactic_tacticNorm__cast____ = _init_l_Lean_Parser_Tactic_tacticNorm__cast____();
lean_mark_persistent(l_Lean_Parser_Tactic_tacticNorm__cast____);
l_Lean_Parser_Tactic_pushCast = _init_l_Lean_Parser_Tactic_pushCast();
lean_mark_persistent(l_Lean_Parser_Tactic_pushCast);
l_Lean_Parser_Tactic_normCastAddElim = _init_l_Lean_Parser_Tactic_normCastAddElim();
lean_mark_persistent(l_Lean_Parser_Tactic_normCastAddElim);
l_Lean_Parser_Tactic_tacticAc__nf__ = _init_l_Lean_Parser_Tactic_tacticAc__nf__();
lean_mark_persistent(l_Lean_Parser_Tactic_tacticAc__nf__);
l_Lean_Parser_Tactic_symm = _init_l_Lean_Parser_Tactic_symm();
lean_mark_persistent(l_Lean_Parser_Tactic_symm);
l_Lean_Parser_Tactic_symmSaturate = _init_l_Lean_Parser_Tactic_symmSaturate();
lean_mark_persistent(l_Lean_Parser_Tactic_symmSaturate);
l_Lean_Parser_Tactic_SolveByElim_erase = _init_l_Lean_Parser_Tactic_SolveByElim_erase();
lean_mark_persistent(l_Lean_Parser_Tactic_SolveByElim_erase);
l_Lean_Parser_Tactic_SolveByElim_star = _init_l_Lean_Parser_Tactic_SolveByElim_star();
lean_mark_persistent(l_Lean_Parser_Tactic_SolveByElim_star);
l_Lean_Parser_Tactic_SolveByElim_arg = _init_l_Lean_Parser_Tactic_SolveByElim_arg();
lean_mark_persistent(l_Lean_Parser_Tactic_SolveByElim_arg);
l_Lean_Parser_Tactic_SolveByElim_args = _init_l_Lean_Parser_Tactic_SolveByElim_args();
lean_mark_persistent(l_Lean_Parser_Tactic_SolveByElim_args);
l_Lean_Parser_Tactic_SolveByElim_using__ = _init_l_Lean_Parser_Tactic_SolveByElim_using__();
lean_mark_persistent(l_Lean_Parser_Tactic_SolveByElim_using__);
l_Lean_Parser_Tactic_solveByElim = _init_l_Lean_Parser_Tactic_solveByElim();
lean_mark_persistent(l_Lean_Parser_Tactic_solveByElim);
l_Lean_Parser_Tactic_applyAssumption = _init_l_Lean_Parser_Tactic_applyAssumption();
lean_mark_persistent(l_Lean_Parser_Tactic_applyAssumption);
l_Lean_Parser_Tactic_applyRules = _init_l_Lean_Parser_Tactic_applyRules();
lean_mark_persistent(l_Lean_Parser_Tactic_applyRules);
l_Lean_Parser_Tactic_exact_x3f = _init_l_Lean_Parser_Tactic_exact_x3f();
lean_mark_persistent(l_Lean_Parser_Tactic_exact_x3f);
l_Lean_Parser_Tactic_apply_x3f = _init_l_Lean_Parser_Tactic_apply_x3f();
lean_mark_persistent(l_Lean_Parser_Tactic_apply_x3f);
l_Lean_Parser_Tactic_rewrites__forbidden = _init_l_Lean_Parser_Tactic_rewrites__forbidden();
lean_mark_persistent(l_Lean_Parser_Tactic_rewrites__forbidden);
l_Lean_Parser_Tactic_rewrites_x3f = _init_l_Lean_Parser_Tactic_rewrites_x3f();
lean_mark_persistent(l_Lean_Parser_Tactic_rewrites_x3f);
l_Lean_Parser_Tactic_showTerm = _init_l_Lean_Parser_Tactic_showTerm();
lean_mark_persistent(l_Lean_Parser_Tactic_showTerm);
l_Lean_Parser_Tactic_showTermElab = _init_l_Lean_Parser_Tactic_showTermElab();
lean_mark_persistent(l_Lean_Parser_Tactic_showTermElab);
l_Lean_Parser_Tactic_by_x3f = _init_l_Lean_Parser_Tactic_by_x3f();
lean_mark_persistent(l_Lean_Parser_Tactic_by_x3f);
l_Lean_Parser_Tactic_exposeNames = _init_l_Lean_Parser_Tactic_exposeNames();
lean_mark_persistent(l_Lean_Parser_Tactic_exposeNames);
l_Lean_Parser_Tactic_suggestPremises = _init_l_Lean_Parser_Tactic_suggestPremises();
lean_mark_persistent(l_Lean_Parser_Tactic_suggestPremises);
l_Lean_Parser_Tactic_bvDecideMacro = _init_l_Lean_Parser_Tactic_bvDecideMacro();
lean_mark_persistent(l_Lean_Parser_Tactic_bvDecideMacro);
l_Lean_Parser_Tactic_bvTraceMacro = _init_l_Lean_Parser_Tactic_bvTraceMacro();
lean_mark_persistent(l_Lean_Parser_Tactic_bvTraceMacro);
l_Lean_Parser_Tactic_bvNormalizeMacro = _init_l_Lean_Parser_Tactic_bvNormalizeMacro();
lean_mark_persistent(l_Lean_Parser_Tactic_bvNormalizeMacro);
l_Lean_Parser_Attr_simp = _init_l_Lean_Parser_Attr_simp();
lean_mark_persistent(l_Lean_Parser_Attr_simp);
l_Lean_Parser_Attr_wf__preprocess = _init_l_Lean_Parser_Attr_wf__preprocess();
lean_mark_persistent(l_Lean_Parser_Attr_wf__preprocess);
l_Lean_Parser_Attr_normCastLabel = _init_l_Lean_Parser_Attr_normCastLabel();
lean_mark_persistent(l_Lean_Parser_Attr_normCastLabel);
l_Lean_Parser_Attr_norm__cast = _init_l_Lean_Parser_Attr_norm__cast();
lean_mark_persistent(l_Lean_Parser_Attr_norm__cast);
l_term_u2039___u203a = _init_l_term_u2039___u203a();
lean_mark_persistent(l_term_u2039___u203a);
l_tacticGet__elem__tactic__trivial = _init_l_tacticGet__elem__tactic__trivial();
lean_mark_persistent(l_tacticGet__elem__tactic__trivial);
l_tacticGet__elem__tactic = _init_l_tacticGet__elem__tactic();
lean_mark_persistent(l_tacticGet__elem__tactic);
l_Lean_Parser_Syntax_exact_x3f = _init_l_Lean_Parser_Syntax_exact_x3f();
lean_mark_persistent(l_Lean_Parser_Syntax_exact_x3f);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
