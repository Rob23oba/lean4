// Lean compiler output
// Module: Lean.Elab.Deriving.Repr
// Imports: Lean.Meta.Transform Lean.Meta.Inductive Lean.Elab.Deriving.Basic Lean.Elab.Deriving.Util
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
LEAN_EXPORT lean_object* l_Lean_isInductive___at___Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkReprInstanceHandler(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1_spec__0(size_t, size_t, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Deriving_mkInstanceCmds(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Deriving_mkDiscrs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkMutualBlock_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Deriving_mkLocalInstanceLetDecls(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_List_head_x21(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__0___boxed(lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Lean_getStructureFields(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_isTracingEnabledFor___at___Lean_Elab_Term_traceAtCmdPos_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkMutualBlock___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_registerDerivingHandler(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkMutualBlock_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Deriving_mkLet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getConstInfo___at___Lean_getConstInfoInduct___at___Lean_Elab_Deriving_mkContext_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Meta_isType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkStrLit(lean_object*, lean_object*);
lean_object* l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__4(size_t, size_t, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkMutualBlock(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at___Lean_Elab_Term_traceAtCmdPos_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Deriving_mkHeader(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInductive___at___Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInductive___at___Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Deriving_mkContext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2_spec__2___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_syntax_ident(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkReprInstanceHandler___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2_spec__2___redArg___lam__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForInduct(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkBody(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkMutualBlock_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Environment_mainModule(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__4___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_BinderInfo_isExplicit(uint8_t);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkSepArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append(lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_FVarId_getBinderInfo___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isStructure(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_initFn____x40_Lean_Elab_Deriving_Repr___hyg_3567_(lean_object*);
lean_object* l_Lean_Elab_Command_liftTermElabM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
extern lean_object* l_Lean_instInhabitedInductiveVal;
uint8_t l_Lean_isInductiveCore(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Command_elabCommand_go_spec__14(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkMutualBlock_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInductive___at___Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkReprHeader(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_____private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__0(lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___at___Lean_Elab_Deriving_mkInductArgNames_spec__1___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_toSubstring_x27(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForStruct(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkNumLit(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Range_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkReprHeader(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_mk_string_unchecked("Repr", 4, 4);
x_10 = l_Lean_Name_mkStr1(x_9);
x_11 = lean_unsigned_to_nat(1u);
lean_inc(x_7);
lean_inc(x_6);
x_12 = l_Lean_Elab_Deriving_mkHeader(x_10, x_11, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
x_16 = lean_st_ref_get(x_7, x_15);
lean_dec(x_7);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_6, 5);
lean_inc(x_19);
x_20 = lean_box(0);
x_21 = lean_unbox(x_20);
x_22 = l_Lean_SourceInfo_fromRef(x_19, x_21);
lean_dec(x_19);
x_23 = lean_ctor_get(x_6, 10);
lean_inc(x_23);
lean_dec(x_6);
x_24 = lean_ctor_get(x_18, 0);
lean_inc(x_24);
lean_dec(x_18);
x_25 = l_Lean_Environment_mainModule(x_24);
lean_dec(x_24);
x_26 = lean_mk_string_unchecked("Lean", 4, 4);
x_27 = lean_mk_string_unchecked("Parser", 6, 6);
x_28 = lean_mk_string_unchecked("Term", 4, 4);
x_29 = lean_mk_string_unchecked("explicitBinder", 14, 14);
lean_inc(x_26);
x_30 = l_Lean_Name_mkStr4(x_26, x_27, x_28, x_29);
x_31 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_22);
lean_ctor_set_tag(x_12, 2);
lean_ctor_set(x_12, 1, x_31);
lean_ctor_set(x_12, 0, x_22);
x_32 = lean_mk_string_unchecked("null", 4, 4);
x_33 = l_Lean_Name_mkStr1(x_32);
x_34 = lean_mk_string_unchecked("prec", 4, 4);
lean_inc(x_34);
x_35 = l_String_toSubstring_x27(x_34);
x_36 = l_Lean_Name_mkStr1(x_34);
lean_inc(x_23);
lean_inc(x_25);
x_37 = l_Lean_addMacroScope(x_25, x_36, x_23);
x_38 = lean_box(0);
lean_inc(x_22);
x_39 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_39, 0, x_22);
lean_ctor_set(x_39, 1, x_35);
lean_ctor_set(x_39, 2, x_37);
lean_ctor_set(x_39, 3, x_38);
lean_inc(x_33);
lean_inc(x_22);
x_40 = l_Lean_Syntax_node1(x_22, x_33, x_39);
x_41 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_22);
x_42 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_42, 0, x_22);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_mk_string_unchecked("Nat", 3, 3);
lean_inc(x_43);
x_44 = l_String_toSubstring_x27(x_43);
lean_inc(x_43);
x_45 = l_Lean_Name_mkStr1(x_43);
lean_inc(x_45);
x_46 = l_Lean_addMacroScope(x_25, x_45, x_23);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_45);
lean_ctor_set(x_48, 1, x_47);
x_49 = l_Lean_Name_mkStr2(x_26, x_43);
x_50 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_50, 0, x_49);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_38);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_48);
lean_ctor_set(x_52, 1, x_51);
lean_inc(x_22);
x_53 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_53, 0, x_22);
lean_ctor_set(x_53, 1, x_44);
lean_ctor_set(x_53, 2, x_46);
lean_ctor_set(x_53, 3, x_52);
lean_inc(x_33);
lean_inc(x_22);
x_54 = l_Lean_Syntax_node2(x_22, x_33, x_42, x_53);
x_55 = l_Array_mkArray0(lean_box(0));
lean_inc(x_22);
x_56 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_56, 0, x_22);
lean_ctor_set(x_56, 1, x_33);
lean_ctor_set(x_56, 2, x_55);
x_57 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_22);
x_58 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_58, 0, x_22);
lean_ctor_set(x_58, 1, x_57);
x_59 = lean_ctor_get(x_14, 0);
lean_inc(x_59);
x_60 = l_Lean_Syntax_node5(x_22, x_30, x_12, x_40, x_54, x_56, x_58);
x_61 = lean_array_push(x_59, x_60);
x_62 = lean_ctor_get(x_14, 1);
lean_inc(x_62);
x_63 = lean_ctor_get(x_14, 2);
lean_inc(x_63);
x_64 = lean_ctor_get(x_14, 3);
lean_inc(x_64);
lean_dec(x_14);
x_65 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_65, 0, x_61);
lean_ctor_set(x_65, 1, x_62);
lean_ctor_set(x_65, 2, x_63);
lean_ctor_set(x_65, 3, x_64);
lean_ctor_set(x_16, 0, x_65);
return x_16;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_66 = lean_ctor_get(x_16, 0);
x_67 = lean_ctor_get(x_16, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_16);
x_68 = lean_ctor_get(x_6, 5);
lean_inc(x_68);
x_69 = lean_box(0);
x_70 = lean_unbox(x_69);
x_71 = l_Lean_SourceInfo_fromRef(x_68, x_70);
lean_dec(x_68);
x_72 = lean_ctor_get(x_6, 10);
lean_inc(x_72);
lean_dec(x_6);
x_73 = lean_ctor_get(x_66, 0);
lean_inc(x_73);
lean_dec(x_66);
x_74 = l_Lean_Environment_mainModule(x_73);
lean_dec(x_73);
x_75 = lean_mk_string_unchecked("Lean", 4, 4);
x_76 = lean_mk_string_unchecked("Parser", 6, 6);
x_77 = lean_mk_string_unchecked("Term", 4, 4);
x_78 = lean_mk_string_unchecked("explicitBinder", 14, 14);
lean_inc(x_75);
x_79 = l_Lean_Name_mkStr4(x_75, x_76, x_77, x_78);
x_80 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_71);
lean_ctor_set_tag(x_12, 2);
lean_ctor_set(x_12, 1, x_80);
lean_ctor_set(x_12, 0, x_71);
x_81 = lean_mk_string_unchecked("null", 4, 4);
x_82 = l_Lean_Name_mkStr1(x_81);
x_83 = lean_mk_string_unchecked("prec", 4, 4);
lean_inc(x_83);
x_84 = l_String_toSubstring_x27(x_83);
x_85 = l_Lean_Name_mkStr1(x_83);
lean_inc(x_72);
lean_inc(x_74);
x_86 = l_Lean_addMacroScope(x_74, x_85, x_72);
x_87 = lean_box(0);
lean_inc(x_71);
x_88 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_88, 0, x_71);
lean_ctor_set(x_88, 1, x_84);
lean_ctor_set(x_88, 2, x_86);
lean_ctor_set(x_88, 3, x_87);
lean_inc(x_82);
lean_inc(x_71);
x_89 = l_Lean_Syntax_node1(x_71, x_82, x_88);
x_90 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_71);
x_91 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_91, 0, x_71);
lean_ctor_set(x_91, 1, x_90);
x_92 = lean_mk_string_unchecked("Nat", 3, 3);
lean_inc(x_92);
x_93 = l_String_toSubstring_x27(x_92);
lean_inc(x_92);
x_94 = l_Lean_Name_mkStr1(x_92);
lean_inc(x_94);
x_95 = l_Lean_addMacroScope(x_74, x_94, x_72);
x_96 = lean_box(0);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_94);
lean_ctor_set(x_97, 1, x_96);
x_98 = l_Lean_Name_mkStr2(x_75, x_92);
x_99 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_99, 0, x_98);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_87);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_97);
lean_ctor_set(x_101, 1, x_100);
lean_inc(x_71);
x_102 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_102, 0, x_71);
lean_ctor_set(x_102, 1, x_93);
lean_ctor_set(x_102, 2, x_95);
lean_ctor_set(x_102, 3, x_101);
lean_inc(x_82);
lean_inc(x_71);
x_103 = l_Lean_Syntax_node2(x_71, x_82, x_91, x_102);
x_104 = l_Array_mkArray0(lean_box(0));
lean_inc(x_71);
x_105 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_105, 0, x_71);
lean_ctor_set(x_105, 1, x_82);
lean_ctor_set(x_105, 2, x_104);
x_106 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_71);
x_107 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_107, 0, x_71);
lean_ctor_set(x_107, 1, x_106);
x_108 = lean_ctor_get(x_14, 0);
lean_inc(x_108);
x_109 = l_Lean_Syntax_node5(x_71, x_79, x_12, x_89, x_103, x_105, x_107);
x_110 = lean_array_push(x_108, x_109);
x_111 = lean_ctor_get(x_14, 1);
lean_inc(x_111);
x_112 = lean_ctor_get(x_14, 2);
lean_inc(x_112);
x_113 = lean_ctor_get(x_14, 3);
lean_inc(x_113);
lean_dec(x_14);
x_114 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_114, 0, x_110);
lean_ctor_set(x_114, 1, x_111);
lean_ctor_set(x_114, 2, x_112);
lean_ctor_set(x_114, 3, x_113);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_67);
return x_115;
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_116 = lean_ctor_get(x_12, 0);
x_117 = lean_ctor_get(x_12, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_12);
x_118 = lean_st_ref_get(x_7, x_117);
lean_dec(x_7);
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_118, 1);
lean_inc(x_120);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 x_121 = x_118;
} else {
 lean_dec_ref(x_118);
 x_121 = lean_box(0);
}
x_122 = lean_ctor_get(x_6, 5);
lean_inc(x_122);
x_123 = lean_box(0);
x_124 = lean_unbox(x_123);
x_125 = l_Lean_SourceInfo_fromRef(x_122, x_124);
lean_dec(x_122);
x_126 = lean_ctor_get(x_6, 10);
lean_inc(x_126);
lean_dec(x_6);
x_127 = lean_ctor_get(x_119, 0);
lean_inc(x_127);
lean_dec(x_119);
x_128 = l_Lean_Environment_mainModule(x_127);
lean_dec(x_127);
x_129 = lean_mk_string_unchecked("Lean", 4, 4);
x_130 = lean_mk_string_unchecked("Parser", 6, 6);
x_131 = lean_mk_string_unchecked("Term", 4, 4);
x_132 = lean_mk_string_unchecked("explicitBinder", 14, 14);
lean_inc(x_129);
x_133 = l_Lean_Name_mkStr4(x_129, x_130, x_131, x_132);
x_134 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_125);
x_135 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_135, 0, x_125);
lean_ctor_set(x_135, 1, x_134);
x_136 = lean_mk_string_unchecked("null", 4, 4);
x_137 = l_Lean_Name_mkStr1(x_136);
x_138 = lean_mk_string_unchecked("prec", 4, 4);
lean_inc(x_138);
x_139 = l_String_toSubstring_x27(x_138);
x_140 = l_Lean_Name_mkStr1(x_138);
lean_inc(x_126);
lean_inc(x_128);
x_141 = l_Lean_addMacroScope(x_128, x_140, x_126);
x_142 = lean_box(0);
lean_inc(x_125);
x_143 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_143, 0, x_125);
lean_ctor_set(x_143, 1, x_139);
lean_ctor_set(x_143, 2, x_141);
lean_ctor_set(x_143, 3, x_142);
lean_inc(x_137);
lean_inc(x_125);
x_144 = l_Lean_Syntax_node1(x_125, x_137, x_143);
x_145 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_125);
x_146 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_146, 0, x_125);
lean_ctor_set(x_146, 1, x_145);
x_147 = lean_mk_string_unchecked("Nat", 3, 3);
lean_inc(x_147);
x_148 = l_String_toSubstring_x27(x_147);
lean_inc(x_147);
x_149 = l_Lean_Name_mkStr1(x_147);
lean_inc(x_149);
x_150 = l_Lean_addMacroScope(x_128, x_149, x_126);
x_151 = lean_box(0);
x_152 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_152, 0, x_149);
lean_ctor_set(x_152, 1, x_151);
x_153 = l_Lean_Name_mkStr2(x_129, x_147);
x_154 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_154, 0, x_153);
x_155 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_155, 1, x_142);
x_156 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_156, 0, x_152);
lean_ctor_set(x_156, 1, x_155);
lean_inc(x_125);
x_157 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_157, 0, x_125);
lean_ctor_set(x_157, 1, x_148);
lean_ctor_set(x_157, 2, x_150);
lean_ctor_set(x_157, 3, x_156);
lean_inc(x_137);
lean_inc(x_125);
x_158 = l_Lean_Syntax_node2(x_125, x_137, x_146, x_157);
x_159 = l_Array_mkArray0(lean_box(0));
lean_inc(x_125);
x_160 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_160, 0, x_125);
lean_ctor_set(x_160, 1, x_137);
lean_ctor_set(x_160, 2, x_159);
x_161 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_125);
x_162 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_162, 0, x_125);
lean_ctor_set(x_162, 1, x_161);
x_163 = lean_ctor_get(x_116, 0);
lean_inc(x_163);
x_164 = l_Lean_Syntax_node5(x_125, x_133, x_135, x_144, x_158, x_160, x_162);
x_165 = lean_array_push(x_163, x_164);
x_166 = lean_ctor_get(x_116, 1);
lean_inc(x_166);
x_167 = lean_ctor_get(x_116, 2);
lean_inc(x_167);
x_168 = lean_ctor_get(x_116, 3);
lean_inc(x_168);
lean_dec(x_116);
x_169 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_169, 0, x_165);
lean_ctor_set(x_169, 1, x_166);
lean_ctor_set(x_169, 2, x_167);
lean_ctor_set(x_169, 3, x_168);
if (lean_is_scalar(x_121)) {
 x_170 = lean_alloc_ctor(0, 2, 0);
} else {
 x_170 = x_121;
}
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_120);
return x_170;
}
}
else
{
lean_dec(x_7);
lean_dec(x_6);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_2);
lean_inc(x_1);
x_9 = l_Lean_getConstInfo___at___Lean_getConstInfoInduct___at___Lean_Elab_Deriving_mkContext_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 6)
{
uint8_t x_11; 
lean_dec(x_2);
lean_dec(x_1);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_9, 0);
lean_dec(x_12);
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
lean_ctor_set(x_9, 0, x_13);
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_dec(x_9);
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_10);
x_17 = lean_ctor_get(x_9, 1);
lean_inc(x_17);
lean_dec(x_9);
x_18 = lean_mk_string_unchecked("'", 1, 1);
x_19 = l_Lean_stringToMessageData(x_18);
lean_dec(x_18);
x_20 = lean_box(0);
x_21 = lean_unbox(x_20);
x_22 = l_Lean_MessageData_ofConstName(x_1, x_21);
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_19);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_mk_string_unchecked("' is not a constructor", 22, 22);
x_25 = l_Lean_stringToMessageData(x_24);
lean_dec(x_24);
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_26, x_2, x_3, x_4, x_5, x_6, x_7, x_17);
return x_27;
}
}
else
{
uint8_t x_28; 
lean_dec(x_2);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_9);
if (x_28 == 0)
{
return x_9;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_9, 0);
x_30 = lean_ctor_get(x_9, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_9);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_Range_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_5, 5);
lean_inc(x_8);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_box(0);
x_10 = lean_unbox(x_9);
x_11 = l_Lean_SourceInfo_fromRef(x_1, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_8);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_5, 1);
x_22 = lean_nat_dec_lt(x_7, x_21);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_6);
lean_ctor_set(x_23, 1, x_14);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; uint8_t x_329; 
x_24 = lean_box(0);
x_25 = lean_ctor_get(x_4, 2);
x_26 = lean_alloc_closure((void*)(l_Std_Range_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__0___boxed), 1, 0);
x_27 = lean_ctor_get(x_2, 1);
x_28 = l_Lean_instInhabitedExpr;
x_29 = lean_unsigned_to_nat(0u);
x_30 = lean_array_get(x_24, x_25, x_29);
x_31 = lean_array_fget(x_1, x_7);
lean_inc(x_31);
x_32 = l_Lean_Name_toString(x_31, x_22, x_26);
x_33 = lean_box(2);
x_313 = lean_nat_add(x_27, x_7);
x_314 = lean_array_get(x_28, x_3, x_313);
lean_dec(x_313);
x_329 = lean_nat_dec_eq(x_7, x_29);
if (x_329 == 0)
{
lean_object* x_330; uint8_t x_331; 
x_330 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1(x_8, x_9, x_10, x_11, x_12, x_13, x_14);
x_331 = !lean_is_exclusive(x_330);
if (x_331 == 0)
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; uint8_t x_335; 
x_332 = lean_ctor_get(x_330, 0);
x_333 = lean_ctor_get(x_330, 1);
x_334 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__2(x_332, x_8, x_9, x_10, x_11, x_12, x_13, x_333);
lean_dec(x_332);
x_335 = !lean_is_exclusive(x_334);
if (x_335 == 0)
{
lean_object* x_336; lean_object* x_337; lean_object* x_338; uint8_t x_339; 
x_336 = lean_ctor_get(x_334, 0);
x_337 = lean_ctor_get(x_334, 1);
x_338 = lean_st_ref_get(x_13, x_337);
x_339 = !lean_is_exclusive(x_338);
if (x_339 == 0)
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; 
x_340 = lean_ctor_get(x_338, 0);
x_341 = lean_ctor_get(x_338, 1);
x_342 = lean_ctor_get(x_12, 10);
lean_inc(x_342);
x_343 = lean_ctor_get(x_340, 0);
lean_inc(x_343);
lean_dec(x_340);
x_344 = l_Lean_Environment_mainModule(x_343);
lean_dec(x_343);
x_345 = lean_mk_string_unchecked("term_++_", 8, 8);
x_346 = l_Lean_Name_mkStr1(x_345);
x_347 = lean_mk_string_unchecked("++", 2, 2);
lean_inc(x_336);
lean_ctor_set_tag(x_338, 2);
lean_ctor_set(x_338, 1, x_347);
lean_ctor_set(x_338, 0, x_336);
x_348 = lean_mk_string_unchecked("str", 3, 3);
x_349 = l_Lean_Name_mkStr1(x_348);
x_350 = lean_mk_string_unchecked("\",\"", 3, 3);
lean_inc(x_336);
lean_ctor_set_tag(x_334, 2);
lean_ctor_set(x_334, 1, x_350);
lean_inc(x_336);
x_351 = l_Lean_Syntax_node1(x_336, x_349, x_334);
lean_inc(x_338);
lean_inc(x_346);
lean_inc(x_336);
x_352 = l_Lean_Syntax_node3(x_336, x_346, x_6, x_338, x_351);
x_353 = lean_mk_string_unchecked("Format.line", 11, 11);
x_354 = l_String_toSubstring_x27(x_353);
x_355 = lean_mk_string_unchecked("Format", 6, 6);
x_356 = lean_mk_string_unchecked("line", 4, 4);
lean_inc(x_356);
lean_inc(x_355);
x_357 = l_Lean_Name_mkStr2(x_355, x_356);
x_358 = l_Lean_addMacroScope(x_344, x_357, x_342);
x_359 = lean_mk_string_unchecked("Std", 3, 3);
x_360 = l_Lean_Name_mkStr3(x_359, x_355, x_356);
x_361 = lean_box(0);
lean_inc(x_360);
lean_ctor_set_tag(x_330, 1);
lean_ctor_set(x_330, 1, x_361);
lean_ctor_set(x_330, 0, x_360);
x_362 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_362, 0, x_360);
x_363 = lean_box(0);
x_364 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_364, 0, x_362);
lean_ctor_set(x_364, 1, x_363);
x_365 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_365, 0, x_330);
lean_ctor_set(x_365, 1, x_364);
lean_inc(x_336);
x_366 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_366, 0, x_336);
lean_ctor_set(x_366, 1, x_354);
lean_ctor_set(x_366, 2, x_358);
lean_ctor_set(x_366, 3, x_365);
x_367 = l_Lean_Syntax_node3(x_336, x_346, x_352, x_338, x_366);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_315 = x_367;
x_316 = x_8;
x_317 = x_9;
x_318 = x_10;
x_319 = x_11;
x_320 = x_12;
x_321 = x_13;
x_322 = x_341;
goto block_328;
}
else
{
lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; 
x_368 = lean_ctor_get(x_338, 0);
x_369 = lean_ctor_get(x_338, 1);
lean_inc(x_369);
lean_inc(x_368);
lean_dec(x_338);
x_370 = lean_ctor_get(x_12, 10);
lean_inc(x_370);
x_371 = lean_ctor_get(x_368, 0);
lean_inc(x_371);
lean_dec(x_368);
x_372 = l_Lean_Environment_mainModule(x_371);
lean_dec(x_371);
x_373 = lean_mk_string_unchecked("term_++_", 8, 8);
x_374 = l_Lean_Name_mkStr1(x_373);
x_375 = lean_mk_string_unchecked("++", 2, 2);
lean_inc(x_336);
x_376 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_376, 0, x_336);
lean_ctor_set(x_376, 1, x_375);
x_377 = lean_mk_string_unchecked("str", 3, 3);
x_378 = l_Lean_Name_mkStr1(x_377);
x_379 = lean_mk_string_unchecked("\",\"", 3, 3);
lean_inc(x_336);
lean_ctor_set_tag(x_334, 2);
lean_ctor_set(x_334, 1, x_379);
lean_inc(x_336);
x_380 = l_Lean_Syntax_node1(x_336, x_378, x_334);
lean_inc(x_376);
lean_inc(x_374);
lean_inc(x_336);
x_381 = l_Lean_Syntax_node3(x_336, x_374, x_6, x_376, x_380);
x_382 = lean_mk_string_unchecked("Format.line", 11, 11);
x_383 = l_String_toSubstring_x27(x_382);
x_384 = lean_mk_string_unchecked("Format", 6, 6);
x_385 = lean_mk_string_unchecked("line", 4, 4);
lean_inc(x_385);
lean_inc(x_384);
x_386 = l_Lean_Name_mkStr2(x_384, x_385);
x_387 = l_Lean_addMacroScope(x_372, x_386, x_370);
x_388 = lean_mk_string_unchecked("Std", 3, 3);
x_389 = l_Lean_Name_mkStr3(x_388, x_384, x_385);
x_390 = lean_box(0);
lean_inc(x_389);
lean_ctor_set_tag(x_330, 1);
lean_ctor_set(x_330, 1, x_390);
lean_ctor_set(x_330, 0, x_389);
x_391 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_391, 0, x_389);
x_392 = lean_box(0);
x_393 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_393, 0, x_391);
lean_ctor_set(x_393, 1, x_392);
x_394 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_394, 0, x_330);
lean_ctor_set(x_394, 1, x_393);
lean_inc(x_336);
x_395 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_395, 0, x_336);
lean_ctor_set(x_395, 1, x_383);
lean_ctor_set(x_395, 2, x_387);
lean_ctor_set(x_395, 3, x_394);
x_396 = l_Lean_Syntax_node3(x_336, x_374, x_381, x_376, x_395);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_315 = x_396;
x_316 = x_8;
x_317 = x_9;
x_318 = x_10;
x_319 = x_11;
x_320 = x_12;
x_321 = x_13;
x_322 = x_369;
goto block_328;
}
}
else
{
lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; 
x_397 = lean_ctor_get(x_334, 0);
x_398 = lean_ctor_get(x_334, 1);
lean_inc(x_398);
lean_inc(x_397);
lean_dec(x_334);
x_399 = lean_st_ref_get(x_13, x_398);
x_400 = lean_ctor_get(x_399, 0);
lean_inc(x_400);
x_401 = lean_ctor_get(x_399, 1);
lean_inc(x_401);
if (lean_is_exclusive(x_399)) {
 lean_ctor_release(x_399, 0);
 lean_ctor_release(x_399, 1);
 x_402 = x_399;
} else {
 lean_dec_ref(x_399);
 x_402 = lean_box(0);
}
x_403 = lean_ctor_get(x_12, 10);
lean_inc(x_403);
x_404 = lean_ctor_get(x_400, 0);
lean_inc(x_404);
lean_dec(x_400);
x_405 = l_Lean_Environment_mainModule(x_404);
lean_dec(x_404);
x_406 = lean_mk_string_unchecked("term_++_", 8, 8);
x_407 = l_Lean_Name_mkStr1(x_406);
x_408 = lean_mk_string_unchecked("++", 2, 2);
lean_inc(x_397);
if (lean_is_scalar(x_402)) {
 x_409 = lean_alloc_ctor(2, 2, 0);
} else {
 x_409 = x_402;
 lean_ctor_set_tag(x_409, 2);
}
lean_ctor_set(x_409, 0, x_397);
lean_ctor_set(x_409, 1, x_408);
x_410 = lean_mk_string_unchecked("str", 3, 3);
x_411 = l_Lean_Name_mkStr1(x_410);
x_412 = lean_mk_string_unchecked("\",\"", 3, 3);
lean_inc(x_397);
x_413 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_413, 0, x_397);
lean_ctor_set(x_413, 1, x_412);
lean_inc(x_397);
x_414 = l_Lean_Syntax_node1(x_397, x_411, x_413);
lean_inc(x_409);
lean_inc(x_407);
lean_inc(x_397);
x_415 = l_Lean_Syntax_node3(x_397, x_407, x_6, x_409, x_414);
x_416 = lean_mk_string_unchecked("Format.line", 11, 11);
x_417 = l_String_toSubstring_x27(x_416);
x_418 = lean_mk_string_unchecked("Format", 6, 6);
x_419 = lean_mk_string_unchecked("line", 4, 4);
lean_inc(x_419);
lean_inc(x_418);
x_420 = l_Lean_Name_mkStr2(x_418, x_419);
x_421 = l_Lean_addMacroScope(x_405, x_420, x_403);
x_422 = lean_mk_string_unchecked("Std", 3, 3);
x_423 = l_Lean_Name_mkStr3(x_422, x_418, x_419);
x_424 = lean_box(0);
lean_inc(x_423);
lean_ctor_set_tag(x_330, 1);
lean_ctor_set(x_330, 1, x_424);
lean_ctor_set(x_330, 0, x_423);
x_425 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_425, 0, x_423);
x_426 = lean_box(0);
x_427 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_427, 0, x_425);
lean_ctor_set(x_427, 1, x_426);
x_428 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_428, 0, x_330);
lean_ctor_set(x_428, 1, x_427);
lean_inc(x_397);
x_429 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_429, 0, x_397);
lean_ctor_set(x_429, 1, x_417);
lean_ctor_set(x_429, 2, x_421);
lean_ctor_set(x_429, 3, x_428);
x_430 = l_Lean_Syntax_node3(x_397, x_407, x_415, x_409, x_429);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_315 = x_430;
x_316 = x_8;
x_317 = x_9;
x_318 = x_10;
x_319 = x_11;
x_320 = x_12;
x_321 = x_13;
x_322 = x_401;
goto block_328;
}
}
else
{
lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; 
x_431 = lean_ctor_get(x_330, 0);
x_432 = lean_ctor_get(x_330, 1);
lean_inc(x_432);
lean_inc(x_431);
lean_dec(x_330);
x_433 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__2(x_431, x_8, x_9, x_10, x_11, x_12, x_13, x_432);
lean_dec(x_431);
x_434 = lean_ctor_get(x_433, 0);
lean_inc(x_434);
x_435 = lean_ctor_get(x_433, 1);
lean_inc(x_435);
if (lean_is_exclusive(x_433)) {
 lean_ctor_release(x_433, 0);
 lean_ctor_release(x_433, 1);
 x_436 = x_433;
} else {
 lean_dec_ref(x_433);
 x_436 = lean_box(0);
}
x_437 = lean_st_ref_get(x_13, x_435);
x_438 = lean_ctor_get(x_437, 0);
lean_inc(x_438);
x_439 = lean_ctor_get(x_437, 1);
lean_inc(x_439);
if (lean_is_exclusive(x_437)) {
 lean_ctor_release(x_437, 0);
 lean_ctor_release(x_437, 1);
 x_440 = x_437;
} else {
 lean_dec_ref(x_437);
 x_440 = lean_box(0);
}
x_441 = lean_ctor_get(x_12, 10);
lean_inc(x_441);
x_442 = lean_ctor_get(x_438, 0);
lean_inc(x_442);
lean_dec(x_438);
x_443 = l_Lean_Environment_mainModule(x_442);
lean_dec(x_442);
x_444 = lean_mk_string_unchecked("term_++_", 8, 8);
x_445 = l_Lean_Name_mkStr1(x_444);
x_446 = lean_mk_string_unchecked("++", 2, 2);
lean_inc(x_434);
if (lean_is_scalar(x_440)) {
 x_447 = lean_alloc_ctor(2, 2, 0);
} else {
 x_447 = x_440;
 lean_ctor_set_tag(x_447, 2);
}
lean_ctor_set(x_447, 0, x_434);
lean_ctor_set(x_447, 1, x_446);
x_448 = lean_mk_string_unchecked("str", 3, 3);
x_449 = l_Lean_Name_mkStr1(x_448);
x_450 = lean_mk_string_unchecked("\",\"", 3, 3);
lean_inc(x_434);
if (lean_is_scalar(x_436)) {
 x_451 = lean_alloc_ctor(2, 2, 0);
} else {
 x_451 = x_436;
 lean_ctor_set_tag(x_451, 2);
}
lean_ctor_set(x_451, 0, x_434);
lean_ctor_set(x_451, 1, x_450);
lean_inc(x_434);
x_452 = l_Lean_Syntax_node1(x_434, x_449, x_451);
lean_inc(x_447);
lean_inc(x_445);
lean_inc(x_434);
x_453 = l_Lean_Syntax_node3(x_434, x_445, x_6, x_447, x_452);
x_454 = lean_mk_string_unchecked("Format.line", 11, 11);
x_455 = l_String_toSubstring_x27(x_454);
x_456 = lean_mk_string_unchecked("Format", 6, 6);
x_457 = lean_mk_string_unchecked("line", 4, 4);
lean_inc(x_457);
lean_inc(x_456);
x_458 = l_Lean_Name_mkStr2(x_456, x_457);
x_459 = l_Lean_addMacroScope(x_443, x_458, x_441);
x_460 = lean_mk_string_unchecked("Std", 3, 3);
x_461 = l_Lean_Name_mkStr3(x_460, x_456, x_457);
x_462 = lean_box(0);
lean_inc(x_461);
x_463 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_463, 0, x_461);
lean_ctor_set(x_463, 1, x_462);
x_464 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_464, 0, x_461);
x_465 = lean_box(0);
x_466 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_466, 0, x_464);
lean_ctor_set(x_466, 1, x_465);
x_467 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_467, 0, x_463);
lean_ctor_set(x_467, 1, x_466);
lean_inc(x_434);
x_468 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_468, 0, x_434);
lean_ctor_set(x_468, 1, x_455);
lean_ctor_set(x_468, 2, x_459);
lean_ctor_set(x_468, 3, x_467);
x_469 = l_Lean_Syntax_node3(x_434, x_445, x_453, x_447, x_468);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_315 = x_469;
x_316 = x_8;
x_317 = x_9;
x_318 = x_10;
x_319 = x_11;
x_320 = x_12;
x_321 = x_13;
x_322 = x_439;
goto block_328;
}
}
else
{
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_315 = x_6;
x_316 = x_8;
x_317 = x_9;
x_318 = x_10;
x_319 = x_11;
x_320 = x_12;
x_321 = x_13;
x_322 = x_14;
goto block_328;
}
block_312:
{
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_unbox(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
lean_dec(x_37);
lean_dec(x_34);
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_dec(x_41);
x_45 = lean_string_length(x_32);
x_46 = lean_unsigned_to_nat(4u);
x_47 = lean_st_ref_get(x_38, x_44);
lean_dec(x_38);
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_49 = lean_ctor_get(x_47, 0);
x_50 = lean_ctor_get(x_47, 1);
x_51 = lean_nat_add(x_45, x_46);
lean_dec(x_45);
x_52 = l___private_Init_Data_Repr_0__Nat_reprFast(x_51);
x_53 = lean_ctor_get(x_40, 5);
lean_inc(x_53);
x_54 = lean_unbox(x_42);
lean_dec(x_42);
x_55 = l_Lean_SourceInfo_fromRef(x_53, x_54);
lean_dec(x_53);
x_56 = lean_ctor_get(x_40, 10);
lean_inc(x_56);
lean_dec(x_40);
x_57 = lean_ctor_get(x_49, 0);
lean_inc(x_57);
lean_dec(x_49);
x_58 = l_Lean_Environment_mainModule(x_57);
lean_dec(x_57);
x_59 = lean_mk_string_unchecked("term_++_", 8, 8);
x_60 = l_Lean_Name_mkStr1(x_59);
x_61 = lean_mk_string_unchecked("++", 2, 2);
lean_inc(x_55);
lean_ctor_set_tag(x_47, 2);
lean_ctor_set(x_47, 1, x_61);
lean_ctor_set(x_47, 0, x_55);
x_62 = l_Lean_Syntax_mkStrLit(x_32, x_33);
lean_dec(x_32);
lean_inc(x_47);
lean_inc(x_60);
lean_inc(x_55);
x_63 = l_Lean_Syntax_node3(x_55, x_60, x_35, x_47, x_62);
x_64 = lean_mk_string_unchecked("str", 3, 3);
x_65 = l_Lean_Name_mkStr1(x_64);
x_66 = lean_mk_string_unchecked("\" := \"", 6, 6);
lean_inc(x_55);
x_67 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_67, 0, x_55);
lean_ctor_set(x_67, 1, x_66);
lean_inc(x_55);
x_68 = l_Lean_Syntax_node1(x_55, x_65, x_67);
lean_inc(x_47);
lean_inc(x_60);
lean_inc(x_55);
x_69 = l_Lean_Syntax_node3(x_55, x_60, x_63, x_47, x_68);
x_70 = lean_mk_string_unchecked("Lean", 4, 4);
x_71 = lean_mk_string_unchecked("Parser", 6, 6);
x_72 = lean_mk_string_unchecked("Term", 4, 4);
x_73 = lean_mk_string_unchecked("paren", 5, 5);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
x_74 = l_Lean_Name_mkStr4(x_70, x_71, x_72, x_73);
x_75 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_55);
x_76 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_76, 0, x_55);
lean_ctor_set(x_76, 1, x_75);
x_77 = lean_mk_string_unchecked("app", 3, 3);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
x_78 = l_Lean_Name_mkStr4(x_70, x_71, x_72, x_77);
x_79 = lean_mk_string_unchecked("Format.group", 12, 12);
x_80 = l_String_toSubstring_x27(x_79);
x_81 = lean_mk_string_unchecked("Format", 6, 6);
x_82 = lean_mk_string_unchecked("group", 5, 5);
lean_inc(x_82);
lean_inc(x_81);
x_83 = l_Lean_Name_mkStr2(x_81, x_82);
lean_inc(x_56);
lean_inc(x_58);
x_84 = l_Lean_addMacroScope(x_58, x_83, x_56);
x_85 = lean_mk_string_unchecked("Std", 3, 3);
lean_inc(x_81);
lean_inc(x_85);
x_86 = l_Lean_Name_mkStr3(x_85, x_81, x_82);
x_87 = lean_box(0);
lean_inc(x_86);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
x_89 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_89, 0, x_86);
x_90 = lean_box(0);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_88);
lean_ctor_set(x_92, 1, x_91);
lean_inc(x_55);
x_93 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_93, 0, x_55);
lean_ctor_set(x_93, 1, x_80);
lean_ctor_set(x_93, 2, x_84);
lean_ctor_set(x_93, 3, x_92);
x_94 = lean_mk_string_unchecked("null", 4, 4);
x_95 = l_Lean_Name_mkStr1(x_94);
x_96 = lean_mk_string_unchecked("Format.nest", 11, 11);
x_97 = l_String_toSubstring_x27(x_96);
x_98 = lean_mk_string_unchecked("nest", 4, 4);
lean_inc(x_98);
lean_inc(x_81);
x_99 = l_Lean_Name_mkStr2(x_81, x_98);
lean_inc(x_56);
lean_inc(x_58);
x_100 = l_Lean_addMacroScope(x_58, x_99, x_56);
x_101 = l_Lean_Name_mkStr3(x_85, x_81, x_98);
lean_inc(x_101);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_87);
x_103 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_103, 0, x_101);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_90);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_102);
lean_ctor_set(x_105, 1, x_104);
lean_inc(x_55);
x_106 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_106, 0, x_55);
lean_ctor_set(x_106, 1, x_97);
lean_ctor_set(x_106, 2, x_100);
lean_ctor_set(x_106, 3, x_105);
x_107 = l_Lean_Syntax_mkNumLit(x_52, x_33);
x_108 = lean_mk_string_unchecked("repr", 4, 4);
lean_inc(x_108);
x_109 = l_String_toSubstring_x27(x_108);
x_110 = l_Lean_Name_mkStr1(x_108);
lean_inc(x_110);
x_111 = l_Lean_addMacroScope(x_58, x_110, x_56);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_87);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_90);
lean_inc(x_55);
x_114 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_114, 0, x_55);
lean_ctor_set(x_114, 1, x_109);
lean_ctor_set(x_114, 2, x_111);
lean_ctor_set(x_114, 3, x_113);
x_115 = lean_mk_string_unchecked("proj", 4, 4);
x_116 = l_Lean_Name_mkStr4(x_70, x_71, x_72, x_115);
x_117 = lean_mk_syntax_ident(x_30);
x_118 = lean_mk_string_unchecked(".", 1, 1);
lean_inc(x_55);
x_119 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_119, 0, x_55);
lean_ctor_set(x_119, 1, x_118);
x_120 = lean_mk_syntax_ident(x_31);
lean_inc(x_55);
x_121 = l_Lean_Syntax_node3(x_55, x_116, x_117, x_119, x_120);
x_122 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_55);
x_123 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_123, 0, x_55);
lean_ctor_set(x_123, 1, x_122);
lean_inc(x_123);
lean_inc(x_76);
lean_inc(x_74);
lean_inc(x_55);
x_124 = l_Lean_Syntax_node3(x_55, x_74, x_76, x_121, x_123);
lean_inc(x_95);
lean_inc(x_55);
x_125 = l_Lean_Syntax_node1(x_55, x_95, x_124);
lean_inc(x_78);
lean_inc(x_55);
x_126 = l_Lean_Syntax_node2(x_55, x_78, x_114, x_125);
lean_inc(x_123);
lean_inc(x_76);
lean_inc(x_74);
lean_inc(x_55);
x_127 = l_Lean_Syntax_node3(x_55, x_74, x_76, x_126, x_123);
lean_inc(x_95);
lean_inc(x_55);
x_128 = l_Lean_Syntax_node2(x_55, x_95, x_107, x_127);
lean_inc(x_78);
lean_inc(x_55);
x_129 = l_Lean_Syntax_node2(x_55, x_78, x_106, x_128);
lean_inc(x_123);
lean_inc(x_76);
lean_inc(x_74);
lean_inc(x_55);
x_130 = l_Lean_Syntax_node3(x_55, x_74, x_76, x_129, x_123);
lean_inc(x_55);
x_131 = l_Lean_Syntax_node1(x_55, x_95, x_130);
lean_inc(x_55);
x_132 = l_Lean_Syntax_node2(x_55, x_78, x_93, x_131);
lean_inc(x_55);
x_133 = l_Lean_Syntax_node3(x_55, x_74, x_76, x_132, x_123);
x_134 = l_Lean_Syntax_node3(x_55, x_60, x_69, x_47, x_133);
x_15 = x_134;
x_16 = x_50;
goto block_20;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_135 = lean_ctor_get(x_47, 0);
x_136 = lean_ctor_get(x_47, 1);
lean_inc(x_136);
lean_inc(x_135);
lean_dec(x_47);
x_137 = lean_nat_add(x_45, x_46);
lean_dec(x_45);
x_138 = l___private_Init_Data_Repr_0__Nat_reprFast(x_137);
x_139 = lean_ctor_get(x_40, 5);
lean_inc(x_139);
x_140 = lean_unbox(x_42);
lean_dec(x_42);
x_141 = l_Lean_SourceInfo_fromRef(x_139, x_140);
lean_dec(x_139);
x_142 = lean_ctor_get(x_40, 10);
lean_inc(x_142);
lean_dec(x_40);
x_143 = lean_ctor_get(x_135, 0);
lean_inc(x_143);
lean_dec(x_135);
x_144 = l_Lean_Environment_mainModule(x_143);
lean_dec(x_143);
x_145 = lean_mk_string_unchecked("term_++_", 8, 8);
x_146 = l_Lean_Name_mkStr1(x_145);
x_147 = lean_mk_string_unchecked("++", 2, 2);
lean_inc(x_141);
x_148 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_148, 0, x_141);
lean_ctor_set(x_148, 1, x_147);
x_149 = l_Lean_Syntax_mkStrLit(x_32, x_33);
lean_dec(x_32);
lean_inc(x_148);
lean_inc(x_146);
lean_inc(x_141);
x_150 = l_Lean_Syntax_node3(x_141, x_146, x_35, x_148, x_149);
x_151 = lean_mk_string_unchecked("str", 3, 3);
x_152 = l_Lean_Name_mkStr1(x_151);
x_153 = lean_mk_string_unchecked("\" := \"", 6, 6);
lean_inc(x_141);
x_154 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_154, 0, x_141);
lean_ctor_set(x_154, 1, x_153);
lean_inc(x_141);
x_155 = l_Lean_Syntax_node1(x_141, x_152, x_154);
lean_inc(x_148);
lean_inc(x_146);
lean_inc(x_141);
x_156 = l_Lean_Syntax_node3(x_141, x_146, x_150, x_148, x_155);
x_157 = lean_mk_string_unchecked("Lean", 4, 4);
x_158 = lean_mk_string_unchecked("Parser", 6, 6);
x_159 = lean_mk_string_unchecked("Term", 4, 4);
x_160 = lean_mk_string_unchecked("paren", 5, 5);
lean_inc(x_159);
lean_inc(x_158);
lean_inc(x_157);
x_161 = l_Lean_Name_mkStr4(x_157, x_158, x_159, x_160);
x_162 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_141);
x_163 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_163, 0, x_141);
lean_ctor_set(x_163, 1, x_162);
x_164 = lean_mk_string_unchecked("app", 3, 3);
lean_inc(x_159);
lean_inc(x_158);
lean_inc(x_157);
x_165 = l_Lean_Name_mkStr4(x_157, x_158, x_159, x_164);
x_166 = lean_mk_string_unchecked("Format.group", 12, 12);
x_167 = l_String_toSubstring_x27(x_166);
x_168 = lean_mk_string_unchecked("Format", 6, 6);
x_169 = lean_mk_string_unchecked("group", 5, 5);
lean_inc(x_169);
lean_inc(x_168);
x_170 = l_Lean_Name_mkStr2(x_168, x_169);
lean_inc(x_142);
lean_inc(x_144);
x_171 = l_Lean_addMacroScope(x_144, x_170, x_142);
x_172 = lean_mk_string_unchecked("Std", 3, 3);
lean_inc(x_168);
lean_inc(x_172);
x_173 = l_Lean_Name_mkStr3(x_172, x_168, x_169);
x_174 = lean_box(0);
lean_inc(x_173);
x_175 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_175, 0, x_173);
lean_ctor_set(x_175, 1, x_174);
x_176 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_176, 0, x_173);
x_177 = lean_box(0);
x_178 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_178, 0, x_176);
lean_ctor_set(x_178, 1, x_177);
x_179 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_179, 0, x_175);
lean_ctor_set(x_179, 1, x_178);
lean_inc(x_141);
x_180 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_180, 0, x_141);
lean_ctor_set(x_180, 1, x_167);
lean_ctor_set(x_180, 2, x_171);
lean_ctor_set(x_180, 3, x_179);
x_181 = lean_mk_string_unchecked("null", 4, 4);
x_182 = l_Lean_Name_mkStr1(x_181);
x_183 = lean_mk_string_unchecked("Format.nest", 11, 11);
x_184 = l_String_toSubstring_x27(x_183);
x_185 = lean_mk_string_unchecked("nest", 4, 4);
lean_inc(x_185);
lean_inc(x_168);
x_186 = l_Lean_Name_mkStr2(x_168, x_185);
lean_inc(x_142);
lean_inc(x_144);
x_187 = l_Lean_addMacroScope(x_144, x_186, x_142);
x_188 = l_Lean_Name_mkStr3(x_172, x_168, x_185);
lean_inc(x_188);
x_189 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_189, 0, x_188);
lean_ctor_set(x_189, 1, x_174);
x_190 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_190, 0, x_188);
x_191 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_191, 0, x_190);
lean_ctor_set(x_191, 1, x_177);
x_192 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_192, 0, x_189);
lean_ctor_set(x_192, 1, x_191);
lean_inc(x_141);
x_193 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_193, 0, x_141);
lean_ctor_set(x_193, 1, x_184);
lean_ctor_set(x_193, 2, x_187);
lean_ctor_set(x_193, 3, x_192);
x_194 = l_Lean_Syntax_mkNumLit(x_138, x_33);
x_195 = lean_mk_string_unchecked("repr", 4, 4);
lean_inc(x_195);
x_196 = l_String_toSubstring_x27(x_195);
x_197 = l_Lean_Name_mkStr1(x_195);
lean_inc(x_197);
x_198 = l_Lean_addMacroScope(x_144, x_197, x_142);
x_199 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_199, 0, x_197);
lean_ctor_set(x_199, 1, x_174);
x_200 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_200, 0, x_199);
lean_ctor_set(x_200, 1, x_177);
lean_inc(x_141);
x_201 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_201, 0, x_141);
lean_ctor_set(x_201, 1, x_196);
lean_ctor_set(x_201, 2, x_198);
lean_ctor_set(x_201, 3, x_200);
x_202 = lean_mk_string_unchecked("proj", 4, 4);
x_203 = l_Lean_Name_mkStr4(x_157, x_158, x_159, x_202);
x_204 = lean_mk_syntax_ident(x_30);
x_205 = lean_mk_string_unchecked(".", 1, 1);
lean_inc(x_141);
x_206 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_206, 0, x_141);
lean_ctor_set(x_206, 1, x_205);
x_207 = lean_mk_syntax_ident(x_31);
lean_inc(x_141);
x_208 = l_Lean_Syntax_node3(x_141, x_203, x_204, x_206, x_207);
x_209 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_141);
x_210 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_210, 0, x_141);
lean_ctor_set(x_210, 1, x_209);
lean_inc(x_210);
lean_inc(x_163);
lean_inc(x_161);
lean_inc(x_141);
x_211 = l_Lean_Syntax_node3(x_141, x_161, x_163, x_208, x_210);
lean_inc(x_182);
lean_inc(x_141);
x_212 = l_Lean_Syntax_node1(x_141, x_182, x_211);
lean_inc(x_165);
lean_inc(x_141);
x_213 = l_Lean_Syntax_node2(x_141, x_165, x_201, x_212);
lean_inc(x_210);
lean_inc(x_163);
lean_inc(x_161);
lean_inc(x_141);
x_214 = l_Lean_Syntax_node3(x_141, x_161, x_163, x_213, x_210);
lean_inc(x_182);
lean_inc(x_141);
x_215 = l_Lean_Syntax_node2(x_141, x_182, x_194, x_214);
lean_inc(x_165);
lean_inc(x_141);
x_216 = l_Lean_Syntax_node2(x_141, x_165, x_193, x_215);
lean_inc(x_210);
lean_inc(x_163);
lean_inc(x_161);
lean_inc(x_141);
x_217 = l_Lean_Syntax_node3(x_141, x_161, x_163, x_216, x_210);
lean_inc(x_141);
x_218 = l_Lean_Syntax_node1(x_141, x_182, x_217);
lean_inc(x_141);
x_219 = l_Lean_Syntax_node2(x_141, x_165, x_180, x_218);
lean_inc(x_141);
x_220 = l_Lean_Syntax_node3(x_141, x_161, x_163, x_219, x_210);
x_221 = l_Lean_Syntax_node3(x_141, x_146, x_156, x_148, x_220);
x_15 = x_221;
x_16 = x_136;
goto block_20;
}
}
else
{
lean_object* x_222; lean_object* x_223; uint8_t x_224; 
lean_dec(x_42);
lean_dec(x_31);
lean_dec(x_30);
x_222 = lean_ctor_get(x_41, 1);
lean_inc(x_222);
lean_dec(x_41);
x_223 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1(x_36, x_39, x_34, x_37, x_40, x_38, x_222);
x_224 = !lean_is_exclusive(x_223);
if (x_224 == 0)
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; uint8_t x_228; 
x_225 = lean_ctor_get(x_223, 0);
x_226 = lean_ctor_get(x_223, 1);
x_227 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__2(x_225, x_36, x_39, x_34, x_37, x_40, x_38, x_226);
lean_dec(x_40);
lean_dec(x_37);
lean_dec(x_34);
lean_dec(x_225);
x_228 = !lean_is_exclusive(x_227);
if (x_228 == 0)
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; uint8_t x_232; 
x_229 = lean_ctor_get(x_227, 0);
x_230 = lean_ctor_get(x_227, 1);
x_231 = lean_st_ref_get(x_38, x_230);
lean_dec(x_38);
x_232 = !lean_is_exclusive(x_231);
if (x_232 == 0)
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; 
x_233 = lean_ctor_get(x_231, 1);
x_234 = lean_ctor_get(x_231, 0);
lean_dec(x_234);
x_235 = lean_mk_string_unchecked("term_++_", 8, 8);
x_236 = l_Lean_Name_mkStr1(x_235);
x_237 = lean_mk_string_unchecked("++", 2, 2);
lean_inc(x_229);
lean_ctor_set_tag(x_231, 2);
lean_ctor_set(x_231, 1, x_237);
lean_ctor_set(x_231, 0, x_229);
x_238 = l_Lean_Syntax_mkStrLit(x_32, x_33);
lean_dec(x_32);
lean_inc(x_231);
lean_inc(x_236);
lean_inc(x_229);
x_239 = l_Lean_Syntax_node3(x_229, x_236, x_35, x_231, x_238);
x_240 = lean_mk_string_unchecked("str", 3, 3);
x_241 = l_Lean_Name_mkStr1(x_240);
x_242 = lean_mk_string_unchecked("\" := \"", 6, 6);
lean_inc(x_229);
lean_ctor_set_tag(x_227, 2);
lean_ctor_set(x_227, 1, x_242);
lean_inc(x_241);
lean_inc(x_229);
x_243 = l_Lean_Syntax_node1(x_229, x_241, x_227);
lean_inc(x_231);
lean_inc(x_236);
lean_inc(x_229);
x_244 = l_Lean_Syntax_node3(x_229, x_236, x_239, x_231, x_243);
x_245 = lean_mk_string_unchecked("\"_\"", 3, 3);
lean_inc(x_229);
lean_ctor_set_tag(x_223, 2);
lean_ctor_set(x_223, 1, x_245);
lean_ctor_set(x_223, 0, x_229);
lean_inc(x_229);
x_246 = l_Lean_Syntax_node1(x_229, x_241, x_223);
x_247 = l_Lean_Syntax_node3(x_229, x_236, x_244, x_231, x_246);
x_15 = x_247;
x_16 = x_233;
goto block_20;
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; 
x_248 = lean_ctor_get(x_231, 1);
lean_inc(x_248);
lean_dec(x_231);
x_249 = lean_mk_string_unchecked("term_++_", 8, 8);
x_250 = l_Lean_Name_mkStr1(x_249);
x_251 = lean_mk_string_unchecked("++", 2, 2);
lean_inc(x_229);
x_252 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_252, 0, x_229);
lean_ctor_set(x_252, 1, x_251);
x_253 = l_Lean_Syntax_mkStrLit(x_32, x_33);
lean_dec(x_32);
lean_inc(x_252);
lean_inc(x_250);
lean_inc(x_229);
x_254 = l_Lean_Syntax_node3(x_229, x_250, x_35, x_252, x_253);
x_255 = lean_mk_string_unchecked("str", 3, 3);
x_256 = l_Lean_Name_mkStr1(x_255);
x_257 = lean_mk_string_unchecked("\" := \"", 6, 6);
lean_inc(x_229);
lean_ctor_set_tag(x_227, 2);
lean_ctor_set(x_227, 1, x_257);
lean_inc(x_256);
lean_inc(x_229);
x_258 = l_Lean_Syntax_node1(x_229, x_256, x_227);
lean_inc(x_252);
lean_inc(x_250);
lean_inc(x_229);
x_259 = l_Lean_Syntax_node3(x_229, x_250, x_254, x_252, x_258);
x_260 = lean_mk_string_unchecked("\"_\"", 3, 3);
lean_inc(x_229);
lean_ctor_set_tag(x_223, 2);
lean_ctor_set(x_223, 1, x_260);
lean_ctor_set(x_223, 0, x_229);
lean_inc(x_229);
x_261 = l_Lean_Syntax_node1(x_229, x_256, x_223);
x_262 = l_Lean_Syntax_node3(x_229, x_250, x_259, x_252, x_261);
x_15 = x_262;
x_16 = x_248;
goto block_20;
}
}
else
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; 
x_263 = lean_ctor_get(x_227, 0);
x_264 = lean_ctor_get(x_227, 1);
lean_inc(x_264);
lean_inc(x_263);
lean_dec(x_227);
x_265 = lean_st_ref_get(x_38, x_264);
lean_dec(x_38);
x_266 = lean_ctor_get(x_265, 1);
lean_inc(x_266);
if (lean_is_exclusive(x_265)) {
 lean_ctor_release(x_265, 0);
 lean_ctor_release(x_265, 1);
 x_267 = x_265;
} else {
 lean_dec_ref(x_265);
 x_267 = lean_box(0);
}
x_268 = lean_mk_string_unchecked("term_++_", 8, 8);
x_269 = l_Lean_Name_mkStr1(x_268);
x_270 = lean_mk_string_unchecked("++", 2, 2);
lean_inc(x_263);
if (lean_is_scalar(x_267)) {
 x_271 = lean_alloc_ctor(2, 2, 0);
} else {
 x_271 = x_267;
 lean_ctor_set_tag(x_271, 2);
}
lean_ctor_set(x_271, 0, x_263);
lean_ctor_set(x_271, 1, x_270);
x_272 = l_Lean_Syntax_mkStrLit(x_32, x_33);
lean_dec(x_32);
lean_inc(x_271);
lean_inc(x_269);
lean_inc(x_263);
x_273 = l_Lean_Syntax_node3(x_263, x_269, x_35, x_271, x_272);
x_274 = lean_mk_string_unchecked("str", 3, 3);
x_275 = l_Lean_Name_mkStr1(x_274);
x_276 = lean_mk_string_unchecked("\" := \"", 6, 6);
lean_inc(x_263);
x_277 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_277, 0, x_263);
lean_ctor_set(x_277, 1, x_276);
lean_inc(x_275);
lean_inc(x_263);
x_278 = l_Lean_Syntax_node1(x_263, x_275, x_277);
lean_inc(x_271);
lean_inc(x_269);
lean_inc(x_263);
x_279 = l_Lean_Syntax_node3(x_263, x_269, x_273, x_271, x_278);
x_280 = lean_mk_string_unchecked("\"_\"", 3, 3);
lean_inc(x_263);
lean_ctor_set_tag(x_223, 2);
lean_ctor_set(x_223, 1, x_280);
lean_ctor_set(x_223, 0, x_263);
lean_inc(x_263);
x_281 = l_Lean_Syntax_node1(x_263, x_275, x_223);
x_282 = l_Lean_Syntax_node3(x_263, x_269, x_279, x_271, x_281);
x_15 = x_282;
x_16 = x_266;
goto block_20;
}
}
else
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; 
x_283 = lean_ctor_get(x_223, 0);
x_284 = lean_ctor_get(x_223, 1);
lean_inc(x_284);
lean_inc(x_283);
lean_dec(x_223);
x_285 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__2(x_283, x_36, x_39, x_34, x_37, x_40, x_38, x_284);
lean_dec(x_40);
lean_dec(x_37);
lean_dec(x_34);
lean_dec(x_283);
x_286 = lean_ctor_get(x_285, 0);
lean_inc(x_286);
x_287 = lean_ctor_get(x_285, 1);
lean_inc(x_287);
if (lean_is_exclusive(x_285)) {
 lean_ctor_release(x_285, 0);
 lean_ctor_release(x_285, 1);
 x_288 = x_285;
} else {
 lean_dec_ref(x_285);
 x_288 = lean_box(0);
}
x_289 = lean_st_ref_get(x_38, x_287);
lean_dec(x_38);
x_290 = lean_ctor_get(x_289, 1);
lean_inc(x_290);
if (lean_is_exclusive(x_289)) {
 lean_ctor_release(x_289, 0);
 lean_ctor_release(x_289, 1);
 x_291 = x_289;
} else {
 lean_dec_ref(x_289);
 x_291 = lean_box(0);
}
x_292 = lean_mk_string_unchecked("term_++_", 8, 8);
x_293 = l_Lean_Name_mkStr1(x_292);
x_294 = lean_mk_string_unchecked("++", 2, 2);
lean_inc(x_286);
if (lean_is_scalar(x_291)) {
 x_295 = lean_alloc_ctor(2, 2, 0);
} else {
 x_295 = x_291;
 lean_ctor_set_tag(x_295, 2);
}
lean_ctor_set(x_295, 0, x_286);
lean_ctor_set(x_295, 1, x_294);
x_296 = l_Lean_Syntax_mkStrLit(x_32, x_33);
lean_dec(x_32);
lean_inc(x_295);
lean_inc(x_293);
lean_inc(x_286);
x_297 = l_Lean_Syntax_node3(x_286, x_293, x_35, x_295, x_296);
x_298 = lean_mk_string_unchecked("str", 3, 3);
x_299 = l_Lean_Name_mkStr1(x_298);
x_300 = lean_mk_string_unchecked("\" := \"", 6, 6);
lean_inc(x_286);
if (lean_is_scalar(x_288)) {
 x_301 = lean_alloc_ctor(2, 2, 0);
} else {
 x_301 = x_288;
 lean_ctor_set_tag(x_301, 2);
}
lean_ctor_set(x_301, 0, x_286);
lean_ctor_set(x_301, 1, x_300);
lean_inc(x_299);
lean_inc(x_286);
x_302 = l_Lean_Syntax_node1(x_286, x_299, x_301);
lean_inc(x_295);
lean_inc(x_293);
lean_inc(x_286);
x_303 = l_Lean_Syntax_node3(x_286, x_293, x_297, x_295, x_302);
x_304 = lean_mk_string_unchecked("\"_\"", 3, 3);
lean_inc(x_286);
x_305 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_305, 0, x_286);
lean_ctor_set(x_305, 1, x_304);
lean_inc(x_286);
x_306 = l_Lean_Syntax_node1(x_286, x_299, x_305);
x_307 = l_Lean_Syntax_node3(x_286, x_293, x_303, x_295, x_306);
x_15 = x_307;
x_16 = x_290;
goto block_20;
}
}
}
else
{
uint8_t x_308; 
lean_dec(x_40);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
x_308 = !lean_is_exclusive(x_41);
if (x_308 == 0)
{
return x_41;
}
else
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; 
x_309 = lean_ctor_get(x_41, 0);
x_310 = lean_ctor_get(x_41, 1);
lean_inc(x_310);
lean_inc(x_309);
lean_dec(x_41);
x_311 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_311, 0, x_309);
lean_ctor_set(x_311, 1, x_310);
return x_311;
}
}
}
block_328:
{
lean_object* x_323; 
lean_inc(x_321);
lean_inc(x_320);
lean_inc(x_319);
lean_inc(x_318);
lean_inc(x_314);
x_323 = l_Lean_Meta_isType(x_314, x_318, x_319, x_320, x_321, x_322);
if (lean_obj_tag(x_323) == 0)
{
lean_object* x_324; uint8_t x_325; 
x_324 = lean_ctor_get(x_323, 0);
lean_inc(x_324);
x_325 = lean_unbox(x_324);
lean_dec(x_324);
if (x_325 == 0)
{
lean_object* x_326; lean_object* x_327; 
x_326 = lean_ctor_get(x_323, 1);
lean_inc(x_326);
lean_dec(x_323);
lean_inc(x_321);
lean_inc(x_320);
lean_inc(x_319);
lean_inc(x_318);
x_327 = l_Lean_Meta_isProof(x_314, x_318, x_319, x_320, x_321, x_326);
x_34 = x_318;
x_35 = x_315;
x_36 = x_316;
x_37 = x_319;
x_38 = x_321;
x_39 = x_317;
x_40 = x_320;
x_41 = x_327;
goto block_312;
}
else
{
lean_dec(x_314);
x_34 = x_318;
x_35 = x_315;
x_36 = x_316;
x_37 = x_319;
x_38 = x_321;
x_39 = x_317;
x_40 = x_320;
x_41 = x_323;
goto block_312;
}
}
else
{
lean_dec(x_314);
x_34 = x_318;
x_35 = x_315;
x_36 = x_316;
x_37 = x_319;
x_38 = x_321;
x_39 = x_317;
x_40 = x_320;
x_41 = x_323;
goto block_312;
}
}
}
block_20:
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_5, 2);
x_18 = lean_nat_add(x_7, x_17);
lean_dec(x_7);
x_6 = x_15;
x_7 = x_18;
x_14 = x_16;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_5, 5);
lean_inc(x_8);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_box(0);
x_10 = lean_unbox(x_9);
x_11 = l_Lean_SourceInfo_fromRef(x_1, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_8);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
lean_inc(x_1);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_17 = lean_apply_7(x_1, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_2);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_20 = lean_apply_8(x_2, x_18, x_10, x_11, x_12, x_13, x_14, x_15, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_st_ref_get(x_15, x_22);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_ctor_get(x_23, 1);
x_27 = lean_ctor_get(x_14, 10);
lean_inc(x_27);
x_28 = lean_ctor_get(x_25, 0);
lean_inc(x_28);
lean_dec(x_25);
x_29 = l_Lean_Environment_mainModule(x_28);
lean_dec(x_28);
x_30 = lean_mk_string_unchecked("Format.nil", 10, 10);
x_31 = l_String_toSubstring_x27(x_30);
x_32 = lean_mk_string_unchecked("Format", 6, 6);
x_33 = lean_mk_string_unchecked("nil", 3, 3);
lean_inc(x_33);
lean_inc(x_32);
x_34 = l_Lean_Name_mkStr2(x_32, x_33);
lean_inc(x_27);
x_35 = l_Lean_addMacroScope(x_29, x_34, x_27);
x_36 = lean_mk_string_unchecked("Std", 3, 3);
lean_inc(x_32);
lean_inc(x_36);
x_37 = l_Lean_Name_mkStr3(x_36, x_32, x_33);
x_38 = lean_box(0);
lean_inc(x_37);
lean_ctor_set_tag(x_23, 1);
lean_ctor_set(x_23, 1, x_38);
lean_ctor_set(x_23, 0, x_37);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_37);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_23);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_43, 0, x_21);
lean_ctor_set(x_43, 1, x_31);
lean_ctor_set(x_43, 2, x_35);
lean_ctor_set(x_43, 3, x_42);
x_44 = lean_array_get_size(x_8);
x_45 = lean_array_get_size(x_3);
x_46 = lean_nat_add(x_7, x_45);
x_47 = lean_nat_dec_eq(x_44, x_46);
lean_dec(x_46);
lean_dec(x_44);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
lean_dec(x_45);
lean_dec(x_43);
lean_dec(x_36);
lean_dec(x_32);
lean_dec(x_27);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_48 = lean_mk_string_unchecked("'deriving Repr' failed, unexpected number of fields in structure", 64, 64);
x_49 = l_Lean_stringToMessageData(x_48);
lean_dec(x_48);
x_50 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_49, x_10, x_11, x_12, x_13, x_14, x_15, x_26);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
return x_50;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_50, 0);
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_50);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_unsigned_to_nat(1u);
lean_inc(x_4);
x_56 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_56, 0, x_4);
lean_ctor_set(x_56, 1, x_45);
lean_ctor_set(x_56, 2, x_55);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_57 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg(x_3, x_5, x_8, x_6, x_56, x_43, x_4, x_10, x_11, x_12, x_13, x_14, x_15, x_26);
lean_dec(x_56);
if (lean_obj_tag(x_57) == 0)
{
uint8_t x_58; 
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_57, 0);
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_61 = lean_apply_7(x_1, x_10, x_11, x_12, x_13, x_14, x_15, x_60);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
lean_inc(x_15);
x_64 = lean_apply_8(x_2, x_62, x_10, x_11, x_12, x_13, x_14, x_15, x_63);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = lean_st_ref_get(x_15, x_66);
lean_dec(x_15);
x_68 = !lean_is_exclusive(x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_69 = lean_ctor_get(x_67, 0);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
lean_dec(x_69);
x_71 = l_Lean_Environment_mainModule(x_70);
lean_dec(x_70);
x_72 = lean_mk_string_unchecked("Lean", 4, 4);
x_73 = lean_mk_string_unchecked("Parser", 6, 6);
x_74 = lean_mk_string_unchecked("Term", 4, 4);
x_75 = lean_mk_string_unchecked("app", 3, 3);
x_76 = l_Lean_Name_mkStr4(x_72, x_73, x_74, x_75);
x_77 = lean_mk_string_unchecked("Format.bracket", 14, 14);
x_78 = l_String_toSubstring_x27(x_77);
x_79 = lean_mk_string_unchecked("bracket", 7, 7);
lean_inc(x_79);
lean_inc(x_32);
x_80 = l_Lean_Name_mkStr2(x_32, x_79);
x_81 = l_Lean_addMacroScope(x_71, x_80, x_27);
x_82 = l_Lean_Name_mkStr3(x_36, x_32, x_79);
lean_ctor_set_tag(x_57, 1);
lean_ctor_set(x_57, 1, x_38);
lean_ctor_set(x_57, 0, x_82);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_57);
lean_ctor_set(x_83, 1, x_40);
lean_inc(x_65);
x_84 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_84, 0, x_65);
lean_ctor_set(x_84, 1, x_78);
lean_ctor_set(x_84, 2, x_81);
lean_ctor_set(x_84, 3, x_83);
x_85 = lean_mk_string_unchecked("null", 4, 4);
x_86 = l_Lean_Name_mkStr1(x_85);
x_87 = lean_mk_string_unchecked("str", 3, 3);
x_88 = l_Lean_Name_mkStr1(x_87);
x_89 = lean_mk_string_unchecked("\"{ \"", 4, 4);
lean_inc(x_65);
x_90 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_90, 0, x_65);
lean_ctor_set(x_90, 1, x_89);
lean_inc(x_88);
lean_inc(x_65);
x_91 = l_Lean_Syntax_node1(x_65, x_88, x_90);
x_92 = lean_mk_string_unchecked("\" }\"", 4, 4);
lean_inc(x_65);
x_93 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_93, 0, x_65);
lean_ctor_set(x_93, 1, x_92);
lean_inc(x_65);
x_94 = l_Lean_Syntax_node1(x_65, x_88, x_93);
lean_inc(x_65);
x_95 = l_Lean_Syntax_node3(x_65, x_86, x_91, x_59, x_94);
x_96 = l_Lean_Syntax_node2(x_65, x_76, x_84, x_95);
lean_ctor_set(x_67, 0, x_96);
return x_67;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_97 = lean_ctor_get(x_67, 0);
x_98 = lean_ctor_get(x_67, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_67);
x_99 = lean_ctor_get(x_97, 0);
lean_inc(x_99);
lean_dec(x_97);
x_100 = l_Lean_Environment_mainModule(x_99);
lean_dec(x_99);
x_101 = lean_mk_string_unchecked("Lean", 4, 4);
x_102 = lean_mk_string_unchecked("Parser", 6, 6);
x_103 = lean_mk_string_unchecked("Term", 4, 4);
x_104 = lean_mk_string_unchecked("app", 3, 3);
x_105 = l_Lean_Name_mkStr4(x_101, x_102, x_103, x_104);
x_106 = lean_mk_string_unchecked("Format.bracket", 14, 14);
x_107 = l_String_toSubstring_x27(x_106);
x_108 = lean_mk_string_unchecked("bracket", 7, 7);
lean_inc(x_108);
lean_inc(x_32);
x_109 = l_Lean_Name_mkStr2(x_32, x_108);
x_110 = l_Lean_addMacroScope(x_100, x_109, x_27);
x_111 = l_Lean_Name_mkStr3(x_36, x_32, x_108);
lean_ctor_set_tag(x_57, 1);
lean_ctor_set(x_57, 1, x_38);
lean_ctor_set(x_57, 0, x_111);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_57);
lean_ctor_set(x_112, 1, x_40);
lean_inc(x_65);
x_113 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_113, 0, x_65);
lean_ctor_set(x_113, 1, x_107);
lean_ctor_set(x_113, 2, x_110);
lean_ctor_set(x_113, 3, x_112);
x_114 = lean_mk_string_unchecked("null", 4, 4);
x_115 = l_Lean_Name_mkStr1(x_114);
x_116 = lean_mk_string_unchecked("str", 3, 3);
x_117 = l_Lean_Name_mkStr1(x_116);
x_118 = lean_mk_string_unchecked("\"{ \"", 4, 4);
lean_inc(x_65);
x_119 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_119, 0, x_65);
lean_ctor_set(x_119, 1, x_118);
lean_inc(x_117);
lean_inc(x_65);
x_120 = l_Lean_Syntax_node1(x_65, x_117, x_119);
x_121 = lean_mk_string_unchecked("\" }\"", 4, 4);
lean_inc(x_65);
x_122 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_122, 0, x_65);
lean_ctor_set(x_122, 1, x_121);
lean_inc(x_65);
x_123 = l_Lean_Syntax_node1(x_65, x_117, x_122);
lean_inc(x_65);
x_124 = l_Lean_Syntax_node3(x_65, x_115, x_120, x_59, x_123);
x_125 = l_Lean_Syntax_node2(x_65, x_105, x_113, x_124);
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_98);
return x_126;
}
}
else
{
uint8_t x_127; 
lean_free_object(x_57);
lean_dec(x_59);
lean_dec(x_36);
lean_dec(x_32);
lean_dec(x_27);
lean_dec(x_15);
x_127 = !lean_is_exclusive(x_64);
if (x_127 == 0)
{
return x_64;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_64, 0);
x_129 = lean_ctor_get(x_64, 1);
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_64);
x_130 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_129);
return x_130;
}
}
}
else
{
uint8_t x_131; 
lean_free_object(x_57);
lean_dec(x_59);
lean_dec(x_36);
lean_dec(x_32);
lean_dec(x_27);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_2);
x_131 = !lean_is_exclusive(x_61);
if (x_131 == 0)
{
return x_61;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_132 = lean_ctor_get(x_61, 0);
x_133 = lean_ctor_get(x_61, 1);
lean_inc(x_133);
lean_inc(x_132);
lean_dec(x_61);
x_134 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_134, 0, x_132);
lean_ctor_set(x_134, 1, x_133);
return x_134;
}
}
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_135 = lean_ctor_get(x_57, 0);
x_136 = lean_ctor_get(x_57, 1);
lean_inc(x_136);
lean_inc(x_135);
lean_dec(x_57);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_137 = lean_apply_7(x_1, x_10, x_11, x_12, x_13, x_14, x_15, x_136);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_137, 1);
lean_inc(x_139);
lean_dec(x_137);
lean_inc(x_15);
x_140 = lean_apply_8(x_2, x_138, x_10, x_11, x_12, x_13, x_14, x_15, x_139);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_140, 1);
lean_inc(x_142);
lean_dec(x_140);
x_143 = lean_st_ref_get(x_15, x_142);
lean_dec(x_15);
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_143, 1);
lean_inc(x_145);
if (lean_is_exclusive(x_143)) {
 lean_ctor_release(x_143, 0);
 lean_ctor_release(x_143, 1);
 x_146 = x_143;
} else {
 lean_dec_ref(x_143);
 x_146 = lean_box(0);
}
x_147 = lean_ctor_get(x_144, 0);
lean_inc(x_147);
lean_dec(x_144);
x_148 = l_Lean_Environment_mainModule(x_147);
lean_dec(x_147);
x_149 = lean_mk_string_unchecked("Lean", 4, 4);
x_150 = lean_mk_string_unchecked("Parser", 6, 6);
x_151 = lean_mk_string_unchecked("Term", 4, 4);
x_152 = lean_mk_string_unchecked("app", 3, 3);
x_153 = l_Lean_Name_mkStr4(x_149, x_150, x_151, x_152);
x_154 = lean_mk_string_unchecked("Format.bracket", 14, 14);
x_155 = l_String_toSubstring_x27(x_154);
x_156 = lean_mk_string_unchecked("bracket", 7, 7);
lean_inc(x_156);
lean_inc(x_32);
x_157 = l_Lean_Name_mkStr2(x_32, x_156);
x_158 = l_Lean_addMacroScope(x_148, x_157, x_27);
x_159 = l_Lean_Name_mkStr3(x_36, x_32, x_156);
x_160 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_38);
x_161 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_161, 1, x_40);
lean_inc(x_141);
x_162 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_162, 0, x_141);
lean_ctor_set(x_162, 1, x_155);
lean_ctor_set(x_162, 2, x_158);
lean_ctor_set(x_162, 3, x_161);
x_163 = lean_mk_string_unchecked("null", 4, 4);
x_164 = l_Lean_Name_mkStr1(x_163);
x_165 = lean_mk_string_unchecked("str", 3, 3);
x_166 = l_Lean_Name_mkStr1(x_165);
x_167 = lean_mk_string_unchecked("\"{ \"", 4, 4);
lean_inc(x_141);
x_168 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_168, 0, x_141);
lean_ctor_set(x_168, 1, x_167);
lean_inc(x_166);
lean_inc(x_141);
x_169 = l_Lean_Syntax_node1(x_141, x_166, x_168);
x_170 = lean_mk_string_unchecked("\" }\"", 4, 4);
lean_inc(x_141);
x_171 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_171, 0, x_141);
lean_ctor_set(x_171, 1, x_170);
lean_inc(x_141);
x_172 = l_Lean_Syntax_node1(x_141, x_166, x_171);
lean_inc(x_141);
x_173 = l_Lean_Syntax_node3(x_141, x_164, x_169, x_135, x_172);
x_174 = l_Lean_Syntax_node2(x_141, x_153, x_162, x_173);
if (lean_is_scalar(x_146)) {
 x_175 = lean_alloc_ctor(0, 2, 0);
} else {
 x_175 = x_146;
}
lean_ctor_set(x_175, 0, x_174);
lean_ctor_set(x_175, 1, x_145);
return x_175;
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
lean_dec(x_135);
lean_dec(x_36);
lean_dec(x_32);
lean_dec(x_27);
lean_dec(x_15);
x_176 = lean_ctor_get(x_140, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_140, 1);
lean_inc(x_177);
if (lean_is_exclusive(x_140)) {
 lean_ctor_release(x_140, 0);
 lean_ctor_release(x_140, 1);
 x_178 = x_140;
} else {
 lean_dec_ref(x_140);
 x_178 = lean_box(0);
}
if (lean_is_scalar(x_178)) {
 x_179 = lean_alloc_ctor(1, 2, 0);
} else {
 x_179 = x_178;
}
lean_ctor_set(x_179, 0, x_176);
lean_ctor_set(x_179, 1, x_177);
return x_179;
}
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
lean_dec(x_135);
lean_dec(x_36);
lean_dec(x_32);
lean_dec(x_27);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_2);
x_180 = lean_ctor_get(x_137, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_137, 1);
lean_inc(x_181);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 lean_ctor_release(x_137, 1);
 x_182 = x_137;
} else {
 lean_dec_ref(x_137);
 x_182 = lean_box(0);
}
if (lean_is_scalar(x_182)) {
 x_183 = lean_alloc_ctor(1, 2, 0);
} else {
 x_183 = x_182;
}
lean_ctor_set(x_183, 0, x_180);
lean_ctor_set(x_183, 1, x_181);
return x_183;
}
}
}
else
{
lean_dec(x_36);
lean_dec(x_32);
lean_dec(x_27);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
return x_57;
}
}
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; uint8_t x_207; 
x_184 = lean_ctor_get(x_23, 0);
x_185 = lean_ctor_get(x_23, 1);
lean_inc(x_185);
lean_inc(x_184);
lean_dec(x_23);
x_186 = lean_ctor_get(x_14, 10);
lean_inc(x_186);
x_187 = lean_ctor_get(x_184, 0);
lean_inc(x_187);
lean_dec(x_184);
x_188 = l_Lean_Environment_mainModule(x_187);
lean_dec(x_187);
x_189 = lean_mk_string_unchecked("Format.nil", 10, 10);
x_190 = l_String_toSubstring_x27(x_189);
x_191 = lean_mk_string_unchecked("Format", 6, 6);
x_192 = lean_mk_string_unchecked("nil", 3, 3);
lean_inc(x_192);
lean_inc(x_191);
x_193 = l_Lean_Name_mkStr2(x_191, x_192);
lean_inc(x_186);
x_194 = l_Lean_addMacroScope(x_188, x_193, x_186);
x_195 = lean_mk_string_unchecked("Std", 3, 3);
lean_inc(x_191);
lean_inc(x_195);
x_196 = l_Lean_Name_mkStr3(x_195, x_191, x_192);
x_197 = lean_box(0);
lean_inc(x_196);
x_198 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_198, 0, x_196);
lean_ctor_set(x_198, 1, x_197);
x_199 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_199, 0, x_196);
x_200 = lean_box(0);
x_201 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_201, 0, x_199);
lean_ctor_set(x_201, 1, x_200);
x_202 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_202, 0, x_198);
lean_ctor_set(x_202, 1, x_201);
x_203 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_203, 0, x_21);
lean_ctor_set(x_203, 1, x_190);
lean_ctor_set(x_203, 2, x_194);
lean_ctor_set(x_203, 3, x_202);
x_204 = lean_array_get_size(x_8);
x_205 = lean_array_get_size(x_3);
x_206 = lean_nat_add(x_7, x_205);
x_207 = lean_nat_dec_eq(x_204, x_206);
lean_dec(x_206);
lean_dec(x_204);
if (x_207 == 0)
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
lean_dec(x_205);
lean_dec(x_203);
lean_dec(x_195);
lean_dec(x_191);
lean_dec(x_186);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_208 = lean_mk_string_unchecked("'deriving Repr' failed, unexpected number of fields in structure", 64, 64);
x_209 = l_Lean_stringToMessageData(x_208);
lean_dec(x_208);
x_210 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_209, x_10, x_11, x_12, x_13, x_14, x_15, x_185);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_211 = lean_ctor_get(x_210, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_210, 1);
lean_inc(x_212);
if (lean_is_exclusive(x_210)) {
 lean_ctor_release(x_210, 0);
 lean_ctor_release(x_210, 1);
 x_213 = x_210;
} else {
 lean_dec_ref(x_210);
 x_213 = lean_box(0);
}
if (lean_is_scalar(x_213)) {
 x_214 = lean_alloc_ctor(1, 2, 0);
} else {
 x_214 = x_213;
}
lean_ctor_set(x_214, 0, x_211);
lean_ctor_set(x_214, 1, x_212);
return x_214;
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_215 = lean_unsigned_to_nat(1u);
lean_inc(x_4);
x_216 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_216, 0, x_4);
lean_ctor_set(x_216, 1, x_205);
lean_ctor_set(x_216, 2, x_215);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_217 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg(x_3, x_5, x_8, x_6, x_216, x_203, x_4, x_10, x_11, x_12, x_13, x_14, x_15, x_185);
lean_dec(x_216);
if (lean_obj_tag(x_217) == 0)
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_218 = lean_ctor_get(x_217, 0);
lean_inc(x_218);
x_219 = lean_ctor_get(x_217, 1);
lean_inc(x_219);
if (lean_is_exclusive(x_217)) {
 lean_ctor_release(x_217, 0);
 lean_ctor_release(x_217, 1);
 x_220 = x_217;
} else {
 lean_dec_ref(x_217);
 x_220 = lean_box(0);
}
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_221 = lean_apply_7(x_1, x_10, x_11, x_12, x_13, x_14, x_15, x_219);
if (lean_obj_tag(x_221) == 0)
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_222 = lean_ctor_get(x_221, 0);
lean_inc(x_222);
x_223 = lean_ctor_get(x_221, 1);
lean_inc(x_223);
lean_dec(x_221);
lean_inc(x_15);
x_224 = lean_apply_8(x_2, x_222, x_10, x_11, x_12, x_13, x_14, x_15, x_223);
if (lean_obj_tag(x_224) == 0)
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; 
x_225 = lean_ctor_get(x_224, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_224, 1);
lean_inc(x_226);
lean_dec(x_224);
x_227 = lean_st_ref_get(x_15, x_226);
lean_dec(x_15);
x_228 = lean_ctor_get(x_227, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_227, 1);
lean_inc(x_229);
if (lean_is_exclusive(x_227)) {
 lean_ctor_release(x_227, 0);
 lean_ctor_release(x_227, 1);
 x_230 = x_227;
} else {
 lean_dec_ref(x_227);
 x_230 = lean_box(0);
}
x_231 = lean_ctor_get(x_228, 0);
lean_inc(x_231);
lean_dec(x_228);
x_232 = l_Lean_Environment_mainModule(x_231);
lean_dec(x_231);
x_233 = lean_mk_string_unchecked("Lean", 4, 4);
x_234 = lean_mk_string_unchecked("Parser", 6, 6);
x_235 = lean_mk_string_unchecked("Term", 4, 4);
x_236 = lean_mk_string_unchecked("app", 3, 3);
x_237 = l_Lean_Name_mkStr4(x_233, x_234, x_235, x_236);
x_238 = lean_mk_string_unchecked("Format.bracket", 14, 14);
x_239 = l_String_toSubstring_x27(x_238);
x_240 = lean_mk_string_unchecked("bracket", 7, 7);
lean_inc(x_240);
lean_inc(x_191);
x_241 = l_Lean_Name_mkStr2(x_191, x_240);
x_242 = l_Lean_addMacroScope(x_232, x_241, x_186);
x_243 = l_Lean_Name_mkStr3(x_195, x_191, x_240);
if (lean_is_scalar(x_220)) {
 x_244 = lean_alloc_ctor(1, 2, 0);
} else {
 x_244 = x_220;
 lean_ctor_set_tag(x_244, 1);
}
lean_ctor_set(x_244, 0, x_243);
lean_ctor_set(x_244, 1, x_197);
x_245 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_245, 0, x_244);
lean_ctor_set(x_245, 1, x_200);
lean_inc(x_225);
x_246 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_246, 0, x_225);
lean_ctor_set(x_246, 1, x_239);
lean_ctor_set(x_246, 2, x_242);
lean_ctor_set(x_246, 3, x_245);
x_247 = lean_mk_string_unchecked("null", 4, 4);
x_248 = l_Lean_Name_mkStr1(x_247);
x_249 = lean_mk_string_unchecked("str", 3, 3);
x_250 = l_Lean_Name_mkStr1(x_249);
x_251 = lean_mk_string_unchecked("\"{ \"", 4, 4);
lean_inc(x_225);
x_252 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_252, 0, x_225);
lean_ctor_set(x_252, 1, x_251);
lean_inc(x_250);
lean_inc(x_225);
x_253 = l_Lean_Syntax_node1(x_225, x_250, x_252);
x_254 = lean_mk_string_unchecked("\" }\"", 4, 4);
lean_inc(x_225);
x_255 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_255, 0, x_225);
lean_ctor_set(x_255, 1, x_254);
lean_inc(x_225);
x_256 = l_Lean_Syntax_node1(x_225, x_250, x_255);
lean_inc(x_225);
x_257 = l_Lean_Syntax_node3(x_225, x_248, x_253, x_218, x_256);
x_258 = l_Lean_Syntax_node2(x_225, x_237, x_246, x_257);
if (lean_is_scalar(x_230)) {
 x_259 = lean_alloc_ctor(0, 2, 0);
} else {
 x_259 = x_230;
}
lean_ctor_set(x_259, 0, x_258);
lean_ctor_set(x_259, 1, x_229);
return x_259;
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; 
lean_dec(x_220);
lean_dec(x_218);
lean_dec(x_195);
lean_dec(x_191);
lean_dec(x_186);
lean_dec(x_15);
x_260 = lean_ctor_get(x_224, 0);
lean_inc(x_260);
x_261 = lean_ctor_get(x_224, 1);
lean_inc(x_261);
if (lean_is_exclusive(x_224)) {
 lean_ctor_release(x_224, 0);
 lean_ctor_release(x_224, 1);
 x_262 = x_224;
} else {
 lean_dec_ref(x_224);
 x_262 = lean_box(0);
}
if (lean_is_scalar(x_262)) {
 x_263 = lean_alloc_ctor(1, 2, 0);
} else {
 x_263 = x_262;
}
lean_ctor_set(x_263, 0, x_260);
lean_ctor_set(x_263, 1, x_261);
return x_263;
}
}
else
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; 
lean_dec(x_220);
lean_dec(x_218);
lean_dec(x_195);
lean_dec(x_191);
lean_dec(x_186);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_2);
x_264 = lean_ctor_get(x_221, 0);
lean_inc(x_264);
x_265 = lean_ctor_get(x_221, 1);
lean_inc(x_265);
if (lean_is_exclusive(x_221)) {
 lean_ctor_release(x_221, 0);
 lean_ctor_release(x_221, 1);
 x_266 = x_221;
} else {
 lean_dec_ref(x_221);
 x_266 = lean_box(0);
}
if (lean_is_scalar(x_266)) {
 x_267 = lean_alloc_ctor(1, 2, 0);
} else {
 x_267 = x_266;
}
lean_ctor_set(x_267, 0, x_264);
lean_ctor_set(x_267, 1, x_265);
return x_267;
}
}
else
{
lean_dec(x_195);
lean_dec(x_191);
lean_dec(x_186);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
return x_217;
}
}
}
}
else
{
uint8_t x_268; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_268 = !lean_is_exclusive(x_20);
if (x_268 == 0)
{
return x_20;
}
else
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; 
x_269 = lean_ctor_get(x_20, 0);
x_270 = lean_ctor_get(x_20, 1);
lean_inc(x_270);
lean_inc(x_269);
lean_dec(x_20);
x_271 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_271, 0, x_269);
lean_ctor_set(x_271, 1, x_270);
return x_271;
}
}
}
else
{
uint8_t x_272; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_4);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForStruct(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_box(0);
x_11 = lean_ctor_get(x_2, 4);
lean_inc(x_11);
x_12 = l_List_head_x21(lean_box(0), x_10, x_11);
lean_dec(x_11);
lean_inc(x_3);
x_13 = l_Lean_getConstInfoCtor___at___Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_st_ref_get(x_8, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_alloc_closure((void*)(l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___boxed), 7, 0);
x_20 = lean_alloc_closure((void*)(l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__1___boxed), 8, 0);
x_21 = lean_ctor_get(x_17, 0);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_ctor_get(x_2, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec(x_22);
x_24 = l_Lean_getStructureFields(x_21, x_23);
x_25 = lean_ctor_get(x_2, 1);
lean_inc(x_25);
x_26 = lean_unsigned_to_nat(0u);
x_27 = lean_alloc_closure((void*)(l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__2___boxed), 16, 7);
lean_closure_set(x_27, 0, x_19);
lean_closure_set(x_27, 1, x_20);
lean_closure_set(x_27, 2, x_24);
lean_closure_set(x_27, 3, x_26);
lean_closure_set(x_27, 4, x_2);
lean_closure_set(x_27, 5, x_1);
lean_closure_set(x_27, 6, x_25);
x_28 = lean_ctor_get(x_14, 0);
lean_inc(x_28);
lean_dec(x_14);
x_29 = lean_ctor_get(x_28, 2);
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_box(0);
x_31 = lean_unbox(x_30);
x_32 = l_Lean_Meta_forallTelescopeReducing___at___Lean_Elab_Deriving_mkInductArgNames_spec__1___redArg(x_29, x_27, x_31, x_3, x_4, x_5, x_6, x_7, x_8, x_18);
return x_32;
}
else
{
uint8_t x_33; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_13);
if (x_33 == 0)
{
return x_13;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_13, 0);
x_35 = lean_ctor_get(x_13, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_13);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_getConstInfoCtor___at___Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_nat_dec_lt(x_3, x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_3);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_st_ref_get(x_5, x_6);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_12 = lean_ctor_get(x_10, 1);
x_13 = lean_ctor_get(x_10, 0);
lean_dec(x_13);
x_14 = lean_ctor_get(x_4, 5);
x_15 = lean_box(0);
x_16 = lean_unbox(x_15);
x_17 = l_Lean_SourceInfo_fromRef(x_14, x_16);
x_18 = lean_mk_string_unchecked("Lean", 4, 4);
x_19 = lean_mk_string_unchecked("Parser", 6, 6);
x_20 = lean_mk_string_unchecked("Term", 4, 4);
x_21 = lean_mk_string_unchecked("hole", 4, 4);
x_22 = l_Lean_Name_mkStr4(x_18, x_19, x_20, x_21);
x_23 = lean_mk_string_unchecked("_", 1, 1);
lean_inc(x_17);
lean_ctor_set_tag(x_10, 2);
lean_ctor_set(x_10, 1, x_23);
lean_ctor_set(x_10, 0, x_17);
x_24 = l_Lean_Syntax_node1(x_17, x_22, x_10);
x_25 = lean_array_push(x_2, x_24);
x_26 = lean_ctor_get(x_1, 2);
x_27 = lean_nat_add(x_3, x_26);
lean_dec(x_3);
x_2 = x_25;
x_3 = x_27;
x_6 = x_12;
goto _start;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_29 = lean_ctor_get(x_10, 1);
lean_inc(x_29);
lean_dec(x_10);
x_30 = lean_ctor_get(x_4, 5);
x_31 = lean_box(0);
x_32 = lean_unbox(x_31);
x_33 = l_Lean_SourceInfo_fromRef(x_30, x_32);
x_34 = lean_mk_string_unchecked("Lean", 4, 4);
x_35 = lean_mk_string_unchecked("Parser", 6, 6);
x_36 = lean_mk_string_unchecked("Term", 4, 4);
x_37 = lean_mk_string_unchecked("hole", 4, 4);
x_38 = l_Lean_Name_mkStr4(x_34, x_35, x_36, x_37);
x_39 = lean_mk_string_unchecked("_", 1, 1);
lean_inc(x_33);
x_40 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_40, 0, x_33);
lean_ctor_set(x_40, 1, x_39);
x_41 = l_Lean_Syntax_node1(x_33, x_38, x_40);
x_42 = lean_array_push(x_2, x_41);
x_43 = lean_ctor_get(x_1, 2);
x_44 = lean_nat_add(x_3, x_43);
lean_dec(x_3);
x_2 = x_42;
x_3 = x_44;
x_6 = x_29;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__0___redArg(x_1, x_2, x_3, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_5, 1);
x_22 = lean_nat_dec_lt(x_7, x_21);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_3);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_6);
lean_ctor_set(x_23, 1, x_14);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_606; uint8_t x_607; lean_object* x_608; lean_object* x_609; 
x_379 = lean_ctor_get(x_6, 0);
lean_inc(x_379);
x_380 = lean_ctor_get(x_6, 1);
lean_inc(x_380);
lean_dec(x_6);
x_381 = lean_array_fget(x_1, x_7);
x_606 = lean_ctor_get(x_2, 1);
x_607 = lean_nat_dec_lt(x_7, x_606);
if (x_607 == 0)
{
lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; 
x_641 = lean_mk_string_unchecked("a", 1, 1);
x_642 = l_Lean_Name_mkStr1(x_641);
x_643 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_642, x_12, x_13, x_14);
x_644 = lean_ctor_get(x_643, 0);
lean_inc(x_644);
x_645 = lean_ctor_get(x_643, 1);
lean_inc(x_645);
lean_dec(x_643);
x_608 = x_644;
x_609 = x_645;
goto block_640;
}
else
{
lean_object* x_646; lean_object* x_647; lean_object* x_648; 
x_646 = lean_box(0);
x_647 = lean_ctor_get(x_4, 1);
x_648 = lean_array_get(x_646, x_647, x_7);
x_608 = x_648;
x_609 = x_14;
goto block_640;
}
block_378:
{
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_unbox(x_34);
lean_dec(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1(x_29, x_27, x_28, x_32, x_30, x_25, x_36);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_39 = lean_ctor_get(x_37, 0);
x_40 = lean_ctor_get(x_37, 1);
x_41 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__2(x_39, x_29, x_27, x_28, x_32, x_30, x_25, x_40);
lean_dec(x_32);
lean_dec(x_28);
lean_dec(x_39);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_43 = lean_ctor_get(x_41, 0);
x_44 = lean_ctor_get(x_41, 1);
x_45 = lean_st_ref_get(x_25, x_44);
lean_dec(x_25);
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_47 = lean_ctor_get(x_45, 0);
x_48 = lean_ctor_get(x_45, 1);
x_49 = lean_ctor_get(x_30, 10);
lean_inc(x_49);
lean_dec(x_30);
x_50 = lean_ctor_get(x_47, 0);
lean_inc(x_50);
lean_dec(x_47);
x_51 = l_Lean_Environment_mainModule(x_50);
lean_dec(x_50);
x_52 = lean_mk_string_unchecked("term_++_", 8, 8);
x_53 = l_Lean_Name_mkStr1(x_52);
x_54 = lean_mk_string_unchecked("++", 2, 2);
lean_inc(x_43);
lean_ctor_set_tag(x_45, 2);
lean_ctor_set(x_45, 1, x_54);
lean_ctor_set(x_45, 0, x_43);
x_55 = lean_mk_string_unchecked("Format.line", 11, 11);
x_56 = l_String_toSubstring_x27(x_55);
x_57 = lean_mk_string_unchecked("Format", 6, 6);
x_58 = lean_mk_string_unchecked("line", 4, 4);
lean_inc(x_58);
lean_inc(x_57);
x_59 = l_Lean_Name_mkStr2(x_57, x_58);
lean_inc(x_49);
lean_inc(x_51);
x_60 = l_Lean_addMacroScope(x_51, x_59, x_49);
x_61 = lean_mk_string_unchecked("Std", 3, 3);
x_62 = l_Lean_Name_mkStr3(x_61, x_57, x_58);
x_63 = lean_box(0);
lean_inc(x_62);
lean_ctor_set_tag(x_41, 1);
lean_ctor_set(x_41, 1, x_63);
lean_ctor_set(x_41, 0, x_62);
x_64 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_64, 0, x_62);
x_65 = lean_box(0);
lean_ctor_set_tag(x_37, 1);
lean_ctor_set(x_37, 1, x_65);
lean_ctor_set(x_37, 0, x_64);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_41);
lean_ctor_set(x_66, 1, x_37);
lean_inc(x_43);
x_67 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_67, 0, x_43);
lean_ctor_set(x_67, 1, x_56);
lean_ctor_set(x_67, 2, x_60);
lean_ctor_set(x_67, 3, x_66);
lean_inc(x_45);
lean_inc(x_53);
lean_inc(x_43);
x_68 = l_Lean_Syntax_node3(x_43, x_53, x_24, x_45, x_67);
x_69 = lean_mk_string_unchecked("Lean", 4, 4);
x_70 = lean_mk_string_unchecked("Parser", 6, 6);
x_71 = lean_mk_string_unchecked("Term", 4, 4);
x_72 = lean_mk_string_unchecked("app", 3, 3);
x_73 = l_Lean_Name_mkStr4(x_69, x_70, x_71, x_72);
x_74 = lean_mk_string_unchecked("reprArg", 7, 7);
lean_inc(x_74);
x_75 = l_String_toSubstring_x27(x_74);
x_76 = l_Lean_Name_mkStr1(x_74);
lean_inc(x_76);
x_77 = l_Lean_addMacroScope(x_51, x_76, x_49);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_63);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_65);
lean_inc(x_43);
x_80 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_80, 0, x_43);
lean_ctor_set(x_80, 1, x_75);
lean_ctor_set(x_80, 2, x_77);
lean_ctor_set(x_80, 3, x_79);
x_81 = lean_mk_string_unchecked("null", 4, 4);
x_82 = l_Lean_Name_mkStr1(x_81);
x_83 = lean_mk_syntax_ident(x_26);
lean_inc(x_43);
x_84 = l_Lean_Syntax_node1(x_43, x_82, x_83);
lean_inc(x_43);
x_85 = l_Lean_Syntax_node2(x_43, x_73, x_80, x_84);
x_86 = l_Lean_Syntax_node3(x_43, x_53, x_68, x_45, x_85);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_31);
lean_ctor_set(x_87, 1, x_86);
x_15 = x_87;
x_16 = x_48;
goto block_20;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_88 = lean_ctor_get(x_45, 0);
x_89 = lean_ctor_get(x_45, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_45);
x_90 = lean_ctor_get(x_30, 10);
lean_inc(x_90);
lean_dec(x_30);
x_91 = lean_ctor_get(x_88, 0);
lean_inc(x_91);
lean_dec(x_88);
x_92 = l_Lean_Environment_mainModule(x_91);
lean_dec(x_91);
x_93 = lean_mk_string_unchecked("term_++_", 8, 8);
x_94 = l_Lean_Name_mkStr1(x_93);
x_95 = lean_mk_string_unchecked("++", 2, 2);
lean_inc(x_43);
x_96 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_96, 0, x_43);
lean_ctor_set(x_96, 1, x_95);
x_97 = lean_mk_string_unchecked("Format.line", 11, 11);
x_98 = l_String_toSubstring_x27(x_97);
x_99 = lean_mk_string_unchecked("Format", 6, 6);
x_100 = lean_mk_string_unchecked("line", 4, 4);
lean_inc(x_100);
lean_inc(x_99);
x_101 = l_Lean_Name_mkStr2(x_99, x_100);
lean_inc(x_90);
lean_inc(x_92);
x_102 = l_Lean_addMacroScope(x_92, x_101, x_90);
x_103 = lean_mk_string_unchecked("Std", 3, 3);
x_104 = l_Lean_Name_mkStr3(x_103, x_99, x_100);
x_105 = lean_box(0);
lean_inc(x_104);
lean_ctor_set_tag(x_41, 1);
lean_ctor_set(x_41, 1, x_105);
lean_ctor_set(x_41, 0, x_104);
x_106 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_106, 0, x_104);
x_107 = lean_box(0);
lean_ctor_set_tag(x_37, 1);
lean_ctor_set(x_37, 1, x_107);
lean_ctor_set(x_37, 0, x_106);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_41);
lean_ctor_set(x_108, 1, x_37);
lean_inc(x_43);
x_109 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_109, 0, x_43);
lean_ctor_set(x_109, 1, x_98);
lean_ctor_set(x_109, 2, x_102);
lean_ctor_set(x_109, 3, x_108);
lean_inc(x_96);
lean_inc(x_94);
lean_inc(x_43);
x_110 = l_Lean_Syntax_node3(x_43, x_94, x_24, x_96, x_109);
x_111 = lean_mk_string_unchecked("Lean", 4, 4);
x_112 = lean_mk_string_unchecked("Parser", 6, 6);
x_113 = lean_mk_string_unchecked("Term", 4, 4);
x_114 = lean_mk_string_unchecked("app", 3, 3);
x_115 = l_Lean_Name_mkStr4(x_111, x_112, x_113, x_114);
x_116 = lean_mk_string_unchecked("reprArg", 7, 7);
lean_inc(x_116);
x_117 = l_String_toSubstring_x27(x_116);
x_118 = l_Lean_Name_mkStr1(x_116);
lean_inc(x_118);
x_119 = l_Lean_addMacroScope(x_92, x_118, x_90);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_105);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_107);
lean_inc(x_43);
x_122 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_122, 0, x_43);
lean_ctor_set(x_122, 1, x_117);
lean_ctor_set(x_122, 2, x_119);
lean_ctor_set(x_122, 3, x_121);
x_123 = lean_mk_string_unchecked("null", 4, 4);
x_124 = l_Lean_Name_mkStr1(x_123);
x_125 = lean_mk_syntax_ident(x_26);
lean_inc(x_43);
x_126 = l_Lean_Syntax_node1(x_43, x_124, x_125);
lean_inc(x_43);
x_127 = l_Lean_Syntax_node2(x_43, x_115, x_122, x_126);
x_128 = l_Lean_Syntax_node3(x_43, x_94, x_110, x_96, x_127);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_31);
lean_ctor_set(x_129, 1, x_128);
x_15 = x_129;
x_16 = x_89;
goto block_20;
}
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_130 = lean_ctor_get(x_41, 0);
x_131 = lean_ctor_get(x_41, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_41);
x_132 = lean_st_ref_get(x_25, x_131);
lean_dec(x_25);
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_135 = x_132;
} else {
 lean_dec_ref(x_132);
 x_135 = lean_box(0);
}
x_136 = lean_ctor_get(x_30, 10);
lean_inc(x_136);
lean_dec(x_30);
x_137 = lean_ctor_get(x_133, 0);
lean_inc(x_137);
lean_dec(x_133);
x_138 = l_Lean_Environment_mainModule(x_137);
lean_dec(x_137);
x_139 = lean_mk_string_unchecked("term_++_", 8, 8);
x_140 = l_Lean_Name_mkStr1(x_139);
x_141 = lean_mk_string_unchecked("++", 2, 2);
lean_inc(x_130);
if (lean_is_scalar(x_135)) {
 x_142 = lean_alloc_ctor(2, 2, 0);
} else {
 x_142 = x_135;
 lean_ctor_set_tag(x_142, 2);
}
lean_ctor_set(x_142, 0, x_130);
lean_ctor_set(x_142, 1, x_141);
x_143 = lean_mk_string_unchecked("Format.line", 11, 11);
x_144 = l_String_toSubstring_x27(x_143);
x_145 = lean_mk_string_unchecked("Format", 6, 6);
x_146 = lean_mk_string_unchecked("line", 4, 4);
lean_inc(x_146);
lean_inc(x_145);
x_147 = l_Lean_Name_mkStr2(x_145, x_146);
lean_inc(x_136);
lean_inc(x_138);
x_148 = l_Lean_addMacroScope(x_138, x_147, x_136);
x_149 = lean_mk_string_unchecked("Std", 3, 3);
x_150 = l_Lean_Name_mkStr3(x_149, x_145, x_146);
x_151 = lean_box(0);
lean_inc(x_150);
x_152 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set(x_152, 1, x_151);
x_153 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_153, 0, x_150);
x_154 = lean_box(0);
lean_ctor_set_tag(x_37, 1);
lean_ctor_set(x_37, 1, x_154);
lean_ctor_set(x_37, 0, x_153);
x_155 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_155, 0, x_152);
lean_ctor_set(x_155, 1, x_37);
lean_inc(x_130);
x_156 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_156, 0, x_130);
lean_ctor_set(x_156, 1, x_144);
lean_ctor_set(x_156, 2, x_148);
lean_ctor_set(x_156, 3, x_155);
lean_inc(x_142);
lean_inc(x_140);
lean_inc(x_130);
x_157 = l_Lean_Syntax_node3(x_130, x_140, x_24, x_142, x_156);
x_158 = lean_mk_string_unchecked("Lean", 4, 4);
x_159 = lean_mk_string_unchecked("Parser", 6, 6);
x_160 = lean_mk_string_unchecked("Term", 4, 4);
x_161 = lean_mk_string_unchecked("app", 3, 3);
x_162 = l_Lean_Name_mkStr4(x_158, x_159, x_160, x_161);
x_163 = lean_mk_string_unchecked("reprArg", 7, 7);
lean_inc(x_163);
x_164 = l_String_toSubstring_x27(x_163);
x_165 = l_Lean_Name_mkStr1(x_163);
lean_inc(x_165);
x_166 = l_Lean_addMacroScope(x_138, x_165, x_136);
x_167 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_167, 0, x_165);
lean_ctor_set(x_167, 1, x_151);
x_168 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_168, 0, x_167);
lean_ctor_set(x_168, 1, x_154);
lean_inc(x_130);
x_169 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_169, 0, x_130);
lean_ctor_set(x_169, 1, x_164);
lean_ctor_set(x_169, 2, x_166);
lean_ctor_set(x_169, 3, x_168);
x_170 = lean_mk_string_unchecked("null", 4, 4);
x_171 = l_Lean_Name_mkStr1(x_170);
x_172 = lean_mk_syntax_ident(x_26);
lean_inc(x_130);
x_173 = l_Lean_Syntax_node1(x_130, x_171, x_172);
lean_inc(x_130);
x_174 = l_Lean_Syntax_node2(x_130, x_162, x_169, x_173);
x_175 = l_Lean_Syntax_node3(x_130, x_140, x_157, x_142, x_174);
x_176 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_176, 0, x_31);
lean_ctor_set(x_176, 1, x_175);
x_15 = x_176;
x_16 = x_134;
goto block_20;
}
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_177 = lean_ctor_get(x_37, 0);
x_178 = lean_ctor_get(x_37, 1);
lean_inc(x_178);
lean_inc(x_177);
lean_dec(x_37);
x_179 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__2(x_177, x_29, x_27, x_28, x_32, x_30, x_25, x_178);
lean_dec(x_32);
lean_dec(x_28);
lean_dec(x_177);
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_179, 1);
lean_inc(x_181);
if (lean_is_exclusive(x_179)) {
 lean_ctor_release(x_179, 0);
 lean_ctor_release(x_179, 1);
 x_182 = x_179;
} else {
 lean_dec_ref(x_179);
 x_182 = lean_box(0);
}
x_183 = lean_st_ref_get(x_25, x_181);
lean_dec(x_25);
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
x_187 = lean_ctor_get(x_30, 10);
lean_inc(x_187);
lean_dec(x_30);
x_188 = lean_ctor_get(x_184, 0);
lean_inc(x_188);
lean_dec(x_184);
x_189 = l_Lean_Environment_mainModule(x_188);
lean_dec(x_188);
x_190 = lean_mk_string_unchecked("term_++_", 8, 8);
x_191 = l_Lean_Name_mkStr1(x_190);
x_192 = lean_mk_string_unchecked("++", 2, 2);
lean_inc(x_180);
if (lean_is_scalar(x_186)) {
 x_193 = lean_alloc_ctor(2, 2, 0);
} else {
 x_193 = x_186;
 lean_ctor_set_tag(x_193, 2);
}
lean_ctor_set(x_193, 0, x_180);
lean_ctor_set(x_193, 1, x_192);
x_194 = lean_mk_string_unchecked("Format.line", 11, 11);
x_195 = l_String_toSubstring_x27(x_194);
x_196 = lean_mk_string_unchecked("Format", 6, 6);
x_197 = lean_mk_string_unchecked("line", 4, 4);
lean_inc(x_197);
lean_inc(x_196);
x_198 = l_Lean_Name_mkStr2(x_196, x_197);
lean_inc(x_187);
lean_inc(x_189);
x_199 = l_Lean_addMacroScope(x_189, x_198, x_187);
x_200 = lean_mk_string_unchecked("Std", 3, 3);
x_201 = l_Lean_Name_mkStr3(x_200, x_196, x_197);
x_202 = lean_box(0);
lean_inc(x_201);
if (lean_is_scalar(x_182)) {
 x_203 = lean_alloc_ctor(1, 2, 0);
} else {
 x_203 = x_182;
 lean_ctor_set_tag(x_203, 1);
}
lean_ctor_set(x_203, 0, x_201);
lean_ctor_set(x_203, 1, x_202);
x_204 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_204, 0, x_201);
x_205 = lean_box(0);
x_206 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_206, 0, x_204);
lean_ctor_set(x_206, 1, x_205);
x_207 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_207, 0, x_203);
lean_ctor_set(x_207, 1, x_206);
lean_inc(x_180);
x_208 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_208, 0, x_180);
lean_ctor_set(x_208, 1, x_195);
lean_ctor_set(x_208, 2, x_199);
lean_ctor_set(x_208, 3, x_207);
lean_inc(x_193);
lean_inc(x_191);
lean_inc(x_180);
x_209 = l_Lean_Syntax_node3(x_180, x_191, x_24, x_193, x_208);
x_210 = lean_mk_string_unchecked("Lean", 4, 4);
x_211 = lean_mk_string_unchecked("Parser", 6, 6);
x_212 = lean_mk_string_unchecked("Term", 4, 4);
x_213 = lean_mk_string_unchecked("app", 3, 3);
x_214 = l_Lean_Name_mkStr4(x_210, x_211, x_212, x_213);
x_215 = lean_mk_string_unchecked("reprArg", 7, 7);
lean_inc(x_215);
x_216 = l_String_toSubstring_x27(x_215);
x_217 = l_Lean_Name_mkStr1(x_215);
lean_inc(x_217);
x_218 = l_Lean_addMacroScope(x_189, x_217, x_187);
x_219 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_219, 0, x_217);
lean_ctor_set(x_219, 1, x_202);
x_220 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_220, 0, x_219);
lean_ctor_set(x_220, 1, x_205);
lean_inc(x_180);
x_221 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_221, 0, x_180);
lean_ctor_set(x_221, 1, x_216);
lean_ctor_set(x_221, 2, x_218);
lean_ctor_set(x_221, 3, x_220);
x_222 = lean_mk_string_unchecked("null", 4, 4);
x_223 = l_Lean_Name_mkStr1(x_222);
x_224 = lean_mk_syntax_ident(x_26);
lean_inc(x_180);
x_225 = l_Lean_Syntax_node1(x_180, x_223, x_224);
lean_inc(x_180);
x_226 = l_Lean_Syntax_node2(x_180, x_214, x_221, x_225);
x_227 = l_Lean_Syntax_node3(x_180, x_191, x_209, x_193, x_226);
x_228 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_228, 0, x_31);
lean_ctor_set(x_228, 1, x_227);
x_15 = x_228;
x_16 = x_185;
goto block_20;
}
}
else
{
lean_object* x_229; lean_object* x_230; uint8_t x_231; 
lean_dec(x_26);
x_229 = lean_ctor_get(x_33, 1);
lean_inc(x_229);
lean_dec(x_33);
x_230 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1(x_29, x_27, x_28, x_32, x_30, x_25, x_229);
x_231 = !lean_is_exclusive(x_230);
if (x_231 == 0)
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; uint8_t x_235; 
x_232 = lean_ctor_get(x_230, 0);
x_233 = lean_ctor_get(x_230, 1);
x_234 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__2(x_232, x_29, x_27, x_28, x_32, x_30, x_25, x_233);
lean_dec(x_32);
lean_dec(x_28);
lean_dec(x_232);
x_235 = !lean_is_exclusive(x_234);
if (x_235 == 0)
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; uint8_t x_239; 
x_236 = lean_ctor_get(x_234, 0);
x_237 = lean_ctor_get(x_234, 1);
x_238 = lean_st_ref_get(x_25, x_237);
lean_dec(x_25);
x_239 = !lean_is_exclusive(x_238);
if (x_239 == 0)
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; 
x_240 = lean_ctor_get(x_238, 0);
x_241 = lean_ctor_get(x_238, 1);
x_242 = lean_ctor_get(x_30, 10);
lean_inc(x_242);
lean_dec(x_30);
x_243 = lean_ctor_get(x_240, 0);
lean_inc(x_243);
lean_dec(x_240);
x_244 = l_Lean_Environment_mainModule(x_243);
lean_dec(x_243);
x_245 = lean_mk_string_unchecked("term_++_", 8, 8);
x_246 = l_Lean_Name_mkStr1(x_245);
x_247 = lean_mk_string_unchecked("++", 2, 2);
lean_inc(x_236);
lean_ctor_set_tag(x_238, 2);
lean_ctor_set(x_238, 1, x_247);
lean_ctor_set(x_238, 0, x_236);
x_248 = lean_mk_string_unchecked("Format.line", 11, 11);
x_249 = l_String_toSubstring_x27(x_248);
x_250 = lean_mk_string_unchecked("Format", 6, 6);
x_251 = lean_mk_string_unchecked("line", 4, 4);
lean_inc(x_251);
lean_inc(x_250);
x_252 = l_Lean_Name_mkStr2(x_250, x_251);
x_253 = l_Lean_addMacroScope(x_244, x_252, x_242);
x_254 = lean_mk_string_unchecked("Std", 3, 3);
x_255 = l_Lean_Name_mkStr3(x_254, x_250, x_251);
x_256 = lean_box(0);
lean_inc(x_255);
lean_ctor_set_tag(x_234, 1);
lean_ctor_set(x_234, 1, x_256);
lean_ctor_set(x_234, 0, x_255);
x_257 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_257, 0, x_255);
x_258 = lean_box(0);
lean_ctor_set_tag(x_230, 1);
lean_ctor_set(x_230, 1, x_258);
lean_ctor_set(x_230, 0, x_257);
x_259 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_259, 0, x_234);
lean_ctor_set(x_259, 1, x_230);
lean_inc(x_236);
x_260 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_260, 0, x_236);
lean_ctor_set(x_260, 1, x_249);
lean_ctor_set(x_260, 2, x_253);
lean_ctor_set(x_260, 3, x_259);
lean_inc(x_238);
lean_inc(x_246);
lean_inc(x_236);
x_261 = l_Lean_Syntax_node3(x_236, x_246, x_24, x_238, x_260);
x_262 = lean_mk_string_unchecked("str", 3, 3);
x_263 = l_Lean_Name_mkStr1(x_262);
x_264 = lean_mk_string_unchecked("\"_\"", 3, 3);
lean_inc(x_236);
x_265 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_265, 0, x_236);
lean_ctor_set(x_265, 1, x_264);
lean_inc(x_236);
x_266 = l_Lean_Syntax_node1(x_236, x_263, x_265);
x_267 = l_Lean_Syntax_node3(x_236, x_246, x_261, x_238, x_266);
x_268 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_268, 0, x_31);
lean_ctor_set(x_268, 1, x_267);
x_15 = x_268;
x_16 = x_241;
goto block_20;
}
else
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; 
x_269 = lean_ctor_get(x_238, 0);
x_270 = lean_ctor_get(x_238, 1);
lean_inc(x_270);
lean_inc(x_269);
lean_dec(x_238);
x_271 = lean_ctor_get(x_30, 10);
lean_inc(x_271);
lean_dec(x_30);
x_272 = lean_ctor_get(x_269, 0);
lean_inc(x_272);
lean_dec(x_269);
x_273 = l_Lean_Environment_mainModule(x_272);
lean_dec(x_272);
x_274 = lean_mk_string_unchecked("term_++_", 8, 8);
x_275 = l_Lean_Name_mkStr1(x_274);
x_276 = lean_mk_string_unchecked("++", 2, 2);
lean_inc(x_236);
x_277 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_277, 0, x_236);
lean_ctor_set(x_277, 1, x_276);
x_278 = lean_mk_string_unchecked("Format.line", 11, 11);
x_279 = l_String_toSubstring_x27(x_278);
x_280 = lean_mk_string_unchecked("Format", 6, 6);
x_281 = lean_mk_string_unchecked("line", 4, 4);
lean_inc(x_281);
lean_inc(x_280);
x_282 = l_Lean_Name_mkStr2(x_280, x_281);
x_283 = l_Lean_addMacroScope(x_273, x_282, x_271);
x_284 = lean_mk_string_unchecked("Std", 3, 3);
x_285 = l_Lean_Name_mkStr3(x_284, x_280, x_281);
x_286 = lean_box(0);
lean_inc(x_285);
lean_ctor_set_tag(x_234, 1);
lean_ctor_set(x_234, 1, x_286);
lean_ctor_set(x_234, 0, x_285);
x_287 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_287, 0, x_285);
x_288 = lean_box(0);
lean_ctor_set_tag(x_230, 1);
lean_ctor_set(x_230, 1, x_288);
lean_ctor_set(x_230, 0, x_287);
x_289 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_289, 0, x_234);
lean_ctor_set(x_289, 1, x_230);
lean_inc(x_236);
x_290 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_290, 0, x_236);
lean_ctor_set(x_290, 1, x_279);
lean_ctor_set(x_290, 2, x_283);
lean_ctor_set(x_290, 3, x_289);
lean_inc(x_277);
lean_inc(x_275);
lean_inc(x_236);
x_291 = l_Lean_Syntax_node3(x_236, x_275, x_24, x_277, x_290);
x_292 = lean_mk_string_unchecked("str", 3, 3);
x_293 = l_Lean_Name_mkStr1(x_292);
x_294 = lean_mk_string_unchecked("\"_\"", 3, 3);
lean_inc(x_236);
x_295 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_295, 0, x_236);
lean_ctor_set(x_295, 1, x_294);
lean_inc(x_236);
x_296 = l_Lean_Syntax_node1(x_236, x_293, x_295);
x_297 = l_Lean_Syntax_node3(x_236, x_275, x_291, x_277, x_296);
x_298 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_298, 0, x_31);
lean_ctor_set(x_298, 1, x_297);
x_15 = x_298;
x_16 = x_270;
goto block_20;
}
}
else
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; 
x_299 = lean_ctor_get(x_234, 0);
x_300 = lean_ctor_get(x_234, 1);
lean_inc(x_300);
lean_inc(x_299);
lean_dec(x_234);
x_301 = lean_st_ref_get(x_25, x_300);
lean_dec(x_25);
x_302 = lean_ctor_get(x_301, 0);
lean_inc(x_302);
x_303 = lean_ctor_get(x_301, 1);
lean_inc(x_303);
if (lean_is_exclusive(x_301)) {
 lean_ctor_release(x_301, 0);
 lean_ctor_release(x_301, 1);
 x_304 = x_301;
} else {
 lean_dec_ref(x_301);
 x_304 = lean_box(0);
}
x_305 = lean_ctor_get(x_30, 10);
lean_inc(x_305);
lean_dec(x_30);
x_306 = lean_ctor_get(x_302, 0);
lean_inc(x_306);
lean_dec(x_302);
x_307 = l_Lean_Environment_mainModule(x_306);
lean_dec(x_306);
x_308 = lean_mk_string_unchecked("term_++_", 8, 8);
x_309 = l_Lean_Name_mkStr1(x_308);
x_310 = lean_mk_string_unchecked("++", 2, 2);
lean_inc(x_299);
if (lean_is_scalar(x_304)) {
 x_311 = lean_alloc_ctor(2, 2, 0);
} else {
 x_311 = x_304;
 lean_ctor_set_tag(x_311, 2);
}
lean_ctor_set(x_311, 0, x_299);
lean_ctor_set(x_311, 1, x_310);
x_312 = lean_mk_string_unchecked("Format.line", 11, 11);
x_313 = l_String_toSubstring_x27(x_312);
x_314 = lean_mk_string_unchecked("Format", 6, 6);
x_315 = lean_mk_string_unchecked("line", 4, 4);
lean_inc(x_315);
lean_inc(x_314);
x_316 = l_Lean_Name_mkStr2(x_314, x_315);
x_317 = l_Lean_addMacroScope(x_307, x_316, x_305);
x_318 = lean_mk_string_unchecked("Std", 3, 3);
x_319 = l_Lean_Name_mkStr3(x_318, x_314, x_315);
x_320 = lean_box(0);
lean_inc(x_319);
x_321 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_321, 0, x_319);
lean_ctor_set(x_321, 1, x_320);
x_322 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_322, 0, x_319);
x_323 = lean_box(0);
lean_ctor_set_tag(x_230, 1);
lean_ctor_set(x_230, 1, x_323);
lean_ctor_set(x_230, 0, x_322);
x_324 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_324, 0, x_321);
lean_ctor_set(x_324, 1, x_230);
lean_inc(x_299);
x_325 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_325, 0, x_299);
lean_ctor_set(x_325, 1, x_313);
lean_ctor_set(x_325, 2, x_317);
lean_ctor_set(x_325, 3, x_324);
lean_inc(x_311);
lean_inc(x_309);
lean_inc(x_299);
x_326 = l_Lean_Syntax_node3(x_299, x_309, x_24, x_311, x_325);
x_327 = lean_mk_string_unchecked("str", 3, 3);
x_328 = l_Lean_Name_mkStr1(x_327);
x_329 = lean_mk_string_unchecked("\"_\"", 3, 3);
lean_inc(x_299);
x_330 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_330, 0, x_299);
lean_ctor_set(x_330, 1, x_329);
lean_inc(x_299);
x_331 = l_Lean_Syntax_node1(x_299, x_328, x_330);
x_332 = l_Lean_Syntax_node3(x_299, x_309, x_326, x_311, x_331);
x_333 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_333, 0, x_31);
lean_ctor_set(x_333, 1, x_332);
x_15 = x_333;
x_16 = x_303;
goto block_20;
}
}
else
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; 
x_334 = lean_ctor_get(x_230, 0);
x_335 = lean_ctor_get(x_230, 1);
lean_inc(x_335);
lean_inc(x_334);
lean_dec(x_230);
x_336 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__2(x_334, x_29, x_27, x_28, x_32, x_30, x_25, x_335);
lean_dec(x_32);
lean_dec(x_28);
lean_dec(x_334);
x_337 = lean_ctor_get(x_336, 0);
lean_inc(x_337);
x_338 = lean_ctor_get(x_336, 1);
lean_inc(x_338);
if (lean_is_exclusive(x_336)) {
 lean_ctor_release(x_336, 0);
 lean_ctor_release(x_336, 1);
 x_339 = x_336;
} else {
 lean_dec_ref(x_336);
 x_339 = lean_box(0);
}
x_340 = lean_st_ref_get(x_25, x_338);
lean_dec(x_25);
x_341 = lean_ctor_get(x_340, 0);
lean_inc(x_341);
x_342 = lean_ctor_get(x_340, 1);
lean_inc(x_342);
if (lean_is_exclusive(x_340)) {
 lean_ctor_release(x_340, 0);
 lean_ctor_release(x_340, 1);
 x_343 = x_340;
} else {
 lean_dec_ref(x_340);
 x_343 = lean_box(0);
}
x_344 = lean_ctor_get(x_30, 10);
lean_inc(x_344);
lean_dec(x_30);
x_345 = lean_ctor_get(x_341, 0);
lean_inc(x_345);
lean_dec(x_341);
x_346 = l_Lean_Environment_mainModule(x_345);
lean_dec(x_345);
x_347 = lean_mk_string_unchecked("term_++_", 8, 8);
x_348 = l_Lean_Name_mkStr1(x_347);
x_349 = lean_mk_string_unchecked("++", 2, 2);
lean_inc(x_337);
if (lean_is_scalar(x_343)) {
 x_350 = lean_alloc_ctor(2, 2, 0);
} else {
 x_350 = x_343;
 lean_ctor_set_tag(x_350, 2);
}
lean_ctor_set(x_350, 0, x_337);
lean_ctor_set(x_350, 1, x_349);
x_351 = lean_mk_string_unchecked("Format.line", 11, 11);
x_352 = l_String_toSubstring_x27(x_351);
x_353 = lean_mk_string_unchecked("Format", 6, 6);
x_354 = lean_mk_string_unchecked("line", 4, 4);
lean_inc(x_354);
lean_inc(x_353);
x_355 = l_Lean_Name_mkStr2(x_353, x_354);
x_356 = l_Lean_addMacroScope(x_346, x_355, x_344);
x_357 = lean_mk_string_unchecked("Std", 3, 3);
x_358 = l_Lean_Name_mkStr3(x_357, x_353, x_354);
x_359 = lean_box(0);
lean_inc(x_358);
if (lean_is_scalar(x_339)) {
 x_360 = lean_alloc_ctor(1, 2, 0);
} else {
 x_360 = x_339;
 lean_ctor_set_tag(x_360, 1);
}
lean_ctor_set(x_360, 0, x_358);
lean_ctor_set(x_360, 1, x_359);
x_361 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_361, 0, x_358);
x_362 = lean_box(0);
x_363 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_363, 0, x_361);
lean_ctor_set(x_363, 1, x_362);
x_364 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_364, 0, x_360);
lean_ctor_set(x_364, 1, x_363);
lean_inc(x_337);
x_365 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_365, 0, x_337);
lean_ctor_set(x_365, 1, x_352);
lean_ctor_set(x_365, 2, x_356);
lean_ctor_set(x_365, 3, x_364);
lean_inc(x_350);
lean_inc(x_348);
lean_inc(x_337);
x_366 = l_Lean_Syntax_node3(x_337, x_348, x_24, x_350, x_365);
x_367 = lean_mk_string_unchecked("str", 3, 3);
x_368 = l_Lean_Name_mkStr1(x_367);
x_369 = lean_mk_string_unchecked("\"_\"", 3, 3);
lean_inc(x_337);
x_370 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_370, 0, x_337);
lean_ctor_set(x_370, 1, x_369);
lean_inc(x_337);
x_371 = l_Lean_Syntax_node1(x_337, x_368, x_370);
x_372 = l_Lean_Syntax_node3(x_337, x_348, x_366, x_350, x_371);
x_373 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_373, 0, x_31);
lean_ctor_set(x_373, 1, x_372);
x_15 = x_373;
x_16 = x_342;
goto block_20;
}
}
}
else
{
uint8_t x_374; 
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_3);
x_374 = !lean_is_exclusive(x_33);
if (x_374 == 0)
{
return x_33;
}
else
{
lean_object* x_375; lean_object* x_376; lean_object* x_377; 
x_375 = lean_ctor_get(x_33, 0);
x_376 = lean_ctor_get(x_33, 1);
lean_inc(x_376);
lean_inc(x_375);
lean_dec(x_33);
x_377 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_377, 0, x_375);
lean_ctor_set(x_377, 1, x_376);
return x_377;
}
}
}
block_605:
{
lean_object* x_391; lean_object* x_392; 
x_391 = l_Lean_Expr_fvarId_x21(x_381);
lean_inc(x_386);
x_392 = l_Lean_FVarId_getBinderInfo___redArg(x_391, x_386, x_388, x_389, x_390);
if (lean_obj_tag(x_392) == 0)
{
lean_object* x_393; lean_object* x_394; uint8_t x_395; uint8_t x_396; 
x_393 = lean_ctor_get(x_392, 0);
lean_inc(x_393);
x_394 = lean_ctor_get(x_392, 1);
lean_inc(x_394);
lean_dec(x_392);
x_395 = lean_unbox(x_393);
lean_dec(x_393);
x_396 = l_Lean_BinderInfo_isExplicit(x_395);
if (x_396 == 0)
{
lean_object* x_397; 
lean_dec(x_389);
lean_dec(x_388);
lean_dec(x_387);
lean_dec(x_386);
lean_dec(x_382);
lean_dec(x_381);
x_397 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_397, 0, x_383);
lean_ctor_set(x_397, 1, x_380);
x_15 = x_397;
x_16 = x_394;
goto block_20;
}
else
{
lean_object* x_398; 
lean_inc(x_389);
lean_inc(x_388);
lean_inc(x_387);
lean_inc(x_386);
lean_inc(x_381);
x_398 = lean_infer_type(x_381, x_386, x_387, x_388, x_389, x_394);
if (lean_obj_tag(x_398) == 0)
{
lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; uint8_t x_403; 
x_399 = lean_ctor_get(x_398, 0);
lean_inc(x_399);
x_400 = lean_ctor_get(x_398, 1);
lean_inc(x_400);
lean_dec(x_398);
x_401 = lean_ctor_get(x_2, 0);
x_402 = lean_ctor_get(x_401, 0);
x_403 = l_Lean_Expr_isAppOf(x_399, x_402);
lean_dec(x_399);
if (x_403 == 0)
{
lean_object* x_404; 
lean_inc(x_389);
lean_inc(x_388);
lean_inc(x_387);
lean_inc(x_386);
lean_inc(x_381);
x_404 = l_Lean_Meta_isType(x_381, x_386, x_387, x_388, x_389, x_400);
if (lean_obj_tag(x_404) == 0)
{
lean_object* x_405; uint8_t x_406; 
x_405 = lean_ctor_get(x_404, 0);
lean_inc(x_405);
x_406 = lean_unbox(x_405);
lean_dec(x_405);
if (x_406 == 0)
{
lean_object* x_407; lean_object* x_408; 
x_407 = lean_ctor_get(x_404, 1);
lean_inc(x_407);
lean_dec(x_404);
lean_inc(x_389);
lean_inc(x_388);
lean_inc(x_387);
lean_inc(x_386);
x_408 = l_Lean_Meta_isProof(x_381, x_386, x_387, x_388, x_389, x_407);
x_24 = x_380;
x_25 = x_389;
x_26 = x_382;
x_27 = x_385;
x_28 = x_386;
x_29 = x_384;
x_30 = x_388;
x_31 = x_383;
x_32 = x_387;
x_33 = x_408;
goto block_378;
}
else
{
lean_dec(x_381);
x_24 = x_380;
x_25 = x_389;
x_26 = x_382;
x_27 = x_385;
x_28 = x_386;
x_29 = x_384;
x_30 = x_388;
x_31 = x_383;
x_32 = x_387;
x_33 = x_404;
goto block_378;
}
}
else
{
lean_dec(x_381);
x_24 = x_380;
x_25 = x_389;
x_26 = x_382;
x_27 = x_385;
x_28 = x_386;
x_29 = x_384;
x_30 = x_388;
x_31 = x_383;
x_32 = x_387;
x_33 = x_404;
goto block_378;
}
}
else
{
lean_object* x_409; uint8_t x_410; 
lean_dec(x_381);
x_409 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1(x_384, x_385, x_386, x_387, x_388, x_389, x_400);
x_410 = !lean_is_exclusive(x_409);
if (x_410 == 0)
{
lean_object* x_411; lean_object* x_412; lean_object* x_413; uint8_t x_414; 
x_411 = lean_ctor_get(x_409, 0);
x_412 = lean_ctor_get(x_409, 1);
x_413 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__2(x_411, x_384, x_385, x_386, x_387, x_388, x_389, x_412);
lean_dec(x_387);
lean_dec(x_386);
lean_dec(x_411);
x_414 = !lean_is_exclusive(x_413);
if (x_414 == 0)
{
lean_object* x_415; lean_object* x_416; lean_object* x_417; uint8_t x_418; 
x_415 = lean_ctor_get(x_413, 0);
x_416 = lean_ctor_get(x_413, 1);
x_417 = lean_st_ref_get(x_389, x_416);
lean_dec(x_389);
x_418 = !lean_is_exclusive(x_417);
if (x_418 == 0)
{
lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; 
x_419 = lean_ctor_get(x_417, 0);
x_420 = lean_ctor_get(x_417, 1);
x_421 = lean_ctor_get(x_388, 10);
lean_inc(x_421);
lean_dec(x_388);
x_422 = lean_ctor_get(x_419, 0);
lean_inc(x_422);
lean_dec(x_419);
x_423 = l_Lean_Environment_mainModule(x_422);
lean_dec(x_422);
x_424 = lean_mk_string_unchecked("term_++_", 8, 8);
x_425 = l_Lean_Name_mkStr1(x_424);
x_426 = lean_mk_string_unchecked("++", 2, 2);
lean_inc(x_415);
lean_ctor_set_tag(x_417, 2);
lean_ctor_set(x_417, 1, x_426);
lean_ctor_set(x_417, 0, x_415);
x_427 = lean_mk_string_unchecked("Format.line", 11, 11);
x_428 = l_String_toSubstring_x27(x_427);
x_429 = lean_mk_string_unchecked("Format", 6, 6);
x_430 = lean_mk_string_unchecked("line", 4, 4);
lean_inc(x_430);
lean_inc(x_429);
x_431 = l_Lean_Name_mkStr2(x_429, x_430);
x_432 = l_Lean_addMacroScope(x_423, x_431, x_421);
x_433 = lean_mk_string_unchecked("Std", 3, 3);
x_434 = l_Lean_Name_mkStr3(x_433, x_429, x_430);
x_435 = lean_box(0);
lean_inc(x_434);
lean_ctor_set_tag(x_413, 1);
lean_ctor_set(x_413, 1, x_435);
lean_ctor_set(x_413, 0, x_434);
x_436 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_436, 0, x_434);
x_437 = lean_box(0);
lean_ctor_set_tag(x_409, 1);
lean_ctor_set(x_409, 1, x_437);
lean_ctor_set(x_409, 0, x_436);
x_438 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_438, 0, x_413);
lean_ctor_set(x_438, 1, x_409);
lean_inc(x_415);
x_439 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_439, 0, x_415);
lean_ctor_set(x_439, 1, x_428);
lean_ctor_set(x_439, 2, x_432);
lean_ctor_set(x_439, 3, x_438);
lean_inc(x_417);
lean_inc(x_425);
lean_inc(x_415);
x_440 = l_Lean_Syntax_node3(x_415, x_425, x_380, x_417, x_439);
x_441 = lean_mk_string_unchecked("Lean", 4, 4);
x_442 = lean_mk_string_unchecked("Parser", 6, 6);
x_443 = lean_mk_string_unchecked("Term", 4, 4);
x_444 = lean_mk_string_unchecked("app", 3, 3);
x_445 = l_Lean_Name_mkStr4(x_441, x_442, x_443, x_444);
lean_inc(x_3);
x_446 = lean_mk_syntax_ident(x_3);
x_447 = lean_mk_string_unchecked("null", 4, 4);
x_448 = l_Lean_Name_mkStr1(x_447);
x_449 = lean_mk_syntax_ident(x_382);
x_450 = lean_mk_string_unchecked("termMax_prec", 12, 12);
x_451 = l_Lean_Name_mkStr1(x_450);
x_452 = lean_mk_string_unchecked("max_prec", 8, 8);
lean_inc(x_415);
x_453 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_453, 0, x_415);
lean_ctor_set(x_453, 1, x_452);
lean_inc(x_415);
x_454 = l_Lean_Syntax_node1(x_415, x_451, x_453);
lean_inc(x_415);
x_455 = l_Lean_Syntax_node2(x_415, x_448, x_449, x_454);
lean_inc(x_415);
x_456 = l_Lean_Syntax_node2(x_415, x_445, x_446, x_455);
x_457 = l_Lean_Syntax_node3(x_415, x_425, x_440, x_417, x_456);
x_458 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_458, 0, x_383);
lean_ctor_set(x_458, 1, x_457);
x_15 = x_458;
x_16 = x_420;
goto block_20;
}
else
{
lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; 
x_459 = lean_ctor_get(x_417, 0);
x_460 = lean_ctor_get(x_417, 1);
lean_inc(x_460);
lean_inc(x_459);
lean_dec(x_417);
x_461 = lean_ctor_get(x_388, 10);
lean_inc(x_461);
lean_dec(x_388);
x_462 = lean_ctor_get(x_459, 0);
lean_inc(x_462);
lean_dec(x_459);
x_463 = l_Lean_Environment_mainModule(x_462);
lean_dec(x_462);
x_464 = lean_mk_string_unchecked("term_++_", 8, 8);
x_465 = l_Lean_Name_mkStr1(x_464);
x_466 = lean_mk_string_unchecked("++", 2, 2);
lean_inc(x_415);
x_467 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_467, 0, x_415);
lean_ctor_set(x_467, 1, x_466);
x_468 = lean_mk_string_unchecked("Format.line", 11, 11);
x_469 = l_String_toSubstring_x27(x_468);
x_470 = lean_mk_string_unchecked("Format", 6, 6);
x_471 = lean_mk_string_unchecked("line", 4, 4);
lean_inc(x_471);
lean_inc(x_470);
x_472 = l_Lean_Name_mkStr2(x_470, x_471);
x_473 = l_Lean_addMacroScope(x_463, x_472, x_461);
x_474 = lean_mk_string_unchecked("Std", 3, 3);
x_475 = l_Lean_Name_mkStr3(x_474, x_470, x_471);
x_476 = lean_box(0);
lean_inc(x_475);
lean_ctor_set_tag(x_413, 1);
lean_ctor_set(x_413, 1, x_476);
lean_ctor_set(x_413, 0, x_475);
x_477 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_477, 0, x_475);
x_478 = lean_box(0);
lean_ctor_set_tag(x_409, 1);
lean_ctor_set(x_409, 1, x_478);
lean_ctor_set(x_409, 0, x_477);
x_479 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_479, 0, x_413);
lean_ctor_set(x_479, 1, x_409);
lean_inc(x_415);
x_480 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_480, 0, x_415);
lean_ctor_set(x_480, 1, x_469);
lean_ctor_set(x_480, 2, x_473);
lean_ctor_set(x_480, 3, x_479);
lean_inc(x_467);
lean_inc(x_465);
lean_inc(x_415);
x_481 = l_Lean_Syntax_node3(x_415, x_465, x_380, x_467, x_480);
x_482 = lean_mk_string_unchecked("Lean", 4, 4);
x_483 = lean_mk_string_unchecked("Parser", 6, 6);
x_484 = lean_mk_string_unchecked("Term", 4, 4);
x_485 = lean_mk_string_unchecked("app", 3, 3);
x_486 = l_Lean_Name_mkStr4(x_482, x_483, x_484, x_485);
lean_inc(x_3);
x_487 = lean_mk_syntax_ident(x_3);
x_488 = lean_mk_string_unchecked("null", 4, 4);
x_489 = l_Lean_Name_mkStr1(x_488);
x_490 = lean_mk_syntax_ident(x_382);
x_491 = lean_mk_string_unchecked("termMax_prec", 12, 12);
x_492 = l_Lean_Name_mkStr1(x_491);
x_493 = lean_mk_string_unchecked("max_prec", 8, 8);
lean_inc(x_415);
x_494 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_494, 0, x_415);
lean_ctor_set(x_494, 1, x_493);
lean_inc(x_415);
x_495 = l_Lean_Syntax_node1(x_415, x_492, x_494);
lean_inc(x_415);
x_496 = l_Lean_Syntax_node2(x_415, x_489, x_490, x_495);
lean_inc(x_415);
x_497 = l_Lean_Syntax_node2(x_415, x_486, x_487, x_496);
x_498 = l_Lean_Syntax_node3(x_415, x_465, x_481, x_467, x_497);
x_499 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_499, 0, x_383);
lean_ctor_set(x_499, 1, x_498);
x_15 = x_499;
x_16 = x_460;
goto block_20;
}
}
else
{
lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; 
x_500 = lean_ctor_get(x_413, 0);
x_501 = lean_ctor_get(x_413, 1);
lean_inc(x_501);
lean_inc(x_500);
lean_dec(x_413);
x_502 = lean_st_ref_get(x_389, x_501);
lean_dec(x_389);
x_503 = lean_ctor_get(x_502, 0);
lean_inc(x_503);
x_504 = lean_ctor_get(x_502, 1);
lean_inc(x_504);
if (lean_is_exclusive(x_502)) {
 lean_ctor_release(x_502, 0);
 lean_ctor_release(x_502, 1);
 x_505 = x_502;
} else {
 lean_dec_ref(x_502);
 x_505 = lean_box(0);
}
x_506 = lean_ctor_get(x_388, 10);
lean_inc(x_506);
lean_dec(x_388);
x_507 = lean_ctor_get(x_503, 0);
lean_inc(x_507);
lean_dec(x_503);
x_508 = l_Lean_Environment_mainModule(x_507);
lean_dec(x_507);
x_509 = lean_mk_string_unchecked("term_++_", 8, 8);
x_510 = l_Lean_Name_mkStr1(x_509);
x_511 = lean_mk_string_unchecked("++", 2, 2);
lean_inc(x_500);
if (lean_is_scalar(x_505)) {
 x_512 = lean_alloc_ctor(2, 2, 0);
} else {
 x_512 = x_505;
 lean_ctor_set_tag(x_512, 2);
}
lean_ctor_set(x_512, 0, x_500);
lean_ctor_set(x_512, 1, x_511);
x_513 = lean_mk_string_unchecked("Format.line", 11, 11);
x_514 = l_String_toSubstring_x27(x_513);
x_515 = lean_mk_string_unchecked("Format", 6, 6);
x_516 = lean_mk_string_unchecked("line", 4, 4);
lean_inc(x_516);
lean_inc(x_515);
x_517 = l_Lean_Name_mkStr2(x_515, x_516);
x_518 = l_Lean_addMacroScope(x_508, x_517, x_506);
x_519 = lean_mk_string_unchecked("Std", 3, 3);
x_520 = l_Lean_Name_mkStr3(x_519, x_515, x_516);
x_521 = lean_box(0);
lean_inc(x_520);
x_522 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_522, 0, x_520);
lean_ctor_set(x_522, 1, x_521);
x_523 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_523, 0, x_520);
x_524 = lean_box(0);
lean_ctor_set_tag(x_409, 1);
lean_ctor_set(x_409, 1, x_524);
lean_ctor_set(x_409, 0, x_523);
x_525 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_525, 0, x_522);
lean_ctor_set(x_525, 1, x_409);
lean_inc(x_500);
x_526 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_526, 0, x_500);
lean_ctor_set(x_526, 1, x_514);
lean_ctor_set(x_526, 2, x_518);
lean_ctor_set(x_526, 3, x_525);
lean_inc(x_512);
lean_inc(x_510);
lean_inc(x_500);
x_527 = l_Lean_Syntax_node3(x_500, x_510, x_380, x_512, x_526);
x_528 = lean_mk_string_unchecked("Lean", 4, 4);
x_529 = lean_mk_string_unchecked("Parser", 6, 6);
x_530 = lean_mk_string_unchecked("Term", 4, 4);
x_531 = lean_mk_string_unchecked("app", 3, 3);
x_532 = l_Lean_Name_mkStr4(x_528, x_529, x_530, x_531);
lean_inc(x_3);
x_533 = lean_mk_syntax_ident(x_3);
x_534 = lean_mk_string_unchecked("null", 4, 4);
x_535 = l_Lean_Name_mkStr1(x_534);
x_536 = lean_mk_syntax_ident(x_382);
x_537 = lean_mk_string_unchecked("termMax_prec", 12, 12);
x_538 = l_Lean_Name_mkStr1(x_537);
x_539 = lean_mk_string_unchecked("max_prec", 8, 8);
lean_inc(x_500);
x_540 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_540, 0, x_500);
lean_ctor_set(x_540, 1, x_539);
lean_inc(x_500);
x_541 = l_Lean_Syntax_node1(x_500, x_538, x_540);
lean_inc(x_500);
x_542 = l_Lean_Syntax_node2(x_500, x_535, x_536, x_541);
lean_inc(x_500);
x_543 = l_Lean_Syntax_node2(x_500, x_532, x_533, x_542);
x_544 = l_Lean_Syntax_node3(x_500, x_510, x_527, x_512, x_543);
x_545 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_545, 0, x_383);
lean_ctor_set(x_545, 1, x_544);
x_15 = x_545;
x_16 = x_504;
goto block_20;
}
}
else
{
lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; 
x_546 = lean_ctor_get(x_409, 0);
x_547 = lean_ctor_get(x_409, 1);
lean_inc(x_547);
lean_inc(x_546);
lean_dec(x_409);
x_548 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__2(x_546, x_384, x_385, x_386, x_387, x_388, x_389, x_547);
lean_dec(x_387);
lean_dec(x_386);
lean_dec(x_546);
x_549 = lean_ctor_get(x_548, 0);
lean_inc(x_549);
x_550 = lean_ctor_get(x_548, 1);
lean_inc(x_550);
if (lean_is_exclusive(x_548)) {
 lean_ctor_release(x_548, 0);
 lean_ctor_release(x_548, 1);
 x_551 = x_548;
} else {
 lean_dec_ref(x_548);
 x_551 = lean_box(0);
}
x_552 = lean_st_ref_get(x_389, x_550);
lean_dec(x_389);
x_553 = lean_ctor_get(x_552, 0);
lean_inc(x_553);
x_554 = lean_ctor_get(x_552, 1);
lean_inc(x_554);
if (lean_is_exclusive(x_552)) {
 lean_ctor_release(x_552, 0);
 lean_ctor_release(x_552, 1);
 x_555 = x_552;
} else {
 lean_dec_ref(x_552);
 x_555 = lean_box(0);
}
x_556 = lean_ctor_get(x_388, 10);
lean_inc(x_556);
lean_dec(x_388);
x_557 = lean_ctor_get(x_553, 0);
lean_inc(x_557);
lean_dec(x_553);
x_558 = l_Lean_Environment_mainModule(x_557);
lean_dec(x_557);
x_559 = lean_mk_string_unchecked("term_++_", 8, 8);
x_560 = l_Lean_Name_mkStr1(x_559);
x_561 = lean_mk_string_unchecked("++", 2, 2);
lean_inc(x_549);
if (lean_is_scalar(x_555)) {
 x_562 = lean_alloc_ctor(2, 2, 0);
} else {
 x_562 = x_555;
 lean_ctor_set_tag(x_562, 2);
}
lean_ctor_set(x_562, 0, x_549);
lean_ctor_set(x_562, 1, x_561);
x_563 = lean_mk_string_unchecked("Format.line", 11, 11);
x_564 = l_String_toSubstring_x27(x_563);
x_565 = lean_mk_string_unchecked("Format", 6, 6);
x_566 = lean_mk_string_unchecked("line", 4, 4);
lean_inc(x_566);
lean_inc(x_565);
x_567 = l_Lean_Name_mkStr2(x_565, x_566);
x_568 = l_Lean_addMacroScope(x_558, x_567, x_556);
x_569 = lean_mk_string_unchecked("Std", 3, 3);
x_570 = l_Lean_Name_mkStr3(x_569, x_565, x_566);
x_571 = lean_box(0);
lean_inc(x_570);
if (lean_is_scalar(x_551)) {
 x_572 = lean_alloc_ctor(1, 2, 0);
} else {
 x_572 = x_551;
 lean_ctor_set_tag(x_572, 1);
}
lean_ctor_set(x_572, 0, x_570);
lean_ctor_set(x_572, 1, x_571);
x_573 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_573, 0, x_570);
x_574 = lean_box(0);
x_575 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_575, 0, x_573);
lean_ctor_set(x_575, 1, x_574);
x_576 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_576, 0, x_572);
lean_ctor_set(x_576, 1, x_575);
lean_inc(x_549);
x_577 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_577, 0, x_549);
lean_ctor_set(x_577, 1, x_564);
lean_ctor_set(x_577, 2, x_568);
lean_ctor_set(x_577, 3, x_576);
lean_inc(x_562);
lean_inc(x_560);
lean_inc(x_549);
x_578 = l_Lean_Syntax_node3(x_549, x_560, x_380, x_562, x_577);
x_579 = lean_mk_string_unchecked("Lean", 4, 4);
x_580 = lean_mk_string_unchecked("Parser", 6, 6);
x_581 = lean_mk_string_unchecked("Term", 4, 4);
x_582 = lean_mk_string_unchecked("app", 3, 3);
x_583 = l_Lean_Name_mkStr4(x_579, x_580, x_581, x_582);
lean_inc(x_3);
x_584 = lean_mk_syntax_ident(x_3);
x_585 = lean_mk_string_unchecked("null", 4, 4);
x_586 = l_Lean_Name_mkStr1(x_585);
x_587 = lean_mk_syntax_ident(x_382);
x_588 = lean_mk_string_unchecked("termMax_prec", 12, 12);
x_589 = l_Lean_Name_mkStr1(x_588);
x_590 = lean_mk_string_unchecked("max_prec", 8, 8);
lean_inc(x_549);
x_591 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_591, 0, x_549);
lean_ctor_set(x_591, 1, x_590);
lean_inc(x_549);
x_592 = l_Lean_Syntax_node1(x_549, x_589, x_591);
lean_inc(x_549);
x_593 = l_Lean_Syntax_node2(x_549, x_586, x_587, x_592);
lean_inc(x_549);
x_594 = l_Lean_Syntax_node2(x_549, x_583, x_584, x_593);
x_595 = l_Lean_Syntax_node3(x_549, x_560, x_578, x_562, x_594);
x_596 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_596, 0, x_383);
lean_ctor_set(x_596, 1, x_595);
x_15 = x_596;
x_16 = x_554;
goto block_20;
}
}
}
else
{
uint8_t x_597; 
lean_dec(x_389);
lean_dec(x_388);
lean_dec(x_387);
lean_dec(x_386);
lean_dec(x_383);
lean_dec(x_382);
lean_dec(x_381);
lean_dec(x_380);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_3);
x_597 = !lean_is_exclusive(x_398);
if (x_597 == 0)
{
return x_398;
}
else
{
lean_object* x_598; lean_object* x_599; lean_object* x_600; 
x_598 = lean_ctor_get(x_398, 0);
x_599 = lean_ctor_get(x_398, 1);
lean_inc(x_599);
lean_inc(x_598);
lean_dec(x_398);
x_600 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_600, 0, x_598);
lean_ctor_set(x_600, 1, x_599);
return x_600;
}
}
}
}
else
{
uint8_t x_601; 
lean_dec(x_389);
lean_dec(x_388);
lean_dec(x_387);
lean_dec(x_386);
lean_dec(x_383);
lean_dec(x_382);
lean_dec(x_381);
lean_dec(x_380);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_3);
x_601 = !lean_is_exclusive(x_392);
if (x_601 == 0)
{
return x_392;
}
else
{
lean_object* x_602; lean_object* x_603; lean_object* x_604; 
x_602 = lean_ctor_get(x_392, 0);
x_603 = lean_ctor_get(x_392, 1);
lean_inc(x_603);
lean_inc(x_602);
lean_dec(x_392);
x_604 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_604, 0, x_602);
lean_ctor_set(x_604, 1, x_603);
return x_604;
}
}
}
block_640:
{
if (x_607 == 0)
{
lean_object* x_610; lean_object* x_611; 
lean_inc(x_608);
x_610 = lean_mk_syntax_ident(x_608);
x_611 = lean_array_push(x_379, x_610);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_382 = x_608;
x_383 = x_611;
x_384 = x_8;
x_385 = x_9;
x_386 = x_10;
x_387 = x_11;
x_388 = x_12;
x_389 = x_13;
x_390 = x_609;
goto block_605;
}
else
{
lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; uint8_t x_619; 
x_612 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1(x_8, x_9, x_10, x_11, x_12, x_13, x_609);
x_613 = lean_ctor_get(x_612, 0);
lean_inc(x_613);
x_614 = lean_ctor_get(x_612, 1);
lean_inc(x_614);
lean_dec(x_612);
x_615 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__2(x_613, x_8, x_9, x_10, x_11, x_12, x_13, x_614);
lean_dec(x_613);
x_616 = lean_ctor_get(x_615, 0);
lean_inc(x_616);
x_617 = lean_ctor_get(x_615, 1);
lean_inc(x_617);
lean_dec(x_615);
x_618 = lean_st_ref_get(x_13, x_617);
x_619 = !lean_is_exclusive(x_618);
if (x_619 == 0)
{
lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; 
x_620 = lean_ctor_get(x_618, 1);
x_621 = lean_ctor_get(x_618, 0);
lean_dec(x_621);
x_622 = lean_mk_string_unchecked("Lean", 4, 4);
x_623 = lean_mk_string_unchecked("Parser", 6, 6);
x_624 = lean_mk_string_unchecked("Term", 4, 4);
x_625 = lean_mk_string_unchecked("hole", 4, 4);
x_626 = l_Lean_Name_mkStr4(x_622, x_623, x_624, x_625);
x_627 = lean_mk_string_unchecked("_", 1, 1);
lean_inc(x_616);
lean_ctor_set_tag(x_618, 2);
lean_ctor_set(x_618, 1, x_627);
lean_ctor_set(x_618, 0, x_616);
x_628 = l_Lean_Syntax_node1(x_616, x_626, x_618);
x_629 = lean_array_push(x_379, x_628);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_382 = x_608;
x_383 = x_629;
x_384 = x_8;
x_385 = x_9;
x_386 = x_10;
x_387 = x_11;
x_388 = x_12;
x_389 = x_13;
x_390 = x_620;
goto block_605;
}
else
{
lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; 
x_630 = lean_ctor_get(x_618, 1);
lean_inc(x_630);
lean_dec(x_618);
x_631 = lean_mk_string_unchecked("Lean", 4, 4);
x_632 = lean_mk_string_unchecked("Parser", 6, 6);
x_633 = lean_mk_string_unchecked("Term", 4, 4);
x_634 = lean_mk_string_unchecked("hole", 4, 4);
x_635 = l_Lean_Name_mkStr4(x_631, x_632, x_633, x_634);
x_636 = lean_mk_string_unchecked("_", 1, 1);
lean_inc(x_616);
x_637 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_637, 0, x_616);
lean_ctor_set(x_637, 1, x_636);
x_638 = l_Lean_Syntax_node1(x_616, x_635, x_637);
x_639 = lean_array_push(x_379, x_638);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_382 = x_608;
x_383 = x_639;
x_384 = x_8;
x_385 = x_9;
x_386 = x_10;
x_387 = x_11;
x_388 = x_12;
x_389 = x_13;
x_390 = x_630;
goto block_605;
}
}
}
}
block_20:
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_5, 2);
x_18 = lean_nat_add(x_7, x_17);
lean_dec(x_7);
x_6 = x_15;
x_7 = x_18;
x_14 = x_16;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_17;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2_spec__2___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19) {
_start:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_20 = lean_ctor_get(x_1, 2);
x_21 = lean_unsigned_to_nat(1u);
lean_inc(x_20);
lean_inc(x_2);
x_22 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_22, 0, x_2);
lean_ctor_set(x_22, 1, x_20);
lean_ctor_set(x_22, 2, x_21);
lean_inc(x_2);
lean_inc(x_3);
x_23 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__0___redArg(x_22, x_3, x_2, x_17, x_18, x_19);
lean_dec(x_22);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_4);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_27 = lean_apply_7(x_4, x_13, x_14, x_15, x_16, x_17, x_18, x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
lean_inc(x_5);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_30 = lean_apply_8(x_5, x_28, x_13, x_14, x_15, x_16, x_17, x_18, x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_st_ref_get(x_18, x_32);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_35 = lean_ctor_get(x_33, 0);
x_36 = lean_ctor_get(x_33, 1);
x_37 = lean_ctor_get(x_6, 0);
lean_inc(x_37);
lean_dec(x_6);
x_38 = lean_box(1);
x_39 = lean_unbox(x_38);
x_40 = l_Lean_Name_toString(x_37, x_39, x_7);
x_41 = lean_box(2);
x_42 = l_Lean_Syntax_mkStrLit(x_40, x_41);
lean_dec(x_40);
x_43 = lean_ctor_get(x_17, 10);
lean_inc(x_43);
x_44 = lean_ctor_get(x_35, 0);
lean_inc(x_44);
lean_dec(x_35);
x_45 = l_Lean_Environment_mainModule(x_44);
lean_dec(x_44);
x_46 = lean_mk_string_unchecked("Lean", 4, 4);
x_47 = lean_mk_string_unchecked("Parser", 6, 6);
x_48 = lean_mk_string_unchecked("Term", 4, 4);
x_49 = lean_mk_string_unchecked("app", 3, 3);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
x_50 = l_Lean_Name_mkStr4(x_46, x_47, x_48, x_49);
x_51 = lean_mk_string_unchecked("Format.text", 11, 11);
x_52 = l_String_toSubstring_x27(x_51);
x_53 = lean_mk_string_unchecked("Format", 6, 6);
x_54 = lean_mk_string_unchecked("text", 4, 4);
lean_inc(x_54);
lean_inc(x_53);
x_55 = l_Lean_Name_mkStr2(x_53, x_54);
lean_inc(x_43);
x_56 = l_Lean_addMacroScope(x_45, x_55, x_43);
x_57 = lean_mk_string_unchecked("Std", 3, 3);
lean_inc(x_53);
lean_inc(x_57);
x_58 = l_Lean_Name_mkStr3(x_57, x_53, x_54);
x_59 = lean_box(0);
lean_inc(x_58);
lean_ctor_set_tag(x_33, 1);
lean_ctor_set(x_33, 1, x_59);
lean_ctor_set(x_33, 0, x_58);
x_60 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_60, 0, x_58);
x_61 = lean_box(0);
lean_ctor_set_tag(x_23, 1);
lean_ctor_set(x_23, 1, x_61);
lean_ctor_set(x_23, 0, x_60);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_33);
lean_ctor_set(x_62, 1, x_23);
lean_inc(x_31);
x_63 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_63, 0, x_31);
lean_ctor_set(x_63, 1, x_52);
lean_ctor_set(x_63, 2, x_56);
lean_ctor_set(x_63, 3, x_62);
x_64 = lean_mk_string_unchecked("null", 4, 4);
x_65 = l_Lean_Name_mkStr1(x_64);
lean_inc(x_65);
lean_inc(x_31);
x_66 = l_Lean_Syntax_node1(x_31, x_65, x_42);
lean_inc(x_50);
x_67 = l_Lean_Syntax_node2(x_31, x_50, x_63, x_66);
x_68 = lean_array_get_size(x_11);
lean_inc(x_2);
x_69 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_69, 0, x_2);
lean_ctor_set(x_69, 1, x_68);
lean_ctor_set(x_69, 2, x_21);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_3);
lean_ctor_set(x_70, 1, x_67);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_2);
x_71 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg(x_11, x_1, x_8, x_9, x_69, x_70, x_2, x_13, x_14, x_15, x_16, x_17, x_18, x_36);
lean_dec(x_69);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_74 = !lean_is_exclusive(x_72);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_72, 0);
x_76 = lean_ctor_get(x_72, 1);
lean_inc(x_4);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_77 = lean_apply_7(x_4, x_13, x_14, x_15, x_16, x_17, x_18, x_73);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
lean_inc(x_5);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_80 = lean_apply_8(x_5, x_78, x_13, x_14, x_15, x_16, x_17, x_18, x_79);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
x_83 = lean_st_ref_get(x_18, x_82);
x_84 = !lean_is_exclusive(x_83);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_85 = lean_ctor_get(x_83, 1);
x_86 = lean_ctor_get(x_83, 0);
lean_dec(x_86);
x_87 = lean_mk_string_unchecked("explicit", 8, 8);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
x_88 = l_Lean_Name_mkStr4(x_46, x_47, x_48, x_87);
x_89 = lean_mk_string_unchecked("@", 1, 1);
lean_inc(x_81);
lean_ctor_set_tag(x_83, 2);
lean_ctor_set(x_83, 1, x_89);
lean_ctor_set(x_83, 0, x_81);
x_90 = lean_mk_syntax_ident(x_10);
x_91 = l_Array_mkArray0(lean_box(0));
lean_inc(x_91);
x_92 = l_Array_append(lean_box(0), x_91, x_75);
lean_dec(x_75);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_93 = lean_apply_7(x_4, x_13, x_14, x_15, x_16, x_17, x_18, x_85);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
lean_inc(x_18);
x_96 = lean_apply_8(x_5, x_94, x_13, x_14, x_15, x_16, x_17, x_18, x_95);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; 
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
lean_dec(x_96);
x_99 = lean_st_ref_get(x_18, x_98);
lean_dec(x_18);
x_100 = !lean_is_exclusive(x_99);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; size_t x_111; size_t x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_101 = lean_ctor_get(x_99, 0);
lean_inc(x_81);
x_102 = l_Lean_Syntax_node2(x_81, x_88, x_83, x_90);
lean_inc(x_65);
lean_inc(x_81);
x_103 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_103, 0, x_81);
lean_ctor_set(x_103, 1, x_65);
lean_ctor_set(x_103, 2, x_92);
lean_inc(x_50);
x_104 = l_Lean_Syntax_node2(x_81, x_50, x_102, x_103);
x_105 = lean_array_push(x_25, x_104);
x_106 = lean_ctor_get(x_101, 0);
lean_inc(x_106);
lean_dec(x_101);
x_107 = l_Lean_Environment_mainModule(x_106);
lean_dec(x_106);
x_108 = lean_mk_string_unchecked("matchAlt", 8, 8);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
x_109 = l_Lean_Name_mkStr4(x_46, x_47, x_48, x_108);
x_110 = lean_mk_string_unchecked("|", 1, 1);
lean_inc(x_97);
lean_ctor_set_tag(x_72, 2);
lean_ctor_set(x_72, 1, x_110);
lean_ctor_set(x_72, 0, x_97);
x_111 = lean_array_size(x_105);
x_112 = lean_usize_of_nat(x_2);
lean_dec(x_2);
x_113 = l_Array_mapMUnsafe_map___at___Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1_spec__0(x_111, x_112, x_105);
x_114 = lean_mk_string_unchecked(",", 1, 1);
x_115 = l_Lean_mkAtom(x_114);
x_116 = l_Lean_mkSepArray(x_113, x_115);
lean_dec(x_113);
x_117 = l_Array_append(lean_box(0), x_91, x_116);
lean_dec(x_116);
lean_inc(x_65);
lean_inc(x_97);
x_118 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_118, 0, x_97);
lean_ctor_set(x_118, 1, x_65);
lean_ctor_set(x_118, 2, x_117);
lean_inc(x_65);
lean_inc(x_97);
x_119 = l_Lean_Syntax_node1(x_97, x_65, x_118);
x_120 = lean_mk_string_unchecked("=>", 2, 2);
lean_inc(x_97);
x_121 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_121, 0, x_97);
lean_ctor_set(x_121, 1, x_120);
x_122 = lean_mk_string_unchecked("Repr.addAppParen", 16, 16);
x_123 = l_String_toSubstring_x27(x_122);
x_124 = lean_mk_string_unchecked("Repr", 4, 4);
x_125 = lean_mk_string_unchecked("addAppParen", 11, 11);
x_126 = l_Lean_Name_mkStr2(x_124, x_125);
lean_inc(x_43);
lean_inc(x_126);
lean_inc(x_107);
x_127 = l_Lean_addMacroScope(x_107, x_126, x_43);
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_59);
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_61);
lean_inc(x_97);
x_130 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_130, 0, x_97);
lean_ctor_set(x_130, 1, x_123);
lean_ctor_set(x_130, 2, x_127);
lean_ctor_set(x_130, 3, x_129);
x_131 = lean_mk_string_unchecked("paren", 5, 5);
x_132 = l_Lean_Name_mkStr4(x_46, x_47, x_48, x_131);
x_133 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_97);
x_134 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_134, 0, x_97);
lean_ctor_set(x_134, 1, x_133);
x_135 = lean_mk_string_unchecked("Format.group", 12, 12);
x_136 = l_String_toSubstring_x27(x_135);
x_137 = lean_mk_string_unchecked("group", 5, 5);
lean_inc(x_137);
lean_inc(x_53);
x_138 = l_Lean_Name_mkStr2(x_53, x_137);
lean_inc(x_43);
lean_inc(x_107);
x_139 = l_Lean_addMacroScope(x_107, x_138, x_43);
lean_inc(x_53);
lean_inc(x_57);
x_140 = l_Lean_Name_mkStr3(x_57, x_53, x_137);
lean_inc(x_140);
x_141 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_59);
x_142 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_142, 0, x_140);
x_143 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_61);
x_144 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_144, 0, x_141);
lean_ctor_set(x_144, 1, x_143);
lean_inc(x_97);
x_145 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_145, 0, x_97);
lean_ctor_set(x_145, 1, x_136);
lean_ctor_set(x_145, 2, x_139);
lean_ctor_set(x_145, 3, x_144);
x_146 = lean_mk_string_unchecked("Format.nest", 11, 11);
x_147 = l_String_toSubstring_x27(x_146);
x_148 = lean_mk_string_unchecked("nest", 4, 4);
lean_inc(x_148);
lean_inc(x_53);
x_149 = l_Lean_Name_mkStr2(x_53, x_148);
lean_inc(x_43);
lean_inc(x_107);
x_150 = l_Lean_addMacroScope(x_107, x_149, x_43);
x_151 = l_Lean_Name_mkStr3(x_57, x_53, x_148);
lean_inc(x_151);
x_152 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_152, 0, x_151);
lean_ctor_set(x_152, 1, x_59);
x_153 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_153, 0, x_151);
x_154 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_61);
x_155 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_155, 0, x_152);
lean_ctor_set(x_155, 1, x_154);
lean_inc(x_97);
x_156 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_156, 0, x_97);
lean_ctor_set(x_156, 1, x_147);
lean_ctor_set(x_156, 2, x_150);
lean_ctor_set(x_156, 3, x_155);
x_157 = lean_mk_string_unchecked("termIfThenElse", 14, 14);
x_158 = l_Lean_Name_mkStr1(x_157);
x_159 = lean_mk_string_unchecked("if", 2, 2);
lean_inc(x_97);
x_160 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_160, 0, x_97);
lean_ctor_set(x_160, 1, x_159);
x_161 = lean_mk_string_unchecked("term_>=_", 8, 8);
x_162 = l_Lean_Name_mkStr1(x_161);
x_163 = lean_mk_string_unchecked("prec", 4, 4);
lean_inc(x_163);
x_164 = l_String_toSubstring_x27(x_163);
x_165 = l_Lean_Name_mkStr1(x_163);
x_166 = l_Lean_addMacroScope(x_107, x_165, x_43);
lean_inc(x_97);
x_167 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_167, 0, x_97);
lean_ctor_set(x_167, 1, x_164);
lean_ctor_set(x_167, 2, x_166);
lean_ctor_set(x_167, 3, x_61);
x_168 = lean_mk_string_unchecked(">=", 2, 2);
lean_inc(x_97);
x_169 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_169, 0, x_97);
lean_ctor_set(x_169, 1, x_168);
x_170 = lean_mk_string_unchecked("termMax_prec", 12, 12);
x_171 = l_Lean_Name_mkStr1(x_170);
x_172 = lean_mk_string_unchecked("max_prec", 8, 8);
lean_inc(x_97);
x_173 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_173, 0, x_97);
lean_ctor_set(x_173, 1, x_172);
lean_inc(x_97);
x_174 = l_Lean_Syntax_node1(x_97, x_171, x_173);
lean_inc(x_167);
lean_inc(x_97);
x_175 = l_Lean_Syntax_node3(x_97, x_162, x_167, x_169, x_174);
x_176 = lean_mk_string_unchecked("then", 4, 4);
lean_inc(x_97);
x_177 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_177, 0, x_97);
lean_ctor_set(x_177, 1, x_176);
x_178 = lean_mk_string_unchecked("num", 3, 3);
x_179 = l_Lean_Name_mkStr1(x_178);
x_180 = lean_mk_string_unchecked("1", 1, 1);
lean_inc(x_97);
x_181 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_181, 0, x_97);
lean_ctor_set(x_181, 1, x_180);
lean_inc(x_179);
lean_inc(x_97);
x_182 = l_Lean_Syntax_node1(x_97, x_179, x_181);
x_183 = lean_mk_string_unchecked("else", 4, 4);
lean_inc(x_97);
x_184 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_184, 0, x_97);
lean_ctor_set(x_184, 1, x_183);
x_185 = lean_mk_string_unchecked("2", 1, 1);
lean_inc(x_97);
x_186 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_186, 0, x_97);
lean_ctor_set(x_186, 1, x_185);
lean_inc(x_97);
x_187 = l_Lean_Syntax_node1(x_97, x_179, x_186);
lean_inc(x_97);
x_188 = l_Lean_Syntax_node6(x_97, x_158, x_160, x_175, x_177, x_182, x_184, x_187);
x_189 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_97);
x_190 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_190, 0, x_97);
lean_ctor_set(x_190, 1, x_189);
lean_inc(x_190);
lean_inc(x_134);
lean_inc(x_132);
lean_inc(x_97);
x_191 = l_Lean_Syntax_node3(x_97, x_132, x_134, x_188, x_190);
lean_inc(x_190);
lean_inc(x_134);
lean_inc(x_132);
lean_inc(x_97);
x_192 = l_Lean_Syntax_node3(x_97, x_132, x_134, x_76, x_190);
lean_inc(x_65);
lean_inc(x_97);
x_193 = l_Lean_Syntax_node2(x_97, x_65, x_191, x_192);
lean_inc(x_50);
lean_inc(x_97);
x_194 = l_Lean_Syntax_node2(x_97, x_50, x_156, x_193);
lean_inc(x_190);
lean_inc(x_134);
lean_inc(x_132);
lean_inc(x_97);
x_195 = l_Lean_Syntax_node3(x_97, x_132, x_134, x_194, x_190);
lean_inc(x_65);
lean_inc(x_97);
x_196 = l_Lean_Syntax_node1(x_97, x_65, x_195);
lean_inc(x_50);
lean_inc(x_97);
x_197 = l_Lean_Syntax_node2(x_97, x_50, x_145, x_196);
lean_inc(x_97);
x_198 = l_Lean_Syntax_node3(x_97, x_132, x_134, x_197, x_190);
lean_inc(x_97);
x_199 = l_Lean_Syntax_node2(x_97, x_65, x_198, x_167);
lean_inc(x_97);
x_200 = l_Lean_Syntax_node2(x_97, x_50, x_130, x_199);
x_201 = l_Lean_Syntax_node4(x_97, x_109, x_72, x_119, x_121, x_200);
lean_ctor_set(x_99, 0, x_201);
return x_99;
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; size_t x_213; size_t x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; 
x_202 = lean_ctor_get(x_99, 0);
x_203 = lean_ctor_get(x_99, 1);
lean_inc(x_203);
lean_inc(x_202);
lean_dec(x_99);
lean_inc(x_81);
x_204 = l_Lean_Syntax_node2(x_81, x_88, x_83, x_90);
lean_inc(x_65);
lean_inc(x_81);
x_205 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_205, 0, x_81);
lean_ctor_set(x_205, 1, x_65);
lean_ctor_set(x_205, 2, x_92);
lean_inc(x_50);
x_206 = l_Lean_Syntax_node2(x_81, x_50, x_204, x_205);
x_207 = lean_array_push(x_25, x_206);
x_208 = lean_ctor_get(x_202, 0);
lean_inc(x_208);
lean_dec(x_202);
x_209 = l_Lean_Environment_mainModule(x_208);
lean_dec(x_208);
x_210 = lean_mk_string_unchecked("matchAlt", 8, 8);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
x_211 = l_Lean_Name_mkStr4(x_46, x_47, x_48, x_210);
x_212 = lean_mk_string_unchecked("|", 1, 1);
lean_inc(x_97);
lean_ctor_set_tag(x_72, 2);
lean_ctor_set(x_72, 1, x_212);
lean_ctor_set(x_72, 0, x_97);
x_213 = lean_array_size(x_207);
x_214 = lean_usize_of_nat(x_2);
lean_dec(x_2);
x_215 = l_Array_mapMUnsafe_map___at___Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1_spec__0(x_213, x_214, x_207);
x_216 = lean_mk_string_unchecked(",", 1, 1);
x_217 = l_Lean_mkAtom(x_216);
x_218 = l_Lean_mkSepArray(x_215, x_217);
lean_dec(x_215);
x_219 = l_Array_append(lean_box(0), x_91, x_218);
lean_dec(x_218);
lean_inc(x_65);
lean_inc(x_97);
x_220 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_220, 0, x_97);
lean_ctor_set(x_220, 1, x_65);
lean_ctor_set(x_220, 2, x_219);
lean_inc(x_65);
lean_inc(x_97);
x_221 = l_Lean_Syntax_node1(x_97, x_65, x_220);
x_222 = lean_mk_string_unchecked("=>", 2, 2);
lean_inc(x_97);
x_223 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_223, 0, x_97);
lean_ctor_set(x_223, 1, x_222);
x_224 = lean_mk_string_unchecked("Repr.addAppParen", 16, 16);
x_225 = l_String_toSubstring_x27(x_224);
x_226 = lean_mk_string_unchecked("Repr", 4, 4);
x_227 = lean_mk_string_unchecked("addAppParen", 11, 11);
x_228 = l_Lean_Name_mkStr2(x_226, x_227);
lean_inc(x_43);
lean_inc(x_228);
lean_inc(x_209);
x_229 = l_Lean_addMacroScope(x_209, x_228, x_43);
x_230 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_230, 0, x_228);
lean_ctor_set(x_230, 1, x_59);
x_231 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_231, 0, x_230);
lean_ctor_set(x_231, 1, x_61);
lean_inc(x_97);
x_232 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_232, 0, x_97);
lean_ctor_set(x_232, 1, x_225);
lean_ctor_set(x_232, 2, x_229);
lean_ctor_set(x_232, 3, x_231);
x_233 = lean_mk_string_unchecked("paren", 5, 5);
x_234 = l_Lean_Name_mkStr4(x_46, x_47, x_48, x_233);
x_235 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_97);
x_236 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_236, 0, x_97);
lean_ctor_set(x_236, 1, x_235);
x_237 = lean_mk_string_unchecked("Format.group", 12, 12);
x_238 = l_String_toSubstring_x27(x_237);
x_239 = lean_mk_string_unchecked("group", 5, 5);
lean_inc(x_239);
lean_inc(x_53);
x_240 = l_Lean_Name_mkStr2(x_53, x_239);
lean_inc(x_43);
lean_inc(x_209);
x_241 = l_Lean_addMacroScope(x_209, x_240, x_43);
lean_inc(x_53);
lean_inc(x_57);
x_242 = l_Lean_Name_mkStr3(x_57, x_53, x_239);
lean_inc(x_242);
x_243 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_243, 0, x_242);
lean_ctor_set(x_243, 1, x_59);
x_244 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_244, 0, x_242);
x_245 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_245, 0, x_244);
lean_ctor_set(x_245, 1, x_61);
x_246 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_246, 0, x_243);
lean_ctor_set(x_246, 1, x_245);
lean_inc(x_97);
x_247 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_247, 0, x_97);
lean_ctor_set(x_247, 1, x_238);
lean_ctor_set(x_247, 2, x_241);
lean_ctor_set(x_247, 3, x_246);
x_248 = lean_mk_string_unchecked("Format.nest", 11, 11);
x_249 = l_String_toSubstring_x27(x_248);
x_250 = lean_mk_string_unchecked("nest", 4, 4);
lean_inc(x_250);
lean_inc(x_53);
x_251 = l_Lean_Name_mkStr2(x_53, x_250);
lean_inc(x_43);
lean_inc(x_209);
x_252 = l_Lean_addMacroScope(x_209, x_251, x_43);
x_253 = l_Lean_Name_mkStr3(x_57, x_53, x_250);
lean_inc(x_253);
x_254 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_254, 0, x_253);
lean_ctor_set(x_254, 1, x_59);
x_255 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_255, 0, x_253);
x_256 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_256, 0, x_255);
lean_ctor_set(x_256, 1, x_61);
x_257 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_257, 0, x_254);
lean_ctor_set(x_257, 1, x_256);
lean_inc(x_97);
x_258 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_258, 0, x_97);
lean_ctor_set(x_258, 1, x_249);
lean_ctor_set(x_258, 2, x_252);
lean_ctor_set(x_258, 3, x_257);
x_259 = lean_mk_string_unchecked("termIfThenElse", 14, 14);
x_260 = l_Lean_Name_mkStr1(x_259);
x_261 = lean_mk_string_unchecked("if", 2, 2);
lean_inc(x_97);
x_262 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_262, 0, x_97);
lean_ctor_set(x_262, 1, x_261);
x_263 = lean_mk_string_unchecked("term_>=_", 8, 8);
x_264 = l_Lean_Name_mkStr1(x_263);
x_265 = lean_mk_string_unchecked("prec", 4, 4);
lean_inc(x_265);
x_266 = l_String_toSubstring_x27(x_265);
x_267 = l_Lean_Name_mkStr1(x_265);
x_268 = l_Lean_addMacroScope(x_209, x_267, x_43);
lean_inc(x_97);
x_269 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_269, 0, x_97);
lean_ctor_set(x_269, 1, x_266);
lean_ctor_set(x_269, 2, x_268);
lean_ctor_set(x_269, 3, x_61);
x_270 = lean_mk_string_unchecked(">=", 2, 2);
lean_inc(x_97);
x_271 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_271, 0, x_97);
lean_ctor_set(x_271, 1, x_270);
x_272 = lean_mk_string_unchecked("termMax_prec", 12, 12);
x_273 = l_Lean_Name_mkStr1(x_272);
x_274 = lean_mk_string_unchecked("max_prec", 8, 8);
lean_inc(x_97);
x_275 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_275, 0, x_97);
lean_ctor_set(x_275, 1, x_274);
lean_inc(x_97);
x_276 = l_Lean_Syntax_node1(x_97, x_273, x_275);
lean_inc(x_269);
lean_inc(x_97);
x_277 = l_Lean_Syntax_node3(x_97, x_264, x_269, x_271, x_276);
x_278 = lean_mk_string_unchecked("then", 4, 4);
lean_inc(x_97);
x_279 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_279, 0, x_97);
lean_ctor_set(x_279, 1, x_278);
x_280 = lean_mk_string_unchecked("num", 3, 3);
x_281 = l_Lean_Name_mkStr1(x_280);
x_282 = lean_mk_string_unchecked("1", 1, 1);
lean_inc(x_97);
x_283 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_283, 0, x_97);
lean_ctor_set(x_283, 1, x_282);
lean_inc(x_281);
lean_inc(x_97);
x_284 = l_Lean_Syntax_node1(x_97, x_281, x_283);
x_285 = lean_mk_string_unchecked("else", 4, 4);
lean_inc(x_97);
x_286 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_286, 0, x_97);
lean_ctor_set(x_286, 1, x_285);
x_287 = lean_mk_string_unchecked("2", 1, 1);
lean_inc(x_97);
x_288 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_288, 0, x_97);
lean_ctor_set(x_288, 1, x_287);
lean_inc(x_97);
x_289 = l_Lean_Syntax_node1(x_97, x_281, x_288);
lean_inc(x_97);
x_290 = l_Lean_Syntax_node6(x_97, x_260, x_262, x_277, x_279, x_284, x_286, x_289);
x_291 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_97);
x_292 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_292, 0, x_97);
lean_ctor_set(x_292, 1, x_291);
lean_inc(x_292);
lean_inc(x_236);
lean_inc(x_234);
lean_inc(x_97);
x_293 = l_Lean_Syntax_node3(x_97, x_234, x_236, x_290, x_292);
lean_inc(x_292);
lean_inc(x_236);
lean_inc(x_234);
lean_inc(x_97);
x_294 = l_Lean_Syntax_node3(x_97, x_234, x_236, x_76, x_292);
lean_inc(x_65);
lean_inc(x_97);
x_295 = l_Lean_Syntax_node2(x_97, x_65, x_293, x_294);
lean_inc(x_50);
lean_inc(x_97);
x_296 = l_Lean_Syntax_node2(x_97, x_50, x_258, x_295);
lean_inc(x_292);
lean_inc(x_236);
lean_inc(x_234);
lean_inc(x_97);
x_297 = l_Lean_Syntax_node3(x_97, x_234, x_236, x_296, x_292);
lean_inc(x_65);
lean_inc(x_97);
x_298 = l_Lean_Syntax_node1(x_97, x_65, x_297);
lean_inc(x_50);
lean_inc(x_97);
x_299 = l_Lean_Syntax_node2(x_97, x_50, x_247, x_298);
lean_inc(x_97);
x_300 = l_Lean_Syntax_node3(x_97, x_234, x_236, x_299, x_292);
lean_inc(x_97);
x_301 = l_Lean_Syntax_node2(x_97, x_65, x_300, x_269);
lean_inc(x_97);
x_302 = l_Lean_Syntax_node2(x_97, x_50, x_232, x_301);
x_303 = l_Lean_Syntax_node4(x_97, x_211, x_72, x_221, x_223, x_302);
x_304 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_304, 0, x_303);
lean_ctor_set(x_304, 1, x_203);
return x_304;
}
}
else
{
uint8_t x_305; 
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_83);
lean_dec(x_88);
lean_dec(x_81);
lean_free_object(x_72);
lean_dec(x_76);
lean_dec(x_65);
lean_dec(x_57);
lean_dec(x_53);
lean_dec(x_50);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_43);
lean_dec(x_25);
lean_dec(x_18);
lean_dec(x_2);
x_305 = !lean_is_exclusive(x_96);
if (x_305 == 0)
{
return x_96;
}
else
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; 
x_306 = lean_ctor_get(x_96, 0);
x_307 = lean_ctor_get(x_96, 1);
lean_inc(x_307);
lean_inc(x_306);
lean_dec(x_96);
x_308 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_308, 0, x_306);
lean_ctor_set(x_308, 1, x_307);
return x_308;
}
}
}
else
{
uint8_t x_309; 
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_83);
lean_dec(x_88);
lean_dec(x_81);
lean_free_object(x_72);
lean_dec(x_76);
lean_dec(x_65);
lean_dec(x_57);
lean_dec(x_53);
lean_dec(x_50);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_43);
lean_dec(x_25);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_2);
x_309 = !lean_is_exclusive(x_93);
if (x_309 == 0)
{
return x_93;
}
else
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; 
x_310 = lean_ctor_get(x_93, 0);
x_311 = lean_ctor_get(x_93, 1);
lean_inc(x_311);
lean_inc(x_310);
lean_dec(x_93);
x_312 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_312, 0, x_310);
lean_ctor_set(x_312, 1, x_311);
return x_312;
}
}
}
else
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; 
x_313 = lean_ctor_get(x_83, 1);
lean_inc(x_313);
lean_dec(x_83);
x_314 = lean_mk_string_unchecked("explicit", 8, 8);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
x_315 = l_Lean_Name_mkStr4(x_46, x_47, x_48, x_314);
x_316 = lean_mk_string_unchecked("@", 1, 1);
lean_inc(x_81);
x_317 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_317, 0, x_81);
lean_ctor_set(x_317, 1, x_316);
x_318 = lean_mk_syntax_ident(x_10);
x_319 = l_Array_mkArray0(lean_box(0));
lean_inc(x_319);
x_320 = l_Array_append(lean_box(0), x_319, x_75);
lean_dec(x_75);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_321 = lean_apply_7(x_4, x_13, x_14, x_15, x_16, x_17, x_18, x_313);
if (lean_obj_tag(x_321) == 0)
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; 
x_322 = lean_ctor_get(x_321, 0);
lean_inc(x_322);
x_323 = lean_ctor_get(x_321, 1);
lean_inc(x_323);
lean_dec(x_321);
lean_inc(x_18);
x_324 = lean_apply_8(x_5, x_322, x_13, x_14, x_15, x_16, x_17, x_18, x_323);
if (lean_obj_tag(x_324) == 0)
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; size_t x_340; size_t x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; 
x_325 = lean_ctor_get(x_324, 0);
lean_inc(x_325);
x_326 = lean_ctor_get(x_324, 1);
lean_inc(x_326);
lean_dec(x_324);
x_327 = lean_st_ref_get(x_18, x_326);
lean_dec(x_18);
x_328 = lean_ctor_get(x_327, 0);
lean_inc(x_328);
x_329 = lean_ctor_get(x_327, 1);
lean_inc(x_329);
if (lean_is_exclusive(x_327)) {
 lean_ctor_release(x_327, 0);
 lean_ctor_release(x_327, 1);
 x_330 = x_327;
} else {
 lean_dec_ref(x_327);
 x_330 = lean_box(0);
}
lean_inc(x_81);
x_331 = l_Lean_Syntax_node2(x_81, x_315, x_317, x_318);
lean_inc(x_65);
lean_inc(x_81);
x_332 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_332, 0, x_81);
lean_ctor_set(x_332, 1, x_65);
lean_ctor_set(x_332, 2, x_320);
lean_inc(x_50);
x_333 = l_Lean_Syntax_node2(x_81, x_50, x_331, x_332);
x_334 = lean_array_push(x_25, x_333);
x_335 = lean_ctor_get(x_328, 0);
lean_inc(x_335);
lean_dec(x_328);
x_336 = l_Lean_Environment_mainModule(x_335);
lean_dec(x_335);
x_337 = lean_mk_string_unchecked("matchAlt", 8, 8);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
x_338 = l_Lean_Name_mkStr4(x_46, x_47, x_48, x_337);
x_339 = lean_mk_string_unchecked("|", 1, 1);
lean_inc(x_325);
lean_ctor_set_tag(x_72, 2);
lean_ctor_set(x_72, 1, x_339);
lean_ctor_set(x_72, 0, x_325);
x_340 = lean_array_size(x_334);
x_341 = lean_usize_of_nat(x_2);
lean_dec(x_2);
x_342 = l_Array_mapMUnsafe_map___at___Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1_spec__0(x_340, x_341, x_334);
x_343 = lean_mk_string_unchecked(",", 1, 1);
x_344 = l_Lean_mkAtom(x_343);
x_345 = l_Lean_mkSepArray(x_342, x_344);
lean_dec(x_342);
x_346 = l_Array_append(lean_box(0), x_319, x_345);
lean_dec(x_345);
lean_inc(x_65);
lean_inc(x_325);
x_347 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_347, 0, x_325);
lean_ctor_set(x_347, 1, x_65);
lean_ctor_set(x_347, 2, x_346);
lean_inc(x_65);
lean_inc(x_325);
x_348 = l_Lean_Syntax_node1(x_325, x_65, x_347);
x_349 = lean_mk_string_unchecked("=>", 2, 2);
lean_inc(x_325);
x_350 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_350, 0, x_325);
lean_ctor_set(x_350, 1, x_349);
x_351 = lean_mk_string_unchecked("Repr.addAppParen", 16, 16);
x_352 = l_String_toSubstring_x27(x_351);
x_353 = lean_mk_string_unchecked("Repr", 4, 4);
x_354 = lean_mk_string_unchecked("addAppParen", 11, 11);
x_355 = l_Lean_Name_mkStr2(x_353, x_354);
lean_inc(x_43);
lean_inc(x_355);
lean_inc(x_336);
x_356 = l_Lean_addMacroScope(x_336, x_355, x_43);
x_357 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_357, 0, x_355);
lean_ctor_set(x_357, 1, x_59);
x_358 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_358, 0, x_357);
lean_ctor_set(x_358, 1, x_61);
lean_inc(x_325);
x_359 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_359, 0, x_325);
lean_ctor_set(x_359, 1, x_352);
lean_ctor_set(x_359, 2, x_356);
lean_ctor_set(x_359, 3, x_358);
x_360 = lean_mk_string_unchecked("paren", 5, 5);
x_361 = l_Lean_Name_mkStr4(x_46, x_47, x_48, x_360);
x_362 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_325);
x_363 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_363, 0, x_325);
lean_ctor_set(x_363, 1, x_362);
x_364 = lean_mk_string_unchecked("Format.group", 12, 12);
x_365 = l_String_toSubstring_x27(x_364);
x_366 = lean_mk_string_unchecked("group", 5, 5);
lean_inc(x_366);
lean_inc(x_53);
x_367 = l_Lean_Name_mkStr2(x_53, x_366);
lean_inc(x_43);
lean_inc(x_336);
x_368 = l_Lean_addMacroScope(x_336, x_367, x_43);
lean_inc(x_53);
lean_inc(x_57);
x_369 = l_Lean_Name_mkStr3(x_57, x_53, x_366);
lean_inc(x_369);
x_370 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_370, 0, x_369);
lean_ctor_set(x_370, 1, x_59);
x_371 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_371, 0, x_369);
x_372 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_372, 0, x_371);
lean_ctor_set(x_372, 1, x_61);
x_373 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_373, 0, x_370);
lean_ctor_set(x_373, 1, x_372);
lean_inc(x_325);
x_374 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_374, 0, x_325);
lean_ctor_set(x_374, 1, x_365);
lean_ctor_set(x_374, 2, x_368);
lean_ctor_set(x_374, 3, x_373);
x_375 = lean_mk_string_unchecked("Format.nest", 11, 11);
x_376 = l_String_toSubstring_x27(x_375);
x_377 = lean_mk_string_unchecked("nest", 4, 4);
lean_inc(x_377);
lean_inc(x_53);
x_378 = l_Lean_Name_mkStr2(x_53, x_377);
lean_inc(x_43);
lean_inc(x_336);
x_379 = l_Lean_addMacroScope(x_336, x_378, x_43);
x_380 = l_Lean_Name_mkStr3(x_57, x_53, x_377);
lean_inc(x_380);
x_381 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_381, 0, x_380);
lean_ctor_set(x_381, 1, x_59);
x_382 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_382, 0, x_380);
x_383 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_383, 0, x_382);
lean_ctor_set(x_383, 1, x_61);
x_384 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_384, 0, x_381);
lean_ctor_set(x_384, 1, x_383);
lean_inc(x_325);
x_385 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_385, 0, x_325);
lean_ctor_set(x_385, 1, x_376);
lean_ctor_set(x_385, 2, x_379);
lean_ctor_set(x_385, 3, x_384);
x_386 = lean_mk_string_unchecked("termIfThenElse", 14, 14);
x_387 = l_Lean_Name_mkStr1(x_386);
x_388 = lean_mk_string_unchecked("if", 2, 2);
lean_inc(x_325);
x_389 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_389, 0, x_325);
lean_ctor_set(x_389, 1, x_388);
x_390 = lean_mk_string_unchecked("term_>=_", 8, 8);
x_391 = l_Lean_Name_mkStr1(x_390);
x_392 = lean_mk_string_unchecked("prec", 4, 4);
lean_inc(x_392);
x_393 = l_String_toSubstring_x27(x_392);
x_394 = l_Lean_Name_mkStr1(x_392);
x_395 = l_Lean_addMacroScope(x_336, x_394, x_43);
lean_inc(x_325);
x_396 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_396, 0, x_325);
lean_ctor_set(x_396, 1, x_393);
lean_ctor_set(x_396, 2, x_395);
lean_ctor_set(x_396, 3, x_61);
x_397 = lean_mk_string_unchecked(">=", 2, 2);
lean_inc(x_325);
x_398 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_398, 0, x_325);
lean_ctor_set(x_398, 1, x_397);
x_399 = lean_mk_string_unchecked("termMax_prec", 12, 12);
x_400 = l_Lean_Name_mkStr1(x_399);
x_401 = lean_mk_string_unchecked("max_prec", 8, 8);
lean_inc(x_325);
x_402 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_402, 0, x_325);
lean_ctor_set(x_402, 1, x_401);
lean_inc(x_325);
x_403 = l_Lean_Syntax_node1(x_325, x_400, x_402);
lean_inc(x_396);
lean_inc(x_325);
x_404 = l_Lean_Syntax_node3(x_325, x_391, x_396, x_398, x_403);
x_405 = lean_mk_string_unchecked("then", 4, 4);
lean_inc(x_325);
x_406 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_406, 0, x_325);
lean_ctor_set(x_406, 1, x_405);
x_407 = lean_mk_string_unchecked("num", 3, 3);
x_408 = l_Lean_Name_mkStr1(x_407);
x_409 = lean_mk_string_unchecked("1", 1, 1);
lean_inc(x_325);
x_410 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_410, 0, x_325);
lean_ctor_set(x_410, 1, x_409);
lean_inc(x_408);
lean_inc(x_325);
x_411 = l_Lean_Syntax_node1(x_325, x_408, x_410);
x_412 = lean_mk_string_unchecked("else", 4, 4);
lean_inc(x_325);
x_413 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_413, 0, x_325);
lean_ctor_set(x_413, 1, x_412);
x_414 = lean_mk_string_unchecked("2", 1, 1);
lean_inc(x_325);
x_415 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_415, 0, x_325);
lean_ctor_set(x_415, 1, x_414);
lean_inc(x_325);
x_416 = l_Lean_Syntax_node1(x_325, x_408, x_415);
lean_inc(x_325);
x_417 = l_Lean_Syntax_node6(x_325, x_387, x_389, x_404, x_406, x_411, x_413, x_416);
x_418 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_325);
x_419 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_419, 0, x_325);
lean_ctor_set(x_419, 1, x_418);
lean_inc(x_419);
lean_inc(x_363);
lean_inc(x_361);
lean_inc(x_325);
x_420 = l_Lean_Syntax_node3(x_325, x_361, x_363, x_417, x_419);
lean_inc(x_419);
lean_inc(x_363);
lean_inc(x_361);
lean_inc(x_325);
x_421 = l_Lean_Syntax_node3(x_325, x_361, x_363, x_76, x_419);
lean_inc(x_65);
lean_inc(x_325);
x_422 = l_Lean_Syntax_node2(x_325, x_65, x_420, x_421);
lean_inc(x_50);
lean_inc(x_325);
x_423 = l_Lean_Syntax_node2(x_325, x_50, x_385, x_422);
lean_inc(x_419);
lean_inc(x_363);
lean_inc(x_361);
lean_inc(x_325);
x_424 = l_Lean_Syntax_node3(x_325, x_361, x_363, x_423, x_419);
lean_inc(x_65);
lean_inc(x_325);
x_425 = l_Lean_Syntax_node1(x_325, x_65, x_424);
lean_inc(x_50);
lean_inc(x_325);
x_426 = l_Lean_Syntax_node2(x_325, x_50, x_374, x_425);
lean_inc(x_325);
x_427 = l_Lean_Syntax_node3(x_325, x_361, x_363, x_426, x_419);
lean_inc(x_325);
x_428 = l_Lean_Syntax_node2(x_325, x_65, x_427, x_396);
lean_inc(x_325);
x_429 = l_Lean_Syntax_node2(x_325, x_50, x_359, x_428);
x_430 = l_Lean_Syntax_node4(x_325, x_338, x_72, x_348, x_350, x_429);
if (lean_is_scalar(x_330)) {
 x_431 = lean_alloc_ctor(0, 2, 0);
} else {
 x_431 = x_330;
}
lean_ctor_set(x_431, 0, x_430);
lean_ctor_set(x_431, 1, x_329);
return x_431;
}
else
{
lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; 
lean_dec(x_320);
lean_dec(x_319);
lean_dec(x_318);
lean_dec(x_317);
lean_dec(x_315);
lean_dec(x_81);
lean_free_object(x_72);
lean_dec(x_76);
lean_dec(x_65);
lean_dec(x_57);
lean_dec(x_53);
lean_dec(x_50);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_43);
lean_dec(x_25);
lean_dec(x_18);
lean_dec(x_2);
x_432 = lean_ctor_get(x_324, 0);
lean_inc(x_432);
x_433 = lean_ctor_get(x_324, 1);
lean_inc(x_433);
if (lean_is_exclusive(x_324)) {
 lean_ctor_release(x_324, 0);
 lean_ctor_release(x_324, 1);
 x_434 = x_324;
} else {
 lean_dec_ref(x_324);
 x_434 = lean_box(0);
}
if (lean_is_scalar(x_434)) {
 x_435 = lean_alloc_ctor(1, 2, 0);
} else {
 x_435 = x_434;
}
lean_ctor_set(x_435, 0, x_432);
lean_ctor_set(x_435, 1, x_433);
return x_435;
}
}
else
{
lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; 
lean_dec(x_320);
lean_dec(x_319);
lean_dec(x_318);
lean_dec(x_317);
lean_dec(x_315);
lean_dec(x_81);
lean_free_object(x_72);
lean_dec(x_76);
lean_dec(x_65);
lean_dec(x_57);
lean_dec(x_53);
lean_dec(x_50);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_43);
lean_dec(x_25);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_2);
x_436 = lean_ctor_get(x_321, 0);
lean_inc(x_436);
x_437 = lean_ctor_get(x_321, 1);
lean_inc(x_437);
if (lean_is_exclusive(x_321)) {
 lean_ctor_release(x_321, 0);
 lean_ctor_release(x_321, 1);
 x_438 = x_321;
} else {
 lean_dec_ref(x_321);
 x_438 = lean_box(0);
}
if (lean_is_scalar(x_438)) {
 x_439 = lean_alloc_ctor(1, 2, 0);
} else {
 x_439 = x_438;
}
lean_ctor_set(x_439, 0, x_436);
lean_ctor_set(x_439, 1, x_437);
return x_439;
}
}
}
else
{
uint8_t x_440; 
lean_free_object(x_72);
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_65);
lean_dec(x_57);
lean_dec(x_53);
lean_dec(x_50);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_43);
lean_dec(x_25);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_440 = !lean_is_exclusive(x_80);
if (x_440 == 0)
{
return x_80;
}
else
{
lean_object* x_441; lean_object* x_442; lean_object* x_443; 
x_441 = lean_ctor_get(x_80, 0);
x_442 = lean_ctor_get(x_80, 1);
lean_inc(x_442);
lean_inc(x_441);
lean_dec(x_80);
x_443 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_443, 0, x_441);
lean_ctor_set(x_443, 1, x_442);
return x_443;
}
}
}
else
{
uint8_t x_444; 
lean_free_object(x_72);
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_65);
lean_dec(x_57);
lean_dec(x_53);
lean_dec(x_50);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_43);
lean_dec(x_25);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_444 = !lean_is_exclusive(x_77);
if (x_444 == 0)
{
return x_77;
}
else
{
lean_object* x_445; lean_object* x_446; lean_object* x_447; 
x_445 = lean_ctor_get(x_77, 0);
x_446 = lean_ctor_get(x_77, 1);
lean_inc(x_446);
lean_inc(x_445);
lean_dec(x_77);
x_447 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_447, 0, x_445);
lean_ctor_set(x_447, 1, x_446);
return x_447;
}
}
}
else
{
lean_object* x_448; lean_object* x_449; lean_object* x_450; 
x_448 = lean_ctor_get(x_72, 0);
x_449 = lean_ctor_get(x_72, 1);
lean_inc(x_449);
lean_inc(x_448);
lean_dec(x_72);
lean_inc(x_4);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_450 = lean_apply_7(x_4, x_13, x_14, x_15, x_16, x_17, x_18, x_73);
if (lean_obj_tag(x_450) == 0)
{
lean_object* x_451; lean_object* x_452; lean_object* x_453; 
x_451 = lean_ctor_get(x_450, 0);
lean_inc(x_451);
x_452 = lean_ctor_get(x_450, 1);
lean_inc(x_452);
lean_dec(x_450);
lean_inc(x_5);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_453 = lean_apply_8(x_5, x_451, x_13, x_14, x_15, x_16, x_17, x_18, x_452);
if (lean_obj_tag(x_453) == 0)
{
lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; 
x_454 = lean_ctor_get(x_453, 0);
lean_inc(x_454);
x_455 = lean_ctor_get(x_453, 1);
lean_inc(x_455);
lean_dec(x_453);
x_456 = lean_st_ref_get(x_18, x_455);
x_457 = lean_ctor_get(x_456, 1);
lean_inc(x_457);
if (lean_is_exclusive(x_456)) {
 lean_ctor_release(x_456, 0);
 lean_ctor_release(x_456, 1);
 x_458 = x_456;
} else {
 lean_dec_ref(x_456);
 x_458 = lean_box(0);
}
x_459 = lean_mk_string_unchecked("explicit", 8, 8);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
x_460 = l_Lean_Name_mkStr4(x_46, x_47, x_48, x_459);
x_461 = lean_mk_string_unchecked("@", 1, 1);
lean_inc(x_454);
if (lean_is_scalar(x_458)) {
 x_462 = lean_alloc_ctor(2, 2, 0);
} else {
 x_462 = x_458;
 lean_ctor_set_tag(x_462, 2);
}
lean_ctor_set(x_462, 0, x_454);
lean_ctor_set(x_462, 1, x_461);
x_463 = lean_mk_syntax_ident(x_10);
x_464 = l_Array_mkArray0(lean_box(0));
lean_inc(x_464);
x_465 = l_Array_append(lean_box(0), x_464, x_448);
lean_dec(x_448);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_466 = lean_apply_7(x_4, x_13, x_14, x_15, x_16, x_17, x_18, x_457);
if (lean_obj_tag(x_466) == 0)
{
lean_object* x_467; lean_object* x_468; lean_object* x_469; 
x_467 = lean_ctor_get(x_466, 0);
lean_inc(x_467);
x_468 = lean_ctor_get(x_466, 1);
lean_inc(x_468);
lean_dec(x_466);
lean_inc(x_18);
x_469 = lean_apply_8(x_5, x_467, x_13, x_14, x_15, x_16, x_17, x_18, x_468);
if (lean_obj_tag(x_469) == 0)
{
lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; size_t x_486; size_t x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; 
x_470 = lean_ctor_get(x_469, 0);
lean_inc(x_470);
x_471 = lean_ctor_get(x_469, 1);
lean_inc(x_471);
lean_dec(x_469);
x_472 = lean_st_ref_get(x_18, x_471);
lean_dec(x_18);
x_473 = lean_ctor_get(x_472, 0);
lean_inc(x_473);
x_474 = lean_ctor_get(x_472, 1);
lean_inc(x_474);
if (lean_is_exclusive(x_472)) {
 lean_ctor_release(x_472, 0);
 lean_ctor_release(x_472, 1);
 x_475 = x_472;
} else {
 lean_dec_ref(x_472);
 x_475 = lean_box(0);
}
lean_inc(x_454);
x_476 = l_Lean_Syntax_node2(x_454, x_460, x_462, x_463);
lean_inc(x_65);
lean_inc(x_454);
x_477 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_477, 0, x_454);
lean_ctor_set(x_477, 1, x_65);
lean_ctor_set(x_477, 2, x_465);
lean_inc(x_50);
x_478 = l_Lean_Syntax_node2(x_454, x_50, x_476, x_477);
x_479 = lean_array_push(x_25, x_478);
x_480 = lean_ctor_get(x_473, 0);
lean_inc(x_480);
lean_dec(x_473);
x_481 = l_Lean_Environment_mainModule(x_480);
lean_dec(x_480);
x_482 = lean_mk_string_unchecked("matchAlt", 8, 8);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
x_483 = l_Lean_Name_mkStr4(x_46, x_47, x_48, x_482);
x_484 = lean_mk_string_unchecked("|", 1, 1);
lean_inc(x_470);
x_485 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_485, 0, x_470);
lean_ctor_set(x_485, 1, x_484);
x_486 = lean_array_size(x_479);
x_487 = lean_usize_of_nat(x_2);
lean_dec(x_2);
x_488 = l_Array_mapMUnsafe_map___at___Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1_spec__0(x_486, x_487, x_479);
x_489 = lean_mk_string_unchecked(",", 1, 1);
x_490 = l_Lean_mkAtom(x_489);
x_491 = l_Lean_mkSepArray(x_488, x_490);
lean_dec(x_488);
x_492 = l_Array_append(lean_box(0), x_464, x_491);
lean_dec(x_491);
lean_inc(x_65);
lean_inc(x_470);
x_493 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_493, 0, x_470);
lean_ctor_set(x_493, 1, x_65);
lean_ctor_set(x_493, 2, x_492);
lean_inc(x_65);
lean_inc(x_470);
x_494 = l_Lean_Syntax_node1(x_470, x_65, x_493);
x_495 = lean_mk_string_unchecked("=>", 2, 2);
lean_inc(x_470);
x_496 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_496, 0, x_470);
lean_ctor_set(x_496, 1, x_495);
x_497 = lean_mk_string_unchecked("Repr.addAppParen", 16, 16);
x_498 = l_String_toSubstring_x27(x_497);
x_499 = lean_mk_string_unchecked("Repr", 4, 4);
x_500 = lean_mk_string_unchecked("addAppParen", 11, 11);
x_501 = l_Lean_Name_mkStr2(x_499, x_500);
lean_inc(x_43);
lean_inc(x_501);
lean_inc(x_481);
x_502 = l_Lean_addMacroScope(x_481, x_501, x_43);
x_503 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_503, 0, x_501);
lean_ctor_set(x_503, 1, x_59);
x_504 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_504, 0, x_503);
lean_ctor_set(x_504, 1, x_61);
lean_inc(x_470);
x_505 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_505, 0, x_470);
lean_ctor_set(x_505, 1, x_498);
lean_ctor_set(x_505, 2, x_502);
lean_ctor_set(x_505, 3, x_504);
x_506 = lean_mk_string_unchecked("paren", 5, 5);
x_507 = l_Lean_Name_mkStr4(x_46, x_47, x_48, x_506);
x_508 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_470);
x_509 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_509, 0, x_470);
lean_ctor_set(x_509, 1, x_508);
x_510 = lean_mk_string_unchecked("Format.group", 12, 12);
x_511 = l_String_toSubstring_x27(x_510);
x_512 = lean_mk_string_unchecked("group", 5, 5);
lean_inc(x_512);
lean_inc(x_53);
x_513 = l_Lean_Name_mkStr2(x_53, x_512);
lean_inc(x_43);
lean_inc(x_481);
x_514 = l_Lean_addMacroScope(x_481, x_513, x_43);
lean_inc(x_53);
lean_inc(x_57);
x_515 = l_Lean_Name_mkStr3(x_57, x_53, x_512);
lean_inc(x_515);
x_516 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_516, 0, x_515);
lean_ctor_set(x_516, 1, x_59);
x_517 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_517, 0, x_515);
x_518 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_518, 0, x_517);
lean_ctor_set(x_518, 1, x_61);
x_519 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_519, 0, x_516);
lean_ctor_set(x_519, 1, x_518);
lean_inc(x_470);
x_520 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_520, 0, x_470);
lean_ctor_set(x_520, 1, x_511);
lean_ctor_set(x_520, 2, x_514);
lean_ctor_set(x_520, 3, x_519);
x_521 = lean_mk_string_unchecked("Format.nest", 11, 11);
x_522 = l_String_toSubstring_x27(x_521);
x_523 = lean_mk_string_unchecked("nest", 4, 4);
lean_inc(x_523);
lean_inc(x_53);
x_524 = l_Lean_Name_mkStr2(x_53, x_523);
lean_inc(x_43);
lean_inc(x_481);
x_525 = l_Lean_addMacroScope(x_481, x_524, x_43);
x_526 = l_Lean_Name_mkStr3(x_57, x_53, x_523);
lean_inc(x_526);
x_527 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_527, 0, x_526);
lean_ctor_set(x_527, 1, x_59);
x_528 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_528, 0, x_526);
x_529 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_529, 0, x_528);
lean_ctor_set(x_529, 1, x_61);
x_530 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_530, 0, x_527);
lean_ctor_set(x_530, 1, x_529);
lean_inc(x_470);
x_531 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_531, 0, x_470);
lean_ctor_set(x_531, 1, x_522);
lean_ctor_set(x_531, 2, x_525);
lean_ctor_set(x_531, 3, x_530);
x_532 = lean_mk_string_unchecked("termIfThenElse", 14, 14);
x_533 = l_Lean_Name_mkStr1(x_532);
x_534 = lean_mk_string_unchecked("if", 2, 2);
lean_inc(x_470);
x_535 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_535, 0, x_470);
lean_ctor_set(x_535, 1, x_534);
x_536 = lean_mk_string_unchecked("term_>=_", 8, 8);
x_537 = l_Lean_Name_mkStr1(x_536);
x_538 = lean_mk_string_unchecked("prec", 4, 4);
lean_inc(x_538);
x_539 = l_String_toSubstring_x27(x_538);
x_540 = l_Lean_Name_mkStr1(x_538);
x_541 = l_Lean_addMacroScope(x_481, x_540, x_43);
lean_inc(x_470);
x_542 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_542, 0, x_470);
lean_ctor_set(x_542, 1, x_539);
lean_ctor_set(x_542, 2, x_541);
lean_ctor_set(x_542, 3, x_61);
x_543 = lean_mk_string_unchecked(">=", 2, 2);
lean_inc(x_470);
x_544 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_544, 0, x_470);
lean_ctor_set(x_544, 1, x_543);
x_545 = lean_mk_string_unchecked("termMax_prec", 12, 12);
x_546 = l_Lean_Name_mkStr1(x_545);
x_547 = lean_mk_string_unchecked("max_prec", 8, 8);
lean_inc(x_470);
x_548 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_548, 0, x_470);
lean_ctor_set(x_548, 1, x_547);
lean_inc(x_470);
x_549 = l_Lean_Syntax_node1(x_470, x_546, x_548);
lean_inc(x_542);
lean_inc(x_470);
x_550 = l_Lean_Syntax_node3(x_470, x_537, x_542, x_544, x_549);
x_551 = lean_mk_string_unchecked("then", 4, 4);
lean_inc(x_470);
x_552 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_552, 0, x_470);
lean_ctor_set(x_552, 1, x_551);
x_553 = lean_mk_string_unchecked("num", 3, 3);
x_554 = l_Lean_Name_mkStr1(x_553);
x_555 = lean_mk_string_unchecked("1", 1, 1);
lean_inc(x_470);
x_556 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_556, 0, x_470);
lean_ctor_set(x_556, 1, x_555);
lean_inc(x_554);
lean_inc(x_470);
x_557 = l_Lean_Syntax_node1(x_470, x_554, x_556);
x_558 = lean_mk_string_unchecked("else", 4, 4);
lean_inc(x_470);
x_559 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_559, 0, x_470);
lean_ctor_set(x_559, 1, x_558);
x_560 = lean_mk_string_unchecked("2", 1, 1);
lean_inc(x_470);
x_561 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_561, 0, x_470);
lean_ctor_set(x_561, 1, x_560);
lean_inc(x_470);
x_562 = l_Lean_Syntax_node1(x_470, x_554, x_561);
lean_inc(x_470);
x_563 = l_Lean_Syntax_node6(x_470, x_533, x_535, x_550, x_552, x_557, x_559, x_562);
x_564 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_470);
x_565 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_565, 0, x_470);
lean_ctor_set(x_565, 1, x_564);
lean_inc(x_565);
lean_inc(x_509);
lean_inc(x_507);
lean_inc(x_470);
x_566 = l_Lean_Syntax_node3(x_470, x_507, x_509, x_563, x_565);
lean_inc(x_565);
lean_inc(x_509);
lean_inc(x_507);
lean_inc(x_470);
x_567 = l_Lean_Syntax_node3(x_470, x_507, x_509, x_449, x_565);
lean_inc(x_65);
lean_inc(x_470);
x_568 = l_Lean_Syntax_node2(x_470, x_65, x_566, x_567);
lean_inc(x_50);
lean_inc(x_470);
x_569 = l_Lean_Syntax_node2(x_470, x_50, x_531, x_568);
lean_inc(x_565);
lean_inc(x_509);
lean_inc(x_507);
lean_inc(x_470);
x_570 = l_Lean_Syntax_node3(x_470, x_507, x_509, x_569, x_565);
lean_inc(x_65);
lean_inc(x_470);
x_571 = l_Lean_Syntax_node1(x_470, x_65, x_570);
lean_inc(x_50);
lean_inc(x_470);
x_572 = l_Lean_Syntax_node2(x_470, x_50, x_520, x_571);
lean_inc(x_470);
x_573 = l_Lean_Syntax_node3(x_470, x_507, x_509, x_572, x_565);
lean_inc(x_470);
x_574 = l_Lean_Syntax_node2(x_470, x_65, x_573, x_542);
lean_inc(x_470);
x_575 = l_Lean_Syntax_node2(x_470, x_50, x_505, x_574);
x_576 = l_Lean_Syntax_node4(x_470, x_483, x_485, x_494, x_496, x_575);
if (lean_is_scalar(x_475)) {
 x_577 = lean_alloc_ctor(0, 2, 0);
} else {
 x_577 = x_475;
}
lean_ctor_set(x_577, 0, x_576);
lean_ctor_set(x_577, 1, x_474);
return x_577;
}
else
{
lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; 
lean_dec(x_465);
lean_dec(x_464);
lean_dec(x_463);
lean_dec(x_462);
lean_dec(x_460);
lean_dec(x_454);
lean_dec(x_449);
lean_dec(x_65);
lean_dec(x_57);
lean_dec(x_53);
lean_dec(x_50);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_43);
lean_dec(x_25);
lean_dec(x_18);
lean_dec(x_2);
x_578 = lean_ctor_get(x_469, 0);
lean_inc(x_578);
x_579 = lean_ctor_get(x_469, 1);
lean_inc(x_579);
if (lean_is_exclusive(x_469)) {
 lean_ctor_release(x_469, 0);
 lean_ctor_release(x_469, 1);
 x_580 = x_469;
} else {
 lean_dec_ref(x_469);
 x_580 = lean_box(0);
}
if (lean_is_scalar(x_580)) {
 x_581 = lean_alloc_ctor(1, 2, 0);
} else {
 x_581 = x_580;
}
lean_ctor_set(x_581, 0, x_578);
lean_ctor_set(x_581, 1, x_579);
return x_581;
}
}
else
{
lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; 
lean_dec(x_465);
lean_dec(x_464);
lean_dec(x_463);
lean_dec(x_462);
lean_dec(x_460);
lean_dec(x_454);
lean_dec(x_449);
lean_dec(x_65);
lean_dec(x_57);
lean_dec(x_53);
lean_dec(x_50);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_43);
lean_dec(x_25);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_2);
x_582 = lean_ctor_get(x_466, 0);
lean_inc(x_582);
x_583 = lean_ctor_get(x_466, 1);
lean_inc(x_583);
if (lean_is_exclusive(x_466)) {
 lean_ctor_release(x_466, 0);
 lean_ctor_release(x_466, 1);
 x_584 = x_466;
} else {
 lean_dec_ref(x_466);
 x_584 = lean_box(0);
}
if (lean_is_scalar(x_584)) {
 x_585 = lean_alloc_ctor(1, 2, 0);
} else {
 x_585 = x_584;
}
lean_ctor_set(x_585, 0, x_582);
lean_ctor_set(x_585, 1, x_583);
return x_585;
}
}
else
{
lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; 
lean_dec(x_449);
lean_dec(x_448);
lean_dec(x_65);
lean_dec(x_57);
lean_dec(x_53);
lean_dec(x_50);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_43);
lean_dec(x_25);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_586 = lean_ctor_get(x_453, 0);
lean_inc(x_586);
x_587 = lean_ctor_get(x_453, 1);
lean_inc(x_587);
if (lean_is_exclusive(x_453)) {
 lean_ctor_release(x_453, 0);
 lean_ctor_release(x_453, 1);
 x_588 = x_453;
} else {
 lean_dec_ref(x_453);
 x_588 = lean_box(0);
}
if (lean_is_scalar(x_588)) {
 x_589 = lean_alloc_ctor(1, 2, 0);
} else {
 x_589 = x_588;
}
lean_ctor_set(x_589, 0, x_586);
lean_ctor_set(x_589, 1, x_587);
return x_589;
}
}
else
{
lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; 
lean_dec(x_449);
lean_dec(x_448);
lean_dec(x_65);
lean_dec(x_57);
lean_dec(x_53);
lean_dec(x_50);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_43);
lean_dec(x_25);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_590 = lean_ctor_get(x_450, 0);
lean_inc(x_590);
x_591 = lean_ctor_get(x_450, 1);
lean_inc(x_591);
if (lean_is_exclusive(x_450)) {
 lean_ctor_release(x_450, 0);
 lean_ctor_release(x_450, 1);
 x_592 = x_450;
} else {
 lean_dec_ref(x_450);
 x_592 = lean_box(0);
}
if (lean_is_scalar(x_592)) {
 x_593 = lean_alloc_ctor(1, 2, 0);
} else {
 x_593 = x_592;
}
lean_ctor_set(x_593, 0, x_590);
lean_ctor_set(x_593, 1, x_591);
return x_593;
}
}
}
else
{
uint8_t x_594; 
lean_dec(x_65);
lean_dec(x_57);
lean_dec(x_53);
lean_dec(x_50);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_43);
lean_dec(x_25);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_594 = !lean_is_exclusive(x_71);
if (x_594 == 0)
{
return x_71;
}
else
{
lean_object* x_595; lean_object* x_596; lean_object* x_597; 
x_595 = lean_ctor_get(x_71, 0);
x_596 = lean_ctor_get(x_71, 1);
lean_inc(x_596);
lean_inc(x_595);
lean_dec(x_71);
x_597 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_597, 0, x_595);
lean_ctor_set(x_597, 1, x_596);
return x_597;
}
}
}
else
{
lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; uint8_t x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; 
x_598 = lean_ctor_get(x_33, 0);
x_599 = lean_ctor_get(x_33, 1);
lean_inc(x_599);
lean_inc(x_598);
lean_dec(x_33);
x_600 = lean_ctor_get(x_6, 0);
lean_inc(x_600);
lean_dec(x_6);
x_601 = lean_box(1);
x_602 = lean_unbox(x_601);
x_603 = l_Lean_Name_toString(x_600, x_602, x_7);
x_604 = lean_box(2);
x_605 = l_Lean_Syntax_mkStrLit(x_603, x_604);
lean_dec(x_603);
x_606 = lean_ctor_get(x_17, 10);
lean_inc(x_606);
x_607 = lean_ctor_get(x_598, 0);
lean_inc(x_607);
lean_dec(x_598);
x_608 = l_Lean_Environment_mainModule(x_607);
lean_dec(x_607);
x_609 = lean_mk_string_unchecked("Lean", 4, 4);
x_610 = lean_mk_string_unchecked("Parser", 6, 6);
x_611 = lean_mk_string_unchecked("Term", 4, 4);
x_612 = lean_mk_string_unchecked("app", 3, 3);
lean_inc(x_611);
lean_inc(x_610);
lean_inc(x_609);
x_613 = l_Lean_Name_mkStr4(x_609, x_610, x_611, x_612);
x_614 = lean_mk_string_unchecked("Format.text", 11, 11);
x_615 = l_String_toSubstring_x27(x_614);
x_616 = lean_mk_string_unchecked("Format", 6, 6);
x_617 = lean_mk_string_unchecked("text", 4, 4);
lean_inc(x_617);
lean_inc(x_616);
x_618 = l_Lean_Name_mkStr2(x_616, x_617);
lean_inc(x_606);
x_619 = l_Lean_addMacroScope(x_608, x_618, x_606);
x_620 = lean_mk_string_unchecked("Std", 3, 3);
lean_inc(x_616);
lean_inc(x_620);
x_621 = l_Lean_Name_mkStr3(x_620, x_616, x_617);
x_622 = lean_box(0);
lean_inc(x_621);
x_623 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_623, 0, x_621);
lean_ctor_set(x_623, 1, x_622);
x_624 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_624, 0, x_621);
x_625 = lean_box(0);
lean_ctor_set_tag(x_23, 1);
lean_ctor_set(x_23, 1, x_625);
lean_ctor_set(x_23, 0, x_624);
x_626 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_626, 0, x_623);
lean_ctor_set(x_626, 1, x_23);
lean_inc(x_31);
x_627 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_627, 0, x_31);
lean_ctor_set(x_627, 1, x_615);
lean_ctor_set(x_627, 2, x_619);
lean_ctor_set(x_627, 3, x_626);
x_628 = lean_mk_string_unchecked("null", 4, 4);
x_629 = l_Lean_Name_mkStr1(x_628);
lean_inc(x_629);
lean_inc(x_31);
x_630 = l_Lean_Syntax_node1(x_31, x_629, x_605);
lean_inc(x_613);
x_631 = l_Lean_Syntax_node2(x_31, x_613, x_627, x_630);
x_632 = lean_array_get_size(x_11);
lean_inc(x_2);
x_633 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_633, 0, x_2);
lean_ctor_set(x_633, 1, x_632);
lean_ctor_set(x_633, 2, x_21);
x_634 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_634, 0, x_3);
lean_ctor_set(x_634, 1, x_631);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_2);
x_635 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg(x_11, x_1, x_8, x_9, x_633, x_634, x_2, x_13, x_14, x_15, x_16, x_17, x_18, x_599);
lean_dec(x_633);
if (lean_obj_tag(x_635) == 0)
{
lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; 
x_636 = lean_ctor_get(x_635, 0);
lean_inc(x_636);
x_637 = lean_ctor_get(x_635, 1);
lean_inc(x_637);
lean_dec(x_635);
x_638 = lean_ctor_get(x_636, 0);
lean_inc(x_638);
x_639 = lean_ctor_get(x_636, 1);
lean_inc(x_639);
if (lean_is_exclusive(x_636)) {
 lean_ctor_release(x_636, 0);
 lean_ctor_release(x_636, 1);
 x_640 = x_636;
} else {
 lean_dec_ref(x_636);
 x_640 = lean_box(0);
}
lean_inc(x_4);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_641 = lean_apply_7(x_4, x_13, x_14, x_15, x_16, x_17, x_18, x_637);
if (lean_obj_tag(x_641) == 0)
{
lean_object* x_642; lean_object* x_643; lean_object* x_644; 
x_642 = lean_ctor_get(x_641, 0);
lean_inc(x_642);
x_643 = lean_ctor_get(x_641, 1);
lean_inc(x_643);
lean_dec(x_641);
lean_inc(x_5);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_644 = lean_apply_8(x_5, x_642, x_13, x_14, x_15, x_16, x_17, x_18, x_643);
if (lean_obj_tag(x_644) == 0)
{
lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; 
x_645 = lean_ctor_get(x_644, 0);
lean_inc(x_645);
x_646 = lean_ctor_get(x_644, 1);
lean_inc(x_646);
lean_dec(x_644);
x_647 = lean_st_ref_get(x_18, x_646);
x_648 = lean_ctor_get(x_647, 1);
lean_inc(x_648);
if (lean_is_exclusive(x_647)) {
 lean_ctor_release(x_647, 0);
 lean_ctor_release(x_647, 1);
 x_649 = x_647;
} else {
 lean_dec_ref(x_647);
 x_649 = lean_box(0);
}
x_650 = lean_mk_string_unchecked("explicit", 8, 8);
lean_inc(x_611);
lean_inc(x_610);
lean_inc(x_609);
x_651 = l_Lean_Name_mkStr4(x_609, x_610, x_611, x_650);
x_652 = lean_mk_string_unchecked("@", 1, 1);
lean_inc(x_645);
if (lean_is_scalar(x_649)) {
 x_653 = lean_alloc_ctor(2, 2, 0);
} else {
 x_653 = x_649;
 lean_ctor_set_tag(x_653, 2);
}
lean_ctor_set(x_653, 0, x_645);
lean_ctor_set(x_653, 1, x_652);
x_654 = lean_mk_syntax_ident(x_10);
x_655 = l_Array_mkArray0(lean_box(0));
lean_inc(x_655);
x_656 = l_Array_append(lean_box(0), x_655, x_638);
lean_dec(x_638);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_657 = lean_apply_7(x_4, x_13, x_14, x_15, x_16, x_17, x_18, x_648);
if (lean_obj_tag(x_657) == 0)
{
lean_object* x_658; lean_object* x_659; lean_object* x_660; 
x_658 = lean_ctor_get(x_657, 0);
lean_inc(x_658);
x_659 = lean_ctor_get(x_657, 1);
lean_inc(x_659);
lean_dec(x_657);
lean_inc(x_18);
x_660 = lean_apply_8(x_5, x_658, x_13, x_14, x_15, x_16, x_17, x_18, x_659);
if (lean_obj_tag(x_660) == 0)
{
lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; size_t x_677; size_t x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; 
x_661 = lean_ctor_get(x_660, 0);
lean_inc(x_661);
x_662 = lean_ctor_get(x_660, 1);
lean_inc(x_662);
lean_dec(x_660);
x_663 = lean_st_ref_get(x_18, x_662);
lean_dec(x_18);
x_664 = lean_ctor_get(x_663, 0);
lean_inc(x_664);
x_665 = lean_ctor_get(x_663, 1);
lean_inc(x_665);
if (lean_is_exclusive(x_663)) {
 lean_ctor_release(x_663, 0);
 lean_ctor_release(x_663, 1);
 x_666 = x_663;
} else {
 lean_dec_ref(x_663);
 x_666 = lean_box(0);
}
lean_inc(x_645);
x_667 = l_Lean_Syntax_node2(x_645, x_651, x_653, x_654);
lean_inc(x_629);
lean_inc(x_645);
x_668 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_668, 0, x_645);
lean_ctor_set(x_668, 1, x_629);
lean_ctor_set(x_668, 2, x_656);
lean_inc(x_613);
x_669 = l_Lean_Syntax_node2(x_645, x_613, x_667, x_668);
x_670 = lean_array_push(x_25, x_669);
x_671 = lean_ctor_get(x_664, 0);
lean_inc(x_671);
lean_dec(x_664);
x_672 = l_Lean_Environment_mainModule(x_671);
lean_dec(x_671);
x_673 = lean_mk_string_unchecked("matchAlt", 8, 8);
lean_inc(x_611);
lean_inc(x_610);
lean_inc(x_609);
x_674 = l_Lean_Name_mkStr4(x_609, x_610, x_611, x_673);
x_675 = lean_mk_string_unchecked("|", 1, 1);
lean_inc(x_661);
if (lean_is_scalar(x_640)) {
 x_676 = lean_alloc_ctor(2, 2, 0);
} else {
 x_676 = x_640;
 lean_ctor_set_tag(x_676, 2);
}
lean_ctor_set(x_676, 0, x_661);
lean_ctor_set(x_676, 1, x_675);
x_677 = lean_array_size(x_670);
x_678 = lean_usize_of_nat(x_2);
lean_dec(x_2);
x_679 = l_Array_mapMUnsafe_map___at___Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1_spec__0(x_677, x_678, x_670);
x_680 = lean_mk_string_unchecked(",", 1, 1);
x_681 = l_Lean_mkAtom(x_680);
x_682 = l_Lean_mkSepArray(x_679, x_681);
lean_dec(x_679);
x_683 = l_Array_append(lean_box(0), x_655, x_682);
lean_dec(x_682);
lean_inc(x_629);
lean_inc(x_661);
x_684 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_684, 0, x_661);
lean_ctor_set(x_684, 1, x_629);
lean_ctor_set(x_684, 2, x_683);
lean_inc(x_629);
lean_inc(x_661);
x_685 = l_Lean_Syntax_node1(x_661, x_629, x_684);
x_686 = lean_mk_string_unchecked("=>", 2, 2);
lean_inc(x_661);
x_687 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_687, 0, x_661);
lean_ctor_set(x_687, 1, x_686);
x_688 = lean_mk_string_unchecked("Repr.addAppParen", 16, 16);
x_689 = l_String_toSubstring_x27(x_688);
x_690 = lean_mk_string_unchecked("Repr", 4, 4);
x_691 = lean_mk_string_unchecked("addAppParen", 11, 11);
x_692 = l_Lean_Name_mkStr2(x_690, x_691);
lean_inc(x_606);
lean_inc(x_692);
lean_inc(x_672);
x_693 = l_Lean_addMacroScope(x_672, x_692, x_606);
x_694 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_694, 0, x_692);
lean_ctor_set(x_694, 1, x_622);
x_695 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_695, 0, x_694);
lean_ctor_set(x_695, 1, x_625);
lean_inc(x_661);
x_696 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_696, 0, x_661);
lean_ctor_set(x_696, 1, x_689);
lean_ctor_set(x_696, 2, x_693);
lean_ctor_set(x_696, 3, x_695);
x_697 = lean_mk_string_unchecked("paren", 5, 5);
x_698 = l_Lean_Name_mkStr4(x_609, x_610, x_611, x_697);
x_699 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_661);
x_700 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_700, 0, x_661);
lean_ctor_set(x_700, 1, x_699);
x_701 = lean_mk_string_unchecked("Format.group", 12, 12);
x_702 = l_String_toSubstring_x27(x_701);
x_703 = lean_mk_string_unchecked("group", 5, 5);
lean_inc(x_703);
lean_inc(x_616);
x_704 = l_Lean_Name_mkStr2(x_616, x_703);
lean_inc(x_606);
lean_inc(x_672);
x_705 = l_Lean_addMacroScope(x_672, x_704, x_606);
lean_inc(x_616);
lean_inc(x_620);
x_706 = l_Lean_Name_mkStr3(x_620, x_616, x_703);
lean_inc(x_706);
x_707 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_707, 0, x_706);
lean_ctor_set(x_707, 1, x_622);
x_708 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_708, 0, x_706);
x_709 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_709, 0, x_708);
lean_ctor_set(x_709, 1, x_625);
x_710 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_710, 0, x_707);
lean_ctor_set(x_710, 1, x_709);
lean_inc(x_661);
x_711 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_711, 0, x_661);
lean_ctor_set(x_711, 1, x_702);
lean_ctor_set(x_711, 2, x_705);
lean_ctor_set(x_711, 3, x_710);
x_712 = lean_mk_string_unchecked("Format.nest", 11, 11);
x_713 = l_String_toSubstring_x27(x_712);
x_714 = lean_mk_string_unchecked("nest", 4, 4);
lean_inc(x_714);
lean_inc(x_616);
x_715 = l_Lean_Name_mkStr2(x_616, x_714);
lean_inc(x_606);
lean_inc(x_672);
x_716 = l_Lean_addMacroScope(x_672, x_715, x_606);
x_717 = l_Lean_Name_mkStr3(x_620, x_616, x_714);
lean_inc(x_717);
x_718 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_718, 0, x_717);
lean_ctor_set(x_718, 1, x_622);
x_719 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_719, 0, x_717);
x_720 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_720, 0, x_719);
lean_ctor_set(x_720, 1, x_625);
x_721 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_721, 0, x_718);
lean_ctor_set(x_721, 1, x_720);
lean_inc(x_661);
x_722 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_722, 0, x_661);
lean_ctor_set(x_722, 1, x_713);
lean_ctor_set(x_722, 2, x_716);
lean_ctor_set(x_722, 3, x_721);
x_723 = lean_mk_string_unchecked("termIfThenElse", 14, 14);
x_724 = l_Lean_Name_mkStr1(x_723);
x_725 = lean_mk_string_unchecked("if", 2, 2);
lean_inc(x_661);
x_726 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_726, 0, x_661);
lean_ctor_set(x_726, 1, x_725);
x_727 = lean_mk_string_unchecked("term_>=_", 8, 8);
x_728 = l_Lean_Name_mkStr1(x_727);
x_729 = lean_mk_string_unchecked("prec", 4, 4);
lean_inc(x_729);
x_730 = l_String_toSubstring_x27(x_729);
x_731 = l_Lean_Name_mkStr1(x_729);
x_732 = l_Lean_addMacroScope(x_672, x_731, x_606);
lean_inc(x_661);
x_733 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_733, 0, x_661);
lean_ctor_set(x_733, 1, x_730);
lean_ctor_set(x_733, 2, x_732);
lean_ctor_set(x_733, 3, x_625);
x_734 = lean_mk_string_unchecked(">=", 2, 2);
lean_inc(x_661);
x_735 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_735, 0, x_661);
lean_ctor_set(x_735, 1, x_734);
x_736 = lean_mk_string_unchecked("termMax_prec", 12, 12);
x_737 = l_Lean_Name_mkStr1(x_736);
x_738 = lean_mk_string_unchecked("max_prec", 8, 8);
lean_inc(x_661);
x_739 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_739, 0, x_661);
lean_ctor_set(x_739, 1, x_738);
lean_inc(x_661);
x_740 = l_Lean_Syntax_node1(x_661, x_737, x_739);
lean_inc(x_733);
lean_inc(x_661);
x_741 = l_Lean_Syntax_node3(x_661, x_728, x_733, x_735, x_740);
x_742 = lean_mk_string_unchecked("then", 4, 4);
lean_inc(x_661);
x_743 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_743, 0, x_661);
lean_ctor_set(x_743, 1, x_742);
x_744 = lean_mk_string_unchecked("num", 3, 3);
x_745 = l_Lean_Name_mkStr1(x_744);
x_746 = lean_mk_string_unchecked("1", 1, 1);
lean_inc(x_661);
x_747 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_747, 0, x_661);
lean_ctor_set(x_747, 1, x_746);
lean_inc(x_745);
lean_inc(x_661);
x_748 = l_Lean_Syntax_node1(x_661, x_745, x_747);
x_749 = lean_mk_string_unchecked("else", 4, 4);
lean_inc(x_661);
x_750 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_750, 0, x_661);
lean_ctor_set(x_750, 1, x_749);
x_751 = lean_mk_string_unchecked("2", 1, 1);
lean_inc(x_661);
x_752 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_752, 0, x_661);
lean_ctor_set(x_752, 1, x_751);
lean_inc(x_661);
x_753 = l_Lean_Syntax_node1(x_661, x_745, x_752);
lean_inc(x_661);
x_754 = l_Lean_Syntax_node6(x_661, x_724, x_726, x_741, x_743, x_748, x_750, x_753);
x_755 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_661);
x_756 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_756, 0, x_661);
lean_ctor_set(x_756, 1, x_755);
lean_inc(x_756);
lean_inc(x_700);
lean_inc(x_698);
lean_inc(x_661);
x_757 = l_Lean_Syntax_node3(x_661, x_698, x_700, x_754, x_756);
lean_inc(x_756);
lean_inc(x_700);
lean_inc(x_698);
lean_inc(x_661);
x_758 = l_Lean_Syntax_node3(x_661, x_698, x_700, x_639, x_756);
lean_inc(x_629);
lean_inc(x_661);
x_759 = l_Lean_Syntax_node2(x_661, x_629, x_757, x_758);
lean_inc(x_613);
lean_inc(x_661);
x_760 = l_Lean_Syntax_node2(x_661, x_613, x_722, x_759);
lean_inc(x_756);
lean_inc(x_700);
lean_inc(x_698);
lean_inc(x_661);
x_761 = l_Lean_Syntax_node3(x_661, x_698, x_700, x_760, x_756);
lean_inc(x_629);
lean_inc(x_661);
x_762 = l_Lean_Syntax_node1(x_661, x_629, x_761);
lean_inc(x_613);
lean_inc(x_661);
x_763 = l_Lean_Syntax_node2(x_661, x_613, x_711, x_762);
lean_inc(x_661);
x_764 = l_Lean_Syntax_node3(x_661, x_698, x_700, x_763, x_756);
lean_inc(x_661);
x_765 = l_Lean_Syntax_node2(x_661, x_629, x_764, x_733);
lean_inc(x_661);
x_766 = l_Lean_Syntax_node2(x_661, x_613, x_696, x_765);
x_767 = l_Lean_Syntax_node4(x_661, x_674, x_676, x_685, x_687, x_766);
if (lean_is_scalar(x_666)) {
 x_768 = lean_alloc_ctor(0, 2, 0);
} else {
 x_768 = x_666;
}
lean_ctor_set(x_768, 0, x_767);
lean_ctor_set(x_768, 1, x_665);
return x_768;
}
else
{
lean_object* x_769; lean_object* x_770; lean_object* x_771; lean_object* x_772; 
lean_dec(x_656);
lean_dec(x_655);
lean_dec(x_654);
lean_dec(x_653);
lean_dec(x_651);
lean_dec(x_645);
lean_dec(x_640);
lean_dec(x_639);
lean_dec(x_629);
lean_dec(x_620);
lean_dec(x_616);
lean_dec(x_613);
lean_dec(x_611);
lean_dec(x_610);
lean_dec(x_609);
lean_dec(x_606);
lean_dec(x_25);
lean_dec(x_18);
lean_dec(x_2);
x_769 = lean_ctor_get(x_660, 0);
lean_inc(x_769);
x_770 = lean_ctor_get(x_660, 1);
lean_inc(x_770);
if (lean_is_exclusive(x_660)) {
 lean_ctor_release(x_660, 0);
 lean_ctor_release(x_660, 1);
 x_771 = x_660;
} else {
 lean_dec_ref(x_660);
 x_771 = lean_box(0);
}
if (lean_is_scalar(x_771)) {
 x_772 = lean_alloc_ctor(1, 2, 0);
} else {
 x_772 = x_771;
}
lean_ctor_set(x_772, 0, x_769);
lean_ctor_set(x_772, 1, x_770);
return x_772;
}
}
else
{
lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; 
lean_dec(x_656);
lean_dec(x_655);
lean_dec(x_654);
lean_dec(x_653);
lean_dec(x_651);
lean_dec(x_645);
lean_dec(x_640);
lean_dec(x_639);
lean_dec(x_629);
lean_dec(x_620);
lean_dec(x_616);
lean_dec(x_613);
lean_dec(x_611);
lean_dec(x_610);
lean_dec(x_609);
lean_dec(x_606);
lean_dec(x_25);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_2);
x_773 = lean_ctor_get(x_657, 0);
lean_inc(x_773);
x_774 = lean_ctor_get(x_657, 1);
lean_inc(x_774);
if (lean_is_exclusive(x_657)) {
 lean_ctor_release(x_657, 0);
 lean_ctor_release(x_657, 1);
 x_775 = x_657;
} else {
 lean_dec_ref(x_657);
 x_775 = lean_box(0);
}
if (lean_is_scalar(x_775)) {
 x_776 = lean_alloc_ctor(1, 2, 0);
} else {
 x_776 = x_775;
}
lean_ctor_set(x_776, 0, x_773);
lean_ctor_set(x_776, 1, x_774);
return x_776;
}
}
else
{
lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; 
lean_dec(x_640);
lean_dec(x_639);
lean_dec(x_638);
lean_dec(x_629);
lean_dec(x_620);
lean_dec(x_616);
lean_dec(x_613);
lean_dec(x_611);
lean_dec(x_610);
lean_dec(x_609);
lean_dec(x_606);
lean_dec(x_25);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_777 = lean_ctor_get(x_644, 0);
lean_inc(x_777);
x_778 = lean_ctor_get(x_644, 1);
lean_inc(x_778);
if (lean_is_exclusive(x_644)) {
 lean_ctor_release(x_644, 0);
 lean_ctor_release(x_644, 1);
 x_779 = x_644;
} else {
 lean_dec_ref(x_644);
 x_779 = lean_box(0);
}
if (lean_is_scalar(x_779)) {
 x_780 = lean_alloc_ctor(1, 2, 0);
} else {
 x_780 = x_779;
}
lean_ctor_set(x_780, 0, x_777);
lean_ctor_set(x_780, 1, x_778);
return x_780;
}
}
else
{
lean_object* x_781; lean_object* x_782; lean_object* x_783; lean_object* x_784; 
lean_dec(x_640);
lean_dec(x_639);
lean_dec(x_638);
lean_dec(x_629);
lean_dec(x_620);
lean_dec(x_616);
lean_dec(x_613);
lean_dec(x_611);
lean_dec(x_610);
lean_dec(x_609);
lean_dec(x_606);
lean_dec(x_25);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_781 = lean_ctor_get(x_641, 0);
lean_inc(x_781);
x_782 = lean_ctor_get(x_641, 1);
lean_inc(x_782);
if (lean_is_exclusive(x_641)) {
 lean_ctor_release(x_641, 0);
 lean_ctor_release(x_641, 1);
 x_783 = x_641;
} else {
 lean_dec_ref(x_641);
 x_783 = lean_box(0);
}
if (lean_is_scalar(x_783)) {
 x_784 = lean_alloc_ctor(1, 2, 0);
} else {
 x_784 = x_783;
}
lean_ctor_set(x_784, 0, x_781);
lean_ctor_set(x_784, 1, x_782);
return x_784;
}
}
else
{
lean_object* x_785; lean_object* x_786; lean_object* x_787; lean_object* x_788; 
lean_dec(x_629);
lean_dec(x_620);
lean_dec(x_616);
lean_dec(x_613);
lean_dec(x_611);
lean_dec(x_610);
lean_dec(x_609);
lean_dec(x_606);
lean_dec(x_25);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_785 = lean_ctor_get(x_635, 0);
lean_inc(x_785);
x_786 = lean_ctor_get(x_635, 1);
lean_inc(x_786);
if (lean_is_exclusive(x_635)) {
 lean_ctor_release(x_635, 0);
 lean_ctor_release(x_635, 1);
 x_787 = x_635;
} else {
 lean_dec_ref(x_635);
 x_787 = lean_box(0);
}
if (lean_is_scalar(x_787)) {
 x_788 = lean_alloc_ctor(1, 2, 0);
} else {
 x_788 = x_787;
}
lean_ctor_set(x_788, 0, x_785);
lean_ctor_set(x_788, 1, x_786);
return x_788;
}
}
}
else
{
uint8_t x_789; 
lean_free_object(x_23);
lean_dec(x_25);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_789 = !lean_is_exclusive(x_30);
if (x_789 == 0)
{
return x_30;
}
else
{
lean_object* x_790; lean_object* x_791; lean_object* x_792; 
x_790 = lean_ctor_get(x_30, 0);
x_791 = lean_ctor_get(x_30, 1);
lean_inc(x_791);
lean_inc(x_790);
lean_dec(x_30);
x_792 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_792, 0, x_790);
lean_ctor_set(x_792, 1, x_791);
return x_792;
}
}
}
else
{
uint8_t x_793; 
lean_free_object(x_23);
lean_dec(x_25);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_793 = !lean_is_exclusive(x_27);
if (x_793 == 0)
{
return x_27;
}
else
{
lean_object* x_794; lean_object* x_795; lean_object* x_796; 
x_794 = lean_ctor_get(x_27, 0);
x_795 = lean_ctor_get(x_27, 1);
lean_inc(x_795);
lean_inc(x_794);
lean_dec(x_27);
x_796 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_796, 0, x_794);
lean_ctor_set(x_796, 1, x_795);
return x_796;
}
}
}
else
{
lean_object* x_797; lean_object* x_798; lean_object* x_799; 
x_797 = lean_ctor_get(x_23, 0);
x_798 = lean_ctor_get(x_23, 1);
lean_inc(x_798);
lean_inc(x_797);
lean_dec(x_23);
lean_inc(x_4);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_799 = lean_apply_7(x_4, x_13, x_14, x_15, x_16, x_17, x_18, x_798);
if (lean_obj_tag(x_799) == 0)
{
lean_object* x_800; lean_object* x_801; lean_object* x_802; 
x_800 = lean_ctor_get(x_799, 0);
lean_inc(x_800);
x_801 = lean_ctor_get(x_799, 1);
lean_inc(x_801);
lean_dec(x_799);
lean_inc(x_5);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_802 = lean_apply_8(x_5, x_800, x_13, x_14, x_15, x_16, x_17, x_18, x_801);
if (lean_obj_tag(x_802) == 0)
{
lean_object* x_803; lean_object* x_804; lean_object* x_805; lean_object* x_806; lean_object* x_807; lean_object* x_808; lean_object* x_809; lean_object* x_810; uint8_t x_811; lean_object* x_812; lean_object* x_813; lean_object* x_814; lean_object* x_815; lean_object* x_816; lean_object* x_817; lean_object* x_818; lean_object* x_819; lean_object* x_820; lean_object* x_821; lean_object* x_822; lean_object* x_823; lean_object* x_824; lean_object* x_825; lean_object* x_826; lean_object* x_827; lean_object* x_828; lean_object* x_829; lean_object* x_830; lean_object* x_831; lean_object* x_832; lean_object* x_833; lean_object* x_834; lean_object* x_835; lean_object* x_836; lean_object* x_837; lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; lean_object* x_844; lean_object* x_845; 
x_803 = lean_ctor_get(x_802, 0);
lean_inc(x_803);
x_804 = lean_ctor_get(x_802, 1);
lean_inc(x_804);
lean_dec(x_802);
x_805 = lean_st_ref_get(x_18, x_804);
x_806 = lean_ctor_get(x_805, 0);
lean_inc(x_806);
x_807 = lean_ctor_get(x_805, 1);
lean_inc(x_807);
if (lean_is_exclusive(x_805)) {
 lean_ctor_release(x_805, 0);
 lean_ctor_release(x_805, 1);
 x_808 = x_805;
} else {
 lean_dec_ref(x_805);
 x_808 = lean_box(0);
}
x_809 = lean_ctor_get(x_6, 0);
lean_inc(x_809);
lean_dec(x_6);
x_810 = lean_box(1);
x_811 = lean_unbox(x_810);
x_812 = l_Lean_Name_toString(x_809, x_811, x_7);
x_813 = lean_box(2);
x_814 = l_Lean_Syntax_mkStrLit(x_812, x_813);
lean_dec(x_812);
x_815 = lean_ctor_get(x_17, 10);
lean_inc(x_815);
x_816 = lean_ctor_get(x_806, 0);
lean_inc(x_816);
lean_dec(x_806);
x_817 = l_Lean_Environment_mainModule(x_816);
lean_dec(x_816);
x_818 = lean_mk_string_unchecked("Lean", 4, 4);
x_819 = lean_mk_string_unchecked("Parser", 6, 6);
x_820 = lean_mk_string_unchecked("Term", 4, 4);
x_821 = lean_mk_string_unchecked("app", 3, 3);
lean_inc(x_820);
lean_inc(x_819);
lean_inc(x_818);
x_822 = l_Lean_Name_mkStr4(x_818, x_819, x_820, x_821);
x_823 = lean_mk_string_unchecked("Format.text", 11, 11);
x_824 = l_String_toSubstring_x27(x_823);
x_825 = lean_mk_string_unchecked("Format", 6, 6);
x_826 = lean_mk_string_unchecked("text", 4, 4);
lean_inc(x_826);
lean_inc(x_825);
x_827 = l_Lean_Name_mkStr2(x_825, x_826);
lean_inc(x_815);
x_828 = l_Lean_addMacroScope(x_817, x_827, x_815);
x_829 = lean_mk_string_unchecked("Std", 3, 3);
lean_inc(x_825);
lean_inc(x_829);
x_830 = l_Lean_Name_mkStr3(x_829, x_825, x_826);
x_831 = lean_box(0);
lean_inc(x_830);
if (lean_is_scalar(x_808)) {
 x_832 = lean_alloc_ctor(1, 2, 0);
} else {
 x_832 = x_808;
 lean_ctor_set_tag(x_832, 1);
}
lean_ctor_set(x_832, 0, x_830);
lean_ctor_set(x_832, 1, x_831);
x_833 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_833, 0, x_830);
x_834 = lean_box(0);
x_835 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_835, 0, x_833);
lean_ctor_set(x_835, 1, x_834);
x_836 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_836, 0, x_832);
lean_ctor_set(x_836, 1, x_835);
lean_inc(x_803);
x_837 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_837, 0, x_803);
lean_ctor_set(x_837, 1, x_824);
lean_ctor_set(x_837, 2, x_828);
lean_ctor_set(x_837, 3, x_836);
x_838 = lean_mk_string_unchecked("null", 4, 4);
x_839 = l_Lean_Name_mkStr1(x_838);
lean_inc(x_839);
lean_inc(x_803);
x_840 = l_Lean_Syntax_node1(x_803, x_839, x_814);
lean_inc(x_822);
x_841 = l_Lean_Syntax_node2(x_803, x_822, x_837, x_840);
x_842 = lean_array_get_size(x_11);
lean_inc(x_2);
x_843 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_843, 0, x_2);
lean_ctor_set(x_843, 1, x_842);
lean_ctor_set(x_843, 2, x_21);
x_844 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_844, 0, x_3);
lean_ctor_set(x_844, 1, x_841);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_2);
x_845 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg(x_11, x_1, x_8, x_9, x_843, x_844, x_2, x_13, x_14, x_15, x_16, x_17, x_18, x_807);
lean_dec(x_843);
if (lean_obj_tag(x_845) == 0)
{
lean_object* x_846; lean_object* x_847; lean_object* x_848; lean_object* x_849; lean_object* x_850; lean_object* x_851; 
x_846 = lean_ctor_get(x_845, 0);
lean_inc(x_846);
x_847 = lean_ctor_get(x_845, 1);
lean_inc(x_847);
lean_dec(x_845);
x_848 = lean_ctor_get(x_846, 0);
lean_inc(x_848);
x_849 = lean_ctor_get(x_846, 1);
lean_inc(x_849);
if (lean_is_exclusive(x_846)) {
 lean_ctor_release(x_846, 0);
 lean_ctor_release(x_846, 1);
 x_850 = x_846;
} else {
 lean_dec_ref(x_846);
 x_850 = lean_box(0);
}
lean_inc(x_4);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_851 = lean_apply_7(x_4, x_13, x_14, x_15, x_16, x_17, x_18, x_847);
if (lean_obj_tag(x_851) == 0)
{
lean_object* x_852; lean_object* x_853; lean_object* x_854; 
x_852 = lean_ctor_get(x_851, 0);
lean_inc(x_852);
x_853 = lean_ctor_get(x_851, 1);
lean_inc(x_853);
lean_dec(x_851);
lean_inc(x_5);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_854 = lean_apply_8(x_5, x_852, x_13, x_14, x_15, x_16, x_17, x_18, x_853);
if (lean_obj_tag(x_854) == 0)
{
lean_object* x_855; lean_object* x_856; lean_object* x_857; lean_object* x_858; lean_object* x_859; lean_object* x_860; lean_object* x_861; lean_object* x_862; lean_object* x_863; lean_object* x_864; lean_object* x_865; lean_object* x_866; lean_object* x_867; 
x_855 = lean_ctor_get(x_854, 0);
lean_inc(x_855);
x_856 = lean_ctor_get(x_854, 1);
lean_inc(x_856);
lean_dec(x_854);
x_857 = lean_st_ref_get(x_18, x_856);
x_858 = lean_ctor_get(x_857, 1);
lean_inc(x_858);
if (lean_is_exclusive(x_857)) {
 lean_ctor_release(x_857, 0);
 lean_ctor_release(x_857, 1);
 x_859 = x_857;
} else {
 lean_dec_ref(x_857);
 x_859 = lean_box(0);
}
x_860 = lean_mk_string_unchecked("explicit", 8, 8);
lean_inc(x_820);
lean_inc(x_819);
lean_inc(x_818);
x_861 = l_Lean_Name_mkStr4(x_818, x_819, x_820, x_860);
x_862 = lean_mk_string_unchecked("@", 1, 1);
lean_inc(x_855);
if (lean_is_scalar(x_859)) {
 x_863 = lean_alloc_ctor(2, 2, 0);
} else {
 x_863 = x_859;
 lean_ctor_set_tag(x_863, 2);
}
lean_ctor_set(x_863, 0, x_855);
lean_ctor_set(x_863, 1, x_862);
x_864 = lean_mk_syntax_ident(x_10);
x_865 = l_Array_mkArray0(lean_box(0));
lean_inc(x_865);
x_866 = l_Array_append(lean_box(0), x_865, x_848);
lean_dec(x_848);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_867 = lean_apply_7(x_4, x_13, x_14, x_15, x_16, x_17, x_18, x_858);
if (lean_obj_tag(x_867) == 0)
{
lean_object* x_868; lean_object* x_869; lean_object* x_870; 
x_868 = lean_ctor_get(x_867, 0);
lean_inc(x_868);
x_869 = lean_ctor_get(x_867, 1);
lean_inc(x_869);
lean_dec(x_867);
lean_inc(x_18);
x_870 = lean_apply_8(x_5, x_868, x_13, x_14, x_15, x_16, x_17, x_18, x_869);
if (lean_obj_tag(x_870) == 0)
{
lean_object* x_871; lean_object* x_872; lean_object* x_873; lean_object* x_874; lean_object* x_875; lean_object* x_876; lean_object* x_877; lean_object* x_878; lean_object* x_879; lean_object* x_880; lean_object* x_881; lean_object* x_882; lean_object* x_883; lean_object* x_884; lean_object* x_885; lean_object* x_886; size_t x_887; size_t x_888; lean_object* x_889; lean_object* x_890; lean_object* x_891; lean_object* x_892; lean_object* x_893; lean_object* x_894; lean_object* x_895; lean_object* x_896; lean_object* x_897; lean_object* x_898; lean_object* x_899; lean_object* x_900; lean_object* x_901; lean_object* x_902; lean_object* x_903; lean_object* x_904; lean_object* x_905; lean_object* x_906; lean_object* x_907; lean_object* x_908; lean_object* x_909; lean_object* x_910; lean_object* x_911; lean_object* x_912; lean_object* x_913; lean_object* x_914; lean_object* x_915; lean_object* x_916; lean_object* x_917; lean_object* x_918; lean_object* x_919; lean_object* x_920; lean_object* x_921; lean_object* x_922; lean_object* x_923; lean_object* x_924; lean_object* x_925; lean_object* x_926; lean_object* x_927; lean_object* x_928; lean_object* x_929; lean_object* x_930; lean_object* x_931; lean_object* x_932; lean_object* x_933; lean_object* x_934; lean_object* x_935; lean_object* x_936; lean_object* x_937; lean_object* x_938; lean_object* x_939; lean_object* x_940; lean_object* x_941; lean_object* x_942; lean_object* x_943; lean_object* x_944; lean_object* x_945; lean_object* x_946; lean_object* x_947; lean_object* x_948; lean_object* x_949; lean_object* x_950; lean_object* x_951; lean_object* x_952; lean_object* x_953; lean_object* x_954; lean_object* x_955; lean_object* x_956; lean_object* x_957; lean_object* x_958; lean_object* x_959; lean_object* x_960; lean_object* x_961; lean_object* x_962; lean_object* x_963; lean_object* x_964; lean_object* x_965; lean_object* x_966; lean_object* x_967; lean_object* x_968; lean_object* x_969; lean_object* x_970; lean_object* x_971; lean_object* x_972; lean_object* x_973; lean_object* x_974; lean_object* x_975; lean_object* x_976; lean_object* x_977; lean_object* x_978; 
x_871 = lean_ctor_get(x_870, 0);
lean_inc(x_871);
x_872 = lean_ctor_get(x_870, 1);
lean_inc(x_872);
lean_dec(x_870);
x_873 = lean_st_ref_get(x_18, x_872);
lean_dec(x_18);
x_874 = lean_ctor_get(x_873, 0);
lean_inc(x_874);
x_875 = lean_ctor_get(x_873, 1);
lean_inc(x_875);
if (lean_is_exclusive(x_873)) {
 lean_ctor_release(x_873, 0);
 lean_ctor_release(x_873, 1);
 x_876 = x_873;
} else {
 lean_dec_ref(x_873);
 x_876 = lean_box(0);
}
lean_inc(x_855);
x_877 = l_Lean_Syntax_node2(x_855, x_861, x_863, x_864);
lean_inc(x_839);
lean_inc(x_855);
x_878 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_878, 0, x_855);
lean_ctor_set(x_878, 1, x_839);
lean_ctor_set(x_878, 2, x_866);
lean_inc(x_822);
x_879 = l_Lean_Syntax_node2(x_855, x_822, x_877, x_878);
x_880 = lean_array_push(x_797, x_879);
x_881 = lean_ctor_get(x_874, 0);
lean_inc(x_881);
lean_dec(x_874);
x_882 = l_Lean_Environment_mainModule(x_881);
lean_dec(x_881);
x_883 = lean_mk_string_unchecked("matchAlt", 8, 8);
lean_inc(x_820);
lean_inc(x_819);
lean_inc(x_818);
x_884 = l_Lean_Name_mkStr4(x_818, x_819, x_820, x_883);
x_885 = lean_mk_string_unchecked("|", 1, 1);
lean_inc(x_871);
if (lean_is_scalar(x_850)) {
 x_886 = lean_alloc_ctor(2, 2, 0);
} else {
 x_886 = x_850;
 lean_ctor_set_tag(x_886, 2);
}
lean_ctor_set(x_886, 0, x_871);
lean_ctor_set(x_886, 1, x_885);
x_887 = lean_array_size(x_880);
x_888 = lean_usize_of_nat(x_2);
lean_dec(x_2);
x_889 = l_Array_mapMUnsafe_map___at___Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1_spec__0(x_887, x_888, x_880);
x_890 = lean_mk_string_unchecked(",", 1, 1);
x_891 = l_Lean_mkAtom(x_890);
x_892 = l_Lean_mkSepArray(x_889, x_891);
lean_dec(x_889);
x_893 = l_Array_append(lean_box(0), x_865, x_892);
lean_dec(x_892);
lean_inc(x_839);
lean_inc(x_871);
x_894 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_894, 0, x_871);
lean_ctor_set(x_894, 1, x_839);
lean_ctor_set(x_894, 2, x_893);
lean_inc(x_839);
lean_inc(x_871);
x_895 = l_Lean_Syntax_node1(x_871, x_839, x_894);
x_896 = lean_mk_string_unchecked("=>", 2, 2);
lean_inc(x_871);
x_897 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_897, 0, x_871);
lean_ctor_set(x_897, 1, x_896);
x_898 = lean_mk_string_unchecked("Repr.addAppParen", 16, 16);
x_899 = l_String_toSubstring_x27(x_898);
x_900 = lean_mk_string_unchecked("Repr", 4, 4);
x_901 = lean_mk_string_unchecked("addAppParen", 11, 11);
x_902 = l_Lean_Name_mkStr2(x_900, x_901);
lean_inc(x_815);
lean_inc(x_902);
lean_inc(x_882);
x_903 = l_Lean_addMacroScope(x_882, x_902, x_815);
x_904 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_904, 0, x_902);
lean_ctor_set(x_904, 1, x_831);
x_905 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_905, 0, x_904);
lean_ctor_set(x_905, 1, x_834);
lean_inc(x_871);
x_906 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_906, 0, x_871);
lean_ctor_set(x_906, 1, x_899);
lean_ctor_set(x_906, 2, x_903);
lean_ctor_set(x_906, 3, x_905);
x_907 = lean_mk_string_unchecked("paren", 5, 5);
x_908 = l_Lean_Name_mkStr4(x_818, x_819, x_820, x_907);
x_909 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_871);
x_910 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_910, 0, x_871);
lean_ctor_set(x_910, 1, x_909);
x_911 = lean_mk_string_unchecked("Format.group", 12, 12);
x_912 = l_String_toSubstring_x27(x_911);
x_913 = lean_mk_string_unchecked("group", 5, 5);
lean_inc(x_913);
lean_inc(x_825);
x_914 = l_Lean_Name_mkStr2(x_825, x_913);
lean_inc(x_815);
lean_inc(x_882);
x_915 = l_Lean_addMacroScope(x_882, x_914, x_815);
lean_inc(x_825);
lean_inc(x_829);
x_916 = l_Lean_Name_mkStr3(x_829, x_825, x_913);
lean_inc(x_916);
x_917 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_917, 0, x_916);
lean_ctor_set(x_917, 1, x_831);
x_918 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_918, 0, x_916);
x_919 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_919, 0, x_918);
lean_ctor_set(x_919, 1, x_834);
x_920 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_920, 0, x_917);
lean_ctor_set(x_920, 1, x_919);
lean_inc(x_871);
x_921 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_921, 0, x_871);
lean_ctor_set(x_921, 1, x_912);
lean_ctor_set(x_921, 2, x_915);
lean_ctor_set(x_921, 3, x_920);
x_922 = lean_mk_string_unchecked("Format.nest", 11, 11);
x_923 = l_String_toSubstring_x27(x_922);
x_924 = lean_mk_string_unchecked("nest", 4, 4);
lean_inc(x_924);
lean_inc(x_825);
x_925 = l_Lean_Name_mkStr2(x_825, x_924);
lean_inc(x_815);
lean_inc(x_882);
x_926 = l_Lean_addMacroScope(x_882, x_925, x_815);
x_927 = l_Lean_Name_mkStr3(x_829, x_825, x_924);
lean_inc(x_927);
x_928 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_928, 0, x_927);
lean_ctor_set(x_928, 1, x_831);
x_929 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_929, 0, x_927);
x_930 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_930, 0, x_929);
lean_ctor_set(x_930, 1, x_834);
x_931 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_931, 0, x_928);
lean_ctor_set(x_931, 1, x_930);
lean_inc(x_871);
x_932 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_932, 0, x_871);
lean_ctor_set(x_932, 1, x_923);
lean_ctor_set(x_932, 2, x_926);
lean_ctor_set(x_932, 3, x_931);
x_933 = lean_mk_string_unchecked("termIfThenElse", 14, 14);
x_934 = l_Lean_Name_mkStr1(x_933);
x_935 = lean_mk_string_unchecked("if", 2, 2);
lean_inc(x_871);
x_936 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_936, 0, x_871);
lean_ctor_set(x_936, 1, x_935);
x_937 = lean_mk_string_unchecked("term_>=_", 8, 8);
x_938 = l_Lean_Name_mkStr1(x_937);
x_939 = lean_mk_string_unchecked("prec", 4, 4);
lean_inc(x_939);
x_940 = l_String_toSubstring_x27(x_939);
x_941 = l_Lean_Name_mkStr1(x_939);
x_942 = l_Lean_addMacroScope(x_882, x_941, x_815);
lean_inc(x_871);
x_943 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_943, 0, x_871);
lean_ctor_set(x_943, 1, x_940);
lean_ctor_set(x_943, 2, x_942);
lean_ctor_set(x_943, 3, x_834);
x_944 = lean_mk_string_unchecked(">=", 2, 2);
lean_inc(x_871);
x_945 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_945, 0, x_871);
lean_ctor_set(x_945, 1, x_944);
x_946 = lean_mk_string_unchecked("termMax_prec", 12, 12);
x_947 = l_Lean_Name_mkStr1(x_946);
x_948 = lean_mk_string_unchecked("max_prec", 8, 8);
lean_inc(x_871);
x_949 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_949, 0, x_871);
lean_ctor_set(x_949, 1, x_948);
lean_inc(x_871);
x_950 = l_Lean_Syntax_node1(x_871, x_947, x_949);
lean_inc(x_943);
lean_inc(x_871);
x_951 = l_Lean_Syntax_node3(x_871, x_938, x_943, x_945, x_950);
x_952 = lean_mk_string_unchecked("then", 4, 4);
lean_inc(x_871);
x_953 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_953, 0, x_871);
lean_ctor_set(x_953, 1, x_952);
x_954 = lean_mk_string_unchecked("num", 3, 3);
x_955 = l_Lean_Name_mkStr1(x_954);
x_956 = lean_mk_string_unchecked("1", 1, 1);
lean_inc(x_871);
x_957 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_957, 0, x_871);
lean_ctor_set(x_957, 1, x_956);
lean_inc(x_955);
lean_inc(x_871);
x_958 = l_Lean_Syntax_node1(x_871, x_955, x_957);
x_959 = lean_mk_string_unchecked("else", 4, 4);
lean_inc(x_871);
x_960 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_960, 0, x_871);
lean_ctor_set(x_960, 1, x_959);
x_961 = lean_mk_string_unchecked("2", 1, 1);
lean_inc(x_871);
x_962 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_962, 0, x_871);
lean_ctor_set(x_962, 1, x_961);
lean_inc(x_871);
x_963 = l_Lean_Syntax_node1(x_871, x_955, x_962);
lean_inc(x_871);
x_964 = l_Lean_Syntax_node6(x_871, x_934, x_936, x_951, x_953, x_958, x_960, x_963);
x_965 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_871);
x_966 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_966, 0, x_871);
lean_ctor_set(x_966, 1, x_965);
lean_inc(x_966);
lean_inc(x_910);
lean_inc(x_908);
lean_inc(x_871);
x_967 = l_Lean_Syntax_node3(x_871, x_908, x_910, x_964, x_966);
lean_inc(x_966);
lean_inc(x_910);
lean_inc(x_908);
lean_inc(x_871);
x_968 = l_Lean_Syntax_node3(x_871, x_908, x_910, x_849, x_966);
lean_inc(x_839);
lean_inc(x_871);
x_969 = l_Lean_Syntax_node2(x_871, x_839, x_967, x_968);
lean_inc(x_822);
lean_inc(x_871);
x_970 = l_Lean_Syntax_node2(x_871, x_822, x_932, x_969);
lean_inc(x_966);
lean_inc(x_910);
lean_inc(x_908);
lean_inc(x_871);
x_971 = l_Lean_Syntax_node3(x_871, x_908, x_910, x_970, x_966);
lean_inc(x_839);
lean_inc(x_871);
x_972 = l_Lean_Syntax_node1(x_871, x_839, x_971);
lean_inc(x_822);
lean_inc(x_871);
x_973 = l_Lean_Syntax_node2(x_871, x_822, x_921, x_972);
lean_inc(x_871);
x_974 = l_Lean_Syntax_node3(x_871, x_908, x_910, x_973, x_966);
lean_inc(x_871);
x_975 = l_Lean_Syntax_node2(x_871, x_839, x_974, x_943);
lean_inc(x_871);
x_976 = l_Lean_Syntax_node2(x_871, x_822, x_906, x_975);
x_977 = l_Lean_Syntax_node4(x_871, x_884, x_886, x_895, x_897, x_976);
if (lean_is_scalar(x_876)) {
 x_978 = lean_alloc_ctor(0, 2, 0);
} else {
 x_978 = x_876;
}
lean_ctor_set(x_978, 0, x_977);
lean_ctor_set(x_978, 1, x_875);
return x_978;
}
else
{
lean_object* x_979; lean_object* x_980; lean_object* x_981; lean_object* x_982; 
lean_dec(x_866);
lean_dec(x_865);
lean_dec(x_864);
lean_dec(x_863);
lean_dec(x_861);
lean_dec(x_855);
lean_dec(x_850);
lean_dec(x_849);
lean_dec(x_839);
lean_dec(x_829);
lean_dec(x_825);
lean_dec(x_822);
lean_dec(x_820);
lean_dec(x_819);
lean_dec(x_818);
lean_dec(x_815);
lean_dec(x_797);
lean_dec(x_18);
lean_dec(x_2);
x_979 = lean_ctor_get(x_870, 0);
lean_inc(x_979);
x_980 = lean_ctor_get(x_870, 1);
lean_inc(x_980);
if (lean_is_exclusive(x_870)) {
 lean_ctor_release(x_870, 0);
 lean_ctor_release(x_870, 1);
 x_981 = x_870;
} else {
 lean_dec_ref(x_870);
 x_981 = lean_box(0);
}
if (lean_is_scalar(x_981)) {
 x_982 = lean_alloc_ctor(1, 2, 0);
} else {
 x_982 = x_981;
}
lean_ctor_set(x_982, 0, x_979);
lean_ctor_set(x_982, 1, x_980);
return x_982;
}
}
else
{
lean_object* x_983; lean_object* x_984; lean_object* x_985; lean_object* x_986; 
lean_dec(x_866);
lean_dec(x_865);
lean_dec(x_864);
lean_dec(x_863);
lean_dec(x_861);
lean_dec(x_855);
lean_dec(x_850);
lean_dec(x_849);
lean_dec(x_839);
lean_dec(x_829);
lean_dec(x_825);
lean_dec(x_822);
lean_dec(x_820);
lean_dec(x_819);
lean_dec(x_818);
lean_dec(x_815);
lean_dec(x_797);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_2);
x_983 = lean_ctor_get(x_867, 0);
lean_inc(x_983);
x_984 = lean_ctor_get(x_867, 1);
lean_inc(x_984);
if (lean_is_exclusive(x_867)) {
 lean_ctor_release(x_867, 0);
 lean_ctor_release(x_867, 1);
 x_985 = x_867;
} else {
 lean_dec_ref(x_867);
 x_985 = lean_box(0);
}
if (lean_is_scalar(x_985)) {
 x_986 = lean_alloc_ctor(1, 2, 0);
} else {
 x_986 = x_985;
}
lean_ctor_set(x_986, 0, x_983);
lean_ctor_set(x_986, 1, x_984);
return x_986;
}
}
else
{
lean_object* x_987; lean_object* x_988; lean_object* x_989; lean_object* x_990; 
lean_dec(x_850);
lean_dec(x_849);
lean_dec(x_848);
lean_dec(x_839);
lean_dec(x_829);
lean_dec(x_825);
lean_dec(x_822);
lean_dec(x_820);
lean_dec(x_819);
lean_dec(x_818);
lean_dec(x_815);
lean_dec(x_797);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_987 = lean_ctor_get(x_854, 0);
lean_inc(x_987);
x_988 = lean_ctor_get(x_854, 1);
lean_inc(x_988);
if (lean_is_exclusive(x_854)) {
 lean_ctor_release(x_854, 0);
 lean_ctor_release(x_854, 1);
 x_989 = x_854;
} else {
 lean_dec_ref(x_854);
 x_989 = lean_box(0);
}
if (lean_is_scalar(x_989)) {
 x_990 = lean_alloc_ctor(1, 2, 0);
} else {
 x_990 = x_989;
}
lean_ctor_set(x_990, 0, x_987);
lean_ctor_set(x_990, 1, x_988);
return x_990;
}
}
else
{
lean_object* x_991; lean_object* x_992; lean_object* x_993; lean_object* x_994; 
lean_dec(x_850);
lean_dec(x_849);
lean_dec(x_848);
lean_dec(x_839);
lean_dec(x_829);
lean_dec(x_825);
lean_dec(x_822);
lean_dec(x_820);
lean_dec(x_819);
lean_dec(x_818);
lean_dec(x_815);
lean_dec(x_797);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_991 = lean_ctor_get(x_851, 0);
lean_inc(x_991);
x_992 = lean_ctor_get(x_851, 1);
lean_inc(x_992);
if (lean_is_exclusive(x_851)) {
 lean_ctor_release(x_851, 0);
 lean_ctor_release(x_851, 1);
 x_993 = x_851;
} else {
 lean_dec_ref(x_851);
 x_993 = lean_box(0);
}
if (lean_is_scalar(x_993)) {
 x_994 = lean_alloc_ctor(1, 2, 0);
} else {
 x_994 = x_993;
}
lean_ctor_set(x_994, 0, x_991);
lean_ctor_set(x_994, 1, x_992);
return x_994;
}
}
else
{
lean_object* x_995; lean_object* x_996; lean_object* x_997; lean_object* x_998; 
lean_dec(x_839);
lean_dec(x_829);
lean_dec(x_825);
lean_dec(x_822);
lean_dec(x_820);
lean_dec(x_819);
lean_dec(x_818);
lean_dec(x_815);
lean_dec(x_797);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_995 = lean_ctor_get(x_845, 0);
lean_inc(x_995);
x_996 = lean_ctor_get(x_845, 1);
lean_inc(x_996);
if (lean_is_exclusive(x_845)) {
 lean_ctor_release(x_845, 0);
 lean_ctor_release(x_845, 1);
 x_997 = x_845;
} else {
 lean_dec_ref(x_845);
 x_997 = lean_box(0);
}
if (lean_is_scalar(x_997)) {
 x_998 = lean_alloc_ctor(1, 2, 0);
} else {
 x_998 = x_997;
}
lean_ctor_set(x_998, 0, x_995);
lean_ctor_set(x_998, 1, x_996);
return x_998;
}
}
else
{
lean_object* x_999; lean_object* x_1000; lean_object* x_1001; lean_object* x_1002; 
lean_dec(x_797);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_999 = lean_ctor_get(x_802, 0);
lean_inc(x_999);
x_1000 = lean_ctor_get(x_802, 1);
lean_inc(x_1000);
if (lean_is_exclusive(x_802)) {
 lean_ctor_release(x_802, 0);
 lean_ctor_release(x_802, 1);
 x_1001 = x_802;
} else {
 lean_dec_ref(x_802);
 x_1001 = lean_box(0);
}
if (lean_is_scalar(x_1001)) {
 x_1002 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1002 = x_1001;
}
lean_ctor_set(x_1002, 0, x_999);
lean_ctor_set(x_1002, 1, x_1000);
return x_1002;
}
}
else
{
lean_object* x_1003; lean_object* x_1004; lean_object* x_1005; lean_object* x_1006; 
lean_dec(x_797);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1003 = lean_ctor_get(x_799, 0);
lean_inc(x_1003);
x_1004 = lean_ctor_get(x_799, 1);
lean_inc(x_1004);
if (lean_is_exclusive(x_799)) {
 lean_ctor_release(x_799, 0);
 lean_ctor_release(x_799, 1);
 x_1005 = x_799;
} else {
 lean_dec_ref(x_799);
 x_1005 = lean_box(0);
}
if (lean_is_scalar(x_1005)) {
 x_1006 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1006 = x_1005;
}
lean_ctor_set(x_1006, 0, x_1003);
lean_ctor_set(x_1006, 1, x_1004);
return x_1006;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_13; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_4, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_4, 1);
lean_inc(x_15);
lean_dec(x_4);
lean_inc(x_6);
lean_inc(x_14);
x_16 = l_Lean_getConstInfoCtor___at___Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0(x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_alloc_closure((void*)(l_Std_Range_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__2___boxed), 8, 0);
x_20 = lean_alloc_closure((void*)(l_Std_Range_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___boxed), 7, 0);
x_21 = lean_alloc_closure((void*)(l_Std_Range_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__0___boxed), 1, 0);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_mk_empty_array_with_capacity(x_22);
x_24 = lean_ctor_get(x_17, 0);
lean_inc(x_24);
lean_dec(x_17);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_24);
lean_inc(x_1);
x_25 = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2_spec__2___redArg___lam__3___boxed), 19, 10);
lean_closure_set(x_25, 0, x_1);
lean_closure_set(x_25, 1, x_22);
lean_closure_set(x_25, 2, x_23);
lean_closure_set(x_25, 3, x_20);
lean_closure_set(x_25, 4, x_19);
lean_closure_set(x_25, 5, x_24);
lean_closure_set(x_25, 6, x_21);
lean_closure_set(x_25, 7, x_2);
lean_closure_set(x_25, 8, x_3);
lean_closure_set(x_25, 9, x_14);
x_26 = lean_ctor_get(x_24, 2);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_box(0);
x_28 = lean_unbox(x_27);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_29 = l_Lean_Meta_forallTelescopeReducing___at___Lean_Elab_Deriving_mkInductArgNames_spec__1___redArg(x_26, x_25, x_28, x_6, x_7, x_8, x_9, x_10, x_11, x_18);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_array_push(x_5, x_30);
x_4 = x_15;
x_5 = x_32;
x_12 = x_31;
goto _start;
}
else
{
uint8_t x_34; 
lean_dec(x_15);
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
x_34 = !lean_is_exclusive(x_29);
if (x_34 == 0)
{
return x_29;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_29, 0);
x_36 = lean_ctor_get(x_29, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_29);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
uint8_t x_38; 
lean_dec(x_15);
lean_dec(x_14);
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
x_38 = !lean_is_exclusive(x_16);
if (x_38 == 0)
{
return x_16;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_16, 0);
x_40 = lean_ctor_get(x_16, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_16);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2_spec__2___redArg(x_1, x_2, x_3, x_5, x_6, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_14; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_6);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_5, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_5, 1);
lean_inc(x_16);
lean_dec(x_5);
lean_inc(x_7);
lean_inc(x_15);
x_17 = l_Lean_getConstInfoCtor___at___Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0(x_15, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_alloc_closure((void*)(l_Std_Range_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__2___boxed), 8, 0);
x_21 = lean_alloc_closure((void*)(l_Std_Range_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___boxed), 7, 0);
x_22 = lean_alloc_closure((void*)(l_Std_Range_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__0___boxed), 1, 0);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_mk_empty_array_with_capacity(x_23);
x_25 = lean_ctor_get(x_18, 0);
lean_inc(x_25);
lean_dec(x_18);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_25);
lean_inc(x_1);
x_26 = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2_spec__2___redArg___lam__3___boxed), 19, 10);
lean_closure_set(x_26, 0, x_1);
lean_closure_set(x_26, 1, x_23);
lean_closure_set(x_26, 2, x_24);
lean_closure_set(x_26, 3, x_21);
lean_closure_set(x_26, 4, x_20);
lean_closure_set(x_26, 5, x_25);
lean_closure_set(x_26, 6, x_22);
lean_closure_set(x_26, 7, x_2);
lean_closure_set(x_26, 8, x_3);
lean_closure_set(x_26, 9, x_15);
x_27 = lean_ctor_get(x_25, 2);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_box(0);
x_29 = lean_unbox(x_28);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_30 = l_Lean_Meta_forallTelescopeReducing___at___Lean_Elab_Deriving_mkInductArgNames_spec__1___redArg(x_27, x_26, x_29, x_7, x_8, x_9, x_10, x_11, x_12, x_19);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_array_push(x_6, x_31);
x_34 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2_spec__2___redArg(x_1, x_2, x_3, x_16, x_33, x_7, x_8, x_9, x_10, x_11, x_12, x_32);
return x_34;
}
else
{
uint8_t x_35; 
lean_dec(x_16);
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
x_35 = !lean_is_exclusive(x_30);
if (x_35 == 0)
{
return x_30;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_30, 0);
x_37 = lean_ctor_get(x_30, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_30);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_16);
lean_dec(x_15);
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
x_39 = !lean_is_exclusive(x_17);
if (x_39 == 0)
{
return x_17;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_17, 0);
x_41 = lean_ctor_get(x_17, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_17);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_List_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__4(size_t x_1, size_t x_2, lean_object* x_3) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_box(0);
lean_inc(x_3);
x_6 = lean_array_uset(x_3, x_2, x_5);
x_7 = lean_array_uget(x_3, x_2);
lean_dec(x_3);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_usize_of_nat(x_8);
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_6, x_2, x_7);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_mk_empty_array_with_capacity(x_11);
x_13 = lean_ctor_get(x_2, 4);
lean_inc(x_13);
lean_inc(x_13);
x_14 = l_List_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg(x_2, x_3, x_1, x_13, x_13, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_13);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_array_size(x_16);
x_18 = lean_usize_of_nat(x_11);
x_19 = l_Array_mapMUnsafe_map___at___Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__4(x_17, x_18, x_16);
lean_ctor_set(x_14, 0, x_19);
return x_14;
}
else
{
lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_14, 0);
x_21 = lean_ctor_get(x_14, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_14);
x_22 = lean_array_size(x_20);
x_23 = lean_usize_of_nat(x_11);
x_24 = l_Array_mapMUnsafe_map___at___Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__4(x_22, x_23, x_20);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_21);
return x_25;
}
}
else
{
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_17;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2_spec__2___redArg___lam__3___boxed(lean_object** _args) {
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
lean_object* x_20; 
x_20 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2_spec__2___redArg___lam__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_1);
return x_20;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_4);
return x_15;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_List_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_4);
return x_14;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_List_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_4);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__4(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForInduct(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
lean_inc(x_2);
lean_inc(x_1);
x_11 = l_Lean_Elab_Deriving_mkDiscrs(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_9);
lean_inc(x_8);
x_15 = l_Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_st_ref_get(x_9, x_17);
lean_dec(x_9);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; size_t x_34; lean_object* x_35; size_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
x_21 = lean_ctor_get(x_8, 5);
lean_inc(x_21);
lean_dec(x_8);
x_22 = lean_box(0);
x_23 = lean_unbox(x_22);
x_24 = l_Lean_SourceInfo_fromRef(x_21, x_23);
lean_dec(x_21);
x_25 = lean_mk_string_unchecked("Lean", 4, 4);
x_26 = lean_mk_string_unchecked("Parser", 6, 6);
x_27 = lean_mk_string_unchecked("Term", 4, 4);
x_28 = lean_mk_string_unchecked("match", 5, 5);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
x_29 = l_Lean_Name_mkStr4(x_25, x_26, x_27, x_28);
lean_inc(x_24);
lean_ctor_set_tag(x_11, 2);
lean_ctor_set(x_11, 1, x_28);
lean_ctor_set(x_11, 0, x_24);
x_30 = lean_mk_string_unchecked("null", 4, 4);
x_31 = l_Lean_Name_mkStr1(x_30);
x_32 = l_Array_mkArray0(lean_box(0));
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_24);
x_33 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_33, 0, x_24);
lean_ctor_set(x_33, 1, x_31);
lean_ctor_set(x_33, 2, x_32);
x_34 = lean_array_size(x_13);
x_35 = lean_unsigned_to_nat(0u);
x_36 = lean_usize_of_nat(x_35);
x_37 = l_Array_mapMUnsafe_map___at___Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1_spec__0(x_34, x_36, x_13);
x_38 = lean_mk_string_unchecked(",", 1, 1);
x_39 = l_Lean_mkAtom(x_38);
x_40 = l_Lean_mkSepArray(x_37, x_39);
lean_dec(x_37);
lean_inc(x_32);
x_41 = l_Array_append(lean_box(0), x_32, x_40);
lean_dec(x_40);
lean_inc(x_31);
lean_inc(x_24);
x_42 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_42, 0, x_24);
lean_ctor_set(x_42, 1, x_31);
lean_ctor_set(x_42, 2, x_41);
x_43 = lean_mk_string_unchecked("with", 4, 4);
lean_inc(x_24);
x_44 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_44, 0, x_24);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_mk_string_unchecked("matchAlts", 9, 9);
x_46 = l_Lean_Name_mkStr4(x_25, x_26, x_27, x_45);
x_47 = l_Array_append(lean_box(0), x_32, x_16);
lean_dec(x_16);
lean_inc(x_24);
x_48 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_48, 0, x_24);
lean_ctor_set(x_48, 1, x_31);
lean_ctor_set(x_48, 2, x_47);
lean_inc(x_24);
x_49 = l_Lean_Syntax_node1(x_24, x_46, x_48);
lean_inc(x_33);
x_50 = l_Lean_Syntax_node6(x_24, x_29, x_11, x_33, x_33, x_42, x_44, x_49);
lean_ctor_set(x_18, 0, x_50);
return x_18;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; size_t x_65; lean_object* x_66; size_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_51 = lean_ctor_get(x_18, 1);
lean_inc(x_51);
lean_dec(x_18);
x_52 = lean_ctor_get(x_8, 5);
lean_inc(x_52);
lean_dec(x_8);
x_53 = lean_box(0);
x_54 = lean_unbox(x_53);
x_55 = l_Lean_SourceInfo_fromRef(x_52, x_54);
lean_dec(x_52);
x_56 = lean_mk_string_unchecked("Lean", 4, 4);
x_57 = lean_mk_string_unchecked("Parser", 6, 6);
x_58 = lean_mk_string_unchecked("Term", 4, 4);
x_59 = lean_mk_string_unchecked("match", 5, 5);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
x_60 = l_Lean_Name_mkStr4(x_56, x_57, x_58, x_59);
lean_inc(x_55);
lean_ctor_set_tag(x_11, 2);
lean_ctor_set(x_11, 1, x_59);
lean_ctor_set(x_11, 0, x_55);
x_61 = lean_mk_string_unchecked("null", 4, 4);
x_62 = l_Lean_Name_mkStr1(x_61);
x_63 = l_Array_mkArray0(lean_box(0));
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_55);
x_64 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_64, 0, x_55);
lean_ctor_set(x_64, 1, x_62);
lean_ctor_set(x_64, 2, x_63);
x_65 = lean_array_size(x_13);
x_66 = lean_unsigned_to_nat(0u);
x_67 = lean_usize_of_nat(x_66);
x_68 = l_Array_mapMUnsafe_map___at___Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1_spec__0(x_65, x_67, x_13);
x_69 = lean_mk_string_unchecked(",", 1, 1);
x_70 = l_Lean_mkAtom(x_69);
x_71 = l_Lean_mkSepArray(x_68, x_70);
lean_dec(x_68);
lean_inc(x_63);
x_72 = l_Array_append(lean_box(0), x_63, x_71);
lean_dec(x_71);
lean_inc(x_62);
lean_inc(x_55);
x_73 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_73, 0, x_55);
lean_ctor_set(x_73, 1, x_62);
lean_ctor_set(x_73, 2, x_72);
x_74 = lean_mk_string_unchecked("with", 4, 4);
lean_inc(x_55);
x_75 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_75, 0, x_55);
lean_ctor_set(x_75, 1, x_74);
x_76 = lean_mk_string_unchecked("matchAlts", 9, 9);
x_77 = l_Lean_Name_mkStr4(x_56, x_57, x_58, x_76);
x_78 = l_Array_append(lean_box(0), x_63, x_16);
lean_dec(x_16);
lean_inc(x_55);
x_79 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_79, 0, x_55);
lean_ctor_set(x_79, 1, x_62);
lean_ctor_set(x_79, 2, x_78);
lean_inc(x_55);
x_80 = l_Lean_Syntax_node1(x_55, x_77, x_79);
lean_inc(x_64);
x_81 = l_Lean_Syntax_node6(x_55, x_60, x_11, x_64, x_64, x_73, x_75, x_80);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_51);
return x_82;
}
}
else
{
uint8_t x_83; 
lean_free_object(x_11);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
x_83 = !lean_is_exclusive(x_15);
if (x_83 == 0)
{
return x_15;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_15, 0);
x_85 = lean_ctor_get(x_15, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_15);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_11, 0);
x_88 = lean_ctor_get(x_11, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_11);
lean_inc(x_9);
lean_inc(x_8);
x_89 = l_Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_88);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; size_t x_109; lean_object* x_110; size_t x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
x_92 = lean_st_ref_get(x_9, x_91);
lean_dec(x_9);
x_93 = lean_ctor_get(x_92, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_94 = x_92;
} else {
 lean_dec_ref(x_92);
 x_94 = lean_box(0);
}
x_95 = lean_ctor_get(x_8, 5);
lean_inc(x_95);
lean_dec(x_8);
x_96 = lean_box(0);
x_97 = lean_unbox(x_96);
x_98 = l_Lean_SourceInfo_fromRef(x_95, x_97);
lean_dec(x_95);
x_99 = lean_mk_string_unchecked("Lean", 4, 4);
x_100 = lean_mk_string_unchecked("Parser", 6, 6);
x_101 = lean_mk_string_unchecked("Term", 4, 4);
x_102 = lean_mk_string_unchecked("match", 5, 5);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
x_103 = l_Lean_Name_mkStr4(x_99, x_100, x_101, x_102);
lean_inc(x_98);
x_104 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_104, 0, x_98);
lean_ctor_set(x_104, 1, x_102);
x_105 = lean_mk_string_unchecked("null", 4, 4);
x_106 = l_Lean_Name_mkStr1(x_105);
x_107 = l_Array_mkArray0(lean_box(0));
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_98);
x_108 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_108, 0, x_98);
lean_ctor_set(x_108, 1, x_106);
lean_ctor_set(x_108, 2, x_107);
x_109 = lean_array_size(x_87);
x_110 = lean_unsigned_to_nat(0u);
x_111 = lean_usize_of_nat(x_110);
x_112 = l_Array_mapMUnsafe_map___at___Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1_spec__0(x_109, x_111, x_87);
x_113 = lean_mk_string_unchecked(",", 1, 1);
x_114 = l_Lean_mkAtom(x_113);
x_115 = l_Lean_mkSepArray(x_112, x_114);
lean_dec(x_112);
lean_inc(x_107);
x_116 = l_Array_append(lean_box(0), x_107, x_115);
lean_dec(x_115);
lean_inc(x_106);
lean_inc(x_98);
x_117 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_117, 0, x_98);
lean_ctor_set(x_117, 1, x_106);
lean_ctor_set(x_117, 2, x_116);
x_118 = lean_mk_string_unchecked("with", 4, 4);
lean_inc(x_98);
x_119 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_119, 0, x_98);
lean_ctor_set(x_119, 1, x_118);
x_120 = lean_mk_string_unchecked("matchAlts", 9, 9);
x_121 = l_Lean_Name_mkStr4(x_99, x_100, x_101, x_120);
x_122 = l_Array_append(lean_box(0), x_107, x_90);
lean_dec(x_90);
lean_inc(x_98);
x_123 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_123, 0, x_98);
lean_ctor_set(x_123, 1, x_106);
lean_ctor_set(x_123, 2, x_122);
lean_inc(x_98);
x_124 = l_Lean_Syntax_node1(x_98, x_121, x_123);
lean_inc(x_108);
x_125 = l_Lean_Syntax_node6(x_98, x_103, x_104, x_108, x_108, x_117, x_119, x_124);
if (lean_is_scalar(x_94)) {
 x_126 = lean_alloc_ctor(0, 2, 0);
} else {
 x_126 = x_94;
}
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_93);
return x_126;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
lean_dec(x_87);
lean_dec(x_9);
lean_dec(x_8);
x_127 = lean_ctor_get(x_89, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_89, 1);
lean_inc(x_128);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_129 = x_89;
} else {
 lean_dec_ref(x_89);
 x_129 = lean_box(0);
}
if (lean_is_scalar(x_129)) {
 x_130 = lean_alloc_ctor(1, 2, 0);
} else {
 x_130 = x_129;
}
lean_ctor_set(x_130, 0, x_127);
lean_ctor_set(x_130, 1, x_128);
return x_130;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkBody(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_11 = lean_st_ref_get(x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_2, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_Lean_isStructure(x_14, x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = l_Lean_Elab_Deriving_Repr_mkBodyForInduct(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
return x_18;
}
else
{
lean_object* x_19; 
lean_dec(x_3);
x_19 = l_Lean_Elab_Deriving_Repr_mkBodyForStruct(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_Lean_instInhabitedInductiveVal;
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_array_get(x_10, x_11, x_2);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_12);
x_13 = l_Lean_Elab_Deriving_Repr_mkReprHeader(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_317; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_box(0);
x_17 = lean_ctor_get(x_1, 1);
x_18 = lean_array_get(x_16, x_17, x_2);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_18);
lean_inc(x_14);
x_317 = l_Lean_Elab_Deriving_Repr_mkBody(x_14, x_12, x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_15);
if (lean_obj_tag(x_317) == 0)
{
uint8_t x_318; 
x_318 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
if (x_318 == 0)
{
lean_object* x_319; lean_object* x_320; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_319 = lean_ctor_get(x_317, 0);
lean_inc(x_319);
x_320 = lean_ctor_get(x_317, 1);
lean_inc(x_320);
lean_dec(x_317);
x_19 = x_319;
x_20 = x_7;
x_21 = x_8;
x_22 = x_320;
goto block_316;
}
else
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; 
x_321 = lean_ctor_get(x_317, 0);
lean_inc(x_321);
x_322 = lean_ctor_get(x_317, 1);
lean_inc(x_322);
lean_dec(x_317);
x_323 = lean_mk_string_unchecked("Repr", 4, 4);
x_324 = l_Lean_Name_mkStr1(x_323);
x_325 = lean_ctor_get(x_14, 1);
lean_inc(x_325);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_326 = l_Lean_Elab_Deriving_mkLocalInstanceLetDecls(x_1, x_324, x_325, x_3, x_4, x_5, x_6, x_7, x_8, x_322);
if (lean_obj_tag(x_326) == 0)
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; 
x_327 = lean_ctor_get(x_326, 0);
lean_inc(x_327);
x_328 = lean_ctor_get(x_326, 1);
lean_inc(x_328);
lean_dec(x_326);
x_329 = l_Lean_Elab_Deriving_mkLet(x_327, x_321, x_3, x_4, x_5, x_6, x_7, x_8, x_328);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_327);
x_330 = lean_ctor_get(x_329, 0);
lean_inc(x_330);
x_331 = lean_ctor_get(x_329, 1);
lean_inc(x_331);
lean_dec(x_329);
x_19 = x_330;
x_20 = x_7;
x_21 = x_8;
x_22 = x_331;
goto block_316;
}
else
{
uint8_t x_332; 
lean_dec(x_321);
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_332 = !lean_is_exclusive(x_326);
if (x_332 == 0)
{
return x_326;
}
else
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; 
x_333 = lean_ctor_get(x_326, 0);
x_334 = lean_ctor_get(x_326, 1);
lean_inc(x_334);
lean_inc(x_333);
lean_dec(x_326);
x_335 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_335, 0, x_333);
lean_ctor_set(x_335, 1, x_334);
return x_335;
}
}
}
}
else
{
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_317;
}
block_316:
{
uint8_t x_23; 
x_23 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_14, 0);
lean_inc(x_24);
lean_dec(x_14);
x_25 = lean_st_ref_get(x_21, x_22);
lean_dec(x_21);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_ctor_get(x_20, 5);
lean_inc(x_28);
x_29 = l_Lean_SourceInfo_fromRef(x_28, x_23);
lean_dec(x_28);
x_30 = lean_ctor_get(x_20, 10);
lean_inc(x_30);
lean_dec(x_20);
x_31 = lean_ctor_get(x_27, 0);
lean_inc(x_31);
lean_dec(x_27);
x_32 = l_Lean_Environment_mainModule(x_31);
lean_dec(x_31);
x_33 = lean_mk_string_unchecked("Lean", 4, 4);
x_34 = lean_mk_string_unchecked("Parser", 6, 6);
x_35 = lean_mk_string_unchecked("Command", 7, 7);
x_36 = lean_mk_string_unchecked("declaration", 11, 11);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
x_37 = l_Lean_Name_mkStr4(x_33, x_34, x_35, x_36);
x_38 = lean_mk_string_unchecked("declModifiers", 13, 13);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
x_39 = l_Lean_Name_mkStr4(x_33, x_34, x_35, x_38);
x_40 = lean_mk_string_unchecked("null", 4, 4);
x_41 = l_Lean_Name_mkStr1(x_40);
x_42 = l_Array_mkArray0(lean_box(0));
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_29);
x_43 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_43, 0, x_29);
lean_ctor_set(x_43, 1, x_41);
lean_ctor_set(x_43, 2, x_42);
x_44 = lean_mk_string_unchecked("private", 7, 7);
lean_inc(x_44);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
x_45 = l_Lean_Name_mkStr4(x_33, x_34, x_35, x_44);
lean_inc(x_29);
x_46 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_46, 0, x_29);
lean_ctor_set(x_46, 1, x_44);
lean_inc(x_29);
x_47 = l_Lean_Syntax_node1(x_29, x_45, x_46);
lean_inc(x_41);
lean_inc(x_29);
x_48 = l_Lean_Syntax_node1(x_29, x_41, x_47);
lean_inc_n(x_43, 5);
lean_inc(x_29);
x_49 = l_Lean_Syntax_node6(x_29, x_39, x_43, x_43, x_48, x_43, x_43, x_43);
x_50 = lean_mk_string_unchecked("definition", 10, 10);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
x_51 = l_Lean_Name_mkStr4(x_33, x_34, x_35, x_50);
x_52 = lean_mk_string_unchecked("def", 3, 3);
lean_inc(x_29);
x_53 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_53, 0, x_29);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_mk_string_unchecked("declId", 6, 6);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
x_55 = l_Lean_Name_mkStr4(x_33, x_34, x_35, x_54);
x_56 = lean_mk_syntax_ident(x_18);
lean_inc(x_43);
lean_inc(x_29);
x_57 = l_Lean_Syntax_node2(x_29, x_55, x_56, x_43);
x_58 = lean_mk_string_unchecked("optDeclSig", 10, 10);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
x_59 = l_Lean_Name_mkStr4(x_33, x_34, x_35, x_58);
x_60 = lean_mk_string_unchecked("Term", 4, 4);
x_61 = l_Array_append(lean_box(0), x_42, x_24);
lean_dec(x_24);
lean_inc(x_41);
lean_inc(x_29);
x_62 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_62, 0, x_29);
lean_ctor_set(x_62, 1, x_41);
lean_ctor_set(x_62, 2, x_61);
x_63 = lean_mk_string_unchecked("typeSpec", 8, 8);
lean_inc(x_34);
lean_inc(x_33);
x_64 = l_Lean_Name_mkStr4(x_33, x_34, x_60, x_63);
x_65 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_29);
x_66 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_66, 0, x_29);
lean_ctor_set(x_66, 1, x_65);
x_67 = lean_mk_string_unchecked("Format", 6, 6);
lean_inc(x_67);
x_68 = l_String_toSubstring_x27(x_67);
lean_inc(x_67);
x_69 = l_Lean_Name_mkStr1(x_67);
x_70 = l_Lean_addMacroScope(x_32, x_69, x_30);
x_71 = lean_mk_string_unchecked("Std", 3, 3);
x_72 = l_Lean_Name_mkStr2(x_71, x_67);
x_73 = lean_box(0);
lean_inc(x_72);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
x_75 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_75, 0, x_72);
x_76 = lean_box(0);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_74);
lean_ctor_set(x_78, 1, x_77);
lean_inc(x_29);
x_79 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_79, 0, x_29);
lean_ctor_set(x_79, 1, x_68);
lean_ctor_set(x_79, 2, x_70);
lean_ctor_set(x_79, 3, x_78);
lean_inc(x_29);
x_80 = l_Lean_Syntax_node2(x_29, x_64, x_66, x_79);
lean_inc(x_29);
x_81 = l_Lean_Syntax_node1(x_29, x_41, x_80);
lean_inc(x_29);
x_82 = l_Lean_Syntax_node2(x_29, x_59, x_62, x_81);
x_83 = lean_mk_string_unchecked("declValSimple", 13, 13);
lean_inc(x_34);
lean_inc(x_33);
x_84 = l_Lean_Name_mkStr4(x_33, x_34, x_35, x_83);
x_85 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_29);
x_86 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_86, 0, x_29);
lean_ctor_set(x_86, 1, x_85);
x_87 = lean_mk_string_unchecked("Termination", 11, 11);
x_88 = lean_mk_string_unchecked("suffix", 6, 6);
x_89 = l_Lean_Name_mkStr4(x_33, x_34, x_87, x_88);
lean_inc_n(x_43, 2);
lean_inc(x_29);
x_90 = l_Lean_Syntax_node2(x_29, x_89, x_43, x_43);
lean_inc(x_43);
lean_inc(x_29);
x_91 = l_Lean_Syntax_node4(x_29, x_84, x_86, x_19, x_90, x_43);
lean_inc(x_29);
x_92 = l_Lean_Syntax_node5(x_29, x_51, x_53, x_57, x_82, x_91, x_43);
x_93 = l_Lean_Syntax_node2(x_29, x_37, x_49, x_92);
lean_ctor_set(x_25, 0, x_93);
return x_25;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_94 = lean_ctor_get(x_25, 0);
x_95 = lean_ctor_get(x_25, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_25);
x_96 = lean_ctor_get(x_20, 5);
lean_inc(x_96);
x_97 = l_Lean_SourceInfo_fromRef(x_96, x_23);
lean_dec(x_96);
x_98 = lean_ctor_get(x_20, 10);
lean_inc(x_98);
lean_dec(x_20);
x_99 = lean_ctor_get(x_94, 0);
lean_inc(x_99);
lean_dec(x_94);
x_100 = l_Lean_Environment_mainModule(x_99);
lean_dec(x_99);
x_101 = lean_mk_string_unchecked("Lean", 4, 4);
x_102 = lean_mk_string_unchecked("Parser", 6, 6);
x_103 = lean_mk_string_unchecked("Command", 7, 7);
x_104 = lean_mk_string_unchecked("declaration", 11, 11);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
x_105 = l_Lean_Name_mkStr4(x_101, x_102, x_103, x_104);
x_106 = lean_mk_string_unchecked("declModifiers", 13, 13);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
x_107 = l_Lean_Name_mkStr4(x_101, x_102, x_103, x_106);
x_108 = lean_mk_string_unchecked("null", 4, 4);
x_109 = l_Lean_Name_mkStr1(x_108);
x_110 = l_Array_mkArray0(lean_box(0));
lean_inc(x_110);
lean_inc(x_109);
lean_inc(x_97);
x_111 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_111, 0, x_97);
lean_ctor_set(x_111, 1, x_109);
lean_ctor_set(x_111, 2, x_110);
x_112 = lean_mk_string_unchecked("private", 7, 7);
lean_inc(x_112);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
x_113 = l_Lean_Name_mkStr4(x_101, x_102, x_103, x_112);
lean_inc(x_97);
x_114 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_114, 0, x_97);
lean_ctor_set(x_114, 1, x_112);
lean_inc(x_97);
x_115 = l_Lean_Syntax_node1(x_97, x_113, x_114);
lean_inc(x_109);
lean_inc(x_97);
x_116 = l_Lean_Syntax_node1(x_97, x_109, x_115);
lean_inc_n(x_111, 5);
lean_inc(x_97);
x_117 = l_Lean_Syntax_node6(x_97, x_107, x_111, x_111, x_116, x_111, x_111, x_111);
x_118 = lean_mk_string_unchecked("definition", 10, 10);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
x_119 = l_Lean_Name_mkStr4(x_101, x_102, x_103, x_118);
x_120 = lean_mk_string_unchecked("def", 3, 3);
lean_inc(x_97);
x_121 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_121, 0, x_97);
lean_ctor_set(x_121, 1, x_120);
x_122 = lean_mk_string_unchecked("declId", 6, 6);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
x_123 = l_Lean_Name_mkStr4(x_101, x_102, x_103, x_122);
x_124 = lean_mk_syntax_ident(x_18);
lean_inc(x_111);
lean_inc(x_97);
x_125 = l_Lean_Syntax_node2(x_97, x_123, x_124, x_111);
x_126 = lean_mk_string_unchecked("optDeclSig", 10, 10);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
x_127 = l_Lean_Name_mkStr4(x_101, x_102, x_103, x_126);
x_128 = lean_mk_string_unchecked("Term", 4, 4);
x_129 = l_Array_append(lean_box(0), x_110, x_24);
lean_dec(x_24);
lean_inc(x_109);
lean_inc(x_97);
x_130 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_130, 0, x_97);
lean_ctor_set(x_130, 1, x_109);
lean_ctor_set(x_130, 2, x_129);
x_131 = lean_mk_string_unchecked("typeSpec", 8, 8);
lean_inc(x_102);
lean_inc(x_101);
x_132 = l_Lean_Name_mkStr4(x_101, x_102, x_128, x_131);
x_133 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_97);
x_134 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_134, 0, x_97);
lean_ctor_set(x_134, 1, x_133);
x_135 = lean_mk_string_unchecked("Format", 6, 6);
lean_inc(x_135);
x_136 = l_String_toSubstring_x27(x_135);
lean_inc(x_135);
x_137 = l_Lean_Name_mkStr1(x_135);
x_138 = l_Lean_addMacroScope(x_100, x_137, x_98);
x_139 = lean_mk_string_unchecked("Std", 3, 3);
x_140 = l_Lean_Name_mkStr2(x_139, x_135);
x_141 = lean_box(0);
lean_inc(x_140);
x_142 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set(x_142, 1, x_141);
x_143 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_143, 0, x_140);
x_144 = lean_box(0);
x_145 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set(x_145, 1, x_144);
x_146 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_146, 0, x_142);
lean_ctor_set(x_146, 1, x_145);
lean_inc(x_97);
x_147 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_147, 0, x_97);
lean_ctor_set(x_147, 1, x_136);
lean_ctor_set(x_147, 2, x_138);
lean_ctor_set(x_147, 3, x_146);
lean_inc(x_97);
x_148 = l_Lean_Syntax_node2(x_97, x_132, x_134, x_147);
lean_inc(x_97);
x_149 = l_Lean_Syntax_node1(x_97, x_109, x_148);
lean_inc(x_97);
x_150 = l_Lean_Syntax_node2(x_97, x_127, x_130, x_149);
x_151 = lean_mk_string_unchecked("declValSimple", 13, 13);
lean_inc(x_102);
lean_inc(x_101);
x_152 = l_Lean_Name_mkStr4(x_101, x_102, x_103, x_151);
x_153 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_97);
x_154 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_154, 0, x_97);
lean_ctor_set(x_154, 1, x_153);
x_155 = lean_mk_string_unchecked("Termination", 11, 11);
x_156 = lean_mk_string_unchecked("suffix", 6, 6);
x_157 = l_Lean_Name_mkStr4(x_101, x_102, x_155, x_156);
lean_inc_n(x_111, 2);
lean_inc(x_97);
x_158 = l_Lean_Syntax_node2(x_97, x_157, x_111, x_111);
lean_inc(x_111);
lean_inc(x_97);
x_159 = l_Lean_Syntax_node4(x_97, x_152, x_154, x_19, x_158, x_111);
lean_inc(x_97);
x_160 = l_Lean_Syntax_node5(x_97, x_119, x_121, x_125, x_150, x_159, x_111);
x_161 = l_Lean_Syntax_node2(x_97, x_105, x_117, x_160);
x_162 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_162, 1, x_95);
return x_162;
}
}
else
{
lean_object* x_163; lean_object* x_164; uint8_t x_165; 
x_163 = lean_ctor_get(x_14, 0);
lean_inc(x_163);
lean_dec(x_14);
x_164 = lean_st_ref_get(x_21, x_22);
lean_dec(x_21);
x_165 = !lean_is_exclusive(x_164);
if (x_165 == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; uint8_t x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_166 = lean_ctor_get(x_164, 0);
x_167 = lean_ctor_get(x_20, 5);
lean_inc(x_167);
x_168 = lean_box(0);
x_169 = lean_unbox(x_168);
x_170 = l_Lean_SourceInfo_fromRef(x_167, x_169);
lean_dec(x_167);
x_171 = lean_ctor_get(x_20, 10);
lean_inc(x_171);
lean_dec(x_20);
x_172 = lean_ctor_get(x_166, 0);
lean_inc(x_172);
lean_dec(x_166);
x_173 = l_Lean_Environment_mainModule(x_172);
lean_dec(x_172);
x_174 = lean_mk_string_unchecked("Lean", 4, 4);
x_175 = lean_mk_string_unchecked("Parser", 6, 6);
x_176 = lean_mk_string_unchecked("Command", 7, 7);
x_177 = lean_mk_string_unchecked("declaration", 11, 11);
lean_inc(x_176);
lean_inc(x_175);
lean_inc(x_174);
x_178 = l_Lean_Name_mkStr4(x_174, x_175, x_176, x_177);
x_179 = lean_mk_string_unchecked("declModifiers", 13, 13);
lean_inc(x_176);
lean_inc(x_175);
lean_inc(x_174);
x_180 = l_Lean_Name_mkStr4(x_174, x_175, x_176, x_179);
x_181 = lean_mk_string_unchecked("null", 4, 4);
x_182 = l_Lean_Name_mkStr1(x_181);
x_183 = l_Array_mkArray0(lean_box(0));
lean_inc(x_183);
lean_inc(x_182);
lean_inc(x_170);
x_184 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_184, 0, x_170);
lean_ctor_set(x_184, 1, x_182);
lean_ctor_set(x_184, 2, x_183);
x_185 = lean_mk_string_unchecked("private", 7, 7);
lean_inc(x_185);
lean_inc(x_176);
lean_inc(x_175);
lean_inc(x_174);
x_186 = l_Lean_Name_mkStr4(x_174, x_175, x_176, x_185);
lean_inc(x_170);
x_187 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_187, 0, x_170);
lean_ctor_set(x_187, 1, x_185);
lean_inc(x_170);
x_188 = l_Lean_Syntax_node1(x_170, x_186, x_187);
lean_inc(x_182);
lean_inc(x_170);
x_189 = l_Lean_Syntax_node1(x_170, x_182, x_188);
x_190 = lean_mk_string_unchecked("partial", 7, 7);
lean_inc(x_190);
lean_inc(x_176);
lean_inc(x_175);
lean_inc(x_174);
x_191 = l_Lean_Name_mkStr4(x_174, x_175, x_176, x_190);
lean_inc(x_170);
x_192 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_192, 0, x_170);
lean_ctor_set(x_192, 1, x_190);
lean_inc(x_170);
x_193 = l_Lean_Syntax_node1(x_170, x_191, x_192);
lean_inc(x_182);
lean_inc(x_170);
x_194 = l_Lean_Syntax_node1(x_170, x_182, x_193);
lean_inc_n(x_184, 4);
lean_inc(x_170);
x_195 = l_Lean_Syntax_node6(x_170, x_180, x_184, x_184, x_189, x_184, x_184, x_194);
x_196 = lean_mk_string_unchecked("definition", 10, 10);
lean_inc(x_176);
lean_inc(x_175);
lean_inc(x_174);
x_197 = l_Lean_Name_mkStr4(x_174, x_175, x_176, x_196);
x_198 = lean_mk_string_unchecked("def", 3, 3);
lean_inc(x_170);
x_199 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_199, 0, x_170);
lean_ctor_set(x_199, 1, x_198);
x_200 = lean_mk_string_unchecked("declId", 6, 6);
lean_inc(x_176);
lean_inc(x_175);
lean_inc(x_174);
x_201 = l_Lean_Name_mkStr4(x_174, x_175, x_176, x_200);
x_202 = lean_mk_syntax_ident(x_18);
lean_inc(x_184);
lean_inc(x_170);
x_203 = l_Lean_Syntax_node2(x_170, x_201, x_202, x_184);
x_204 = lean_mk_string_unchecked("optDeclSig", 10, 10);
lean_inc(x_176);
lean_inc(x_175);
lean_inc(x_174);
x_205 = l_Lean_Name_mkStr4(x_174, x_175, x_176, x_204);
x_206 = lean_mk_string_unchecked("Term", 4, 4);
x_207 = l_Array_append(lean_box(0), x_183, x_163);
lean_dec(x_163);
lean_inc(x_182);
lean_inc(x_170);
x_208 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_208, 0, x_170);
lean_ctor_set(x_208, 1, x_182);
lean_ctor_set(x_208, 2, x_207);
x_209 = lean_mk_string_unchecked("typeSpec", 8, 8);
lean_inc(x_175);
lean_inc(x_174);
x_210 = l_Lean_Name_mkStr4(x_174, x_175, x_206, x_209);
x_211 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_170);
x_212 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_212, 0, x_170);
lean_ctor_set(x_212, 1, x_211);
x_213 = lean_mk_string_unchecked("Format", 6, 6);
lean_inc(x_213);
x_214 = l_String_toSubstring_x27(x_213);
lean_inc(x_213);
x_215 = l_Lean_Name_mkStr1(x_213);
x_216 = l_Lean_addMacroScope(x_173, x_215, x_171);
x_217 = lean_mk_string_unchecked("Std", 3, 3);
x_218 = l_Lean_Name_mkStr2(x_217, x_213);
x_219 = lean_box(0);
lean_inc(x_218);
x_220 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_220, 0, x_218);
lean_ctor_set(x_220, 1, x_219);
x_221 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_221, 0, x_218);
x_222 = lean_box(0);
x_223 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_223, 0, x_221);
lean_ctor_set(x_223, 1, x_222);
x_224 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_224, 0, x_220);
lean_ctor_set(x_224, 1, x_223);
lean_inc(x_170);
x_225 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_225, 0, x_170);
lean_ctor_set(x_225, 1, x_214);
lean_ctor_set(x_225, 2, x_216);
lean_ctor_set(x_225, 3, x_224);
lean_inc(x_170);
x_226 = l_Lean_Syntax_node2(x_170, x_210, x_212, x_225);
lean_inc(x_170);
x_227 = l_Lean_Syntax_node1(x_170, x_182, x_226);
lean_inc(x_170);
x_228 = l_Lean_Syntax_node2(x_170, x_205, x_208, x_227);
x_229 = lean_mk_string_unchecked("declValSimple", 13, 13);
lean_inc(x_175);
lean_inc(x_174);
x_230 = l_Lean_Name_mkStr4(x_174, x_175, x_176, x_229);
x_231 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_170);
x_232 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_232, 0, x_170);
lean_ctor_set(x_232, 1, x_231);
x_233 = lean_mk_string_unchecked("Termination", 11, 11);
x_234 = lean_mk_string_unchecked("suffix", 6, 6);
x_235 = l_Lean_Name_mkStr4(x_174, x_175, x_233, x_234);
lean_inc_n(x_184, 2);
lean_inc(x_170);
x_236 = l_Lean_Syntax_node2(x_170, x_235, x_184, x_184);
lean_inc(x_184);
lean_inc(x_170);
x_237 = l_Lean_Syntax_node4(x_170, x_230, x_232, x_19, x_236, x_184);
lean_inc(x_170);
x_238 = l_Lean_Syntax_node5(x_170, x_197, x_199, x_203, x_228, x_237, x_184);
x_239 = l_Lean_Syntax_node2(x_170, x_178, x_195, x_238);
lean_ctor_set(x_164, 0, x_239);
return x_164;
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; uint8_t x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; 
x_240 = lean_ctor_get(x_164, 0);
x_241 = lean_ctor_get(x_164, 1);
lean_inc(x_241);
lean_inc(x_240);
lean_dec(x_164);
x_242 = lean_ctor_get(x_20, 5);
lean_inc(x_242);
x_243 = lean_box(0);
x_244 = lean_unbox(x_243);
x_245 = l_Lean_SourceInfo_fromRef(x_242, x_244);
lean_dec(x_242);
x_246 = lean_ctor_get(x_20, 10);
lean_inc(x_246);
lean_dec(x_20);
x_247 = lean_ctor_get(x_240, 0);
lean_inc(x_247);
lean_dec(x_240);
x_248 = l_Lean_Environment_mainModule(x_247);
lean_dec(x_247);
x_249 = lean_mk_string_unchecked("Lean", 4, 4);
x_250 = lean_mk_string_unchecked("Parser", 6, 6);
x_251 = lean_mk_string_unchecked("Command", 7, 7);
x_252 = lean_mk_string_unchecked("declaration", 11, 11);
lean_inc(x_251);
lean_inc(x_250);
lean_inc(x_249);
x_253 = l_Lean_Name_mkStr4(x_249, x_250, x_251, x_252);
x_254 = lean_mk_string_unchecked("declModifiers", 13, 13);
lean_inc(x_251);
lean_inc(x_250);
lean_inc(x_249);
x_255 = l_Lean_Name_mkStr4(x_249, x_250, x_251, x_254);
x_256 = lean_mk_string_unchecked("null", 4, 4);
x_257 = l_Lean_Name_mkStr1(x_256);
x_258 = l_Array_mkArray0(lean_box(0));
lean_inc(x_258);
lean_inc(x_257);
lean_inc(x_245);
x_259 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_259, 0, x_245);
lean_ctor_set(x_259, 1, x_257);
lean_ctor_set(x_259, 2, x_258);
x_260 = lean_mk_string_unchecked("private", 7, 7);
lean_inc(x_260);
lean_inc(x_251);
lean_inc(x_250);
lean_inc(x_249);
x_261 = l_Lean_Name_mkStr4(x_249, x_250, x_251, x_260);
lean_inc(x_245);
x_262 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_262, 0, x_245);
lean_ctor_set(x_262, 1, x_260);
lean_inc(x_245);
x_263 = l_Lean_Syntax_node1(x_245, x_261, x_262);
lean_inc(x_257);
lean_inc(x_245);
x_264 = l_Lean_Syntax_node1(x_245, x_257, x_263);
x_265 = lean_mk_string_unchecked("partial", 7, 7);
lean_inc(x_265);
lean_inc(x_251);
lean_inc(x_250);
lean_inc(x_249);
x_266 = l_Lean_Name_mkStr4(x_249, x_250, x_251, x_265);
lean_inc(x_245);
x_267 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_267, 0, x_245);
lean_ctor_set(x_267, 1, x_265);
lean_inc(x_245);
x_268 = l_Lean_Syntax_node1(x_245, x_266, x_267);
lean_inc(x_257);
lean_inc(x_245);
x_269 = l_Lean_Syntax_node1(x_245, x_257, x_268);
lean_inc_n(x_259, 4);
lean_inc(x_245);
x_270 = l_Lean_Syntax_node6(x_245, x_255, x_259, x_259, x_264, x_259, x_259, x_269);
x_271 = lean_mk_string_unchecked("definition", 10, 10);
lean_inc(x_251);
lean_inc(x_250);
lean_inc(x_249);
x_272 = l_Lean_Name_mkStr4(x_249, x_250, x_251, x_271);
x_273 = lean_mk_string_unchecked("def", 3, 3);
lean_inc(x_245);
x_274 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_274, 0, x_245);
lean_ctor_set(x_274, 1, x_273);
x_275 = lean_mk_string_unchecked("declId", 6, 6);
lean_inc(x_251);
lean_inc(x_250);
lean_inc(x_249);
x_276 = l_Lean_Name_mkStr4(x_249, x_250, x_251, x_275);
x_277 = lean_mk_syntax_ident(x_18);
lean_inc(x_259);
lean_inc(x_245);
x_278 = l_Lean_Syntax_node2(x_245, x_276, x_277, x_259);
x_279 = lean_mk_string_unchecked("optDeclSig", 10, 10);
lean_inc(x_251);
lean_inc(x_250);
lean_inc(x_249);
x_280 = l_Lean_Name_mkStr4(x_249, x_250, x_251, x_279);
x_281 = lean_mk_string_unchecked("Term", 4, 4);
x_282 = l_Array_append(lean_box(0), x_258, x_163);
lean_dec(x_163);
lean_inc(x_257);
lean_inc(x_245);
x_283 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_283, 0, x_245);
lean_ctor_set(x_283, 1, x_257);
lean_ctor_set(x_283, 2, x_282);
x_284 = lean_mk_string_unchecked("typeSpec", 8, 8);
lean_inc(x_250);
lean_inc(x_249);
x_285 = l_Lean_Name_mkStr4(x_249, x_250, x_281, x_284);
x_286 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_245);
x_287 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_287, 0, x_245);
lean_ctor_set(x_287, 1, x_286);
x_288 = lean_mk_string_unchecked("Format", 6, 6);
lean_inc(x_288);
x_289 = l_String_toSubstring_x27(x_288);
lean_inc(x_288);
x_290 = l_Lean_Name_mkStr1(x_288);
x_291 = l_Lean_addMacroScope(x_248, x_290, x_246);
x_292 = lean_mk_string_unchecked("Std", 3, 3);
x_293 = l_Lean_Name_mkStr2(x_292, x_288);
x_294 = lean_box(0);
lean_inc(x_293);
x_295 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_295, 0, x_293);
lean_ctor_set(x_295, 1, x_294);
x_296 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_296, 0, x_293);
x_297 = lean_box(0);
x_298 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_298, 0, x_296);
lean_ctor_set(x_298, 1, x_297);
x_299 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_299, 0, x_295);
lean_ctor_set(x_299, 1, x_298);
lean_inc(x_245);
x_300 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_300, 0, x_245);
lean_ctor_set(x_300, 1, x_289);
lean_ctor_set(x_300, 2, x_291);
lean_ctor_set(x_300, 3, x_299);
lean_inc(x_245);
x_301 = l_Lean_Syntax_node2(x_245, x_285, x_287, x_300);
lean_inc(x_245);
x_302 = l_Lean_Syntax_node1(x_245, x_257, x_301);
lean_inc(x_245);
x_303 = l_Lean_Syntax_node2(x_245, x_280, x_283, x_302);
x_304 = lean_mk_string_unchecked("declValSimple", 13, 13);
lean_inc(x_250);
lean_inc(x_249);
x_305 = l_Lean_Name_mkStr4(x_249, x_250, x_251, x_304);
x_306 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_245);
x_307 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_307, 0, x_245);
lean_ctor_set(x_307, 1, x_306);
x_308 = lean_mk_string_unchecked("Termination", 11, 11);
x_309 = lean_mk_string_unchecked("suffix", 6, 6);
x_310 = l_Lean_Name_mkStr4(x_249, x_250, x_308, x_309);
lean_inc_n(x_259, 2);
lean_inc(x_245);
x_311 = l_Lean_Syntax_node2(x_245, x_310, x_259, x_259);
lean_inc(x_259);
lean_inc(x_245);
x_312 = l_Lean_Syntax_node4(x_245, x_305, x_307, x_19, x_311, x_259);
lean_inc(x_245);
x_313 = l_Lean_Syntax_node5(x_245, x_272, x_274, x_278, x_303, x_312, x_259);
x_314 = l_Lean_Syntax_node2(x_245, x_253, x_270, x_313);
x_315 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_315, 0, x_314);
lean_ctor_set(x_315, 1, x_241);
return x_315;
}
}
}
}
else
{
uint8_t x_336; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_336 = !lean_is_exclusive(x_13);
if (x_336 == 0)
{
return x_13;
}
else
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; 
x_337 = lean_ctor_get(x_13, 0);
x_338 = lean_ctor_get(x_13, 1);
lean_inc(x_338);
lean_inc(x_337);
lean_dec(x_13);
x_339 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_339, 0, x_337);
lean_ctor_set(x_339, 1, x_338);
return x_339;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Deriving_Repr_mkAuxFunction(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkMutualBlock_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_2, 1);
x_13 = lean_nat_dec_lt(x_4, x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_3);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
else
{
lean_object* x_15; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_15 = l_Lean_Elab_Deriving_Repr_mkAuxFunction(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_array_push(x_3, x_16);
x_19 = lean_ctor_get(x_2, 2);
x_20 = lean_nat_add(x_4, x_19);
lean_dec(x_4);
x_3 = x_18;
x_4 = x_20;
x_11 = x_17;
goto _start;
}
else
{
uint8_t x_22; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_22 = !lean_is_exclusive(x_15);
if (x_22 == 0)
{
return x_15;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_15, 0);
x_24 = lean_ctor_get(x_15, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_15);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkMutualBlock_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkMutualBlock_spec__0___redArg(x_1, x_2, x_3, x_4, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkMutualBlock(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_mk_empty_array_with_capacity(x_9);
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_array_get_size(x_11);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_14, 0, x_9);
lean_ctor_set(x_14, 1, x_12);
lean_ctor_set(x_14, 2, x_13);
lean_inc(x_7);
lean_inc(x_6);
x_15 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkMutualBlock_spec__0___redArg(x_1, x_14, x_10, x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_st_ref_get(x_7, x_17);
lean_dec(x_7);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
x_21 = lean_ctor_get(x_6, 5);
lean_inc(x_21);
lean_dec(x_6);
x_22 = lean_box(0);
x_23 = lean_unbox(x_22);
x_24 = l_Lean_SourceInfo_fromRef(x_21, x_23);
lean_dec(x_21);
x_25 = lean_mk_string_unchecked("Lean", 4, 4);
x_26 = lean_mk_string_unchecked("Parser", 6, 6);
x_27 = lean_mk_string_unchecked("Command", 7, 7);
x_28 = lean_mk_string_unchecked("mutual", 6, 6);
lean_inc(x_28);
x_29 = l_Lean_Name_mkStr4(x_25, x_26, x_27, x_28);
lean_inc(x_24);
x_30 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_30, 0, x_24);
lean_ctor_set(x_30, 1, x_28);
x_31 = lean_mk_string_unchecked("null", 4, 4);
x_32 = l_Lean_Name_mkStr1(x_31);
x_33 = l_Array_mkArray0(lean_box(0));
x_34 = l_Array_append(lean_box(0), x_33, x_16);
lean_dec(x_16);
lean_inc(x_24);
x_35 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_35, 0, x_24);
lean_ctor_set(x_35, 1, x_32);
lean_ctor_set(x_35, 2, x_34);
x_36 = lean_mk_string_unchecked("end", 3, 3);
lean_inc(x_24);
x_37 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_37, 0, x_24);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_Lean_Syntax_node3(x_24, x_29, x_30, x_35, x_37);
lean_ctor_set(x_18, 0, x_38);
return x_18;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_39 = lean_ctor_get(x_18, 1);
lean_inc(x_39);
lean_dec(x_18);
x_40 = lean_ctor_get(x_6, 5);
lean_inc(x_40);
lean_dec(x_6);
x_41 = lean_box(0);
x_42 = lean_unbox(x_41);
x_43 = l_Lean_SourceInfo_fromRef(x_40, x_42);
lean_dec(x_40);
x_44 = lean_mk_string_unchecked("Lean", 4, 4);
x_45 = lean_mk_string_unchecked("Parser", 6, 6);
x_46 = lean_mk_string_unchecked("Command", 7, 7);
x_47 = lean_mk_string_unchecked("mutual", 6, 6);
lean_inc(x_47);
x_48 = l_Lean_Name_mkStr4(x_44, x_45, x_46, x_47);
lean_inc(x_43);
x_49 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_49, 0, x_43);
lean_ctor_set(x_49, 1, x_47);
x_50 = lean_mk_string_unchecked("null", 4, 4);
x_51 = l_Lean_Name_mkStr1(x_50);
x_52 = l_Array_mkArray0(lean_box(0));
x_53 = l_Array_append(lean_box(0), x_52, x_16);
lean_dec(x_16);
lean_inc(x_43);
x_54 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_54, 0, x_43);
lean_ctor_set(x_54, 1, x_51);
lean_ctor_set(x_54, 2, x_53);
x_55 = lean_mk_string_unchecked("end", 3, 3);
lean_inc(x_43);
x_56 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_56, 0, x_43);
lean_ctor_set(x_56, 1, x_55);
x_57 = l_Lean_Syntax_node3(x_43, x_48, x_49, x_54, x_56);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_39);
return x_58;
}
}
else
{
uint8_t x_59; 
lean_dec(x_7);
lean_dec(x_6);
x_59 = !lean_is_exclusive(x_15);
if (x_59 == 0)
{
return x_15;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_15, 0);
x_61 = lean_ctor_get(x_15, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_15);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkMutualBlock_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkMutualBlock_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkMutualBlock_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Deriving_Repr_mkMutualBlock_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkMutualBlock___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Deriving_Repr_mkMutualBlock(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_____private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__0(lean_object* x_1, lean_object* x_2) {
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
x_7 = l_Lean_MessageData_ofSyntax(x_5);
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
x_11 = l_Lean_MessageData_ofSyntax(x_9);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_mk_string_unchecked("repr", 4, 4);
lean_inc(x_2);
lean_inc(x_1);
lean_inc(x_9);
x_10 = l_Lean_Elab_Deriving_mkContext(x_9, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_13 = l_Lean_Elab_Deriving_Repr_mkMutualBlock(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_mk_string_unchecked("Repr", 4, 4);
x_17 = l_Lean_Name_mkStr1(x_16);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_mk_empty_array_with_capacity(x_18);
lean_inc(x_19);
x_20 = lean_array_push(x_19, x_1);
x_21 = lean_box(1);
x_22 = lean_unbox(x_21);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_23 = l_Lean_Elab_Deriving_mkInstanceCmds(x_11, x_17, x_20, x_22, x_2, x_3, x_4, x_5, x_6, x_7, x_15);
lean_dec(x_20);
lean_dec(x_11);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_mk_string_unchecked("Elab", 4, 4);
x_27 = lean_mk_string_unchecked("Deriving", 8, 8);
x_28 = l_Lean_Name_mkStr3(x_26, x_27, x_9);
lean_inc(x_28);
x_29 = l_Lean_isTracingEnabledFor___at___Lean_Elab_Term_traceAtCmdPos_spec__0___redArg(x_28, x_6, x_25);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = lean_ctor_get(x_29, 1);
x_33 = lean_array_push(x_19, x_14);
x_34 = l_Array_append(lean_box(0), x_33, x_24);
lean_dec(x_24);
x_35 = lean_unbox(x_31);
lean_dec(x_31);
if (x_35 == 0)
{
lean_dec(x_28);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_ctor_set(x_29, 0, x_34);
return x_29;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
lean_free_object(x_29);
x_36 = lean_mk_string_unchecked("\n", 1, 1);
x_37 = l_Lean_stringToMessageData(x_36);
lean_dec(x_36);
lean_inc(x_34);
x_38 = lean_array_to_list(x_34);
x_39 = lean_box(0);
x_40 = l_List_mapTR_loop___at_____private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__0(x_38, x_39);
x_41 = l_Lean_MessageData_ofList(x_40);
x_42 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_42, 0, x_37);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_mk_string_unchecked("", 0, 0);
x_44 = l_Lean_stringToMessageData(x_43);
lean_dec(x_43);
x_45 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_44);
x_46 = l_Lean_addTrace___at___Lean_Elab_Term_traceAtCmdPos_spec__1___redArg(x_28, x_45, x_4, x_5, x_6, x_7, x_32);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_46, 0);
lean_dec(x_48);
lean_ctor_set(x_46, 0, x_34);
return x_46;
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_46, 1);
lean_inc(x_49);
lean_dec(x_46);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_34);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_51 = lean_ctor_get(x_29, 0);
x_52 = lean_ctor_get(x_29, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_29);
x_53 = lean_array_push(x_19, x_14);
x_54 = l_Array_append(lean_box(0), x_53, x_24);
lean_dec(x_24);
x_55 = lean_unbox(x_51);
lean_dec(x_51);
if (x_55 == 0)
{
lean_object* x_56; 
lean_dec(x_28);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_52);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_57 = lean_mk_string_unchecked("\n", 1, 1);
x_58 = l_Lean_stringToMessageData(x_57);
lean_dec(x_57);
lean_inc(x_54);
x_59 = lean_array_to_list(x_54);
x_60 = lean_box(0);
x_61 = l_List_mapTR_loop___at_____private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__0(x_59, x_60);
x_62 = l_Lean_MessageData_ofList(x_61);
x_63 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_63, 0, x_58);
lean_ctor_set(x_63, 1, x_62);
x_64 = lean_mk_string_unchecked("", 0, 0);
x_65 = l_Lean_stringToMessageData(x_64);
lean_dec(x_64);
x_66 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_65);
x_67 = l_Lean_addTrace___at___Lean_Elab_Term_traceAtCmdPos_spec__1___redArg(x_28, x_66, x_4, x_5, x_6, x_7, x_52);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_69 = x_67;
} else {
 lean_dec_ref(x_67);
 x_69 = lean_box(0);
}
if (lean_is_scalar(x_69)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_69;
}
lean_ctor_set(x_70, 0, x_54);
lean_ctor_set(x_70, 1, x_68);
return x_70;
}
}
}
else
{
uint8_t x_71; 
lean_dec(x_19);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_71 = !lean_is_exclusive(x_23);
if (x_71 == 0)
{
return x_23;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_23, 0);
x_73 = lean_ctor_get(x_23, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_23);
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
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_75 = !lean_is_exclusive(x_13);
if (x_75 == 0)
{
return x_13;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_13, 0);
x_77 = lean_ctor_get(x_13, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_13);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
else
{
uint8_t x_79; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_79 = !lean_is_exclusive(x_10);
if (x_79 == 0)
{
return x_10;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_10, 0);
x_81 = lean_ctor_get(x_10, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_10);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_Lean_isInductiveCore(x_7, x_1);
x_9 = lean_box(x_8);
lean_ctor_set(x_4, 0, x_9);
return x_4;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_4);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_isInductiveCore(x_12, x_1);
x_14 = lean_box(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_isInductive___at___Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__0___redArg(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_15; 
x_15 = lean_usize_dec_lt(x_3, x_2);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_6);
lean_dec(x_5);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_4);
lean_ctor_set(x_16, 1, x_7);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_4);
x_17 = lean_array_uget(x_1, x_3);
x_18 = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd), 8, 1);
lean_closure_set(x_18, 0, x_17);
x_19 = l_Lean_Elab_Command_liftTermElabM___redArg(x_18, x_5, x_6, x_7);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_box(0);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_array_get_size(x_20);
x_25 = lean_nat_dec_lt(x_23, x_24);
if (x_25 == 0)
{
lean_dec(x_24);
lean_dec(x_20);
x_8 = x_22;
x_9 = x_21;
goto block_14;
}
else
{
uint8_t x_26; 
x_26 = lean_nat_dec_le(x_24, x_24);
if (x_26 == 0)
{
lean_dec(x_24);
lean_dec(x_20);
x_8 = x_22;
x_9 = x_21;
goto block_14;
}
else
{
size_t x_27; size_t x_28; lean_object* x_29; 
x_27 = lean_usize_of_nat(x_23);
x_28 = lean_usize_of_nat(x_24);
lean_dec(x_24);
lean_inc(x_6);
lean_inc(x_5);
x_29 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_Command_elabCommand_go_spec__14(x_20, x_27, x_28, x_22, x_5, x_6, x_21);
lean_dec(x_20);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_8 = x_22;
x_9 = x_30;
goto block_14;
}
else
{
lean_dec(x_6);
lean_dec(x_5);
return x_29;
}
}
}
}
else
{
uint8_t x_31; 
lean_dec(x_6);
lean_dec(x_5);
x_31 = !lean_is_exclusive(x_19);
if (x_31 == 0)
{
return x_19;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_19, 0);
x_33 = lean_ctor_get(x_19, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_19);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
block_14:
{
lean_object* x_10; size_t x_11; size_t x_12; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_usize_of_nat(x_10);
x_12 = lean_usize_add(x_3, x_11);
x_3 = x_12;
x_4 = x_8;
x_7 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_2, x_3);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_8 = lean_box(1);
x_17 = lean_array_uget(x_1, x_2);
x_18 = l_Lean_isInductive___at___Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__0___redArg(x_17, x_5, x_6);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_unbox(x_19);
lean_dec(x_19);
if (x_20 == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_18);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_18, 0);
lean_dec(x_22);
lean_ctor_set(x_18, 0, x_8);
return x_18;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_18, 1);
lean_inc(x_23);
lean_dec(x_18);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_8);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_18, 1);
lean_inc(x_25);
lean_dec(x_18);
x_9 = x_7;
x_10 = x_25;
goto block_16;
}
block_16:
{
if (x_9 == 0)
{
lean_object* x_11; size_t x_12; size_t x_13; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_usize_of_nat(x_11);
x_13 = lean_usize_add(x_2, x_12);
x_2 = x_13;
x_6 = x_10;
goto _start;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_10);
return x_15;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_6);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkReprInstanceHandler(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_22; uint8_t x_23; 
x_5 = lean_unsigned_to_nat(0u);
x_22 = lean_array_get_size(x_1);
x_23 = lean_nat_dec_lt(x_5, x_22);
if (x_23 == 0)
{
lean_dec(x_22);
x_6 = x_4;
goto block_21;
}
else
{
if (x_23 == 0)
{
lean_dec(x_22);
x_6 = x_4;
goto block_21;
}
else
{
size_t x_24; size_t x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_24 = lean_usize_of_nat(x_5);
x_25 = lean_usize_of_nat(x_22);
lean_dec(x_22);
x_26 = l_Array_anyMUnsafe_any___at___Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__2(x_1, x_24, x_25, x_2, x_3, x_4);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_unbox(x_27);
lean_dec(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_6 = x_29;
goto block_21;
}
else
{
uint8_t x_30; 
lean_dec(x_3);
lean_dec(x_2);
x_30 = !lean_is_exclusive(x_26);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_26, 0);
lean_dec(x_31);
x_32 = lean_box(0);
lean_ctor_set(x_26, 0, x_32);
return x_26;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_26, 1);
lean_inc(x_33);
lean_dec(x_26);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
}
}
}
block_21:
{
lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; 
x_7 = lean_box(0);
x_8 = lean_array_size(x_1);
x_9 = lean_usize_of_nat(x_5);
x_10 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__1(x_1, x_8, x_9, x_7, x_2, x_3, x_6);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
lean_dec(x_12);
x_13 = lean_box(1);
lean_ctor_set(x_10, 0, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_box(1);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_10);
if (x_17 == 0)
{
return x_10;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_10, 0);
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_10);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_isInductive___at___Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_isInductive___at___Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__1(x_1, x_8, x_9, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Array_anyMUnsafe_any___at___Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__2(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkReprInstanceHandler___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Deriving_Repr_mkReprInstanceHandler(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_initFn____x40_Lean_Elab_Deriving_Repr___hyg_3567_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_mk_string_unchecked("Repr", 4, 4);
lean_inc(x_2);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_alloc_closure((void*)(l_Lean_Elab_Deriving_Repr_mkReprInstanceHandler___boxed), 4, 0);
x_5 = l_Lean_Elab_registerDerivingHandler(x_3, x_4, x_1);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_mk_string_unchecked("Elab", 4, 4);
x_8 = lean_mk_string_unchecked("Deriving", 8, 8);
x_9 = lean_mk_string_unchecked("repr", 4, 4);
lean_inc(x_8);
lean_inc(x_7);
x_10 = l_Lean_Name_mkStr3(x_7, x_8, x_9);
x_11 = lean_box(0);
x_12 = lean_box(0);
x_13 = lean_mk_string_unchecked("Lean", 4, 4);
lean_inc(x_13);
x_14 = l_Lean_Name_str___override(x_12, x_13);
lean_inc(x_7);
x_15 = l_Lean_Name_str___override(x_14, x_7);
lean_inc(x_8);
x_16 = l_Lean_Name_str___override(x_15, x_8);
lean_inc(x_2);
x_17 = l_Lean_Name_str___override(x_16, x_2);
x_18 = lean_mk_string_unchecked("initFn", 6, 6);
x_19 = l_Lean_Name_str___override(x_17, x_18);
x_20 = lean_mk_string_unchecked("_@", 2, 2);
x_21 = l_Lean_Name_str___override(x_19, x_20);
x_22 = l_Lean_Name_str___override(x_21, x_13);
x_23 = l_Lean_Name_str___override(x_22, x_7);
x_24 = l_Lean_Name_str___override(x_23, x_8);
x_25 = l_Lean_Name_str___override(x_24, x_2);
x_26 = lean_mk_string_unchecked("_hyg", 4, 4);
x_27 = l_Lean_Name_str___override(x_25, x_26);
x_28 = lean_unsigned_to_nat(3567u);
x_29 = l_Lean_Name_num___override(x_27, x_28);
x_30 = lean_unbox(x_11);
x_31 = l_Lean_registerTraceClass(x_10, x_30, x_29, x_6);
return x_31;
}
else
{
lean_dec(x_2);
return x_5;
}
}
}
lean_object* initialize_Lean_Meta_Transform(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Inductive(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Deriving_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Deriving_Util(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Deriving_Repr(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Transform(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Inductive(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Deriving_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Deriving_Util(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
if (builtin) {res = l_Lean_Elab_Deriving_Repr_initFn____x40_Lean_Elab_Deriving_Repr___hyg_3567_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
