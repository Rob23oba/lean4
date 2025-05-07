// Lean compiler output
// Module: Lean.Compiler.LCNF.ToMono
// Imports: Lean.Compiler.LCNF.MonoTypes Lean.Compiler.LCNF.InferType
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_argToMono___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ctorAppToMono_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_toMono___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_toMono___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_FunDeclCore_toMono_spec__0___redArg(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_argToMono___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_toMono(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ctorAppToMono_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_toMono___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloatArrayToMono___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_instInhabitedCode;
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_decToMono___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_decToMono_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ctorAppToMono_spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Arg_toLetValue(lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDeclCore_toMono(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesUIntToMono___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedAltCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesNatToMono(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___Lean_Compiler_LCNF_Decl_toMono_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesByteArrayToMono___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesUIntToMono___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___at___Lean_Compiler_LCNF_Code_instantiateValueLevelParams_instCode_spec__0(lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_toMono(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_argToMono(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
lean_object* l_ReaderT_instMonad(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_saveMono___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isTrivialConstructorApp_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Code_toMono_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseParams___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_toMono___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesStringToMono___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Expr_0__Lean_beqFVarId____x40_Lean_Expr___hyg_1672_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesStringToMono___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_toMono_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toMono___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ToMono___hyg_4097_(lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloatArrayToMono(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_casesIntToMono_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesStringToMono(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_toMono(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesUIntToMono(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Array_ofSubarray___redArg(lean_object*);
uint8_t l_Lean_Compiler_LCNF_isTypeFormerType(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesArrayToMono___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_addLetDecl(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_findCore___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___redArg(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ctorAppToMono___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_trivialStructToMono___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ctorAppToMono_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_casesNatToMono_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_casesNatToMono_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesStringToMono___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesByteArrayToMono(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toMono;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_FunDeclCore_toMono_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_toMono(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_toMono(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ctorAppToMono_spec__1___redArg(size_t, size_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarIdSet_insert(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isTrivialConstructorApp_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Code_toMono_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ctorAppToMono_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_toMonoType(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isTrivialConstructorApp_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_toMono_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_toMono_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Compiler_LCNF_trivialStructToMono_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_instInhabitedParam;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_trivialStructToMono(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_decToMono(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_hasTrivialStructure_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_seqRight(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ctorAppToMono_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesIntToMono(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
extern lean_object* l_Lean_Compiler_LCNF_anyExpr;
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltImp(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_argToMono___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesArrayToMono___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesUIntToMono___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesNatToMono___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesArrayToMono___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isTrivialConstructorApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_casesIntToMono_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_toMono___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_FunDeclCore_toMono_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesArrayToMono(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_FunDeclCore_toMono_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_decToMono_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_toMono_go___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ctorAppToMono_spec__0___redArg(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ctorAppToMono(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesIntToMono___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_toMono___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_1, 2);
lean_inc(x_21);
x_22 = l_Lean_Compiler_LCNF_isTypeFormerType(x_21);
if (x_22 == 0)
{
x_7 = x_3;
x_8 = x_4;
x_9 = x_5;
x_10 = x_6;
goto block_20;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_23 = lean_st_ref_take(x_2, x_6);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_ctor_get(x_1, 0);
lean_inc(x_26);
x_27 = l_Lean_FVarIdSet_insert(x_24, x_26);
x_28 = lean_st_ref_set(x_2, x_27, x_25);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_7 = x_3;
x_8 = x_4;
x_9 = x_5;
x_10 = x_29;
goto block_20;
}
block_20:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_1, 2);
lean_inc(x_11);
x_12 = l_Lean_Compiler_LCNF_toMonoType(x_11, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(x_1, x_13, x_7, x_14);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_12);
if (x_16 == 0)
{
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_12, 0);
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_12);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_toMono(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_Param_toMono___redArg(x_1, x_2, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_toMono___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_Param_toMono___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_toMono___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_Param_toMono(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isTrivialConstructorApp_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_6 = lean_st_ref_get(x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_9 = x_6;
} else {
 lean_dec_ref(x_6);
 x_9 = lean_box(0);
}
x_13 = lean_ctor_get(x_7, 0);
lean_inc(x_13);
lean_dec(x_7);
x_14 = lean_box(0);
x_15 = lean_unbox(x_14);
x_16 = l_Lean_Environment_find_x3f(x_13, x_1, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_dec(x_4);
lean_dec(x_3);
goto block_12;
}
else
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
if (lean_obj_tag(x_17) == 6)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_9);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
x_20 = l_Lean_Compiler_LCNF_hasTrivialStructure_x3f(x_19, x_3, x_4, x_8);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
lean_dec(x_18);
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 0);
lean_dec(x_23);
x_24 = lean_box(0);
lean_ctor_set(x_20, 0, x_24);
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_dec(x_20);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_20);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_20, 0);
lean_dec(x_29);
x_30 = !lean_is_exclusive(x_21);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_31 = lean_ctor_get(x_21, 0);
x_32 = lean_box(0);
x_33 = lean_ctor_get(x_18, 3);
lean_inc(x_33);
lean_dec(x_18);
x_34 = lean_ctor_get(x_31, 2);
lean_inc(x_34);
lean_dec(x_31);
x_35 = lean_nat_add(x_33, x_34);
lean_dec(x_34);
lean_dec(x_33);
x_36 = lean_array_get(x_32, x_2, x_35);
lean_dec(x_35);
x_37 = l_Lean_Compiler_LCNF_Arg_toLetValue(x_36);
lean_dec(x_36);
lean_ctor_set(x_21, 0, x_37);
return x_20;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_38 = lean_ctor_get(x_21, 0);
lean_inc(x_38);
lean_dec(x_21);
x_39 = lean_box(0);
x_40 = lean_ctor_get(x_18, 3);
lean_inc(x_40);
lean_dec(x_18);
x_41 = lean_ctor_get(x_38, 2);
lean_inc(x_41);
lean_dec(x_38);
x_42 = lean_nat_add(x_40, x_41);
lean_dec(x_41);
lean_dec(x_40);
x_43 = lean_array_get(x_39, x_2, x_42);
lean_dec(x_42);
x_44 = l_Lean_Compiler_LCNF_Arg_toLetValue(x_43);
lean_dec(x_43);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_20, 0, x_45);
return x_20;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_46 = lean_ctor_get(x_20, 1);
lean_inc(x_46);
lean_dec(x_20);
x_47 = lean_ctor_get(x_21, 0);
lean_inc(x_47);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 x_48 = x_21;
} else {
 lean_dec_ref(x_21);
 x_48 = lean_box(0);
}
x_49 = lean_box(0);
x_50 = lean_ctor_get(x_18, 3);
lean_inc(x_50);
lean_dec(x_18);
x_51 = lean_ctor_get(x_47, 2);
lean_inc(x_51);
lean_dec(x_47);
x_52 = lean_nat_add(x_50, x_51);
lean_dec(x_51);
lean_dec(x_50);
x_53 = lean_array_get(x_49, x_2, x_52);
lean_dec(x_52);
x_54 = l_Lean_Compiler_LCNF_Arg_toLetValue(x_53);
lean_dec(x_53);
if (lean_is_scalar(x_48)) {
 x_55 = lean_alloc_ctor(1, 1, 0);
} else {
 x_55 = x_48;
}
lean_ctor_set(x_55, 0, x_54);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_46);
return x_56;
}
}
}
else
{
uint8_t x_57; 
lean_dec(x_18);
x_57 = !lean_is_exclusive(x_20);
if (x_57 == 0)
{
return x_20;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_20, 0);
x_59 = lean_ctor_get(x_20, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_20);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
else
{
lean_dec(x_17);
lean_dec(x_4);
lean_dec(x_3);
goto block_12;
}
}
block_12:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
if (lean_is_scalar(x_9)) {
 x_11 = lean_alloc_ctor(0, 2, 0);
} else {
 x_11 = x_9;
}
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isTrivialConstructorApp_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_isTrivialConstructorApp_x3f___redArg(x_1, x_2, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isTrivialConstructorApp_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_LCNF_isTrivialConstructorApp_x3f___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isTrivialConstructorApp_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_isTrivialConstructorApp_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_argToMono___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
case 1:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_st_ref_get(x_2, x_3);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = l_Lean_RBNode_findCore___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___redArg(x_8, x_5);
lean_dec(x_5);
lean_dec(x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_ctor_set(x_6, 0, x_1);
return x_6;
}
else
{
lean_object* x_10; 
lean_dec(x_9);
lean_dec(x_1);
x_10 = lean_box(0);
lean_ctor_set(x_6, 0, x_10);
return x_6;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_6, 0);
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_6);
x_13 = l_Lean_RBNode_findCore___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___redArg(x_11, x_5);
lean_dec(x_5);
lean_dec(x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_13);
lean_dec(x_1);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_12);
return x_16;
}
}
}
default: 
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_1);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_3);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_argToMono(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_argToMono___redArg(x_1, x_2, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_argToMono___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Compiler_LCNF_argToMono___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_argToMono___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_argToMono(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ctorAppToMono_spec__0___redArg(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_2, x_1);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_5);
lean_dec(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_array_uget(x_3, x_2);
x_10 = lean_box(0);
x_11 = lean_array_uset(x_3, x_2, x_10);
switch (lean_obj_tag(x_9)) {
case 0:
{
x_12 = x_9;
x_13 = x_6;
goto block_19;
}
case 1:
{
lean_object* x_20; 
lean_dec(x_9);
x_20 = lean_box(0);
x_12 = x_20;
x_13 = x_6;
goto block_19;
}
default: 
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_9);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_9, 0);
lean_inc(x_5);
lean_inc(x_4);
x_23 = l_Lean_Compiler_LCNF_toMonoType(x_22, x_4, x_5, x_6);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_ctor_set(x_9, 0, x_24);
x_12 = x_9;
x_13 = x_25;
goto block_19;
}
else
{
uint8_t x_26; 
lean_free_object(x_9);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
x_26 = !lean_is_exclusive(x_23);
if (x_26 == 0)
{
return x_23;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_23, 0);
x_28 = lean_ctor_get(x_23, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_23);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_9, 0);
lean_inc(x_30);
lean_dec(x_9);
lean_inc(x_5);
lean_inc(x_4);
x_31 = l_Lean_Compiler_LCNF_toMonoType(x_30, x_4, x_5, x_6);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_34, 0, x_32);
x_12 = x_34;
x_13 = x_33;
goto block_19;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
x_35 = lean_ctor_get(x_31, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_31, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_37 = x_31;
} else {
 lean_dec_ref(x_31);
 x_37 = lean_box(0);
}
if (lean_is_scalar(x_37)) {
 x_38 = lean_alloc_ctor(1, 2, 0);
} else {
 x_38 = x_37;
}
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
}
}
block_19:
{
lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_usize_of_nat(x_14);
x_16 = lean_usize_add(x_2, x_15);
x_17 = lean_array_uset(x_11, x_2, x_12);
x_2 = x_16;
x_3 = x_17;
x_6 = x_13;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ctorAppToMono_spec__0(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ctorAppToMono_spec__0___redArg(x_1, x_2, x_3, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ctorAppToMono_spec__1___redArg(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_2, x_1);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_8 = lean_array_uget(x_3, x_2);
x_9 = l_Lean_Compiler_LCNF_argToMono___redArg(x_8, x_4, x_5);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_box(0);
x_13 = lean_array_uset(x_3, x_2, x_12);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_usize_of_nat(x_14);
x_16 = lean_usize_add(x_2, x_15);
x_17 = lean_array_uset(x_13, x_2, x_10);
x_2 = x_16;
x_3 = x_17;
x_5 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ctorAppToMono_spec__1(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ctorAppToMono_spec__1___redArg(x_1, x_2, x_3, x_4, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ctorAppToMono(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_ctor_get(x_1, 3);
lean_inc(x_10);
lean_inc(x_10);
lean_inc(x_2);
x_11 = l_Array_toSubarray___redArg(x_2, x_9, x_10);
x_12 = l_Array_ofSubarray___redArg(x_11);
lean_dec(x_11);
x_13 = lean_array_size(x_12);
x_14 = lean_usize_of_nat(x_9);
x_15 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ctorAppToMono_spec__0___redArg(x_13, x_14, x_12, x_6, x_7, x_8);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; lean_object* x_22; uint8_t x_23; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_array_get_size(x_2);
x_19 = l_Array_toSubarray___redArg(x_2, x_10, x_18);
x_20 = l_Array_ofSubarray___redArg(x_19);
lean_dec(x_19);
x_21 = lean_array_size(x_20);
x_22 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ctorAppToMono_spec__1___redArg(x_21, x_14, x_20, x_3, x_17);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = l_Array_append(lean_box(0), x_16, x_24);
lean_dec(x_24);
x_26 = lean_ctor_get(x_1, 0);
lean_inc(x_26);
lean_dec(x_1);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set(x_29, 2, x_25);
lean_ctor_set(x_22, 0, x_29);
return x_22;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_30 = lean_ctor_get(x_22, 0);
x_31 = lean_ctor_get(x_22, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_22);
x_32 = l_Array_append(lean_box(0), x_16, x_30);
lean_dec(x_30);
x_33 = lean_ctor_get(x_1, 0);
lean_inc(x_33);
lean_dec(x_1);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec(x_33);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
lean_ctor_set(x_36, 2, x_32);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_31);
return x_37;
}
}
else
{
uint8_t x_38; 
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_15);
if (x_38 == 0)
{
return x_15;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_15, 0);
x_40 = lean_ctor_get(x_15, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_15);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ctorAppToMono_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ctorAppToMono_spec__0___redArg(x_7, x_8, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ctorAppToMono_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ctorAppToMono_spec__0(x_10, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ctorAppToMono_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ctorAppToMono_spec__1___redArg(x_6, x_7, x_3, x_4, x_5);
lean_dec(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ctorAppToMono_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ctorAppToMono_spec__1(x_10, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ctorAppToMono___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_ctorAppToMono(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_toMono(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 2);
lean_inc(x_10);
x_11 = lean_st_ref_get(x_2, x_7);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = l_Lean_RBNode_findCore___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___redArg(x_13, x_10);
lean_dec(x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
lean_free_object(x_11);
x_16 = l_Lean_Compiler_LCNF_hasTrivialStructure_x3f(x_8, x_5, x_6, x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
lean_dec(x_10);
lean_dec(x_9);
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_16, 0);
lean_dec(x_19);
lean_ctor_set(x_16, 0, x_1);
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_dec(x_16);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_1);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
uint8_t x_22; 
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_16);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_ctor_get(x_16, 0);
lean_dec(x_23);
x_24 = lean_ctor_get(x_17, 0);
lean_inc(x_24);
lean_dec(x_17);
x_25 = lean_ctor_get(x_24, 2);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_nat_dec_eq(x_25, x_9);
lean_dec(x_9);
lean_dec(x_25);
if (x_26 == 0)
{
lean_object* x_27; 
lean_dec(x_10);
x_27 = lean_box(1);
lean_ctor_set(x_16, 0, x_27);
return x_16;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_unsigned_to_nat(0u);
x_29 = lean_mk_empty_array_with_capacity(x_28);
x_30 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_30, 0, x_10);
lean_ctor_set(x_30, 1, x_29);
lean_ctor_set(x_16, 0, x_30);
return x_16;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = lean_ctor_get(x_16, 1);
lean_inc(x_31);
lean_dec(x_16);
x_32 = lean_ctor_get(x_17, 0);
lean_inc(x_32);
lean_dec(x_17);
x_33 = lean_ctor_get(x_32, 2);
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_nat_dec_eq(x_33, x_9);
lean_dec(x_9);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_10);
x_35 = lean_box(1);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_31);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_unsigned_to_nat(0u);
x_38 = lean_mk_empty_array_with_capacity(x_37);
x_39 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_39, 0, x_10);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_31);
return x_40;
}
}
}
}
else
{
uint8_t x_41; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_41 = !lean_is_exclusive(x_16);
if (x_41 == 0)
{
return x_16;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_16, 0);
x_43 = lean_ctor_get(x_16, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_16);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
lean_object* x_45; 
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_45 = lean_box(1);
lean_ctor_set(x_11, 0, x_45);
return x_11;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_11, 0);
x_47 = lean_ctor_get(x_11, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_11);
x_48 = l_Lean_RBNode_findCore___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___redArg(x_46, x_10);
lean_dec(x_46);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; 
x_49 = l_Lean_Compiler_LCNF_hasTrivialStructure_x3f(x_8, x_5, x_6, x_47);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_10);
lean_dec(x_9);
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
if (lean_is_scalar(x_52)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_52;
}
lean_ctor_set(x_53, 0, x_1);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
lean_dec(x_1);
x_54 = lean_ctor_get(x_49, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_55 = x_49;
} else {
 lean_dec_ref(x_49);
 x_55 = lean_box(0);
}
x_56 = lean_ctor_get(x_50, 0);
lean_inc(x_56);
lean_dec(x_50);
x_57 = lean_ctor_get(x_56, 2);
lean_inc(x_57);
lean_dec(x_56);
x_58 = lean_nat_dec_eq(x_57, x_9);
lean_dec(x_9);
lean_dec(x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; 
lean_dec(x_10);
x_59 = lean_box(1);
if (lean_is_scalar(x_55)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_55;
}
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_54);
return x_60;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_61 = lean_unsigned_to_nat(0u);
x_62 = lean_mk_empty_array_with_capacity(x_61);
x_63 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_63, 0, x_10);
lean_ctor_set(x_63, 1, x_62);
if (lean_is_scalar(x_55)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_55;
}
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_54);
return x_64;
}
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_65 = lean_ctor_get(x_49, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_49, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_67 = x_49;
} else {
 lean_dec_ref(x_49);
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
else
{
lean_object* x_69; lean_object* x_70; 
lean_dec(x_48);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_69 = lean_box(1);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_47);
return x_70;
}
}
}
case 3:
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_71 = lean_ctor_get(x_1, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_1, 2);
lean_inc(x_72);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 x_73 = x_1;
} else {
 lean_dec_ref(x_1);
 x_73 = lean_box(0);
}
x_74 = lean_mk_string_unchecked("Decidable", 9, 9);
x_75 = lean_mk_string_unchecked("isTrue", 6, 6);
lean_inc(x_74);
x_76 = l_Lean_Name_mkStr2(x_74, x_75);
x_77 = lean_name_eq(x_71, x_76);
lean_dec(x_76);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_78 = lean_mk_string_unchecked("isFalse", 7, 7);
lean_inc(x_74);
x_79 = l_Lean_Name_mkStr2(x_74, x_78);
x_80 = lean_name_eq(x_71, x_79);
lean_dec(x_79);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_81 = lean_mk_string_unchecked("decide", 6, 6);
x_82 = l_Lean_Name_mkStr2(x_74, x_81);
x_83 = lean_name_eq(x_71, x_82);
lean_dec(x_82);
if (x_83 == 0)
{
lean_object* x_84; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_71);
x_84 = l_Lean_Compiler_LCNF_isTrivialConstructorApp_x3f___redArg(x_71, x_72, x_5, x_6, x_7);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_105; lean_object* x_106; 
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = lean_st_ref_get(x_6, x_86);
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
x_105 = lean_ctor_get(x_88, 0);
lean_inc(x_105);
lean_dec(x_88);
lean_inc(x_71);
x_106 = l_Lean_Environment_find_x3f(x_105, x_71, x_83);
if (lean_obj_tag(x_106) == 0)
{
lean_dec(x_6);
lean_dec(x_5);
x_90 = x_2;
goto block_104;
}
else
{
lean_object* x_107; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
lean_dec(x_106);
if (lean_obj_tag(x_107) == 6)
{
lean_object* x_108; lean_object* x_109; 
lean_dec(x_73);
lean_dec(x_71);
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
lean_dec(x_107);
x_109 = l_Lean_Compiler_LCNF_ctorAppToMono(x_108, x_72, x_2, x_3, x_4, x_5, x_6, x_89);
return x_109;
}
else
{
lean_dec(x_107);
lean_dec(x_6);
lean_dec(x_5);
x_90 = x_2;
goto block_104;
}
}
block_104:
{
size_t x_91; lean_object* x_92; size_t x_93; lean_object* x_94; uint8_t x_95; 
x_91 = lean_array_size(x_72);
x_92 = lean_unsigned_to_nat(0u);
x_93 = lean_usize_of_nat(x_92);
x_94 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ctorAppToMono_spec__1___redArg(x_91, x_93, x_72, x_90, x_89);
x_95 = !lean_is_exclusive(x_94);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_94, 0);
x_97 = lean_box(0);
if (lean_is_scalar(x_73)) {
 x_98 = lean_alloc_ctor(3, 3, 0);
} else {
 x_98 = x_73;
}
lean_ctor_set(x_98, 0, x_71);
lean_ctor_set(x_98, 1, x_97);
lean_ctor_set(x_98, 2, x_96);
lean_ctor_set(x_94, 0, x_98);
return x_94;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_99 = lean_ctor_get(x_94, 0);
x_100 = lean_ctor_get(x_94, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_94);
x_101 = lean_box(0);
if (lean_is_scalar(x_73)) {
 x_102 = lean_alloc_ctor(3, 3, 0);
} else {
 x_102 = x_73;
}
lean_ctor_set(x_102, 0, x_71);
lean_ctor_set(x_102, 1, x_101);
lean_ctor_set(x_102, 2, x_99);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_100);
return x_103;
}
}
}
else
{
lean_object* x_110; lean_object* x_111; 
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_71);
x_110 = lean_ctor_get(x_84, 1);
lean_inc(x_110);
lean_dec(x_84);
x_111 = lean_ctor_get(x_85, 0);
lean_inc(x_111);
lean_dec(x_85);
x_1 = x_111;
x_7 = x_110;
goto _start;
}
}
else
{
uint8_t x_113; 
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_6);
lean_dec(x_5);
x_113 = !lean_is_exclusive(x_84);
if (x_113 == 0)
{
return x_84;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_84, 0);
x_115 = lean_ctor_get(x_84, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_84);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_6);
lean_dec(x_5);
x_117 = lean_box(0);
x_118 = lean_unsigned_to_nat(1u);
x_119 = lean_array_get(x_117, x_72, x_118);
lean_dec(x_72);
x_120 = l_Lean_Compiler_LCNF_Arg_toLetValue(x_119);
lean_dec(x_119);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_7);
return x_121;
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_dec(x_74);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_6);
lean_dec(x_5);
x_122 = lean_mk_string_unchecked("Bool", 4, 4);
x_123 = lean_mk_string_unchecked("false", 5, 5);
x_124 = l_Lean_Name_mkStr2(x_122, x_123);
x_125 = lean_box(0);
x_126 = lean_unsigned_to_nat(0u);
x_127 = lean_mk_empty_array_with_capacity(x_126);
if (lean_is_scalar(x_73)) {
 x_128 = lean_alloc_ctor(3, 3, 0);
} else {
 x_128 = x_73;
}
lean_ctor_set(x_128, 0, x_124);
lean_ctor_set(x_128, 1, x_125);
lean_ctor_set(x_128, 2, x_127);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_7);
return x_129;
}
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
lean_dec(x_74);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_6);
lean_dec(x_5);
x_130 = lean_mk_string_unchecked("Bool", 4, 4);
x_131 = lean_mk_string_unchecked("true", 4, 4);
x_132 = l_Lean_Name_mkStr2(x_130, x_131);
x_133 = lean_box(0);
x_134 = lean_unsigned_to_nat(0u);
x_135 = lean_mk_empty_array_with_capacity(x_134);
if (lean_is_scalar(x_73)) {
 x_136 = lean_alloc_ctor(3, 3, 0);
} else {
 x_136 = x_73;
}
lean_ctor_set(x_136, 0, x_132);
lean_ctor_set(x_136, 1, x_133);
lean_ctor_set(x_136, 2, x_135);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_7);
return x_137;
}
}
case 4:
{
uint8_t x_138; 
lean_dec(x_6);
lean_dec(x_5);
x_138 = !lean_is_exclusive(x_1);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; uint8_t x_142; 
x_139 = lean_ctor_get(x_1, 0);
x_140 = lean_ctor_get(x_1, 1);
x_141 = lean_st_ref_get(x_2, x_7);
x_142 = !lean_is_exclusive(x_141);
if (x_142 == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_143 = lean_ctor_get(x_141, 0);
x_144 = lean_ctor_get(x_141, 1);
x_145 = l_Lean_RBNode_findCore___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___redArg(x_143, x_139);
lean_dec(x_143);
if (lean_obj_tag(x_145) == 0)
{
size_t x_146; lean_object* x_147; size_t x_148; lean_object* x_149; uint8_t x_150; 
lean_free_object(x_141);
x_146 = lean_array_size(x_140);
x_147 = lean_unsigned_to_nat(0u);
x_148 = lean_usize_of_nat(x_147);
x_149 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ctorAppToMono_spec__1___redArg(x_146, x_148, x_140, x_2, x_144);
x_150 = !lean_is_exclusive(x_149);
if (x_150 == 0)
{
lean_object* x_151; 
x_151 = lean_ctor_get(x_149, 0);
lean_ctor_set(x_1, 1, x_151);
lean_ctor_set(x_149, 0, x_1);
return x_149;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_152 = lean_ctor_get(x_149, 0);
x_153 = lean_ctor_get(x_149, 1);
lean_inc(x_153);
lean_inc(x_152);
lean_dec(x_149);
lean_ctor_set(x_1, 1, x_152);
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_1);
lean_ctor_set(x_154, 1, x_153);
return x_154;
}
}
else
{
lean_object* x_155; 
lean_dec(x_145);
lean_free_object(x_1);
lean_dec(x_140);
lean_dec(x_139);
x_155 = lean_box(1);
lean_ctor_set(x_141, 0, x_155);
return x_141;
}
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_156 = lean_ctor_get(x_141, 0);
x_157 = lean_ctor_get(x_141, 1);
lean_inc(x_157);
lean_inc(x_156);
lean_dec(x_141);
x_158 = l_Lean_RBNode_findCore___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___redArg(x_156, x_139);
lean_dec(x_156);
if (lean_obj_tag(x_158) == 0)
{
size_t x_159; lean_object* x_160; size_t x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_159 = lean_array_size(x_140);
x_160 = lean_unsigned_to_nat(0u);
x_161 = lean_usize_of_nat(x_160);
x_162 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ctorAppToMono_spec__1___redArg(x_159, x_161, x_140, x_2, x_157);
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_162, 1);
lean_inc(x_164);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 lean_ctor_release(x_162, 1);
 x_165 = x_162;
} else {
 lean_dec_ref(x_162);
 x_165 = lean_box(0);
}
lean_ctor_set(x_1, 1, x_163);
if (lean_is_scalar(x_165)) {
 x_166 = lean_alloc_ctor(0, 2, 0);
} else {
 x_166 = x_165;
}
lean_ctor_set(x_166, 0, x_1);
lean_ctor_set(x_166, 1, x_164);
return x_166;
}
else
{
lean_object* x_167; lean_object* x_168; 
lean_dec(x_158);
lean_free_object(x_1);
lean_dec(x_140);
lean_dec(x_139);
x_167 = lean_box(1);
x_168 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_168, 0, x_167);
lean_ctor_set(x_168, 1, x_157);
return x_168;
}
}
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_169 = lean_ctor_get(x_1, 0);
x_170 = lean_ctor_get(x_1, 1);
lean_inc(x_170);
lean_inc(x_169);
lean_dec(x_1);
x_171 = lean_st_ref_get(x_2, x_7);
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_171, 1);
lean_inc(x_173);
if (lean_is_exclusive(x_171)) {
 lean_ctor_release(x_171, 0);
 lean_ctor_release(x_171, 1);
 x_174 = x_171;
} else {
 lean_dec_ref(x_171);
 x_174 = lean_box(0);
}
x_175 = l_Lean_RBNode_findCore___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___redArg(x_172, x_169);
lean_dec(x_172);
if (lean_obj_tag(x_175) == 0)
{
size_t x_176; lean_object* x_177; size_t x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
lean_dec(x_174);
x_176 = lean_array_size(x_170);
x_177 = lean_unsigned_to_nat(0u);
x_178 = lean_usize_of_nat(x_177);
x_179 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ctorAppToMono_spec__1___redArg(x_176, x_178, x_170, x_2, x_173);
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
x_183 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_183, 0, x_169);
lean_ctor_set(x_183, 1, x_180);
if (lean_is_scalar(x_182)) {
 x_184 = lean_alloc_ctor(0, 2, 0);
} else {
 x_184 = x_182;
}
lean_ctor_set(x_184, 0, x_183);
lean_ctor_set(x_184, 1, x_181);
return x_184;
}
else
{
lean_object* x_185; lean_object* x_186; 
lean_dec(x_175);
lean_dec(x_170);
lean_dec(x_169);
x_185 = lean_box(1);
if (lean_is_scalar(x_174)) {
 x_186 = lean_alloc_ctor(0, 2, 0);
} else {
 x_186 = x_174;
}
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set(x_186, 1, x_173);
return x_186;
}
}
}
default: 
{
lean_object* x_187; 
lean_dec(x_6);
lean_dec(x_5);
x_187 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_187, 0, x_1);
lean_ctor_set(x_187, 1, x_7);
return x_187;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_toMono___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_LetValue_toMono(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_toMono(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
x_9 = l_Lean_Compiler_LCNF_toMonoType(x_8, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_1, 3);
lean_inc(x_12);
x_13 = l_Lean_Compiler_LCNF_LetValue_toMono(x_12, x_2, x_3, x_4, x_5, x_6, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(x_1, x_10, x_14, x_4, x_15);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_10);
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_13);
if (x_17 == 0)
{
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 0);
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_13);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
else
{
uint8_t x_21; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_9);
if (x_21 == 0)
{
return x_9;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_9, 0);
x_23 = lean_ctor_get(x_9, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_9);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_toMono___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_LetDecl_toMono(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_FunDeclCore_toMono_spec__0___redArg(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_2, x_1);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_6);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_array_uget(x_3, x_2);
lean_inc(x_7);
lean_inc(x_6);
x_12 = l_Lean_Compiler_LCNF_Param_toMono___redArg(x_11, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_box(0);
x_16 = lean_array_uset(x_3, x_2, x_15);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_usize_of_nat(x_17);
x_19 = lean_usize_add(x_2, x_18);
x_20 = lean_array_uset(x_16, x_2, x_13);
x_2 = x_19;
x_3 = x_20;
x_8 = x_14;
goto _start;
}
else
{
uint8_t x_22; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_22 = !lean_is_exclusive(x_12);
if (x_22 == 0)
{
return x_12;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_12, 0);
x_24 = lean_ctor_get(x_12, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_12);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_FunDeclCore_toMono_spec__0(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_FunDeclCore_toMono_spec__0___redArg(x_1, x_2, x_3, x_4, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDeclCore_toMono(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_1, 3);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
x_9 = l_Lean_Compiler_LCNF_toMonoType(x_8, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; lean_object* x_14; size_t x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_1, 2);
lean_inc(x_12);
x_13 = lean_array_size(x_12);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_usize_of_nat(x_14);
lean_inc(x_6);
lean_inc(x_5);
x_16 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_FunDeclCore_toMono_spec__0___redArg(x_13, x_15, x_12, x_2, x_4, x_5, x_6, x_11);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_1, 4);
lean_inc(x_19);
lean_inc(x_4);
x_20 = l_Lean_Compiler_LCNF_Code_toMono(x_19, x_2, x_3, x_4, x_5, x_6, x_18);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(x_1, x_10, x_17, x_21, x_4, x_22);
lean_dec(x_4);
return x_23;
}
else
{
uint8_t x_24; 
lean_dec(x_17);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_20);
if (x_24 == 0)
{
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_20, 0);
x_26 = lean_ctor_get(x_20, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_20);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
uint8_t x_28; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_16);
if (x_28 == 0)
{
return x_16;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_16, 0);
x_30 = lean_ctor_get(x_16, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_16);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
uint8_t x_32; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_9);
if (x_32 == 0)
{
return x_9;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_9, 0);
x_34 = lean_ctor_get(x_9, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_9);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Code_toMono_spec__0(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_2, x_1);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_array_uget(x_3, x_2);
x_13 = lean_box(0);
x_14 = lean_array_uset(x_3, x_2, x_13);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_23; lean_object* x_24; size_t x_25; lean_object* x_26; size_t x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_12, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_12, 2);
lean_inc(x_24);
x_25 = lean_array_size(x_23);
x_26 = lean_unsigned_to_nat(0u);
x_27 = lean_usize_of_nat(x_26);
lean_inc(x_8);
lean_inc(x_7);
x_28 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_FunDeclCore_toMono_spec__0___redArg(x_25, x_27, x_23, x_4, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_31 = l_Lean_Compiler_LCNF_Code_toMono(x_24, x_4, x_5, x_6, x_7, x_8, x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltImp(x_12, x_29, x_32);
x_15 = x_34;
x_16 = x_33;
goto block_22;
}
else
{
uint8_t x_35; 
lean_dec(x_29);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_35 = !lean_is_exclusive(x_31);
if (x_35 == 0)
{
return x_31;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_31, 0);
x_37 = lean_ctor_get(x_31, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_31);
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
lean_dec(x_24);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_39 = !lean_is_exclusive(x_28);
if (x_39 == 0)
{
return x_28;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_28, 0);
x_41 = lean_ctor_get(x_28, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_28);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_12, 0);
lean_inc(x_43);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_44 = l_Lean_Compiler_LCNF_Code_toMono(x_43, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_12, x_45);
x_15 = x_47;
x_16 = x_46;
goto block_22;
}
else
{
uint8_t x_48; 
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_48 = !lean_is_exclusive(x_44);
if (x_48 == 0)
{
return x_44;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_44, 0);
x_50 = lean_ctor_get(x_44, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_44);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
block_22:
{
lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_usize_of_nat(x_17);
x_19 = lean_usize_add(x_2, x_18);
x_20 = lean_array_uset(x_14, x_2, x_15);
x_2 = x_19;
x_3 = x_20;
x_9 = x_16;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_toMono(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_1, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_1, 1);
lean_inc(x_80);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_79);
x_81 = l_Lean_Compiler_LCNF_LetDecl_toMono(x_79, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
lean_inc(x_80);
x_84 = l_Lean_Compiler_LCNF_Code_toMono(x_80, x_2, x_3, x_4, x_5, x_6, x_83);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; size_t x_97; size_t x_98; uint8_t x_99; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_87 = x_84;
} else {
 lean_dec_ref(x_84);
 x_87 = lean_box(0);
}
x_97 = lean_ptr_addr(x_80);
lean_dec(x_80);
x_98 = lean_ptr_addr(x_85);
x_99 = lean_usize_dec_eq(x_97, x_98);
if (x_99 == 0)
{
lean_dec(x_79);
x_88 = x_99;
goto block_96;
}
else
{
size_t x_100; size_t x_101; uint8_t x_102; 
x_100 = lean_ptr_addr(x_79);
lean_dec(x_79);
x_101 = lean_ptr_addr(x_82);
x_102 = lean_usize_dec_eq(x_100, x_101);
x_88 = x_102;
goto block_96;
}
block_96:
{
if (x_88 == 0)
{
uint8_t x_89; 
x_89 = !lean_is_exclusive(x_1);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_1, 1);
lean_dec(x_90);
x_91 = lean_ctor_get(x_1, 0);
lean_dec(x_91);
lean_ctor_set(x_1, 1, x_85);
lean_ctor_set(x_1, 0, x_82);
if (lean_is_scalar(x_87)) {
 x_92 = lean_alloc_ctor(0, 2, 0);
} else {
 x_92 = x_87;
}
lean_ctor_set(x_92, 0, x_1);
lean_ctor_set(x_92, 1, x_86);
return x_92;
}
else
{
lean_object* x_93; lean_object* x_94; 
lean_dec(x_1);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_82);
lean_ctor_set(x_93, 1, x_85);
if (lean_is_scalar(x_87)) {
 x_94 = lean_alloc_ctor(0, 2, 0);
} else {
 x_94 = x_87;
}
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_86);
return x_94;
}
}
else
{
lean_object* x_95; 
lean_dec(x_85);
lean_dec(x_82);
if (lean_is_scalar(x_87)) {
 x_95 = lean_alloc_ctor(0, 2, 0);
} else {
 x_95 = x_87;
}
lean_ctor_set(x_95, 0, x_1);
lean_ctor_set(x_95, 1, x_86);
return x_95;
}
}
}
else
{
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_1);
return x_84;
}
}
else
{
uint8_t x_103; 
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_103 = !lean_is_exclusive(x_81);
if (x_103 == 0)
{
return x_81;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_81, 0);
x_105 = lean_ctor_get(x_81, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_81);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
return x_106;
}
}
}
case 1:
{
lean_object* x_107; lean_object* x_108; 
x_107 = lean_ctor_get(x_1, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_1, 1);
lean_inc(x_108);
x_24 = x_107;
x_25 = x_108;
x_26 = x_2;
x_27 = x_3;
x_28 = x_4;
x_29 = x_5;
x_30 = x_6;
x_31 = x_7;
goto block_78;
}
case 2:
{
lean_object* x_109; lean_object* x_110; 
x_109 = lean_ctor_get(x_1, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_1, 1);
lean_inc(x_110);
x_24 = x_109;
x_25 = x_110;
x_26 = x_2;
x_27 = x_3;
x_28 = x_4;
x_29 = x_5;
x_30 = x_6;
x_31 = x_7;
goto block_78;
}
case 4:
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; 
x_111 = lean_ctor_get(x_1, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_mk_string_unchecked("Decidable", 9, 9);
x_114 = l_Lean_Name_mkStr1(x_113);
x_115 = lean_name_eq(x_112, x_114);
lean_dec(x_114);
if (x_115 == 0)
{
lean_object* x_116; lean_object* x_117; uint8_t x_118; 
x_116 = lean_mk_string_unchecked("Nat", 3, 3);
x_117 = l_Lean_Name_mkStr1(x_116);
x_118 = lean_name_eq(x_112, x_117);
lean_dec(x_117);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; uint8_t x_121; 
x_119 = lean_mk_string_unchecked("Int", 3, 3);
x_120 = l_Lean_Name_mkStr1(x_119);
x_121 = lean_name_eq(x_112, x_120);
lean_dec(x_120);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; uint8_t x_124; 
x_122 = lean_mk_string_unchecked("UInt8", 5, 5);
x_123 = l_Lean_Name_mkStr1(x_122);
x_124 = lean_name_eq(x_112, x_123);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; uint8_t x_127; 
lean_dec(x_123);
x_125 = lean_mk_string_unchecked("UInt16", 6, 6);
x_126 = l_Lean_Name_mkStr1(x_125);
x_127 = lean_name_eq(x_112, x_126);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; uint8_t x_130; 
lean_dec(x_126);
x_128 = lean_mk_string_unchecked("UInt32", 6, 6);
x_129 = l_Lean_Name_mkStr1(x_128);
x_130 = lean_name_eq(x_112, x_129);
if (x_130 == 0)
{
lean_object* x_131; lean_object* x_132; uint8_t x_133; 
lean_dec(x_129);
x_131 = lean_mk_string_unchecked("UInt64", 6, 6);
x_132 = l_Lean_Name_mkStr1(x_131);
x_133 = lean_name_eq(x_112, x_132);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; uint8_t x_136; 
lean_dec(x_132);
x_134 = lean_mk_string_unchecked("Array", 5, 5);
x_135 = l_Lean_Name_mkStr1(x_134);
x_136 = lean_name_eq(x_112, x_135);
lean_dec(x_135);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; uint8_t x_139; 
x_137 = lean_mk_string_unchecked("ByteArray", 9, 9);
x_138 = l_Lean_Name_mkStr1(x_137);
x_139 = lean_name_eq(x_112, x_138);
lean_dec(x_138);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; uint8_t x_142; 
x_140 = lean_mk_string_unchecked("FloatArray", 10, 10);
x_141 = l_Lean_Name_mkStr1(x_140);
x_142 = lean_name_eq(x_112, x_141);
lean_dec(x_141);
if (x_142 == 0)
{
lean_object* x_143; lean_object* x_144; uint8_t x_145; 
x_143 = lean_mk_string_unchecked("String", 6, 6);
x_144 = l_Lean_Name_mkStr1(x_143);
x_145 = lean_name_eq(x_112, x_144);
lean_dec(x_144);
if (x_145 == 0)
{
lean_object* x_146; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_112);
x_146 = l_Lean_Compiler_LCNF_hasTrivialStructure_x3f(x_112, x_5, x_6, x_7);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; 
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
lean_dec(x_146);
x_149 = lean_ctor_get(x_111, 1);
lean_inc(x_149);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_149);
x_150 = l_Lean_Compiler_LCNF_toMonoType(x_149, x_5, x_6, x_148);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; size_t x_154; lean_object* x_155; size_t x_156; lean_object* x_157; 
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_150, 1);
lean_inc(x_152);
lean_dec(x_150);
x_153 = lean_ctor_get(x_111, 3);
lean_inc(x_153);
x_154 = lean_array_size(x_153);
x_155 = lean_unsigned_to_nat(0u);
x_156 = lean_usize_of_nat(x_155);
lean_inc(x_153);
x_157 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Code_toMono_spec__0(x_154, x_156, x_153, x_2, x_3, x_4, x_5, x_6, x_152);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; uint8_t x_172; size_t x_175; size_t x_176; uint8_t x_177; 
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_157, 1);
lean_inc(x_159);
if (lean_is_exclusive(x_157)) {
 lean_ctor_release(x_157, 0);
 lean_ctor_release(x_157, 1);
 x_160 = x_157;
} else {
 lean_dec_ref(x_157);
 x_160 = lean_box(0);
}
x_161 = lean_ctor_get(x_111, 2);
lean_inc(x_161);
lean_dec(x_111);
x_175 = lean_ptr_addr(x_153);
lean_dec(x_153);
x_176 = lean_ptr_addr(x_158);
x_177 = lean_usize_dec_eq(x_175, x_176);
if (x_177 == 0)
{
lean_dec(x_149);
x_172 = x_145;
goto block_174;
}
else
{
size_t x_178; size_t x_179; uint8_t x_180; 
x_178 = lean_ptr_addr(x_149);
lean_dec(x_149);
x_179 = lean_ptr_addr(x_151);
x_180 = lean_usize_dec_eq(x_178, x_179);
x_172 = x_180;
goto block_174;
}
block_171:
{
if (x_162 == 0)
{
uint8_t x_163; 
x_163 = !lean_is_exclusive(x_1);
if (x_163 == 0)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_164 = lean_ctor_get(x_1, 0);
lean_dec(x_164);
x_165 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_165, 0, x_112);
lean_ctor_set(x_165, 1, x_151);
lean_ctor_set(x_165, 2, x_161);
lean_ctor_set(x_165, 3, x_158);
lean_ctor_set(x_1, 0, x_165);
if (lean_is_scalar(x_160)) {
 x_166 = lean_alloc_ctor(0, 2, 0);
} else {
 x_166 = x_160;
}
lean_ctor_set(x_166, 0, x_1);
lean_ctor_set(x_166, 1, x_159);
return x_166;
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; 
lean_dec(x_1);
x_167 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_167, 0, x_112);
lean_ctor_set(x_167, 1, x_151);
lean_ctor_set(x_167, 2, x_161);
lean_ctor_set(x_167, 3, x_158);
x_168 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_168, 0, x_167);
if (lean_is_scalar(x_160)) {
 x_169 = lean_alloc_ctor(0, 2, 0);
} else {
 x_169 = x_160;
}
lean_ctor_set(x_169, 0, x_168);
lean_ctor_set(x_169, 1, x_159);
return x_169;
}
}
else
{
lean_object* x_170; 
lean_dec(x_161);
lean_dec(x_158);
lean_dec(x_151);
lean_dec(x_112);
if (lean_is_scalar(x_160)) {
 x_170 = lean_alloc_ctor(0, 2, 0);
} else {
 x_170 = x_160;
}
lean_ctor_set(x_170, 0, x_1);
lean_ctor_set(x_170, 1, x_159);
return x_170;
}
}
block_174:
{
if (x_172 == 0)
{
x_162 = x_145;
goto block_171;
}
else
{
uint8_t x_173; 
x_173 = l___private_Lean_Expr_0__Lean_beqFVarId____x40_Lean_Expr___hyg_1672_(x_161, x_161);
x_162 = x_173;
goto block_171;
}
}
}
else
{
uint8_t x_181; 
lean_dec(x_153);
lean_dec(x_151);
lean_dec(x_149);
lean_dec(x_112);
lean_dec(x_111);
lean_dec(x_1);
x_181 = !lean_is_exclusive(x_157);
if (x_181 == 0)
{
return x_157;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_182 = lean_ctor_get(x_157, 0);
x_183 = lean_ctor_get(x_157, 1);
lean_inc(x_183);
lean_inc(x_182);
lean_dec(x_157);
x_184 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_184, 0, x_182);
lean_ctor_set(x_184, 1, x_183);
return x_184;
}
}
}
else
{
uint8_t x_185; 
lean_dec(x_149);
lean_dec(x_112);
lean_dec(x_111);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_185 = !lean_is_exclusive(x_150);
if (x_185 == 0)
{
return x_150;
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_186 = lean_ctor_get(x_150, 0);
x_187 = lean_ctor_get(x_150, 1);
lean_inc(x_187);
lean_inc(x_186);
lean_dec(x_150);
x_188 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_188, 0, x_186);
lean_ctor_set(x_188, 1, x_187);
return x_188;
}
}
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; 
lean_dec(x_112);
lean_dec(x_1);
x_189 = lean_ctor_get(x_146, 1);
lean_inc(x_189);
lean_dec(x_146);
x_190 = lean_ctor_get(x_147, 0);
lean_inc(x_190);
lean_dec(x_147);
x_191 = l_Lean_Compiler_LCNF_trivialStructToMono(x_190, x_111, x_2, x_3, x_4, x_5, x_6, x_189);
lean_dec(x_111);
lean_dec(x_190);
return x_191;
}
}
else
{
uint8_t x_192; 
lean_dec(x_112);
lean_dec(x_111);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_192 = !lean_is_exclusive(x_146);
if (x_192 == 0)
{
return x_146;
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_193 = lean_ctor_get(x_146, 0);
x_194 = lean_ctor_get(x_146, 1);
lean_inc(x_194);
lean_inc(x_193);
lean_dec(x_146);
x_195 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_195, 0, x_193);
lean_ctor_set(x_195, 1, x_194);
return x_195;
}
}
}
else
{
lean_object* x_196; 
lean_dec(x_112);
lean_dec(x_1);
x_196 = l_Lean_Compiler_LCNF_casesStringToMono___redArg(x_111, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_111);
return x_196;
}
}
else
{
lean_object* x_197; 
lean_dec(x_112);
lean_dec(x_1);
x_197 = l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg(x_111, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_111);
return x_197;
}
}
else
{
lean_object* x_198; 
lean_dec(x_112);
lean_dec(x_1);
x_198 = l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg(x_111, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_111);
return x_198;
}
}
else
{
lean_object* x_199; 
lean_dec(x_112);
lean_dec(x_1);
x_199 = l_Lean_Compiler_LCNF_casesArrayToMono___redArg(x_111, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_111);
return x_199;
}
}
else
{
lean_object* x_200; 
lean_dec(x_112);
lean_dec(x_1);
x_200 = l_Lean_Compiler_LCNF_casesUIntToMono___redArg(x_111, x_132, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_111);
return x_200;
}
}
else
{
lean_object* x_201; 
lean_dec(x_112);
lean_dec(x_1);
x_201 = l_Lean_Compiler_LCNF_casesUIntToMono___redArg(x_111, x_129, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_111);
return x_201;
}
}
else
{
lean_object* x_202; 
lean_dec(x_112);
lean_dec(x_1);
x_202 = l_Lean_Compiler_LCNF_casesUIntToMono___redArg(x_111, x_126, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_111);
return x_202;
}
}
else
{
lean_object* x_203; 
lean_dec(x_112);
lean_dec(x_1);
x_203 = l_Lean_Compiler_LCNF_casesUIntToMono___redArg(x_111, x_123, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_111);
return x_203;
}
}
else
{
lean_object* x_204; 
lean_dec(x_112);
lean_dec(x_1);
x_204 = l_Lean_Compiler_LCNF_casesIntToMono___redArg(x_111, x_2, x_3, x_4, x_5, x_6, x_7);
return x_204;
}
}
else
{
lean_object* x_205; 
lean_dec(x_112);
lean_dec(x_1);
x_205 = l_Lean_Compiler_LCNF_casesNatToMono___redArg(x_111, x_2, x_3, x_4, x_5, x_6, x_7);
return x_205;
}
}
else
{
lean_object* x_206; 
lean_dec(x_112);
lean_dec(x_1);
x_206 = l_Lean_Compiler_LCNF_decToMono___redArg(x_111, x_2, x_3, x_4, x_5, x_6, x_7);
return x_206;
}
}
case 6:
{
uint8_t x_207; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_207 = !lean_is_exclusive(x_1);
if (x_207 == 0)
{
lean_object* x_208; lean_object* x_209; 
x_208 = lean_ctor_get(x_1, 0);
x_209 = l_Lean_Compiler_LCNF_toMonoType(x_208, x_5, x_6, x_7);
if (lean_obj_tag(x_209) == 0)
{
uint8_t x_210; 
x_210 = !lean_is_exclusive(x_209);
if (x_210 == 0)
{
lean_object* x_211; 
x_211 = lean_ctor_get(x_209, 0);
lean_ctor_set(x_1, 0, x_211);
lean_ctor_set(x_209, 0, x_1);
return x_209;
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_212 = lean_ctor_get(x_209, 0);
x_213 = lean_ctor_get(x_209, 1);
lean_inc(x_213);
lean_inc(x_212);
lean_dec(x_209);
lean_ctor_set(x_1, 0, x_212);
x_214 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_214, 0, x_1);
lean_ctor_set(x_214, 1, x_213);
return x_214;
}
}
else
{
uint8_t x_215; 
lean_free_object(x_1);
x_215 = !lean_is_exclusive(x_209);
if (x_215 == 0)
{
return x_209;
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_216 = lean_ctor_get(x_209, 0);
x_217 = lean_ctor_get(x_209, 1);
lean_inc(x_217);
lean_inc(x_216);
lean_dec(x_209);
x_218 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_218, 0, x_216);
lean_ctor_set(x_218, 1, x_217);
return x_218;
}
}
}
else
{
lean_object* x_219; lean_object* x_220; 
x_219 = lean_ctor_get(x_1, 0);
lean_inc(x_219);
lean_dec(x_1);
x_220 = l_Lean_Compiler_LCNF_toMonoType(x_219, x_5, x_6, x_7);
if (lean_obj_tag(x_220) == 0)
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_221 = lean_ctor_get(x_220, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_220, 1);
lean_inc(x_222);
if (lean_is_exclusive(x_220)) {
 lean_ctor_release(x_220, 0);
 lean_ctor_release(x_220, 1);
 x_223 = x_220;
} else {
 lean_dec_ref(x_220);
 x_223 = lean_box(0);
}
x_224 = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(x_224, 0, x_221);
if (lean_is_scalar(x_223)) {
 x_225 = lean_alloc_ctor(0, 2, 0);
} else {
 x_225 = x_223;
}
lean_ctor_set(x_225, 0, x_224);
lean_ctor_set(x_225, 1, x_222);
return x_225;
}
else
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_226 = lean_ctor_get(x_220, 0);
lean_inc(x_226);
x_227 = lean_ctor_get(x_220, 1);
lean_inc(x_227);
if (lean_is_exclusive(x_220)) {
 lean_ctor_release(x_220, 0);
 lean_ctor_release(x_220, 1);
 x_228 = x_220;
} else {
 lean_dec_ref(x_220);
 x_228 = lean_box(0);
}
if (lean_is_scalar(x_228)) {
 x_229 = lean_alloc_ctor(1, 2, 0);
} else {
 x_229 = x_228;
}
lean_ctor_set(x_229, 0, x_226);
lean_ctor_set(x_229, 1, x_227);
return x_229;
}
}
}
default: 
{
lean_object* x_230; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_230 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_230, 0, x_1);
lean_ctor_set(x_230, 1, x_7);
return x_230;
}
}
block_15:
{
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_1);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_10);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_9);
return x_13;
}
else
{
lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_8);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_9);
return x_14;
}
}
block_23:
{
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_1);
x_20 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_20, 0, x_16);
lean_ctor_set(x_20, 1, x_18);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_17);
return x_21;
}
else
{
lean_object* x_22; 
lean_dec(x_18);
lean_dec(x_16);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_1);
lean_ctor_set(x_22, 1, x_17);
return x_22;
}
}
block_78:
{
lean_object* x_32; 
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
x_32 = l_Lean_Compiler_LCNF_FunDeclCore_toMono(x_24, x_26, x_27, x_28, x_29, x_30, x_31);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = l_Lean_Compiler_LCNF_Code_toMono(x_25, x_26, x_27, x_28, x_29, x_30, x_34);
if (lean_obj_tag(x_35) == 0)
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; size_t x_40; size_t x_41; uint8_t x_42; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_ctor_get(x_1, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_1, 1);
lean_inc(x_39);
x_40 = lean_ptr_addr(x_39);
lean_dec(x_39);
x_41 = lean_ptr_addr(x_36);
x_42 = lean_usize_dec_eq(x_40, x_41);
if (x_42 == 0)
{
lean_dec(x_38);
x_8 = x_33;
x_9 = x_37;
x_10 = x_36;
x_11 = x_42;
goto block_15;
}
else
{
size_t x_43; size_t x_44; uint8_t x_45; 
x_43 = lean_ptr_addr(x_38);
lean_dec(x_38);
x_44 = lean_ptr_addr(x_33);
x_45 = lean_usize_dec_eq(x_43, x_44);
x_8 = x_33;
x_9 = x_37;
x_10 = x_36;
x_11 = x_45;
goto block_15;
}
}
case 2:
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; size_t x_50; size_t x_51; uint8_t x_52; 
x_46 = lean_ctor_get(x_35, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_35, 1);
lean_inc(x_47);
lean_dec(x_35);
x_48 = lean_ctor_get(x_1, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_1, 1);
lean_inc(x_49);
x_50 = lean_ptr_addr(x_49);
lean_dec(x_49);
x_51 = lean_ptr_addr(x_46);
x_52 = lean_usize_dec_eq(x_50, x_51);
if (x_52 == 0)
{
lean_dec(x_48);
x_16 = x_33;
x_17 = x_47;
x_18 = x_46;
x_19 = x_52;
goto block_23;
}
else
{
size_t x_53; size_t x_54; uint8_t x_55; 
x_53 = lean_ptr_addr(x_48);
lean_dec(x_48);
x_54 = lean_ptr_addr(x_33);
x_55 = lean_usize_dec_eq(x_53, x_54);
x_16 = x_33;
x_17 = x_47;
x_18 = x_46;
x_19 = x_55;
goto block_23;
}
}
default: 
{
uint8_t x_56; 
lean_dec(x_33);
lean_dec(x_1);
x_56 = !lean_is_exclusive(x_35);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_57 = lean_ctor_get(x_35, 0);
lean_dec(x_57);
x_58 = lean_mk_string_unchecked("Lean.Compiler.LCNF.Basic", 24, 24);
x_59 = lean_mk_string_unchecked("_private.Lean.Compiler.LCNF.Basic.0.Lean.Compiler.LCNF.updateFunImp", 67, 67);
x_60 = lean_unsigned_to_nat(305u);
x_61 = lean_unsigned_to_nat(9u);
x_62 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_63 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_58, x_59, x_60, x_61, x_62);
lean_dec(x_62);
lean_dec(x_59);
lean_dec(x_58);
x_64 = l_panic___at___Lean_Compiler_LCNF_Code_instantiateValueLevelParams_instCode_spec__0(x_63);
lean_ctor_set(x_35, 0, x_64);
return x_35;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_65 = lean_ctor_get(x_35, 1);
lean_inc(x_65);
lean_dec(x_35);
x_66 = lean_mk_string_unchecked("Lean.Compiler.LCNF.Basic", 24, 24);
x_67 = lean_mk_string_unchecked("_private.Lean.Compiler.LCNF.Basic.0.Lean.Compiler.LCNF.updateFunImp", 67, 67);
x_68 = lean_unsigned_to_nat(305u);
x_69 = lean_unsigned_to_nat(9u);
x_70 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_71 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_66, x_67, x_68, x_69, x_70);
lean_dec(x_70);
lean_dec(x_67);
lean_dec(x_66);
x_72 = l_panic___at___Lean_Compiler_LCNF_Code_instantiateValueLevelParams_instCode_spec__0(x_71);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_65);
return x_73;
}
}
}
}
else
{
lean_dec(x_33);
lean_dec(x_1);
return x_35;
}
}
else
{
uint8_t x_74; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_1);
x_74 = !lean_is_exclusive(x_32);
if (x_74 == 0)
{
return x_32;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_32, 0);
x_76 = lean_ctor_get(x_32, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_32);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Compiler_LCNF_trivialStructToMono_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_8 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed), 7, 0);
x_9 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1), 9, 0);
x_10 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__0___boxed), 5, 0);
x_11 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__1), 7, 0);
x_12 = l_instMonadEIO(lean_box(0));
x_13 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
lean_inc(x_15);
x_16 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_17, 0, x_15);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_closure((void*)(l_instMonadEIO___lam__1), 5, 0);
x_20 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_20, 0, x_19);
x_21 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_21, 0, x_20);
x_22 = lean_alloc_closure((void*)(l_instMonadEIO___lam__2), 5, 0);
x_23 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_23, 0, x_22);
x_24 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_24, 0, x_23);
x_25 = lean_alloc_closure((void*)(l_EStateM_seqRight), 7, 2);
lean_closure_set(x_25, 0, lean_box(0));
lean_closure_set(x_25, 1, lean_box(0));
x_26 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_26, 0, x_25);
x_27 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_27, 0, x_26);
lean_inc(x_27);
lean_inc(x_24);
lean_inc(x_21);
x_28 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_28, 0, x_18);
lean_ctor_set(x_28, 1, x_10);
lean_ctor_set(x_28, 2, x_21);
lean_ctor_set(x_28, 3, x_24);
lean_ctor_set(x_28, 4, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_11);
x_30 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_29);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec(x_31);
lean_inc(x_32);
x_33 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_33, 0, x_32);
x_34 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_34, 0, x_32);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_36, 0, x_21);
x_37 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_37, 0, x_36);
x_38 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_38, 0, x_24);
x_39 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_39, 0, x_38);
x_40 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_40, 0, x_27);
x_41 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_41, 0, x_40);
x_42 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_42, 0, x_35);
lean_ctor_set(x_42, 1, x_8);
lean_ctor_set(x_42, 2, x_37);
lean_ctor_set(x_42, 3, x_39);
lean_ctor_set(x_42, 4, x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_9);
x_44 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_43);
x_45 = l_Lean_Compiler_LCNF_instInhabitedCode;
x_46 = l_instInhabitedOfMonad___redArg(x_44, x_45);
x_47 = lean_panic_fn(x_46, x_1);
x_48 = lean_apply_6(x_47, x_2, x_3, x_4, x_5, x_6, x_7);
return x_48;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_trivialStructToMono(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_2, 3);
x_10 = lean_array_get_size(x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_dec_eq(x_10, x_11);
lean_dec(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_mk_string_unchecked("Lean.Compiler.LCNF.ToMono", 25, 25);
x_14 = lean_mk_string_unchecked("Lean.Compiler.LCNF.trivialStructToMono", 38, 38);
x_15 = lean_unsigned_to_nat(207u);
x_16 = lean_unsigned_to_nat(2u);
x_17 = lean_mk_string_unchecked("assertion violation: c.alts.size == 1\n  ", 40, 40);
x_18 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_13, x_14, x_15, x_16, x_17);
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_13);
x_19 = l_panic___at___Lean_Compiler_LCNF_trivialStructToMono_spec__0(x_18, x_3, x_4, x_5, x_6, x_7, x_8);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = l_Lean_Compiler_LCNF_instInhabitedCode;
x_21 = l_Lean_Compiler_LCNF_instInhabitedAltCore(lean_box(0), x_20);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_array_get(x_21, x_9, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
x_26 = lean_ctor_get(x_23, 2);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_ctor_get(x_1, 0);
x_28 = lean_name_eq(x_24, x_27);
lean_dec(x_24);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_26);
lean_dec(x_25);
x_29 = lean_mk_string_unchecked("Lean.Compiler.LCNF.ToMono", 25, 25);
x_30 = lean_mk_string_unchecked("Lean.Compiler.LCNF.trivialStructToMono", 38, 38);
x_31 = lean_unsigned_to_nat(209u);
x_32 = lean_unsigned_to_nat(2u);
x_33 = lean_mk_string_unchecked("assertion violation: ctorName == info.ctorName\n  ", 49, 49);
x_34 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_29, x_30, x_31, x_32, x_33);
lean_dec(x_33);
lean_dec(x_30);
lean_dec(x_29);
x_35 = l_panic___at___Lean_Compiler_LCNF_trivialStructToMono_spec__0(x_34, x_3, x_4, x_5, x_6, x_7, x_8);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_36 = lean_ctor_get(x_1, 2);
x_37 = lean_array_get_size(x_25);
x_38 = lean_nat_dec_lt(x_36, x_37);
lean_dec(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_26);
lean_dec(x_25);
x_39 = lean_mk_string_unchecked("Lean.Compiler.LCNF.ToMono", 25, 25);
x_40 = lean_mk_string_unchecked("Lean.Compiler.LCNF.trivialStructToMono", 38, 38);
x_41 = lean_unsigned_to_nat(210u);
x_42 = lean_unsigned_to_nat(2u);
x_43 = lean_mk_string_unchecked("assertion violation: info.fieldIdx < ps.size\n  ", 47, 47);
x_44 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_39, x_40, x_41, x_42, x_43);
lean_dec(x_43);
lean_dec(x_40);
lean_dec(x_39);
x_45 = l_panic___at___Lean_Compiler_LCNF_trivialStructToMono_spec__0(x_44, x_3, x_4, x_5, x_6, x_7, x_8);
return x_45;
}
else
{
lean_object* x_46; uint8_t x_47; 
x_46 = l_Lean_Compiler_LCNF_eraseParams___redArg(x_25, x_5, x_8);
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_48 = lean_ctor_get(x_46, 1);
x_49 = lean_ctor_get(x_46, 0);
lean_dec(x_49);
x_50 = l_Lean_Compiler_LCNF_instInhabitedParam;
x_51 = lean_array_get(x_50, x_25, x_36);
lean_dec(x_25);
x_52 = lean_ctor_get(x_51, 2);
lean_inc(x_52);
lean_inc(x_7);
lean_inc(x_6);
x_53 = l_Lean_Compiler_LCNF_toMonoType(x_52, x_6, x_7, x_48);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_st_ref_take(x_5, x_55);
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_58 = lean_ctor_get(x_56, 0);
x_59 = lean_ctor_get(x_56, 1);
x_60 = lean_ctor_get(x_2, 2);
x_61 = lean_mk_empty_array_with_capacity(x_22);
x_62 = lean_ctor_get(x_51, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_51, 1);
lean_inc(x_63);
lean_dec(x_51);
lean_inc(x_60);
lean_ctor_set_tag(x_56, 4);
lean_ctor_set(x_56, 1, x_61);
lean_ctor_set(x_56, 0, x_60);
x_64 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
lean_ctor_set(x_64, 2, x_54);
lean_ctor_set(x_64, 3, x_56);
x_65 = lean_ctor_get(x_58, 0);
lean_inc(x_65);
lean_inc(x_64);
x_66 = l_Lean_Compiler_LCNF_LCtx_addLetDecl(x_65, x_64);
x_67 = lean_ctor_get(x_58, 1);
lean_inc(x_67);
lean_dec(x_58);
lean_ctor_set(x_46, 1, x_67);
lean_ctor_set(x_46, 0, x_66);
x_68 = lean_st_ref_set(x_5, x_46, x_59);
x_69 = !lean_is_exclusive(x_68);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_68, 1);
x_71 = lean_ctor_get(x_68, 0);
lean_dec(x_71);
x_72 = l_Lean_Compiler_LCNF_Code_toMono(x_26, x_3, x_4, x_5, x_6, x_7, x_70);
if (lean_obj_tag(x_72) == 0)
{
uint8_t x_73; 
x_73 = !lean_is_exclusive(x_72);
if (x_73 == 0)
{
lean_object* x_74; 
x_74 = lean_ctor_get(x_72, 0);
lean_ctor_set(x_68, 1, x_74);
lean_ctor_set(x_68, 0, x_64);
lean_ctor_set(x_72, 0, x_68);
return x_72;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_72, 0);
x_76 = lean_ctor_get(x_72, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_72);
lean_ctor_set(x_68, 1, x_75);
lean_ctor_set(x_68, 0, x_64);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_68);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
else
{
lean_free_object(x_68);
lean_dec(x_64);
return x_72;
}
}
else
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_68, 1);
lean_inc(x_78);
lean_dec(x_68);
x_79 = l_Lean_Compiler_LCNF_Code_toMono(x_26, x_3, x_4, x_5, x_6, x_7, x_78);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_82 = x_79;
} else {
 lean_dec_ref(x_79);
 x_82 = lean_box(0);
}
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_64);
lean_ctor_set(x_83, 1, x_80);
if (lean_is_scalar(x_82)) {
 x_84 = lean_alloc_ctor(0, 2, 0);
} else {
 x_84 = x_82;
}
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_81);
return x_84;
}
else
{
lean_dec(x_64);
return x_79;
}
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_85 = lean_ctor_get(x_56, 0);
x_86 = lean_ctor_get(x_56, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_56);
x_87 = lean_ctor_get(x_2, 2);
x_88 = lean_mk_empty_array_with_capacity(x_22);
x_89 = lean_ctor_get(x_51, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_51, 1);
lean_inc(x_90);
lean_dec(x_51);
lean_inc(x_87);
x_91 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_91, 0, x_87);
lean_ctor_set(x_91, 1, x_88);
x_92 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_92, 0, x_89);
lean_ctor_set(x_92, 1, x_90);
lean_ctor_set(x_92, 2, x_54);
lean_ctor_set(x_92, 3, x_91);
x_93 = lean_ctor_get(x_85, 0);
lean_inc(x_93);
lean_inc(x_92);
x_94 = l_Lean_Compiler_LCNF_LCtx_addLetDecl(x_93, x_92);
x_95 = lean_ctor_get(x_85, 1);
lean_inc(x_95);
lean_dec(x_85);
lean_ctor_set(x_46, 1, x_95);
lean_ctor_set(x_46, 0, x_94);
x_96 = lean_st_ref_set(x_5, x_46, x_86);
x_97 = lean_ctor_get(x_96, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 lean_ctor_release(x_96, 1);
 x_98 = x_96;
} else {
 lean_dec_ref(x_96);
 x_98 = lean_box(0);
}
x_99 = l_Lean_Compiler_LCNF_Code_toMono(x_26, x_3, x_4, x_5, x_6, x_7, x_97);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
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
if (lean_is_scalar(x_98)) {
 x_103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_103 = x_98;
}
lean_ctor_set(x_103, 0, x_92);
lean_ctor_set(x_103, 1, x_100);
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
lean_dec(x_98);
lean_dec(x_92);
return x_99;
}
}
}
else
{
uint8_t x_105; 
lean_dec(x_51);
lean_free_object(x_46);
lean_dec(x_26);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_105 = !lean_is_exclusive(x_53);
if (x_105 == 0)
{
return x_53;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_53, 0);
x_107 = lean_ctor_get(x_53, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_53);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
return x_108;
}
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_109 = lean_ctor_get(x_46, 1);
lean_inc(x_109);
lean_dec(x_46);
x_110 = l_Lean_Compiler_LCNF_instInhabitedParam;
x_111 = lean_array_get(x_110, x_25, x_36);
lean_dec(x_25);
x_112 = lean_ctor_get(x_111, 2);
lean_inc(x_112);
lean_inc(x_7);
lean_inc(x_6);
x_113 = l_Lean_Compiler_LCNF_toMonoType(x_112, x_6, x_7, x_109);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
lean_dec(x_113);
x_116 = lean_st_ref_take(x_5, x_115);
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_119 = x_116;
} else {
 lean_dec_ref(x_116);
 x_119 = lean_box(0);
}
x_120 = lean_ctor_get(x_2, 2);
x_121 = lean_mk_empty_array_with_capacity(x_22);
x_122 = lean_ctor_get(x_111, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_111, 1);
lean_inc(x_123);
lean_dec(x_111);
lean_inc(x_120);
if (lean_is_scalar(x_119)) {
 x_124 = lean_alloc_ctor(4, 2, 0);
} else {
 x_124 = x_119;
 lean_ctor_set_tag(x_124, 4);
}
lean_ctor_set(x_124, 0, x_120);
lean_ctor_set(x_124, 1, x_121);
x_125 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_125, 0, x_122);
lean_ctor_set(x_125, 1, x_123);
lean_ctor_set(x_125, 2, x_114);
lean_ctor_set(x_125, 3, x_124);
x_126 = lean_ctor_get(x_117, 0);
lean_inc(x_126);
lean_inc(x_125);
x_127 = l_Lean_Compiler_LCNF_LCtx_addLetDecl(x_126, x_125);
x_128 = lean_ctor_get(x_117, 1);
lean_inc(x_128);
lean_dec(x_117);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
x_130 = lean_st_ref_set(x_5, x_129, x_118);
x_131 = lean_ctor_get(x_130, 1);
lean_inc(x_131);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_132 = x_130;
} else {
 lean_dec_ref(x_130);
 x_132 = lean_box(0);
}
x_133 = l_Lean_Compiler_LCNF_Code_toMono(x_26, x_3, x_4, x_5, x_6, x_7, x_131);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_136 = x_133;
} else {
 lean_dec_ref(x_133);
 x_136 = lean_box(0);
}
if (lean_is_scalar(x_132)) {
 x_137 = lean_alloc_ctor(0, 2, 0);
} else {
 x_137 = x_132;
}
lean_ctor_set(x_137, 0, x_125);
lean_ctor_set(x_137, 1, x_134);
if (lean_is_scalar(x_136)) {
 x_138 = lean_alloc_ctor(0, 2, 0);
} else {
 x_138 = x_136;
}
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_135);
return x_138;
}
else
{
lean_dec(x_132);
lean_dec(x_125);
return x_133;
}
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
lean_dec(x_111);
lean_dec(x_26);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_139 = lean_ctor_get(x_113, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_113, 1);
lean_inc(x_140);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 x_141 = x_113;
} else {
 lean_dec_ref(x_113);
 x_141 = lean_box(0);
}
if (lean_is_scalar(x_141)) {
 x_142 = lean_alloc_ctor(1, 2, 0);
} else {
 x_142 = x_141;
}
lean_ctor_set(x_142, 0, x_139);
lean_ctor_set(x_142, 1, x_140);
return x_142;
}
}
}
}
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
lean_dec(x_23);
x_143 = lean_mk_string_unchecked("Lean.Compiler.LCNF.ToMono", 25, 25);
x_144 = lean_mk_string_unchecked("Lean.Compiler.LCNF.trivialStructToMono", 38, 38);
x_145 = lean_unsigned_to_nat(208u);
x_146 = lean_unsigned_to_nat(41u);
x_147 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_148 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_143, x_144, x_145, x_146, x_147);
lean_dec(x_147);
lean_dec(x_144);
lean_dec(x_143);
x_149 = l_panic___at___Lean_Compiler_LCNF_trivialStructToMono_spec__0(x_148, x_3, x_4, x_5, x_6, x_7, x_8);
return x_149;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesStringToMono___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_1, 3);
x_9 = lean_array_get_size(x_8);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_dec_eq(x_9, x_10);
lean_dec(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_mk_string_unchecked("Lean.Compiler.LCNF.ToMono", 25, 25);
x_13 = lean_mk_string_unchecked("Lean.Compiler.LCNF.casesStringToMono", 36, 36);
x_14 = lean_unsigned_to_nat(196u);
x_15 = lean_unsigned_to_nat(2u);
x_16 = lean_mk_string_unchecked("assertion violation: c.alts.size == 1\n  ", 40, 40);
x_17 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_12, x_13, x_14, x_15, x_16);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_12);
x_18 = l_panic___at___Lean_Compiler_LCNF_trivialStructToMono_spec__0(x_17, x_2, x_3, x_4, x_5, x_6, x_7);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = l_Lean_Compiler_LCNF_instInhabitedCode;
x_20 = l_Lean_Compiler_LCNF_instInhabitedAltCore(lean_box(0), x_19);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_array_get(x_20, x_8, x_21);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_24 = lean_ctor_get(x_22, 1);
x_25 = lean_ctor_get(x_22, 2);
x_26 = lean_ctor_get(x_22, 0);
lean_dec(x_26);
x_27 = l_Lean_Compiler_LCNF_eraseParams___redArg(x_24, x_4, x_7);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = l_Lean_Compiler_LCNF_instInhabitedParam;
x_30 = lean_mk_string_unchecked("String", 6, 6);
x_31 = lean_mk_string_unchecked("toList", 6, 6);
x_32 = lean_ctor_get(x_1, 2);
lean_inc(x_32);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = lean_mk_empty_array_with_capacity(x_10);
x_35 = lean_st_ref_take(x_4, x_28);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_37 = lean_ctor_get(x_35, 0);
x_38 = lean_ctor_get(x_35, 1);
x_39 = lean_array_get(x_29, x_24, x_21);
lean_dec(x_24);
x_40 = l_Lean_Name_mkStr2(x_30, x_31);
x_41 = lean_box(0);
x_42 = lean_array_push(x_34, x_33);
x_43 = lean_ctor_get(x_39, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_39, 1);
lean_inc(x_44);
lean_dec(x_39);
x_45 = l_Lean_Compiler_LCNF_anyExpr;
lean_ctor_set_tag(x_22, 3);
lean_ctor_set(x_22, 2, x_42);
lean_ctor_set(x_22, 1, x_41);
lean_ctor_set(x_22, 0, x_40);
x_46 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_44);
lean_ctor_set(x_46, 2, x_45);
lean_ctor_set(x_46, 3, x_22);
x_47 = lean_ctor_get(x_37, 0);
lean_inc(x_47);
lean_inc(x_46);
x_48 = l_Lean_Compiler_LCNF_LCtx_addLetDecl(x_47, x_46);
x_49 = lean_ctor_get(x_37, 1);
lean_inc(x_49);
lean_dec(x_37);
lean_ctor_set(x_35, 1, x_49);
lean_ctor_set(x_35, 0, x_48);
x_50 = lean_st_ref_set(x_4, x_35, x_38);
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_50, 1);
x_53 = lean_ctor_get(x_50, 0);
lean_dec(x_53);
x_54 = l_Lean_Compiler_LCNF_Code_toMono(x_25, x_2, x_3, x_4, x_5, x_6, x_52);
if (lean_obj_tag(x_54) == 0)
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_54, 0);
lean_ctor_set(x_50, 1, x_56);
lean_ctor_set(x_50, 0, x_46);
lean_ctor_set(x_54, 0, x_50);
return x_54;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_54, 0);
x_58 = lean_ctor_get(x_54, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_54);
lean_ctor_set(x_50, 1, x_57);
lean_ctor_set(x_50, 0, x_46);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_50);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
else
{
lean_free_object(x_50);
lean_dec(x_46);
return x_54;
}
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_50, 1);
lean_inc(x_60);
lean_dec(x_50);
x_61 = l_Lean_Compiler_LCNF_Code_toMono(x_25, x_2, x_3, x_4, x_5, x_6, x_60);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
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
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_46);
lean_ctor_set(x_65, 1, x_62);
if (lean_is_scalar(x_64)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_64;
}
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_63);
return x_66;
}
else
{
lean_dec(x_46);
return x_61;
}
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_67 = lean_ctor_get(x_35, 0);
x_68 = lean_ctor_get(x_35, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_35);
x_69 = lean_array_get(x_29, x_24, x_21);
lean_dec(x_24);
x_70 = l_Lean_Name_mkStr2(x_30, x_31);
x_71 = lean_box(0);
x_72 = lean_array_push(x_34, x_33);
x_73 = lean_ctor_get(x_69, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_69, 1);
lean_inc(x_74);
lean_dec(x_69);
x_75 = l_Lean_Compiler_LCNF_anyExpr;
lean_ctor_set_tag(x_22, 3);
lean_ctor_set(x_22, 2, x_72);
lean_ctor_set(x_22, 1, x_71);
lean_ctor_set(x_22, 0, x_70);
x_76 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_76, 0, x_73);
lean_ctor_set(x_76, 1, x_74);
lean_ctor_set(x_76, 2, x_75);
lean_ctor_set(x_76, 3, x_22);
x_77 = lean_ctor_get(x_67, 0);
lean_inc(x_77);
lean_inc(x_76);
x_78 = l_Lean_Compiler_LCNF_LCtx_addLetDecl(x_77, x_76);
x_79 = lean_ctor_get(x_67, 1);
lean_inc(x_79);
lean_dec(x_67);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
x_81 = lean_st_ref_set(x_4, x_80, x_68);
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_83 = x_81;
} else {
 lean_dec_ref(x_81);
 x_83 = lean_box(0);
}
x_84 = l_Lean_Compiler_LCNF_Code_toMono(x_25, x_2, x_3, x_4, x_5, x_6, x_82);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_87 = x_84;
} else {
 lean_dec_ref(x_84);
 x_87 = lean_box(0);
}
if (lean_is_scalar(x_83)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_83;
}
lean_ctor_set(x_88, 0, x_76);
lean_ctor_set(x_88, 1, x_85);
if (lean_is_scalar(x_87)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_87;
}
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_86);
return x_89;
}
else
{
lean_dec(x_83);
lean_dec(x_76);
return x_84;
}
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_90 = lean_ctor_get(x_22, 1);
x_91 = lean_ctor_get(x_22, 2);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_22);
x_92 = l_Lean_Compiler_LCNF_eraseParams___redArg(x_90, x_4, x_7);
x_93 = lean_ctor_get(x_92, 1);
lean_inc(x_93);
lean_dec(x_92);
x_94 = l_Lean_Compiler_LCNF_instInhabitedParam;
x_95 = lean_mk_string_unchecked("String", 6, 6);
x_96 = lean_mk_string_unchecked("toList", 6, 6);
x_97 = lean_ctor_get(x_1, 2);
lean_inc(x_97);
x_98 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_98, 0, x_97);
x_99 = lean_mk_empty_array_with_capacity(x_10);
x_100 = lean_st_ref_take(x_4, x_93);
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_103 = x_100;
} else {
 lean_dec_ref(x_100);
 x_103 = lean_box(0);
}
x_104 = lean_array_get(x_94, x_90, x_21);
lean_dec(x_90);
x_105 = l_Lean_Name_mkStr2(x_95, x_96);
x_106 = lean_box(0);
x_107 = lean_array_push(x_99, x_98);
x_108 = lean_ctor_get(x_104, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_104, 1);
lean_inc(x_109);
lean_dec(x_104);
x_110 = l_Lean_Compiler_LCNF_anyExpr;
x_111 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_111, 0, x_105);
lean_ctor_set(x_111, 1, x_106);
lean_ctor_set(x_111, 2, x_107);
x_112 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_112, 0, x_108);
lean_ctor_set(x_112, 1, x_109);
lean_ctor_set(x_112, 2, x_110);
lean_ctor_set(x_112, 3, x_111);
x_113 = lean_ctor_get(x_101, 0);
lean_inc(x_113);
lean_inc(x_112);
x_114 = l_Lean_Compiler_LCNF_LCtx_addLetDecl(x_113, x_112);
x_115 = lean_ctor_get(x_101, 1);
lean_inc(x_115);
lean_dec(x_101);
if (lean_is_scalar(x_103)) {
 x_116 = lean_alloc_ctor(0, 2, 0);
} else {
 x_116 = x_103;
}
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
x_117 = lean_st_ref_set(x_4, x_116, x_102);
x_118 = lean_ctor_get(x_117, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_119 = x_117;
} else {
 lean_dec_ref(x_117);
 x_119 = lean_box(0);
}
x_120 = l_Lean_Compiler_LCNF_Code_toMono(x_91, x_2, x_3, x_4, x_5, x_6, x_118);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 x_123 = x_120;
} else {
 lean_dec_ref(x_120);
 x_123 = lean_box(0);
}
if (lean_is_scalar(x_119)) {
 x_124 = lean_alloc_ctor(0, 2, 0);
} else {
 x_124 = x_119;
}
lean_ctor_set(x_124, 0, x_112);
lean_ctor_set(x_124, 1, x_121);
if (lean_is_scalar(x_123)) {
 x_125 = lean_alloc_ctor(0, 2, 0);
} else {
 x_125 = x_123;
}
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_122);
return x_125;
}
else
{
lean_dec(x_119);
lean_dec(x_112);
return x_120;
}
}
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_dec(x_22);
x_126 = lean_mk_string_unchecked("Lean.Compiler.LCNF.ToMono", 25, 25);
x_127 = lean_mk_string_unchecked("Lean.Compiler.LCNF.casesStringToMono", 36, 36);
x_128 = lean_unsigned_to_nat(197u);
x_129 = lean_unsigned_to_nat(34u);
x_130 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_131 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_126, x_127, x_128, x_129, x_130);
lean_dec(x_130);
lean_dec(x_127);
lean_dec(x_126);
x_132 = l_panic___at___Lean_Compiler_LCNF_trivialStructToMono_spec__0(x_131, x_2, x_3, x_4, x_5, x_6, x_7);
return x_132;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesStringToMono(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_casesStringToMono___redArg(x_1, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_1, 3);
x_9 = lean_array_get_size(x_8);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_dec_eq(x_9, x_10);
lean_dec(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_mk_string_unchecked("Lean.Compiler.LCNF.ToMono", 25, 25);
x_13 = lean_mk_string_unchecked("Lean.Compiler.LCNF.casesFloatArrayToMono", 40, 40);
x_14 = lean_unsigned_to_nat(185u);
x_15 = lean_unsigned_to_nat(2u);
x_16 = lean_mk_string_unchecked("assertion violation: c.alts.size == 1\n  ", 40, 40);
x_17 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_12, x_13, x_14, x_15, x_16);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_12);
x_18 = l_panic___at___Lean_Compiler_LCNF_trivialStructToMono_spec__0(x_17, x_2, x_3, x_4, x_5, x_6, x_7);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = l_Lean_Compiler_LCNF_instInhabitedCode;
x_20 = l_Lean_Compiler_LCNF_instInhabitedAltCore(lean_box(0), x_19);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_array_get(x_20, x_8, x_21);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_24 = lean_ctor_get(x_22, 1);
x_25 = lean_ctor_get(x_22, 2);
x_26 = lean_ctor_get(x_22, 0);
lean_dec(x_26);
x_27 = l_Lean_Compiler_LCNF_eraseParams___redArg(x_24, x_4, x_7);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = l_Lean_Compiler_LCNF_instInhabitedParam;
x_30 = lean_mk_string_unchecked("FloatArray", 10, 10);
x_31 = lean_mk_string_unchecked("data", 4, 4);
x_32 = lean_ctor_get(x_1, 2);
lean_inc(x_32);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = lean_mk_empty_array_with_capacity(x_10);
x_35 = lean_st_ref_take(x_4, x_28);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_37 = lean_ctor_get(x_35, 0);
x_38 = lean_ctor_get(x_35, 1);
x_39 = lean_array_get(x_29, x_24, x_21);
lean_dec(x_24);
x_40 = l_Lean_Name_mkStr2(x_30, x_31);
x_41 = lean_box(0);
x_42 = lean_array_push(x_34, x_33);
x_43 = lean_ctor_get(x_39, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_39, 1);
lean_inc(x_44);
lean_dec(x_39);
x_45 = l_Lean_Compiler_LCNF_anyExpr;
lean_ctor_set_tag(x_22, 3);
lean_ctor_set(x_22, 2, x_42);
lean_ctor_set(x_22, 1, x_41);
lean_ctor_set(x_22, 0, x_40);
x_46 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_44);
lean_ctor_set(x_46, 2, x_45);
lean_ctor_set(x_46, 3, x_22);
x_47 = lean_ctor_get(x_37, 0);
lean_inc(x_47);
lean_inc(x_46);
x_48 = l_Lean_Compiler_LCNF_LCtx_addLetDecl(x_47, x_46);
x_49 = lean_ctor_get(x_37, 1);
lean_inc(x_49);
lean_dec(x_37);
lean_ctor_set(x_35, 1, x_49);
lean_ctor_set(x_35, 0, x_48);
x_50 = lean_st_ref_set(x_4, x_35, x_38);
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_50, 1);
x_53 = lean_ctor_get(x_50, 0);
lean_dec(x_53);
x_54 = l_Lean_Compiler_LCNF_Code_toMono(x_25, x_2, x_3, x_4, x_5, x_6, x_52);
if (lean_obj_tag(x_54) == 0)
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_54, 0);
lean_ctor_set(x_50, 1, x_56);
lean_ctor_set(x_50, 0, x_46);
lean_ctor_set(x_54, 0, x_50);
return x_54;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_54, 0);
x_58 = lean_ctor_get(x_54, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_54);
lean_ctor_set(x_50, 1, x_57);
lean_ctor_set(x_50, 0, x_46);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_50);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
else
{
lean_free_object(x_50);
lean_dec(x_46);
return x_54;
}
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_50, 1);
lean_inc(x_60);
lean_dec(x_50);
x_61 = l_Lean_Compiler_LCNF_Code_toMono(x_25, x_2, x_3, x_4, x_5, x_6, x_60);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
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
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_46);
lean_ctor_set(x_65, 1, x_62);
if (lean_is_scalar(x_64)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_64;
}
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_63);
return x_66;
}
else
{
lean_dec(x_46);
return x_61;
}
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_67 = lean_ctor_get(x_35, 0);
x_68 = lean_ctor_get(x_35, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_35);
x_69 = lean_array_get(x_29, x_24, x_21);
lean_dec(x_24);
x_70 = l_Lean_Name_mkStr2(x_30, x_31);
x_71 = lean_box(0);
x_72 = lean_array_push(x_34, x_33);
x_73 = lean_ctor_get(x_69, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_69, 1);
lean_inc(x_74);
lean_dec(x_69);
x_75 = l_Lean_Compiler_LCNF_anyExpr;
lean_ctor_set_tag(x_22, 3);
lean_ctor_set(x_22, 2, x_72);
lean_ctor_set(x_22, 1, x_71);
lean_ctor_set(x_22, 0, x_70);
x_76 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_76, 0, x_73);
lean_ctor_set(x_76, 1, x_74);
lean_ctor_set(x_76, 2, x_75);
lean_ctor_set(x_76, 3, x_22);
x_77 = lean_ctor_get(x_67, 0);
lean_inc(x_77);
lean_inc(x_76);
x_78 = l_Lean_Compiler_LCNF_LCtx_addLetDecl(x_77, x_76);
x_79 = lean_ctor_get(x_67, 1);
lean_inc(x_79);
lean_dec(x_67);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
x_81 = lean_st_ref_set(x_4, x_80, x_68);
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_83 = x_81;
} else {
 lean_dec_ref(x_81);
 x_83 = lean_box(0);
}
x_84 = l_Lean_Compiler_LCNF_Code_toMono(x_25, x_2, x_3, x_4, x_5, x_6, x_82);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_87 = x_84;
} else {
 lean_dec_ref(x_84);
 x_87 = lean_box(0);
}
if (lean_is_scalar(x_83)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_83;
}
lean_ctor_set(x_88, 0, x_76);
lean_ctor_set(x_88, 1, x_85);
if (lean_is_scalar(x_87)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_87;
}
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_86);
return x_89;
}
else
{
lean_dec(x_83);
lean_dec(x_76);
return x_84;
}
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_90 = lean_ctor_get(x_22, 1);
x_91 = lean_ctor_get(x_22, 2);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_22);
x_92 = l_Lean_Compiler_LCNF_eraseParams___redArg(x_90, x_4, x_7);
x_93 = lean_ctor_get(x_92, 1);
lean_inc(x_93);
lean_dec(x_92);
x_94 = l_Lean_Compiler_LCNF_instInhabitedParam;
x_95 = lean_mk_string_unchecked("FloatArray", 10, 10);
x_96 = lean_mk_string_unchecked("data", 4, 4);
x_97 = lean_ctor_get(x_1, 2);
lean_inc(x_97);
x_98 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_98, 0, x_97);
x_99 = lean_mk_empty_array_with_capacity(x_10);
x_100 = lean_st_ref_take(x_4, x_93);
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_103 = x_100;
} else {
 lean_dec_ref(x_100);
 x_103 = lean_box(0);
}
x_104 = lean_array_get(x_94, x_90, x_21);
lean_dec(x_90);
x_105 = l_Lean_Name_mkStr2(x_95, x_96);
x_106 = lean_box(0);
x_107 = lean_array_push(x_99, x_98);
x_108 = lean_ctor_get(x_104, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_104, 1);
lean_inc(x_109);
lean_dec(x_104);
x_110 = l_Lean_Compiler_LCNF_anyExpr;
x_111 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_111, 0, x_105);
lean_ctor_set(x_111, 1, x_106);
lean_ctor_set(x_111, 2, x_107);
x_112 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_112, 0, x_108);
lean_ctor_set(x_112, 1, x_109);
lean_ctor_set(x_112, 2, x_110);
lean_ctor_set(x_112, 3, x_111);
x_113 = lean_ctor_get(x_101, 0);
lean_inc(x_113);
lean_inc(x_112);
x_114 = l_Lean_Compiler_LCNF_LCtx_addLetDecl(x_113, x_112);
x_115 = lean_ctor_get(x_101, 1);
lean_inc(x_115);
lean_dec(x_101);
if (lean_is_scalar(x_103)) {
 x_116 = lean_alloc_ctor(0, 2, 0);
} else {
 x_116 = x_103;
}
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
x_117 = lean_st_ref_set(x_4, x_116, x_102);
x_118 = lean_ctor_get(x_117, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_119 = x_117;
} else {
 lean_dec_ref(x_117);
 x_119 = lean_box(0);
}
x_120 = l_Lean_Compiler_LCNF_Code_toMono(x_91, x_2, x_3, x_4, x_5, x_6, x_118);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 x_123 = x_120;
} else {
 lean_dec_ref(x_120);
 x_123 = lean_box(0);
}
if (lean_is_scalar(x_119)) {
 x_124 = lean_alloc_ctor(0, 2, 0);
} else {
 x_124 = x_119;
}
lean_ctor_set(x_124, 0, x_112);
lean_ctor_set(x_124, 1, x_121);
if (lean_is_scalar(x_123)) {
 x_125 = lean_alloc_ctor(0, 2, 0);
} else {
 x_125 = x_123;
}
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_122);
return x_125;
}
else
{
lean_dec(x_119);
lean_dec(x_112);
return x_120;
}
}
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_dec(x_22);
x_126 = lean_mk_string_unchecked("Lean.Compiler.LCNF.ToMono", 25, 25);
x_127 = lean_mk_string_unchecked("Lean.Compiler.LCNF.casesFloatArrayToMono", 40, 40);
x_128 = lean_unsigned_to_nat(186u);
x_129 = lean_unsigned_to_nat(34u);
x_130 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_131 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_126, x_127, x_128, x_129, x_130);
lean_dec(x_130);
lean_dec(x_127);
lean_dec(x_126);
x_132 = l_panic___at___Lean_Compiler_LCNF_trivialStructToMono_spec__0(x_131, x_2, x_3, x_4, x_5, x_6, x_7);
return x_132;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloatArrayToMono(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg(x_1, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_1, 3);
x_9 = lean_array_get_size(x_8);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_dec_eq(x_9, x_10);
lean_dec(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_mk_string_unchecked("Lean.Compiler.LCNF.ToMono", 25, 25);
x_13 = lean_mk_string_unchecked("Lean.Compiler.LCNF.casesByteArrayToMono", 39, 39);
x_14 = lean_unsigned_to_nat(174u);
x_15 = lean_unsigned_to_nat(2u);
x_16 = lean_mk_string_unchecked("assertion violation: c.alts.size == 1\n  ", 40, 40);
x_17 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_12, x_13, x_14, x_15, x_16);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_12);
x_18 = l_panic___at___Lean_Compiler_LCNF_trivialStructToMono_spec__0(x_17, x_2, x_3, x_4, x_5, x_6, x_7);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = l_Lean_Compiler_LCNF_instInhabitedCode;
x_20 = l_Lean_Compiler_LCNF_instInhabitedAltCore(lean_box(0), x_19);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_array_get(x_20, x_8, x_21);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_24 = lean_ctor_get(x_22, 1);
x_25 = lean_ctor_get(x_22, 2);
x_26 = lean_ctor_get(x_22, 0);
lean_dec(x_26);
x_27 = l_Lean_Compiler_LCNF_eraseParams___redArg(x_24, x_4, x_7);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = l_Lean_Compiler_LCNF_instInhabitedParam;
x_30 = lean_mk_string_unchecked("ByteArray", 9, 9);
x_31 = lean_mk_string_unchecked("data", 4, 4);
x_32 = lean_ctor_get(x_1, 2);
lean_inc(x_32);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = lean_mk_empty_array_with_capacity(x_10);
x_35 = lean_st_ref_take(x_4, x_28);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_37 = lean_ctor_get(x_35, 0);
x_38 = lean_ctor_get(x_35, 1);
x_39 = lean_array_get(x_29, x_24, x_21);
lean_dec(x_24);
x_40 = l_Lean_Name_mkStr2(x_30, x_31);
x_41 = lean_box(0);
x_42 = lean_array_push(x_34, x_33);
x_43 = lean_ctor_get(x_39, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_39, 1);
lean_inc(x_44);
lean_dec(x_39);
x_45 = l_Lean_Compiler_LCNF_anyExpr;
lean_ctor_set_tag(x_22, 3);
lean_ctor_set(x_22, 2, x_42);
lean_ctor_set(x_22, 1, x_41);
lean_ctor_set(x_22, 0, x_40);
x_46 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_44);
lean_ctor_set(x_46, 2, x_45);
lean_ctor_set(x_46, 3, x_22);
x_47 = lean_ctor_get(x_37, 0);
lean_inc(x_47);
lean_inc(x_46);
x_48 = l_Lean_Compiler_LCNF_LCtx_addLetDecl(x_47, x_46);
x_49 = lean_ctor_get(x_37, 1);
lean_inc(x_49);
lean_dec(x_37);
lean_ctor_set(x_35, 1, x_49);
lean_ctor_set(x_35, 0, x_48);
x_50 = lean_st_ref_set(x_4, x_35, x_38);
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_50, 1);
x_53 = lean_ctor_get(x_50, 0);
lean_dec(x_53);
x_54 = l_Lean_Compiler_LCNF_Code_toMono(x_25, x_2, x_3, x_4, x_5, x_6, x_52);
if (lean_obj_tag(x_54) == 0)
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_54, 0);
lean_ctor_set(x_50, 1, x_56);
lean_ctor_set(x_50, 0, x_46);
lean_ctor_set(x_54, 0, x_50);
return x_54;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_54, 0);
x_58 = lean_ctor_get(x_54, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_54);
lean_ctor_set(x_50, 1, x_57);
lean_ctor_set(x_50, 0, x_46);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_50);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
else
{
lean_free_object(x_50);
lean_dec(x_46);
return x_54;
}
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_50, 1);
lean_inc(x_60);
lean_dec(x_50);
x_61 = l_Lean_Compiler_LCNF_Code_toMono(x_25, x_2, x_3, x_4, x_5, x_6, x_60);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
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
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_46);
lean_ctor_set(x_65, 1, x_62);
if (lean_is_scalar(x_64)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_64;
}
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_63);
return x_66;
}
else
{
lean_dec(x_46);
return x_61;
}
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_67 = lean_ctor_get(x_35, 0);
x_68 = lean_ctor_get(x_35, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_35);
x_69 = lean_array_get(x_29, x_24, x_21);
lean_dec(x_24);
x_70 = l_Lean_Name_mkStr2(x_30, x_31);
x_71 = lean_box(0);
x_72 = lean_array_push(x_34, x_33);
x_73 = lean_ctor_get(x_69, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_69, 1);
lean_inc(x_74);
lean_dec(x_69);
x_75 = l_Lean_Compiler_LCNF_anyExpr;
lean_ctor_set_tag(x_22, 3);
lean_ctor_set(x_22, 2, x_72);
lean_ctor_set(x_22, 1, x_71);
lean_ctor_set(x_22, 0, x_70);
x_76 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_76, 0, x_73);
lean_ctor_set(x_76, 1, x_74);
lean_ctor_set(x_76, 2, x_75);
lean_ctor_set(x_76, 3, x_22);
x_77 = lean_ctor_get(x_67, 0);
lean_inc(x_77);
lean_inc(x_76);
x_78 = l_Lean_Compiler_LCNF_LCtx_addLetDecl(x_77, x_76);
x_79 = lean_ctor_get(x_67, 1);
lean_inc(x_79);
lean_dec(x_67);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
x_81 = lean_st_ref_set(x_4, x_80, x_68);
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_83 = x_81;
} else {
 lean_dec_ref(x_81);
 x_83 = lean_box(0);
}
x_84 = l_Lean_Compiler_LCNF_Code_toMono(x_25, x_2, x_3, x_4, x_5, x_6, x_82);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_87 = x_84;
} else {
 lean_dec_ref(x_84);
 x_87 = lean_box(0);
}
if (lean_is_scalar(x_83)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_83;
}
lean_ctor_set(x_88, 0, x_76);
lean_ctor_set(x_88, 1, x_85);
if (lean_is_scalar(x_87)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_87;
}
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_86);
return x_89;
}
else
{
lean_dec(x_83);
lean_dec(x_76);
return x_84;
}
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_90 = lean_ctor_get(x_22, 1);
x_91 = lean_ctor_get(x_22, 2);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_22);
x_92 = l_Lean_Compiler_LCNF_eraseParams___redArg(x_90, x_4, x_7);
x_93 = lean_ctor_get(x_92, 1);
lean_inc(x_93);
lean_dec(x_92);
x_94 = l_Lean_Compiler_LCNF_instInhabitedParam;
x_95 = lean_mk_string_unchecked("ByteArray", 9, 9);
x_96 = lean_mk_string_unchecked("data", 4, 4);
x_97 = lean_ctor_get(x_1, 2);
lean_inc(x_97);
x_98 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_98, 0, x_97);
x_99 = lean_mk_empty_array_with_capacity(x_10);
x_100 = lean_st_ref_take(x_4, x_93);
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_103 = x_100;
} else {
 lean_dec_ref(x_100);
 x_103 = lean_box(0);
}
x_104 = lean_array_get(x_94, x_90, x_21);
lean_dec(x_90);
x_105 = l_Lean_Name_mkStr2(x_95, x_96);
x_106 = lean_box(0);
x_107 = lean_array_push(x_99, x_98);
x_108 = lean_ctor_get(x_104, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_104, 1);
lean_inc(x_109);
lean_dec(x_104);
x_110 = l_Lean_Compiler_LCNF_anyExpr;
x_111 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_111, 0, x_105);
lean_ctor_set(x_111, 1, x_106);
lean_ctor_set(x_111, 2, x_107);
x_112 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_112, 0, x_108);
lean_ctor_set(x_112, 1, x_109);
lean_ctor_set(x_112, 2, x_110);
lean_ctor_set(x_112, 3, x_111);
x_113 = lean_ctor_get(x_101, 0);
lean_inc(x_113);
lean_inc(x_112);
x_114 = l_Lean_Compiler_LCNF_LCtx_addLetDecl(x_113, x_112);
x_115 = lean_ctor_get(x_101, 1);
lean_inc(x_115);
lean_dec(x_101);
if (lean_is_scalar(x_103)) {
 x_116 = lean_alloc_ctor(0, 2, 0);
} else {
 x_116 = x_103;
}
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
x_117 = lean_st_ref_set(x_4, x_116, x_102);
x_118 = lean_ctor_get(x_117, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_119 = x_117;
} else {
 lean_dec_ref(x_117);
 x_119 = lean_box(0);
}
x_120 = l_Lean_Compiler_LCNF_Code_toMono(x_91, x_2, x_3, x_4, x_5, x_6, x_118);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 x_123 = x_120;
} else {
 lean_dec_ref(x_120);
 x_123 = lean_box(0);
}
if (lean_is_scalar(x_119)) {
 x_124 = lean_alloc_ctor(0, 2, 0);
} else {
 x_124 = x_119;
}
lean_ctor_set(x_124, 0, x_112);
lean_ctor_set(x_124, 1, x_121);
if (lean_is_scalar(x_123)) {
 x_125 = lean_alloc_ctor(0, 2, 0);
} else {
 x_125 = x_123;
}
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_122);
return x_125;
}
else
{
lean_dec(x_119);
lean_dec(x_112);
return x_120;
}
}
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_dec(x_22);
x_126 = lean_mk_string_unchecked("Lean.Compiler.LCNF.ToMono", 25, 25);
x_127 = lean_mk_string_unchecked("Lean.Compiler.LCNF.casesByteArrayToMono", 39, 39);
x_128 = lean_unsigned_to_nat(175u);
x_129 = lean_unsigned_to_nat(34u);
x_130 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_131 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_126, x_127, x_128, x_129, x_130);
lean_dec(x_130);
lean_dec(x_127);
lean_dec(x_126);
x_132 = l_panic___at___Lean_Compiler_LCNF_trivialStructToMono_spec__0(x_131, x_2, x_3, x_4, x_5, x_6, x_7);
return x_132;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesByteArrayToMono(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg(x_1, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesArrayToMono___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_1, 3);
x_9 = lean_array_get_size(x_8);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_dec_eq(x_9, x_10);
lean_dec(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_mk_string_unchecked("Lean.Compiler.LCNF.ToMono", 25, 25);
x_13 = lean_mk_string_unchecked("Lean.Compiler.LCNF.casesArrayToMono", 35, 35);
x_14 = lean_unsigned_to_nat(163u);
x_15 = lean_unsigned_to_nat(2u);
x_16 = lean_mk_string_unchecked("assertion violation: c.alts.size == 1\n  ", 40, 40);
x_17 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_12, x_13, x_14, x_15, x_16);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_12);
x_18 = l_panic___at___Lean_Compiler_LCNF_trivialStructToMono_spec__0(x_17, x_2, x_3, x_4, x_5, x_6, x_7);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = l_Lean_Compiler_LCNF_instInhabitedCode;
x_20 = l_Lean_Compiler_LCNF_instInhabitedAltCore(lean_box(0), x_19);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_array_get(x_20, x_8, x_21);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_24 = lean_ctor_get(x_22, 1);
x_25 = lean_ctor_get(x_22, 2);
x_26 = lean_ctor_get(x_22, 0);
lean_dec(x_26);
x_27 = l_Lean_Compiler_LCNF_eraseParams___redArg(x_24, x_4, x_7);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = l_Lean_Compiler_LCNF_instInhabitedParam;
x_30 = lean_mk_string_unchecked("Array", 5, 5);
x_31 = lean_mk_string_unchecked("toList", 6, 6);
x_32 = lean_box(0);
x_33 = lean_ctor_get(x_1, 2);
lean_inc(x_33);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = lean_unsigned_to_nat(2u);
x_36 = lean_mk_empty_array_with_capacity(x_35);
x_37 = lean_array_push(x_36, x_32);
x_38 = lean_st_ref_take(x_4, x_28);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_40 = lean_ctor_get(x_38, 0);
x_41 = lean_ctor_get(x_38, 1);
x_42 = lean_array_get(x_29, x_24, x_21);
lean_dec(x_24);
x_43 = l_Lean_Name_mkStr2(x_30, x_31);
x_44 = lean_box(0);
x_45 = lean_array_push(x_37, x_34);
x_46 = lean_ctor_get(x_42, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_42, 1);
lean_inc(x_47);
lean_dec(x_42);
x_48 = l_Lean_Compiler_LCNF_anyExpr;
lean_ctor_set_tag(x_22, 3);
lean_ctor_set(x_22, 2, x_45);
lean_ctor_set(x_22, 1, x_44);
lean_ctor_set(x_22, 0, x_43);
x_49 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_47);
lean_ctor_set(x_49, 2, x_48);
lean_ctor_set(x_49, 3, x_22);
x_50 = lean_ctor_get(x_40, 0);
lean_inc(x_50);
lean_inc(x_49);
x_51 = l_Lean_Compiler_LCNF_LCtx_addLetDecl(x_50, x_49);
x_52 = lean_ctor_get(x_40, 1);
lean_inc(x_52);
lean_dec(x_40);
lean_ctor_set(x_38, 1, x_52);
lean_ctor_set(x_38, 0, x_51);
x_53 = lean_st_ref_set(x_4, x_38, x_41);
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_53, 1);
x_56 = lean_ctor_get(x_53, 0);
lean_dec(x_56);
x_57 = l_Lean_Compiler_LCNF_Code_toMono(x_25, x_2, x_3, x_4, x_5, x_6, x_55);
if (lean_obj_tag(x_57) == 0)
{
uint8_t x_58; 
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
lean_object* x_59; 
x_59 = lean_ctor_get(x_57, 0);
lean_ctor_set(x_53, 1, x_59);
lean_ctor_set(x_53, 0, x_49);
lean_ctor_set(x_57, 0, x_53);
return x_57;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_57, 0);
x_61 = lean_ctor_get(x_57, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_57);
lean_ctor_set(x_53, 1, x_60);
lean_ctor_set(x_53, 0, x_49);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_53);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
else
{
lean_free_object(x_53);
lean_dec(x_49);
return x_57;
}
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_53, 1);
lean_inc(x_63);
lean_dec(x_53);
x_64 = l_Lean_Compiler_LCNF_Code_toMono(x_25, x_2, x_3, x_4, x_5, x_6, x_63);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
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
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_49);
lean_ctor_set(x_68, 1, x_65);
if (lean_is_scalar(x_67)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_67;
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_66);
return x_69;
}
else
{
lean_dec(x_49);
return x_64;
}
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_70 = lean_ctor_get(x_38, 0);
x_71 = lean_ctor_get(x_38, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_38);
x_72 = lean_array_get(x_29, x_24, x_21);
lean_dec(x_24);
x_73 = l_Lean_Name_mkStr2(x_30, x_31);
x_74 = lean_box(0);
x_75 = lean_array_push(x_37, x_34);
x_76 = lean_ctor_get(x_72, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_72, 1);
lean_inc(x_77);
lean_dec(x_72);
x_78 = l_Lean_Compiler_LCNF_anyExpr;
lean_ctor_set_tag(x_22, 3);
lean_ctor_set(x_22, 2, x_75);
lean_ctor_set(x_22, 1, x_74);
lean_ctor_set(x_22, 0, x_73);
x_79 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_79, 0, x_76);
lean_ctor_set(x_79, 1, x_77);
lean_ctor_set(x_79, 2, x_78);
lean_ctor_set(x_79, 3, x_22);
x_80 = lean_ctor_get(x_70, 0);
lean_inc(x_80);
lean_inc(x_79);
x_81 = l_Lean_Compiler_LCNF_LCtx_addLetDecl(x_80, x_79);
x_82 = lean_ctor_get(x_70, 1);
lean_inc(x_82);
lean_dec(x_70);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
x_84 = lean_st_ref_set(x_4, x_83, x_71);
x_85 = lean_ctor_get(x_84, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_86 = x_84;
} else {
 lean_dec_ref(x_84);
 x_86 = lean_box(0);
}
x_87 = l_Lean_Compiler_LCNF_Code_toMono(x_25, x_2, x_3, x_4, x_5, x_6, x_85);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_90 = x_87;
} else {
 lean_dec_ref(x_87);
 x_90 = lean_box(0);
}
if (lean_is_scalar(x_86)) {
 x_91 = lean_alloc_ctor(0, 2, 0);
} else {
 x_91 = x_86;
}
lean_ctor_set(x_91, 0, x_79);
lean_ctor_set(x_91, 1, x_88);
if (lean_is_scalar(x_90)) {
 x_92 = lean_alloc_ctor(0, 2, 0);
} else {
 x_92 = x_90;
}
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_89);
return x_92;
}
else
{
lean_dec(x_86);
lean_dec(x_79);
return x_87;
}
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_93 = lean_ctor_get(x_22, 1);
x_94 = lean_ctor_get(x_22, 2);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_22);
x_95 = l_Lean_Compiler_LCNF_eraseParams___redArg(x_93, x_4, x_7);
x_96 = lean_ctor_get(x_95, 1);
lean_inc(x_96);
lean_dec(x_95);
x_97 = l_Lean_Compiler_LCNF_instInhabitedParam;
x_98 = lean_mk_string_unchecked("Array", 5, 5);
x_99 = lean_mk_string_unchecked("toList", 6, 6);
x_100 = lean_box(0);
x_101 = lean_ctor_get(x_1, 2);
lean_inc(x_101);
x_102 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_102, 0, x_101);
x_103 = lean_unsigned_to_nat(2u);
x_104 = lean_mk_empty_array_with_capacity(x_103);
x_105 = lean_array_push(x_104, x_100);
x_106 = lean_st_ref_take(x_4, x_96);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 x_109 = x_106;
} else {
 lean_dec_ref(x_106);
 x_109 = lean_box(0);
}
x_110 = lean_array_get(x_97, x_93, x_21);
lean_dec(x_93);
x_111 = l_Lean_Name_mkStr2(x_98, x_99);
x_112 = lean_box(0);
x_113 = lean_array_push(x_105, x_102);
x_114 = lean_ctor_get(x_110, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_110, 1);
lean_inc(x_115);
lean_dec(x_110);
x_116 = l_Lean_Compiler_LCNF_anyExpr;
x_117 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_117, 0, x_111);
lean_ctor_set(x_117, 1, x_112);
lean_ctor_set(x_117, 2, x_113);
x_118 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_118, 0, x_114);
lean_ctor_set(x_118, 1, x_115);
lean_ctor_set(x_118, 2, x_116);
lean_ctor_set(x_118, 3, x_117);
x_119 = lean_ctor_get(x_107, 0);
lean_inc(x_119);
lean_inc(x_118);
x_120 = l_Lean_Compiler_LCNF_LCtx_addLetDecl(x_119, x_118);
x_121 = lean_ctor_get(x_107, 1);
lean_inc(x_121);
lean_dec(x_107);
if (lean_is_scalar(x_109)) {
 x_122 = lean_alloc_ctor(0, 2, 0);
} else {
 x_122 = x_109;
}
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
x_123 = lean_st_ref_set(x_4, x_122, x_108);
x_124 = lean_ctor_get(x_123, 1);
lean_inc(x_124);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 x_125 = x_123;
} else {
 lean_dec_ref(x_123);
 x_125 = lean_box(0);
}
x_126 = l_Lean_Compiler_LCNF_Code_toMono(x_94, x_2, x_3, x_4, x_5, x_6, x_124);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 x_129 = x_126;
} else {
 lean_dec_ref(x_126);
 x_129 = lean_box(0);
}
if (lean_is_scalar(x_125)) {
 x_130 = lean_alloc_ctor(0, 2, 0);
} else {
 x_130 = x_125;
}
lean_ctor_set(x_130, 0, x_118);
lean_ctor_set(x_130, 1, x_127);
if (lean_is_scalar(x_129)) {
 x_131 = lean_alloc_ctor(0, 2, 0);
} else {
 x_131 = x_129;
}
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_128);
return x_131;
}
else
{
lean_dec(x_125);
lean_dec(x_118);
return x_126;
}
}
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
lean_dec(x_22);
x_132 = lean_mk_string_unchecked("Lean.Compiler.LCNF.ToMono", 25, 25);
x_133 = lean_mk_string_unchecked("Lean.Compiler.LCNF.casesArrayToMono", 35, 35);
x_134 = lean_unsigned_to_nat(164u);
x_135 = lean_unsigned_to_nat(34u);
x_136 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_137 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_132, x_133, x_134, x_135, x_136);
lean_dec(x_136);
lean_dec(x_133);
lean_dec(x_132);
x_138 = l_panic___at___Lean_Compiler_LCNF_trivialStructToMono_spec__0(x_137, x_2, x_3, x_4, x_5, x_6, x_7);
return x_138;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesArrayToMono(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_casesArrayToMono___redArg(x_1, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesUIntToMono___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_1, 3);
x_10 = lean_array_get_size(x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_dec_eq(x_10, x_11);
lean_dec(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_2);
x_13 = lean_mk_string_unchecked("Lean.Compiler.LCNF.ToMono", 25, 25);
x_14 = lean_mk_string_unchecked("Lean.Compiler.LCNF.casesUIntToMono", 34, 34);
x_15 = lean_unsigned_to_nat(152u);
x_16 = lean_unsigned_to_nat(2u);
x_17 = lean_mk_string_unchecked("assertion violation: c.alts.size == 1\n  ", 40, 40);
x_18 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_13, x_14, x_15, x_16, x_17);
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_13);
x_19 = l_panic___at___Lean_Compiler_LCNF_trivialStructToMono_spec__0(x_18, x_3, x_4, x_5, x_6, x_7, x_8);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = l_Lean_Compiler_LCNF_instInhabitedCode;
x_21 = l_Lean_Compiler_LCNF_instInhabitedAltCore(lean_box(0), x_20);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_array_get(x_21, x_9, x_22);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_25 = lean_ctor_get(x_23, 1);
x_26 = lean_ctor_get(x_23, 2);
x_27 = lean_ctor_get(x_23, 0);
lean_dec(x_27);
x_28 = l_Lean_Compiler_LCNF_eraseParams___redArg(x_25, x_5, x_8);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = l_Lean_Compiler_LCNF_instInhabitedParam;
x_31 = lean_mk_string_unchecked("toBitVec", 8, 8);
x_32 = lean_ctor_get(x_1, 2);
lean_inc(x_32);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = lean_mk_empty_array_with_capacity(x_11);
x_35 = lean_st_ref_take(x_5, x_29);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_37 = lean_ctor_get(x_35, 0);
x_38 = lean_ctor_get(x_35, 1);
x_39 = lean_array_get(x_30, x_25, x_22);
lean_dec(x_25);
x_40 = l_Lean_Name_str___override(x_2, x_31);
x_41 = lean_box(0);
x_42 = lean_array_push(x_34, x_33);
x_43 = lean_ctor_get(x_39, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_39, 1);
lean_inc(x_44);
lean_dec(x_39);
x_45 = l_Lean_Compiler_LCNF_anyExpr;
lean_ctor_set_tag(x_23, 3);
lean_ctor_set(x_23, 2, x_42);
lean_ctor_set(x_23, 1, x_41);
lean_ctor_set(x_23, 0, x_40);
x_46 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_44);
lean_ctor_set(x_46, 2, x_45);
lean_ctor_set(x_46, 3, x_23);
x_47 = lean_ctor_get(x_37, 0);
lean_inc(x_47);
lean_inc(x_46);
x_48 = l_Lean_Compiler_LCNF_LCtx_addLetDecl(x_47, x_46);
x_49 = lean_ctor_get(x_37, 1);
lean_inc(x_49);
lean_dec(x_37);
lean_ctor_set(x_35, 1, x_49);
lean_ctor_set(x_35, 0, x_48);
x_50 = lean_st_ref_set(x_5, x_35, x_38);
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_50, 1);
x_53 = lean_ctor_get(x_50, 0);
lean_dec(x_53);
x_54 = l_Lean_Compiler_LCNF_Code_toMono(x_26, x_3, x_4, x_5, x_6, x_7, x_52);
if (lean_obj_tag(x_54) == 0)
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_54, 0);
lean_ctor_set(x_50, 1, x_56);
lean_ctor_set(x_50, 0, x_46);
lean_ctor_set(x_54, 0, x_50);
return x_54;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_54, 0);
x_58 = lean_ctor_get(x_54, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_54);
lean_ctor_set(x_50, 1, x_57);
lean_ctor_set(x_50, 0, x_46);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_50);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
else
{
lean_free_object(x_50);
lean_dec(x_46);
return x_54;
}
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_50, 1);
lean_inc(x_60);
lean_dec(x_50);
x_61 = l_Lean_Compiler_LCNF_Code_toMono(x_26, x_3, x_4, x_5, x_6, x_7, x_60);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
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
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_46);
lean_ctor_set(x_65, 1, x_62);
if (lean_is_scalar(x_64)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_64;
}
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_63);
return x_66;
}
else
{
lean_dec(x_46);
return x_61;
}
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_67 = lean_ctor_get(x_35, 0);
x_68 = lean_ctor_get(x_35, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_35);
x_69 = lean_array_get(x_30, x_25, x_22);
lean_dec(x_25);
x_70 = l_Lean_Name_str___override(x_2, x_31);
x_71 = lean_box(0);
x_72 = lean_array_push(x_34, x_33);
x_73 = lean_ctor_get(x_69, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_69, 1);
lean_inc(x_74);
lean_dec(x_69);
x_75 = l_Lean_Compiler_LCNF_anyExpr;
lean_ctor_set_tag(x_23, 3);
lean_ctor_set(x_23, 2, x_72);
lean_ctor_set(x_23, 1, x_71);
lean_ctor_set(x_23, 0, x_70);
x_76 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_76, 0, x_73);
lean_ctor_set(x_76, 1, x_74);
lean_ctor_set(x_76, 2, x_75);
lean_ctor_set(x_76, 3, x_23);
x_77 = lean_ctor_get(x_67, 0);
lean_inc(x_77);
lean_inc(x_76);
x_78 = l_Lean_Compiler_LCNF_LCtx_addLetDecl(x_77, x_76);
x_79 = lean_ctor_get(x_67, 1);
lean_inc(x_79);
lean_dec(x_67);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
x_81 = lean_st_ref_set(x_5, x_80, x_68);
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_83 = x_81;
} else {
 lean_dec_ref(x_81);
 x_83 = lean_box(0);
}
x_84 = l_Lean_Compiler_LCNF_Code_toMono(x_26, x_3, x_4, x_5, x_6, x_7, x_82);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_87 = x_84;
} else {
 lean_dec_ref(x_84);
 x_87 = lean_box(0);
}
if (lean_is_scalar(x_83)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_83;
}
lean_ctor_set(x_88, 0, x_76);
lean_ctor_set(x_88, 1, x_85);
if (lean_is_scalar(x_87)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_87;
}
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_86);
return x_89;
}
else
{
lean_dec(x_83);
lean_dec(x_76);
return x_84;
}
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_90 = lean_ctor_get(x_23, 1);
x_91 = lean_ctor_get(x_23, 2);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_23);
x_92 = l_Lean_Compiler_LCNF_eraseParams___redArg(x_90, x_5, x_8);
x_93 = lean_ctor_get(x_92, 1);
lean_inc(x_93);
lean_dec(x_92);
x_94 = l_Lean_Compiler_LCNF_instInhabitedParam;
x_95 = lean_mk_string_unchecked("toBitVec", 8, 8);
x_96 = lean_ctor_get(x_1, 2);
lean_inc(x_96);
x_97 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_97, 0, x_96);
x_98 = lean_mk_empty_array_with_capacity(x_11);
x_99 = lean_st_ref_take(x_5, x_93);
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
x_103 = lean_array_get(x_94, x_90, x_22);
lean_dec(x_90);
x_104 = l_Lean_Name_str___override(x_2, x_95);
x_105 = lean_box(0);
x_106 = lean_array_push(x_98, x_97);
x_107 = lean_ctor_get(x_103, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_103, 1);
lean_inc(x_108);
lean_dec(x_103);
x_109 = l_Lean_Compiler_LCNF_anyExpr;
x_110 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_110, 0, x_104);
lean_ctor_set(x_110, 1, x_105);
lean_ctor_set(x_110, 2, x_106);
x_111 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_111, 0, x_107);
lean_ctor_set(x_111, 1, x_108);
lean_ctor_set(x_111, 2, x_109);
lean_ctor_set(x_111, 3, x_110);
x_112 = lean_ctor_get(x_100, 0);
lean_inc(x_112);
lean_inc(x_111);
x_113 = l_Lean_Compiler_LCNF_LCtx_addLetDecl(x_112, x_111);
x_114 = lean_ctor_get(x_100, 1);
lean_inc(x_114);
lean_dec(x_100);
if (lean_is_scalar(x_102)) {
 x_115 = lean_alloc_ctor(0, 2, 0);
} else {
 x_115 = x_102;
}
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
x_116 = lean_st_ref_set(x_5, x_115, x_101);
x_117 = lean_ctor_get(x_116, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_118 = x_116;
} else {
 lean_dec_ref(x_116);
 x_118 = lean_box(0);
}
x_119 = l_Lean_Compiler_LCNF_Code_toMono(x_91, x_3, x_4, x_5, x_6, x_7, x_117);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_122 = x_119;
} else {
 lean_dec_ref(x_119);
 x_122 = lean_box(0);
}
if (lean_is_scalar(x_118)) {
 x_123 = lean_alloc_ctor(0, 2, 0);
} else {
 x_123 = x_118;
}
lean_ctor_set(x_123, 0, x_111);
lean_ctor_set(x_123, 1, x_120);
if (lean_is_scalar(x_122)) {
 x_124 = lean_alloc_ctor(0, 2, 0);
} else {
 x_124 = x_122;
}
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_121);
return x_124;
}
else
{
lean_dec(x_118);
lean_dec(x_111);
return x_119;
}
}
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_dec(x_23);
lean_dec(x_2);
x_125 = lean_mk_string_unchecked("Lean.Compiler.LCNF.ToMono", 25, 25);
x_126 = lean_mk_string_unchecked("Lean.Compiler.LCNF.casesUIntToMono", 34, 34);
x_127 = lean_unsigned_to_nat(153u);
x_128 = lean_unsigned_to_nat(34u);
x_129 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_130 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_125, x_126, x_127, x_128, x_129);
lean_dec(x_129);
lean_dec(x_126);
lean_dec(x_125);
x_131 = l_panic___at___Lean_Compiler_LCNF_trivialStructToMono_spec__0(x_130, x_3, x_4, x_5, x_6, x_7, x_8);
return x_131;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesUIntToMono(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_casesUIntToMono___redArg(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_casesIntToMono_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_3, x_2);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_array_uget(x_4, x_3);
x_14 = lean_box(0);
x_15 = lean_array_uset(x_4, x_3, x_14);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_13);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_25 = lean_ctor_get(x_13, 0);
x_26 = lean_ctor_get(x_13, 1);
x_27 = lean_ctor_get(x_13, 2);
x_28 = l_Lean_Compiler_LCNF_eraseParams___redArg(x_26, x_7, x_10);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_ctor_get(x_1, 2);
x_31 = lean_mk_string_unchecked("Nat", 3, 3);
lean_inc(x_31);
x_32 = l_Lean_Name_mkStr1(x_31);
x_33 = l_Lean_Compiler_LCNF_instInhabitedParam;
x_34 = lean_unsigned_to_nat(0u);
x_35 = lean_mk_string_unchecked("Int", 3, 3);
lean_inc(x_30);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_30);
x_37 = lean_box(0);
x_38 = l_Lean_Expr_const___override(x_32, x_37);
x_39 = lean_mk_string_unchecked("Bool", 4, 4);
x_40 = lean_array_get(x_33, x_26, x_34);
lean_dec(x_26);
x_41 = lean_mk_string_unchecked("negSucc", 7, 7);
lean_inc(x_35);
x_42 = l_Lean_Name_mkStr2(x_35, x_41);
x_43 = lean_name_eq(x_25, x_42);
lean_dec(x_42);
lean_dec(x_25);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
lean_dec(x_31);
x_44 = lean_mk_string_unchecked("natAbs", 6, 6);
x_45 = lean_unsigned_to_nat(1u);
x_46 = lean_mk_empty_array_with_capacity(x_45);
x_47 = lean_st_ref_take(x_7, x_29);
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_49 = lean_ctor_get(x_47, 0);
x_50 = lean_ctor_get(x_47, 1);
x_51 = l_Lean_Name_mkStr2(x_35, x_44);
x_52 = lean_array_push(x_46, x_36);
x_53 = lean_ctor_get(x_40, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_40, 1);
lean_inc(x_54);
lean_dec(x_40);
x_55 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_55, 0, x_51);
lean_ctor_set(x_55, 1, x_37);
lean_ctor_set(x_55, 2, x_52);
x_56 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_56, 0, x_53);
lean_ctor_set(x_56, 1, x_54);
lean_ctor_set(x_56, 2, x_38);
lean_ctor_set(x_56, 3, x_55);
x_57 = lean_ctor_get(x_49, 0);
lean_inc(x_57);
lean_inc(x_56);
x_58 = l_Lean_Compiler_LCNF_LCtx_addLetDecl(x_57, x_56);
x_59 = lean_ctor_get(x_49, 1);
lean_inc(x_59);
lean_dec(x_49);
lean_ctor_set(x_47, 1, x_59);
lean_ctor_set(x_47, 0, x_58);
x_60 = lean_st_ref_set(x_7, x_47, x_50);
x_61 = !lean_is_exclusive(x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_60, 1);
x_63 = lean_ctor_get(x_60, 0);
lean_dec(x_63);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_64 = l_Lean_Compiler_LCNF_Code_toMono(x_27, x_5, x_6, x_7, x_8, x_9, x_62);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = lean_mk_string_unchecked("false", 5, 5);
x_68 = l_Lean_Name_mkStr2(x_39, x_67);
x_69 = lean_mk_empty_array_with_capacity(x_34);
lean_ctor_set(x_60, 1, x_65);
lean_ctor_set(x_60, 0, x_56);
lean_ctor_set(x_13, 2, x_60);
lean_ctor_set(x_13, 1, x_69);
lean_ctor_set(x_13, 0, x_68);
x_16 = x_13;
x_17 = x_66;
goto block_23;
}
else
{
uint8_t x_70; 
lean_free_object(x_60);
lean_dec(x_56);
lean_dec(x_39);
lean_free_object(x_13);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_70 = !lean_is_exclusive(x_64);
if (x_70 == 0)
{
return x_64;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_64, 0);
x_72 = lean_ctor_get(x_64, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_64);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
else
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_60, 1);
lean_inc(x_74);
lean_dec(x_60);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_75 = l_Lean_Compiler_LCNF_Code_toMono(x_27, x_5, x_6, x_7, x_8, x_9, x_74);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
x_78 = lean_mk_string_unchecked("false", 5, 5);
x_79 = l_Lean_Name_mkStr2(x_39, x_78);
x_80 = lean_mk_empty_array_with_capacity(x_34);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_56);
lean_ctor_set(x_81, 1, x_76);
lean_ctor_set(x_13, 2, x_81);
lean_ctor_set(x_13, 1, x_80);
lean_ctor_set(x_13, 0, x_79);
x_16 = x_13;
x_17 = x_77;
goto block_23;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_56);
lean_dec(x_39);
lean_free_object(x_13);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_82 = lean_ctor_get(x_75, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_75, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_84 = x_75;
} else {
 lean_dec_ref(x_75);
 x_84 = lean_box(0);
}
if (lean_is_scalar(x_84)) {
 x_85 = lean_alloc_ctor(1, 2, 0);
} else {
 x_85 = x_84;
}
lean_ctor_set(x_85, 0, x_82);
lean_ctor_set(x_85, 1, x_83);
return x_85;
}
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_86 = lean_ctor_get(x_47, 0);
x_87 = lean_ctor_get(x_47, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_47);
x_88 = l_Lean_Name_mkStr2(x_35, x_44);
x_89 = lean_array_push(x_46, x_36);
x_90 = lean_ctor_get(x_40, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_40, 1);
lean_inc(x_91);
lean_dec(x_40);
x_92 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_92, 0, x_88);
lean_ctor_set(x_92, 1, x_37);
lean_ctor_set(x_92, 2, x_89);
x_93 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_93, 0, x_90);
lean_ctor_set(x_93, 1, x_91);
lean_ctor_set(x_93, 2, x_38);
lean_ctor_set(x_93, 3, x_92);
x_94 = lean_ctor_get(x_86, 0);
lean_inc(x_94);
lean_inc(x_93);
x_95 = l_Lean_Compiler_LCNF_LCtx_addLetDecl(x_94, x_93);
x_96 = lean_ctor_get(x_86, 1);
lean_inc(x_96);
lean_dec(x_86);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
x_98 = lean_st_ref_set(x_7, x_97, x_87);
x_99 = lean_ctor_get(x_98, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_100 = x_98;
} else {
 lean_dec_ref(x_98);
 x_100 = lean_box(0);
}
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_101 = l_Lean_Compiler_LCNF_Code_toMono(x_27, x_5, x_6, x_7, x_8, x_9, x_99);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
lean_dec(x_101);
x_104 = lean_mk_string_unchecked("false", 5, 5);
x_105 = l_Lean_Name_mkStr2(x_39, x_104);
x_106 = lean_mk_empty_array_with_capacity(x_34);
if (lean_is_scalar(x_100)) {
 x_107 = lean_alloc_ctor(0, 2, 0);
} else {
 x_107 = x_100;
}
lean_ctor_set(x_107, 0, x_93);
lean_ctor_set(x_107, 1, x_102);
lean_ctor_set(x_13, 2, x_107);
lean_ctor_set(x_13, 1, x_106);
lean_ctor_set(x_13, 0, x_105);
x_16 = x_13;
x_17 = x_103;
goto block_23;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
lean_dec(x_100);
lean_dec(x_93);
lean_dec(x_39);
lean_free_object(x_13);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_108 = lean_ctor_get(x_101, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_101, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_110 = x_101;
} else {
 lean_dec_ref(x_101);
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
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; 
x_112 = lean_mk_string_unchecked("abs", 3, 3);
x_113 = l_Lean_Name_mkStr1(x_112);
x_114 = lean_mk_string_unchecked("natAbs", 6, 6);
x_115 = l_Lean_Name_mkStr2(x_35, x_114);
x_116 = lean_unsigned_to_nat(1u);
x_117 = lean_mk_empty_array_with_capacity(x_116);
x_118 = lean_array_push(x_117, x_36);
x_119 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_119, 0, x_115);
lean_ctor_set(x_119, 1, x_37);
lean_ctor_set(x_119, 2, x_118);
lean_inc(x_38);
x_120 = l_Lean_Compiler_LCNF_mkLetDecl(x_113, x_38, x_119, x_6, x_7, x_8, x_9, x_29);
x_121 = !lean_is_exclusive(x_120);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; uint8_t x_129; 
x_122 = lean_ctor_get(x_120, 0);
x_123 = lean_ctor_get(x_120, 1);
x_124 = lean_mk_string_unchecked("one", 3, 3);
x_125 = l_Lean_Name_mkStr1(x_124);
x_126 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_126, 0, x_116);
x_127 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_127, 0, x_126);
lean_inc(x_38);
x_128 = l_Lean_Compiler_LCNF_mkLetDecl(x_125, x_38, x_127, x_6, x_7, x_8, x_9, x_123);
x_129 = !lean_is_exclusive(x_128);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; 
x_130 = lean_ctor_get(x_128, 0);
x_131 = lean_ctor_get(x_128, 1);
x_132 = lean_mk_string_unchecked("sub", 3, 3);
x_133 = lean_ctor_get(x_122, 0);
lean_inc(x_133);
x_134 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_134, 0, x_133);
x_135 = lean_ctor_get(x_130, 0);
lean_inc(x_135);
x_136 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_136, 0, x_135);
x_137 = lean_unsigned_to_nat(2u);
x_138 = lean_mk_empty_array_with_capacity(x_137);
x_139 = lean_array_push(x_138, x_134);
x_140 = lean_st_ref_take(x_7, x_131);
x_141 = !lean_is_exclusive(x_140);
if (x_141 == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; 
x_142 = lean_ctor_get(x_140, 0);
x_143 = lean_ctor_get(x_140, 1);
x_144 = l_Lean_Name_mkStr2(x_31, x_132);
x_145 = lean_array_push(x_139, x_136);
x_146 = lean_ctor_get(x_40, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_40, 1);
lean_inc(x_147);
lean_dec(x_40);
x_148 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_148, 0, x_144);
lean_ctor_set(x_148, 1, x_37);
lean_ctor_set(x_148, 2, x_145);
x_149 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_149, 0, x_146);
lean_ctor_set(x_149, 1, x_147);
lean_ctor_set(x_149, 2, x_38);
lean_ctor_set(x_149, 3, x_148);
x_150 = lean_ctor_get(x_142, 0);
lean_inc(x_150);
lean_inc(x_149);
x_151 = l_Lean_Compiler_LCNF_LCtx_addLetDecl(x_150, x_149);
x_152 = lean_ctor_get(x_142, 1);
lean_inc(x_152);
lean_dec(x_142);
lean_ctor_set(x_140, 1, x_152);
lean_ctor_set(x_140, 0, x_151);
x_153 = lean_st_ref_set(x_7, x_140, x_143);
x_154 = !lean_is_exclusive(x_153);
if (x_154 == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_155 = lean_ctor_get(x_153, 1);
x_156 = lean_ctor_get(x_153, 0);
lean_dec(x_156);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_157 = l_Lean_Compiler_LCNF_Code_toMono(x_27, x_5, x_6, x_7, x_8, x_9, x_155);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_157, 1);
lean_inc(x_159);
lean_dec(x_157);
x_160 = lean_mk_string_unchecked("true", 4, 4);
x_161 = l_Lean_Name_mkStr2(x_39, x_160);
x_162 = lean_mk_empty_array_with_capacity(x_34);
lean_ctor_set(x_153, 1, x_158);
lean_ctor_set(x_153, 0, x_149);
lean_ctor_set(x_128, 1, x_153);
lean_ctor_set(x_120, 1, x_128);
lean_ctor_set(x_13, 2, x_120);
lean_ctor_set(x_13, 1, x_162);
lean_ctor_set(x_13, 0, x_161);
x_16 = x_13;
x_17 = x_159;
goto block_23;
}
else
{
uint8_t x_163; 
lean_free_object(x_153);
lean_dec(x_149);
lean_free_object(x_128);
lean_dec(x_130);
lean_free_object(x_120);
lean_dec(x_122);
lean_dec(x_39);
lean_free_object(x_13);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_163 = !lean_is_exclusive(x_157);
if (x_163 == 0)
{
return x_157;
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_164 = lean_ctor_get(x_157, 0);
x_165 = lean_ctor_get(x_157, 1);
lean_inc(x_165);
lean_inc(x_164);
lean_dec(x_157);
x_166 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_166, 0, x_164);
lean_ctor_set(x_166, 1, x_165);
return x_166;
}
}
}
else
{
lean_object* x_167; lean_object* x_168; 
x_167 = lean_ctor_get(x_153, 1);
lean_inc(x_167);
lean_dec(x_153);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_168 = l_Lean_Compiler_LCNF_Code_toMono(x_27, x_5, x_6, x_7, x_8, x_9, x_167);
if (lean_obj_tag(x_168) == 0)
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_168, 1);
lean_inc(x_170);
lean_dec(x_168);
x_171 = lean_mk_string_unchecked("true", 4, 4);
x_172 = l_Lean_Name_mkStr2(x_39, x_171);
x_173 = lean_mk_empty_array_with_capacity(x_34);
x_174 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_174, 0, x_149);
lean_ctor_set(x_174, 1, x_169);
lean_ctor_set(x_128, 1, x_174);
lean_ctor_set(x_120, 1, x_128);
lean_ctor_set(x_13, 2, x_120);
lean_ctor_set(x_13, 1, x_173);
lean_ctor_set(x_13, 0, x_172);
x_16 = x_13;
x_17 = x_170;
goto block_23;
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
lean_dec(x_149);
lean_free_object(x_128);
lean_dec(x_130);
lean_free_object(x_120);
lean_dec(x_122);
lean_dec(x_39);
lean_free_object(x_13);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_175 = lean_ctor_get(x_168, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_168, 1);
lean_inc(x_176);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 lean_ctor_release(x_168, 1);
 x_177 = x_168;
} else {
 lean_dec_ref(x_168);
 x_177 = lean_box(0);
}
if (lean_is_scalar(x_177)) {
 x_178 = lean_alloc_ctor(1, 2, 0);
} else {
 x_178 = x_177;
}
lean_ctor_set(x_178, 0, x_175);
lean_ctor_set(x_178, 1, x_176);
return x_178;
}
}
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_179 = lean_ctor_get(x_140, 0);
x_180 = lean_ctor_get(x_140, 1);
lean_inc(x_180);
lean_inc(x_179);
lean_dec(x_140);
x_181 = l_Lean_Name_mkStr2(x_31, x_132);
x_182 = lean_array_push(x_139, x_136);
x_183 = lean_ctor_get(x_40, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_40, 1);
lean_inc(x_184);
lean_dec(x_40);
x_185 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_185, 0, x_181);
lean_ctor_set(x_185, 1, x_37);
lean_ctor_set(x_185, 2, x_182);
x_186 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_186, 0, x_183);
lean_ctor_set(x_186, 1, x_184);
lean_ctor_set(x_186, 2, x_38);
lean_ctor_set(x_186, 3, x_185);
x_187 = lean_ctor_get(x_179, 0);
lean_inc(x_187);
lean_inc(x_186);
x_188 = l_Lean_Compiler_LCNF_LCtx_addLetDecl(x_187, x_186);
x_189 = lean_ctor_get(x_179, 1);
lean_inc(x_189);
lean_dec(x_179);
x_190 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_190, 0, x_188);
lean_ctor_set(x_190, 1, x_189);
x_191 = lean_st_ref_set(x_7, x_190, x_180);
x_192 = lean_ctor_get(x_191, 1);
lean_inc(x_192);
if (lean_is_exclusive(x_191)) {
 lean_ctor_release(x_191, 0);
 lean_ctor_release(x_191, 1);
 x_193 = x_191;
} else {
 lean_dec_ref(x_191);
 x_193 = lean_box(0);
}
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_194 = l_Lean_Compiler_LCNF_Code_toMono(x_27, x_5, x_6, x_7, x_8, x_9, x_192);
if (lean_obj_tag(x_194) == 0)
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_195 = lean_ctor_get(x_194, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_194, 1);
lean_inc(x_196);
lean_dec(x_194);
x_197 = lean_mk_string_unchecked("true", 4, 4);
x_198 = l_Lean_Name_mkStr2(x_39, x_197);
x_199 = lean_mk_empty_array_with_capacity(x_34);
if (lean_is_scalar(x_193)) {
 x_200 = lean_alloc_ctor(0, 2, 0);
} else {
 x_200 = x_193;
}
lean_ctor_set(x_200, 0, x_186);
lean_ctor_set(x_200, 1, x_195);
lean_ctor_set(x_128, 1, x_200);
lean_ctor_set(x_120, 1, x_128);
lean_ctor_set(x_13, 2, x_120);
lean_ctor_set(x_13, 1, x_199);
lean_ctor_set(x_13, 0, x_198);
x_16 = x_13;
x_17 = x_196;
goto block_23;
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
lean_dec(x_193);
lean_dec(x_186);
lean_free_object(x_128);
lean_dec(x_130);
lean_free_object(x_120);
lean_dec(x_122);
lean_dec(x_39);
lean_free_object(x_13);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_201 = lean_ctor_get(x_194, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_194, 1);
lean_inc(x_202);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 lean_ctor_release(x_194, 1);
 x_203 = x_194;
} else {
 lean_dec_ref(x_194);
 x_203 = lean_box(0);
}
if (lean_is_scalar(x_203)) {
 x_204 = lean_alloc_ctor(1, 2, 0);
} else {
 x_204 = x_203;
}
lean_ctor_set(x_204, 0, x_201);
lean_ctor_set(x_204, 1, x_202);
return x_204;
}
}
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_205 = lean_ctor_get(x_128, 0);
x_206 = lean_ctor_get(x_128, 1);
lean_inc(x_206);
lean_inc(x_205);
lean_dec(x_128);
x_207 = lean_mk_string_unchecked("sub", 3, 3);
x_208 = lean_ctor_get(x_122, 0);
lean_inc(x_208);
x_209 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_209, 0, x_208);
x_210 = lean_ctor_get(x_205, 0);
lean_inc(x_210);
x_211 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_211, 0, x_210);
x_212 = lean_unsigned_to_nat(2u);
x_213 = lean_mk_empty_array_with_capacity(x_212);
x_214 = lean_array_push(x_213, x_209);
x_215 = lean_st_ref_take(x_7, x_206);
x_216 = lean_ctor_get(x_215, 0);
lean_inc(x_216);
x_217 = lean_ctor_get(x_215, 1);
lean_inc(x_217);
if (lean_is_exclusive(x_215)) {
 lean_ctor_release(x_215, 0);
 lean_ctor_release(x_215, 1);
 x_218 = x_215;
} else {
 lean_dec_ref(x_215);
 x_218 = lean_box(0);
}
x_219 = l_Lean_Name_mkStr2(x_31, x_207);
x_220 = lean_array_push(x_214, x_211);
x_221 = lean_ctor_get(x_40, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_40, 1);
lean_inc(x_222);
lean_dec(x_40);
x_223 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_223, 0, x_219);
lean_ctor_set(x_223, 1, x_37);
lean_ctor_set(x_223, 2, x_220);
x_224 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_224, 0, x_221);
lean_ctor_set(x_224, 1, x_222);
lean_ctor_set(x_224, 2, x_38);
lean_ctor_set(x_224, 3, x_223);
x_225 = lean_ctor_get(x_216, 0);
lean_inc(x_225);
lean_inc(x_224);
x_226 = l_Lean_Compiler_LCNF_LCtx_addLetDecl(x_225, x_224);
x_227 = lean_ctor_get(x_216, 1);
lean_inc(x_227);
lean_dec(x_216);
if (lean_is_scalar(x_218)) {
 x_228 = lean_alloc_ctor(0, 2, 0);
} else {
 x_228 = x_218;
}
lean_ctor_set(x_228, 0, x_226);
lean_ctor_set(x_228, 1, x_227);
x_229 = lean_st_ref_set(x_7, x_228, x_217);
x_230 = lean_ctor_get(x_229, 1);
lean_inc(x_230);
if (lean_is_exclusive(x_229)) {
 lean_ctor_release(x_229, 0);
 lean_ctor_release(x_229, 1);
 x_231 = x_229;
} else {
 lean_dec_ref(x_229);
 x_231 = lean_box(0);
}
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_232 = l_Lean_Compiler_LCNF_Code_toMono(x_27, x_5, x_6, x_7, x_8, x_9, x_230);
if (lean_obj_tag(x_232) == 0)
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_233 = lean_ctor_get(x_232, 0);
lean_inc(x_233);
x_234 = lean_ctor_get(x_232, 1);
lean_inc(x_234);
lean_dec(x_232);
x_235 = lean_mk_string_unchecked("true", 4, 4);
x_236 = l_Lean_Name_mkStr2(x_39, x_235);
x_237 = lean_mk_empty_array_with_capacity(x_34);
if (lean_is_scalar(x_231)) {
 x_238 = lean_alloc_ctor(0, 2, 0);
} else {
 x_238 = x_231;
}
lean_ctor_set(x_238, 0, x_224);
lean_ctor_set(x_238, 1, x_233);
x_239 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_239, 0, x_205);
lean_ctor_set(x_239, 1, x_238);
lean_ctor_set(x_120, 1, x_239);
lean_ctor_set(x_13, 2, x_120);
lean_ctor_set(x_13, 1, x_237);
lean_ctor_set(x_13, 0, x_236);
x_16 = x_13;
x_17 = x_234;
goto block_23;
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; 
lean_dec(x_231);
lean_dec(x_224);
lean_dec(x_205);
lean_free_object(x_120);
lean_dec(x_122);
lean_dec(x_39);
lean_free_object(x_13);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_240 = lean_ctor_get(x_232, 0);
lean_inc(x_240);
x_241 = lean_ctor_get(x_232, 1);
lean_inc(x_241);
if (lean_is_exclusive(x_232)) {
 lean_ctor_release(x_232, 0);
 lean_ctor_release(x_232, 1);
 x_242 = x_232;
} else {
 lean_dec_ref(x_232);
 x_242 = lean_box(0);
}
if (lean_is_scalar(x_242)) {
 x_243 = lean_alloc_ctor(1, 2, 0);
} else {
 x_243 = x_242;
}
lean_ctor_set(x_243, 0, x_240);
lean_ctor_set(x_243, 1, x_241);
return x_243;
}
}
}
else
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; 
x_244 = lean_ctor_get(x_120, 0);
x_245 = lean_ctor_get(x_120, 1);
lean_inc(x_245);
lean_inc(x_244);
lean_dec(x_120);
x_246 = lean_mk_string_unchecked("one", 3, 3);
x_247 = l_Lean_Name_mkStr1(x_246);
x_248 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_248, 0, x_116);
x_249 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_249, 0, x_248);
lean_inc(x_38);
x_250 = l_Lean_Compiler_LCNF_mkLetDecl(x_247, x_38, x_249, x_6, x_7, x_8, x_9, x_245);
x_251 = lean_ctor_get(x_250, 0);
lean_inc(x_251);
x_252 = lean_ctor_get(x_250, 1);
lean_inc(x_252);
if (lean_is_exclusive(x_250)) {
 lean_ctor_release(x_250, 0);
 lean_ctor_release(x_250, 1);
 x_253 = x_250;
} else {
 lean_dec_ref(x_250);
 x_253 = lean_box(0);
}
x_254 = lean_mk_string_unchecked("sub", 3, 3);
x_255 = lean_ctor_get(x_244, 0);
lean_inc(x_255);
x_256 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_256, 0, x_255);
x_257 = lean_ctor_get(x_251, 0);
lean_inc(x_257);
x_258 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_258, 0, x_257);
x_259 = lean_unsigned_to_nat(2u);
x_260 = lean_mk_empty_array_with_capacity(x_259);
x_261 = lean_array_push(x_260, x_256);
x_262 = lean_st_ref_take(x_7, x_252);
x_263 = lean_ctor_get(x_262, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_262, 1);
lean_inc(x_264);
if (lean_is_exclusive(x_262)) {
 lean_ctor_release(x_262, 0);
 lean_ctor_release(x_262, 1);
 x_265 = x_262;
} else {
 lean_dec_ref(x_262);
 x_265 = lean_box(0);
}
x_266 = l_Lean_Name_mkStr2(x_31, x_254);
x_267 = lean_array_push(x_261, x_258);
x_268 = lean_ctor_get(x_40, 0);
lean_inc(x_268);
x_269 = lean_ctor_get(x_40, 1);
lean_inc(x_269);
lean_dec(x_40);
x_270 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_270, 0, x_266);
lean_ctor_set(x_270, 1, x_37);
lean_ctor_set(x_270, 2, x_267);
x_271 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_271, 0, x_268);
lean_ctor_set(x_271, 1, x_269);
lean_ctor_set(x_271, 2, x_38);
lean_ctor_set(x_271, 3, x_270);
x_272 = lean_ctor_get(x_263, 0);
lean_inc(x_272);
lean_inc(x_271);
x_273 = l_Lean_Compiler_LCNF_LCtx_addLetDecl(x_272, x_271);
x_274 = lean_ctor_get(x_263, 1);
lean_inc(x_274);
lean_dec(x_263);
if (lean_is_scalar(x_265)) {
 x_275 = lean_alloc_ctor(0, 2, 0);
} else {
 x_275 = x_265;
}
lean_ctor_set(x_275, 0, x_273);
lean_ctor_set(x_275, 1, x_274);
x_276 = lean_st_ref_set(x_7, x_275, x_264);
x_277 = lean_ctor_get(x_276, 1);
lean_inc(x_277);
if (lean_is_exclusive(x_276)) {
 lean_ctor_release(x_276, 0);
 lean_ctor_release(x_276, 1);
 x_278 = x_276;
} else {
 lean_dec_ref(x_276);
 x_278 = lean_box(0);
}
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_279 = l_Lean_Compiler_LCNF_Code_toMono(x_27, x_5, x_6, x_7, x_8, x_9, x_277);
if (lean_obj_tag(x_279) == 0)
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; 
x_280 = lean_ctor_get(x_279, 0);
lean_inc(x_280);
x_281 = lean_ctor_get(x_279, 1);
lean_inc(x_281);
lean_dec(x_279);
x_282 = lean_mk_string_unchecked("true", 4, 4);
x_283 = l_Lean_Name_mkStr2(x_39, x_282);
x_284 = lean_mk_empty_array_with_capacity(x_34);
if (lean_is_scalar(x_278)) {
 x_285 = lean_alloc_ctor(0, 2, 0);
} else {
 x_285 = x_278;
}
lean_ctor_set(x_285, 0, x_271);
lean_ctor_set(x_285, 1, x_280);
if (lean_is_scalar(x_253)) {
 x_286 = lean_alloc_ctor(0, 2, 0);
} else {
 x_286 = x_253;
}
lean_ctor_set(x_286, 0, x_251);
lean_ctor_set(x_286, 1, x_285);
x_287 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_287, 0, x_244);
lean_ctor_set(x_287, 1, x_286);
lean_ctor_set(x_13, 2, x_287);
lean_ctor_set(x_13, 1, x_284);
lean_ctor_set(x_13, 0, x_283);
x_16 = x_13;
x_17 = x_281;
goto block_23;
}
else
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; 
lean_dec(x_278);
lean_dec(x_271);
lean_dec(x_253);
lean_dec(x_251);
lean_dec(x_244);
lean_dec(x_39);
lean_free_object(x_13);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_288 = lean_ctor_get(x_279, 0);
lean_inc(x_288);
x_289 = lean_ctor_get(x_279, 1);
lean_inc(x_289);
if (lean_is_exclusive(x_279)) {
 lean_ctor_release(x_279, 0);
 lean_ctor_release(x_279, 1);
 x_290 = x_279;
} else {
 lean_dec_ref(x_279);
 x_290 = lean_box(0);
}
if (lean_is_scalar(x_290)) {
 x_291 = lean_alloc_ctor(1, 2, 0);
} else {
 x_291 = x_290;
}
lean_ctor_set(x_291, 0, x_288);
lean_ctor_set(x_291, 1, x_289);
return x_291;
}
}
}
}
else
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; uint8_t x_310; 
x_292 = lean_ctor_get(x_13, 0);
x_293 = lean_ctor_get(x_13, 1);
x_294 = lean_ctor_get(x_13, 2);
lean_inc(x_294);
lean_inc(x_293);
lean_inc(x_292);
lean_dec(x_13);
x_295 = l_Lean_Compiler_LCNF_eraseParams___redArg(x_293, x_7, x_10);
x_296 = lean_ctor_get(x_295, 1);
lean_inc(x_296);
lean_dec(x_295);
x_297 = lean_ctor_get(x_1, 2);
x_298 = lean_mk_string_unchecked("Nat", 3, 3);
lean_inc(x_298);
x_299 = l_Lean_Name_mkStr1(x_298);
x_300 = l_Lean_Compiler_LCNF_instInhabitedParam;
x_301 = lean_unsigned_to_nat(0u);
x_302 = lean_mk_string_unchecked("Int", 3, 3);
lean_inc(x_297);
x_303 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_303, 0, x_297);
x_304 = lean_box(0);
x_305 = l_Lean_Expr_const___override(x_299, x_304);
x_306 = lean_mk_string_unchecked("Bool", 4, 4);
x_307 = lean_array_get(x_300, x_293, x_301);
lean_dec(x_293);
x_308 = lean_mk_string_unchecked("negSucc", 7, 7);
lean_inc(x_302);
x_309 = l_Lean_Name_mkStr2(x_302, x_308);
x_310 = lean_name_eq(x_292, x_309);
lean_dec(x_309);
lean_dec(x_292);
if (x_310 == 0)
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; 
lean_dec(x_298);
x_311 = lean_mk_string_unchecked("natAbs", 6, 6);
x_312 = lean_unsigned_to_nat(1u);
x_313 = lean_mk_empty_array_with_capacity(x_312);
x_314 = lean_st_ref_take(x_7, x_296);
x_315 = lean_ctor_get(x_314, 0);
lean_inc(x_315);
x_316 = lean_ctor_get(x_314, 1);
lean_inc(x_316);
if (lean_is_exclusive(x_314)) {
 lean_ctor_release(x_314, 0);
 lean_ctor_release(x_314, 1);
 x_317 = x_314;
} else {
 lean_dec_ref(x_314);
 x_317 = lean_box(0);
}
x_318 = l_Lean_Name_mkStr2(x_302, x_311);
x_319 = lean_array_push(x_313, x_303);
x_320 = lean_ctor_get(x_307, 0);
lean_inc(x_320);
x_321 = lean_ctor_get(x_307, 1);
lean_inc(x_321);
lean_dec(x_307);
x_322 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_322, 0, x_318);
lean_ctor_set(x_322, 1, x_304);
lean_ctor_set(x_322, 2, x_319);
x_323 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_323, 0, x_320);
lean_ctor_set(x_323, 1, x_321);
lean_ctor_set(x_323, 2, x_305);
lean_ctor_set(x_323, 3, x_322);
x_324 = lean_ctor_get(x_315, 0);
lean_inc(x_324);
lean_inc(x_323);
x_325 = l_Lean_Compiler_LCNF_LCtx_addLetDecl(x_324, x_323);
x_326 = lean_ctor_get(x_315, 1);
lean_inc(x_326);
lean_dec(x_315);
if (lean_is_scalar(x_317)) {
 x_327 = lean_alloc_ctor(0, 2, 0);
} else {
 x_327 = x_317;
}
lean_ctor_set(x_327, 0, x_325);
lean_ctor_set(x_327, 1, x_326);
x_328 = lean_st_ref_set(x_7, x_327, x_316);
x_329 = lean_ctor_get(x_328, 1);
lean_inc(x_329);
if (lean_is_exclusive(x_328)) {
 lean_ctor_release(x_328, 0);
 lean_ctor_release(x_328, 1);
 x_330 = x_328;
} else {
 lean_dec_ref(x_328);
 x_330 = lean_box(0);
}
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_331 = l_Lean_Compiler_LCNF_Code_toMono(x_294, x_5, x_6, x_7, x_8, x_9, x_329);
if (lean_obj_tag(x_331) == 0)
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; 
x_332 = lean_ctor_get(x_331, 0);
lean_inc(x_332);
x_333 = lean_ctor_get(x_331, 1);
lean_inc(x_333);
lean_dec(x_331);
x_334 = lean_mk_string_unchecked("false", 5, 5);
x_335 = l_Lean_Name_mkStr2(x_306, x_334);
x_336 = lean_mk_empty_array_with_capacity(x_301);
if (lean_is_scalar(x_330)) {
 x_337 = lean_alloc_ctor(0, 2, 0);
} else {
 x_337 = x_330;
}
lean_ctor_set(x_337, 0, x_323);
lean_ctor_set(x_337, 1, x_332);
x_338 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_338, 0, x_335);
lean_ctor_set(x_338, 1, x_336);
lean_ctor_set(x_338, 2, x_337);
x_16 = x_338;
x_17 = x_333;
goto block_23;
}
else
{
lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; 
lean_dec(x_330);
lean_dec(x_323);
lean_dec(x_306);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_339 = lean_ctor_get(x_331, 0);
lean_inc(x_339);
x_340 = lean_ctor_get(x_331, 1);
lean_inc(x_340);
if (lean_is_exclusive(x_331)) {
 lean_ctor_release(x_331, 0);
 lean_ctor_release(x_331, 1);
 x_341 = x_331;
} else {
 lean_dec_ref(x_331);
 x_341 = lean_box(0);
}
if (lean_is_scalar(x_341)) {
 x_342 = lean_alloc_ctor(1, 2, 0);
} else {
 x_342 = x_341;
}
lean_ctor_set(x_342, 0, x_339);
lean_ctor_set(x_342, 1, x_340);
return x_342;
}
}
else
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; 
x_343 = lean_mk_string_unchecked("abs", 3, 3);
x_344 = l_Lean_Name_mkStr1(x_343);
x_345 = lean_mk_string_unchecked("natAbs", 6, 6);
x_346 = l_Lean_Name_mkStr2(x_302, x_345);
x_347 = lean_unsigned_to_nat(1u);
x_348 = lean_mk_empty_array_with_capacity(x_347);
x_349 = lean_array_push(x_348, x_303);
x_350 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_350, 0, x_346);
lean_ctor_set(x_350, 1, x_304);
lean_ctor_set(x_350, 2, x_349);
lean_inc(x_305);
x_351 = l_Lean_Compiler_LCNF_mkLetDecl(x_344, x_305, x_350, x_6, x_7, x_8, x_9, x_296);
x_352 = lean_ctor_get(x_351, 0);
lean_inc(x_352);
x_353 = lean_ctor_get(x_351, 1);
lean_inc(x_353);
if (lean_is_exclusive(x_351)) {
 lean_ctor_release(x_351, 0);
 lean_ctor_release(x_351, 1);
 x_354 = x_351;
} else {
 lean_dec_ref(x_351);
 x_354 = lean_box(0);
}
x_355 = lean_mk_string_unchecked("one", 3, 3);
x_356 = l_Lean_Name_mkStr1(x_355);
x_357 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_357, 0, x_347);
x_358 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_358, 0, x_357);
lean_inc(x_305);
x_359 = l_Lean_Compiler_LCNF_mkLetDecl(x_356, x_305, x_358, x_6, x_7, x_8, x_9, x_353);
x_360 = lean_ctor_get(x_359, 0);
lean_inc(x_360);
x_361 = lean_ctor_get(x_359, 1);
lean_inc(x_361);
if (lean_is_exclusive(x_359)) {
 lean_ctor_release(x_359, 0);
 lean_ctor_release(x_359, 1);
 x_362 = x_359;
} else {
 lean_dec_ref(x_359);
 x_362 = lean_box(0);
}
x_363 = lean_mk_string_unchecked("sub", 3, 3);
x_364 = lean_ctor_get(x_352, 0);
lean_inc(x_364);
x_365 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_365, 0, x_364);
x_366 = lean_ctor_get(x_360, 0);
lean_inc(x_366);
x_367 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_367, 0, x_366);
x_368 = lean_unsigned_to_nat(2u);
x_369 = lean_mk_empty_array_with_capacity(x_368);
x_370 = lean_array_push(x_369, x_365);
x_371 = lean_st_ref_take(x_7, x_361);
x_372 = lean_ctor_get(x_371, 0);
lean_inc(x_372);
x_373 = lean_ctor_get(x_371, 1);
lean_inc(x_373);
if (lean_is_exclusive(x_371)) {
 lean_ctor_release(x_371, 0);
 lean_ctor_release(x_371, 1);
 x_374 = x_371;
} else {
 lean_dec_ref(x_371);
 x_374 = lean_box(0);
}
x_375 = l_Lean_Name_mkStr2(x_298, x_363);
x_376 = lean_array_push(x_370, x_367);
x_377 = lean_ctor_get(x_307, 0);
lean_inc(x_377);
x_378 = lean_ctor_get(x_307, 1);
lean_inc(x_378);
lean_dec(x_307);
x_379 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_379, 0, x_375);
lean_ctor_set(x_379, 1, x_304);
lean_ctor_set(x_379, 2, x_376);
x_380 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_380, 0, x_377);
lean_ctor_set(x_380, 1, x_378);
lean_ctor_set(x_380, 2, x_305);
lean_ctor_set(x_380, 3, x_379);
x_381 = lean_ctor_get(x_372, 0);
lean_inc(x_381);
lean_inc(x_380);
x_382 = l_Lean_Compiler_LCNF_LCtx_addLetDecl(x_381, x_380);
x_383 = lean_ctor_get(x_372, 1);
lean_inc(x_383);
lean_dec(x_372);
if (lean_is_scalar(x_374)) {
 x_384 = lean_alloc_ctor(0, 2, 0);
} else {
 x_384 = x_374;
}
lean_ctor_set(x_384, 0, x_382);
lean_ctor_set(x_384, 1, x_383);
x_385 = lean_st_ref_set(x_7, x_384, x_373);
x_386 = lean_ctor_get(x_385, 1);
lean_inc(x_386);
if (lean_is_exclusive(x_385)) {
 lean_ctor_release(x_385, 0);
 lean_ctor_release(x_385, 1);
 x_387 = x_385;
} else {
 lean_dec_ref(x_385);
 x_387 = lean_box(0);
}
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_388 = l_Lean_Compiler_LCNF_Code_toMono(x_294, x_5, x_6, x_7, x_8, x_9, x_386);
if (lean_obj_tag(x_388) == 0)
{
lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; 
x_389 = lean_ctor_get(x_388, 0);
lean_inc(x_389);
x_390 = lean_ctor_get(x_388, 1);
lean_inc(x_390);
lean_dec(x_388);
x_391 = lean_mk_string_unchecked("true", 4, 4);
x_392 = l_Lean_Name_mkStr2(x_306, x_391);
x_393 = lean_mk_empty_array_with_capacity(x_301);
if (lean_is_scalar(x_387)) {
 x_394 = lean_alloc_ctor(0, 2, 0);
} else {
 x_394 = x_387;
}
lean_ctor_set(x_394, 0, x_380);
lean_ctor_set(x_394, 1, x_389);
if (lean_is_scalar(x_362)) {
 x_395 = lean_alloc_ctor(0, 2, 0);
} else {
 x_395 = x_362;
}
lean_ctor_set(x_395, 0, x_360);
lean_ctor_set(x_395, 1, x_394);
if (lean_is_scalar(x_354)) {
 x_396 = lean_alloc_ctor(0, 2, 0);
} else {
 x_396 = x_354;
}
lean_ctor_set(x_396, 0, x_352);
lean_ctor_set(x_396, 1, x_395);
x_397 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_397, 0, x_392);
lean_ctor_set(x_397, 1, x_393);
lean_ctor_set(x_397, 2, x_396);
x_16 = x_397;
x_17 = x_390;
goto block_23;
}
else
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; 
lean_dec(x_387);
lean_dec(x_380);
lean_dec(x_362);
lean_dec(x_360);
lean_dec(x_354);
lean_dec(x_352);
lean_dec(x_306);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_398 = lean_ctor_get(x_388, 0);
lean_inc(x_398);
x_399 = lean_ctor_get(x_388, 1);
lean_inc(x_399);
if (lean_is_exclusive(x_388)) {
 lean_ctor_release(x_388, 0);
 lean_ctor_release(x_388, 1);
 x_400 = x_388;
} else {
 lean_dec_ref(x_388);
 x_400 = lean_box(0);
}
if (lean_is_scalar(x_400)) {
 x_401 = lean_alloc_ctor(1, 2, 0);
} else {
 x_401 = x_400;
}
lean_ctor_set(x_401, 0, x_398);
lean_ctor_set(x_401, 1, x_399);
return x_401;
}
}
}
}
else
{
lean_object* x_402; lean_object* x_403; 
x_402 = lean_ctor_get(x_13, 0);
lean_inc(x_402);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_403 = l_Lean_Compiler_LCNF_Code_toMono(x_402, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_403) == 0)
{
lean_object* x_404; lean_object* x_405; lean_object* x_406; 
x_404 = lean_ctor_get(x_403, 0);
lean_inc(x_404);
x_405 = lean_ctor_get(x_403, 1);
lean_inc(x_405);
lean_dec(x_403);
x_406 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_13, x_404);
x_16 = x_406;
x_17 = x_405;
goto block_23;
}
else
{
uint8_t x_407; 
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_407 = !lean_is_exclusive(x_403);
if (x_407 == 0)
{
return x_403;
}
else
{
lean_object* x_408; lean_object* x_409; lean_object* x_410; 
x_408 = lean_ctor_get(x_403, 0);
x_409 = lean_ctor_get(x_403, 1);
lean_inc(x_409);
lean_inc(x_408);
lean_dec(x_403);
x_410 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_410, 0, x_408);
lean_ctor_set(x_410, 1, x_409);
return x_410;
}
}
}
block_23:
{
lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; 
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_usize_of_nat(x_18);
x_20 = lean_usize_add(x_3, x_19);
x_21 = lean_array_uset(x_15, x_3, x_16);
x_3 = x_20;
x_4 = x_21;
x_10 = x_17;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesIntToMono___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
x_9 = l_Lean_Compiler_LCNF_toMonoType(x_8, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_mk_string_unchecked("Nat", 3, 3);
x_13 = l_Lean_Name_mkStr1(x_12);
x_14 = lean_box(0);
x_15 = l_Lean_Expr_const___override(x_13, x_14);
x_16 = lean_mk_string_unchecked("natZero", 7, 7);
x_17 = l_Lean_Name_mkStr1(x_16);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = l_Lean_Compiler_LCNF_mkLetDecl(x_17, x_15, x_20, x_3, x_4, x_5, x_6, x_11);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_21, 1);
x_25 = lean_mk_string_unchecked("intZero", 7, 7);
x_26 = l_Lean_Name_mkStr1(x_25);
x_27 = lean_mk_string_unchecked("Int", 3, 3);
lean_inc(x_27);
x_28 = l_Lean_Name_mkStr1(x_27);
x_29 = l_Lean_Expr_const___override(x_28, x_14);
x_30 = lean_mk_string_unchecked("ofNat", 5, 5);
lean_inc(x_27);
x_31 = l_Lean_Name_mkStr2(x_27, x_30);
x_32 = lean_ctor_get(x_23, 0);
lean_inc(x_32);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_mk_empty_array_with_capacity(x_34);
x_36 = lean_array_push(x_35, x_33);
x_37 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_37, 0, x_31);
lean_ctor_set(x_37, 1, x_14);
lean_ctor_set(x_37, 2, x_36);
x_38 = l_Lean_Compiler_LCNF_mkLetDecl(x_26, x_29, x_37, x_3, x_4, x_5, x_6, x_24);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_40 = lean_ctor_get(x_38, 0);
x_41 = lean_ctor_get(x_38, 1);
x_42 = lean_mk_string_unchecked("isNeg", 5, 5);
x_43 = l_Lean_Name_mkStr1(x_42);
x_44 = lean_mk_string_unchecked("Bool", 4, 4);
x_45 = l_Lean_Name_mkStr1(x_44);
lean_inc(x_45);
x_46 = l_Lean_Expr_const___override(x_45, x_14);
x_47 = lean_mk_string_unchecked("decLt", 5, 5);
x_48 = l_Lean_Name_mkStr2(x_27, x_47);
x_49 = lean_ctor_get(x_1, 2);
lean_inc(x_49);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_49);
x_51 = lean_ctor_get(x_40, 0);
lean_inc(x_51);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_51);
x_53 = lean_unsigned_to_nat(2u);
x_54 = lean_mk_empty_array_with_capacity(x_53);
x_55 = lean_array_push(x_54, x_50);
x_56 = lean_array_push(x_55, x_52);
x_57 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_57, 0, x_48);
lean_ctor_set(x_57, 1, x_14);
lean_ctor_set(x_57, 2, x_56);
x_58 = l_Lean_Compiler_LCNF_mkLetDecl(x_43, x_46, x_57, x_3, x_4, x_5, x_6, x_41);
x_59 = !lean_is_exclusive(x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; size_t x_63; size_t x_64; lean_object* x_65; 
x_60 = lean_ctor_get(x_58, 0);
x_61 = lean_ctor_get(x_58, 1);
x_62 = lean_ctor_get(x_1, 3);
lean_inc(x_62);
x_63 = lean_array_size(x_62);
x_64 = lean_usize_of_nat(x_18);
x_65 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_casesIntToMono_spec__0(x_1, x_63, x_64, x_62, x_2, x_3, x_4, x_5, x_6, x_61);
lean_dec(x_1);
if (lean_obj_tag(x_65) == 0)
{
uint8_t x_66; 
x_66 = !lean_is_exclusive(x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_67 = lean_ctor_get(x_65, 0);
x_68 = lean_ctor_get(x_60, 0);
lean_inc(x_68);
x_69 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_69, 0, x_45);
lean_ctor_set(x_69, 1, x_10);
lean_ctor_set(x_69, 2, x_68);
lean_ctor_set(x_69, 3, x_67);
x_70 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_58, 1, x_70);
lean_ctor_set(x_38, 1, x_58);
lean_ctor_set(x_21, 1, x_38);
lean_ctor_set(x_65, 0, x_21);
return x_65;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_71 = lean_ctor_get(x_65, 0);
x_72 = lean_ctor_get(x_65, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_65);
x_73 = lean_ctor_get(x_60, 0);
lean_inc(x_73);
x_74 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_74, 0, x_45);
lean_ctor_set(x_74, 1, x_10);
lean_ctor_set(x_74, 2, x_73);
lean_ctor_set(x_74, 3, x_71);
x_75 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_58, 1, x_75);
lean_ctor_set(x_38, 1, x_58);
lean_ctor_set(x_21, 1, x_38);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_21);
lean_ctor_set(x_76, 1, x_72);
return x_76;
}
}
else
{
uint8_t x_77; 
lean_free_object(x_58);
lean_dec(x_60);
lean_dec(x_45);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_21);
lean_dec(x_23);
lean_dec(x_10);
x_77 = !lean_is_exclusive(x_65);
if (x_77 == 0)
{
return x_65;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_65, 0);
x_79 = lean_ctor_get(x_65, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_65);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; size_t x_84; size_t x_85; lean_object* x_86; 
x_81 = lean_ctor_get(x_58, 0);
x_82 = lean_ctor_get(x_58, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_58);
x_83 = lean_ctor_get(x_1, 3);
lean_inc(x_83);
x_84 = lean_array_size(x_83);
x_85 = lean_usize_of_nat(x_18);
x_86 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_casesIntToMono_spec__0(x_1, x_84, x_85, x_83, x_2, x_3, x_4, x_5, x_6, x_82);
lean_dec(x_1);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_89 = x_86;
} else {
 lean_dec_ref(x_86);
 x_89 = lean_box(0);
}
x_90 = lean_ctor_get(x_81, 0);
lean_inc(x_90);
x_91 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_91, 0, x_45);
lean_ctor_set(x_91, 1, x_10);
lean_ctor_set(x_91, 2, x_90);
lean_ctor_set(x_91, 3, x_87);
x_92 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_92, 0, x_91);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_81);
lean_ctor_set(x_93, 1, x_92);
lean_ctor_set(x_38, 1, x_93);
lean_ctor_set(x_21, 1, x_38);
if (lean_is_scalar(x_89)) {
 x_94 = lean_alloc_ctor(0, 2, 0);
} else {
 x_94 = x_89;
}
lean_ctor_set(x_94, 0, x_21);
lean_ctor_set(x_94, 1, x_88);
return x_94;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_81);
lean_dec(x_45);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_21);
lean_dec(x_23);
lean_dec(x_10);
x_95 = lean_ctor_get(x_86, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_86, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_97 = x_86;
} else {
 lean_dec_ref(x_86);
 x_97 = lean_box(0);
}
if (lean_is_scalar(x_97)) {
 x_98 = lean_alloc_ctor(1, 2, 0);
} else {
 x_98 = x_97;
}
lean_ctor_set(x_98, 0, x_95);
lean_ctor_set(x_98, 1, x_96);
return x_98;
}
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; size_t x_122; size_t x_123; lean_object* x_124; 
x_99 = lean_ctor_get(x_38, 0);
x_100 = lean_ctor_get(x_38, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_38);
x_101 = lean_mk_string_unchecked("isNeg", 5, 5);
x_102 = l_Lean_Name_mkStr1(x_101);
x_103 = lean_mk_string_unchecked("Bool", 4, 4);
x_104 = l_Lean_Name_mkStr1(x_103);
lean_inc(x_104);
x_105 = l_Lean_Expr_const___override(x_104, x_14);
x_106 = lean_mk_string_unchecked("decLt", 5, 5);
x_107 = l_Lean_Name_mkStr2(x_27, x_106);
x_108 = lean_ctor_get(x_1, 2);
lean_inc(x_108);
x_109 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_109, 0, x_108);
x_110 = lean_ctor_get(x_99, 0);
lean_inc(x_110);
x_111 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_111, 0, x_110);
x_112 = lean_unsigned_to_nat(2u);
x_113 = lean_mk_empty_array_with_capacity(x_112);
x_114 = lean_array_push(x_113, x_109);
x_115 = lean_array_push(x_114, x_111);
x_116 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_116, 0, x_107);
lean_ctor_set(x_116, 1, x_14);
lean_ctor_set(x_116, 2, x_115);
x_117 = l_Lean_Compiler_LCNF_mkLetDecl(x_102, x_105, x_116, x_3, x_4, x_5, x_6, x_100);
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_120 = x_117;
} else {
 lean_dec_ref(x_117);
 x_120 = lean_box(0);
}
x_121 = lean_ctor_get(x_1, 3);
lean_inc(x_121);
x_122 = lean_array_size(x_121);
x_123 = lean_usize_of_nat(x_18);
x_124 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_casesIntToMono_spec__0(x_1, x_122, x_123, x_121, x_2, x_3, x_4, x_5, x_6, x_119);
lean_dec(x_1);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_124, 1);
lean_inc(x_126);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_127 = x_124;
} else {
 lean_dec_ref(x_124);
 x_127 = lean_box(0);
}
x_128 = lean_ctor_get(x_118, 0);
lean_inc(x_128);
x_129 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_129, 0, x_104);
lean_ctor_set(x_129, 1, x_10);
lean_ctor_set(x_129, 2, x_128);
lean_ctor_set(x_129, 3, x_125);
x_130 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_130, 0, x_129);
if (lean_is_scalar(x_120)) {
 x_131 = lean_alloc_ctor(0, 2, 0);
} else {
 x_131 = x_120;
}
lean_ctor_set(x_131, 0, x_118);
lean_ctor_set(x_131, 1, x_130);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_99);
lean_ctor_set(x_132, 1, x_131);
lean_ctor_set(x_21, 1, x_132);
if (lean_is_scalar(x_127)) {
 x_133 = lean_alloc_ctor(0, 2, 0);
} else {
 x_133 = x_127;
}
lean_ctor_set(x_133, 0, x_21);
lean_ctor_set(x_133, 1, x_126);
return x_133;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
lean_dec(x_120);
lean_dec(x_118);
lean_dec(x_104);
lean_dec(x_99);
lean_free_object(x_21);
lean_dec(x_23);
lean_dec(x_10);
x_134 = lean_ctor_get(x_124, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_124, 1);
lean_inc(x_135);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_136 = x_124;
} else {
 lean_dec_ref(x_124);
 x_136 = lean_box(0);
}
if (lean_is_scalar(x_136)) {
 x_137 = lean_alloc_ctor(1, 2, 0);
} else {
 x_137 = x_136;
}
lean_ctor_set(x_137, 0, x_134);
lean_ctor_set(x_137, 1, x_135);
return x_137;
}
}
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; size_t x_178; size_t x_179; lean_object* x_180; 
x_138 = lean_ctor_get(x_21, 0);
x_139 = lean_ctor_get(x_21, 1);
lean_inc(x_139);
lean_inc(x_138);
lean_dec(x_21);
x_140 = lean_mk_string_unchecked("intZero", 7, 7);
x_141 = l_Lean_Name_mkStr1(x_140);
x_142 = lean_mk_string_unchecked("Int", 3, 3);
lean_inc(x_142);
x_143 = l_Lean_Name_mkStr1(x_142);
x_144 = l_Lean_Expr_const___override(x_143, x_14);
x_145 = lean_mk_string_unchecked("ofNat", 5, 5);
lean_inc(x_142);
x_146 = l_Lean_Name_mkStr2(x_142, x_145);
x_147 = lean_ctor_get(x_138, 0);
lean_inc(x_147);
x_148 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_148, 0, x_147);
x_149 = lean_unsigned_to_nat(1u);
x_150 = lean_mk_empty_array_with_capacity(x_149);
x_151 = lean_array_push(x_150, x_148);
x_152 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_152, 0, x_146);
lean_ctor_set(x_152, 1, x_14);
lean_ctor_set(x_152, 2, x_151);
x_153 = l_Lean_Compiler_LCNF_mkLetDecl(x_141, x_144, x_152, x_3, x_4, x_5, x_6, x_139);
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_153, 1);
lean_inc(x_155);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 lean_ctor_release(x_153, 1);
 x_156 = x_153;
} else {
 lean_dec_ref(x_153);
 x_156 = lean_box(0);
}
x_157 = lean_mk_string_unchecked("isNeg", 5, 5);
x_158 = l_Lean_Name_mkStr1(x_157);
x_159 = lean_mk_string_unchecked("Bool", 4, 4);
x_160 = l_Lean_Name_mkStr1(x_159);
lean_inc(x_160);
x_161 = l_Lean_Expr_const___override(x_160, x_14);
x_162 = lean_mk_string_unchecked("decLt", 5, 5);
x_163 = l_Lean_Name_mkStr2(x_142, x_162);
x_164 = lean_ctor_get(x_1, 2);
lean_inc(x_164);
x_165 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_165, 0, x_164);
x_166 = lean_ctor_get(x_154, 0);
lean_inc(x_166);
x_167 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_167, 0, x_166);
x_168 = lean_unsigned_to_nat(2u);
x_169 = lean_mk_empty_array_with_capacity(x_168);
x_170 = lean_array_push(x_169, x_165);
x_171 = lean_array_push(x_170, x_167);
x_172 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_172, 0, x_163);
lean_ctor_set(x_172, 1, x_14);
lean_ctor_set(x_172, 2, x_171);
x_173 = l_Lean_Compiler_LCNF_mkLetDecl(x_158, x_161, x_172, x_3, x_4, x_5, x_6, x_155);
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_173, 1);
lean_inc(x_175);
if (lean_is_exclusive(x_173)) {
 lean_ctor_release(x_173, 0);
 lean_ctor_release(x_173, 1);
 x_176 = x_173;
} else {
 lean_dec_ref(x_173);
 x_176 = lean_box(0);
}
x_177 = lean_ctor_get(x_1, 3);
lean_inc(x_177);
x_178 = lean_array_size(x_177);
x_179 = lean_usize_of_nat(x_18);
x_180 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_casesIntToMono_spec__0(x_1, x_178, x_179, x_177, x_2, x_3, x_4, x_5, x_6, x_175);
lean_dec(x_1);
if (lean_obj_tag(x_180) == 0)
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_181 = lean_ctor_get(x_180, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_180, 1);
lean_inc(x_182);
if (lean_is_exclusive(x_180)) {
 lean_ctor_release(x_180, 0);
 lean_ctor_release(x_180, 1);
 x_183 = x_180;
} else {
 lean_dec_ref(x_180);
 x_183 = lean_box(0);
}
x_184 = lean_ctor_get(x_174, 0);
lean_inc(x_184);
x_185 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_185, 0, x_160);
lean_ctor_set(x_185, 1, x_10);
lean_ctor_set(x_185, 2, x_184);
lean_ctor_set(x_185, 3, x_181);
x_186 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_186, 0, x_185);
if (lean_is_scalar(x_176)) {
 x_187 = lean_alloc_ctor(0, 2, 0);
} else {
 x_187 = x_176;
}
lean_ctor_set(x_187, 0, x_174);
lean_ctor_set(x_187, 1, x_186);
if (lean_is_scalar(x_156)) {
 x_188 = lean_alloc_ctor(0, 2, 0);
} else {
 x_188 = x_156;
}
lean_ctor_set(x_188, 0, x_154);
lean_ctor_set(x_188, 1, x_187);
x_189 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_189, 0, x_138);
lean_ctor_set(x_189, 1, x_188);
if (lean_is_scalar(x_183)) {
 x_190 = lean_alloc_ctor(0, 2, 0);
} else {
 x_190 = x_183;
}
lean_ctor_set(x_190, 0, x_189);
lean_ctor_set(x_190, 1, x_182);
return x_190;
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
lean_dec(x_176);
lean_dec(x_174);
lean_dec(x_160);
lean_dec(x_156);
lean_dec(x_154);
lean_dec(x_138);
lean_dec(x_10);
x_191 = lean_ctor_get(x_180, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_180, 1);
lean_inc(x_192);
if (lean_is_exclusive(x_180)) {
 lean_ctor_release(x_180, 0);
 lean_ctor_release(x_180, 1);
 x_193 = x_180;
} else {
 lean_dec_ref(x_180);
 x_193 = lean_box(0);
}
if (lean_is_scalar(x_193)) {
 x_194 = lean_alloc_ctor(1, 2, 0);
} else {
 x_194 = x_193;
}
lean_ctor_set(x_194, 0, x_191);
lean_ctor_set(x_194, 1, x_192);
return x_194;
}
}
}
else
{
uint8_t x_195; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_195 = !lean_is_exclusive(x_9);
if (x_195 == 0)
{
return x_9;
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_196 = lean_ctor_get(x_9, 0);
x_197 = lean_ctor_get(x_9, 1);
lean_inc(x_197);
lean_inc(x_196);
lean_dec(x_9);
x_198 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_198, 0, x_196);
lean_ctor_set(x_198, 1, x_197);
return x_198;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesIntToMono(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_casesIntToMono___redArg(x_1, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_casesNatToMono_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_3, x_2);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_array_uget(x_4, x_3);
x_14 = lean_box(0);
x_15 = lean_array_uset(x_4, x_3, x_14);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_13);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_25 = lean_ctor_get(x_13, 0);
x_26 = lean_ctor_get(x_13, 1);
x_27 = lean_ctor_get(x_13, 2);
x_28 = l_Lean_Compiler_LCNF_eraseParams___redArg(x_26, x_7, x_10);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_mk_string_unchecked("Nat", 3, 3);
x_31 = lean_mk_string_unchecked("Bool", 4, 4);
x_32 = lean_unsigned_to_nat(0u);
x_33 = lean_mk_string_unchecked("succ", 4, 4);
lean_inc(x_30);
x_34 = l_Lean_Name_mkStr2(x_30, x_33);
x_35 = lean_name_eq(x_25, x_34);
lean_dec(x_34);
lean_dec(x_25);
if (x_35 == 0)
{
lean_object* x_36; 
lean_dec(x_30);
lean_dec(x_26);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_36 = l_Lean_Compiler_LCNF_Code_toMono(x_27, x_5, x_6, x_7, x_8, x_9, x_29);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_mk_string_unchecked("true", 4, 4);
x_40 = l_Lean_Name_mkStr2(x_31, x_39);
x_41 = lean_mk_empty_array_with_capacity(x_32);
lean_ctor_set(x_13, 2, x_37);
lean_ctor_set(x_13, 1, x_41);
lean_ctor_set(x_13, 0, x_40);
x_16 = x_13;
x_17 = x_38;
goto block_23;
}
else
{
uint8_t x_42; 
lean_dec(x_31);
lean_free_object(x_13);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_42 = !lean_is_exclusive(x_36);
if (x_42 == 0)
{
return x_36;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_36, 0);
x_44 = lean_ctor_get(x_36, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_36);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
lean_inc(x_30);
x_46 = l_Lean_Name_mkStr1(x_30);
x_47 = lean_box(0);
x_48 = l_Lean_Expr_const___override(x_46, x_47);
x_49 = lean_mk_string_unchecked("one", 3, 3);
x_50 = l_Lean_Name_mkStr1(x_49);
x_51 = lean_unsigned_to_nat(1u);
x_52 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_52, 0, x_51);
x_53 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_53, 0, x_52);
lean_inc(x_48);
x_54 = l_Lean_Compiler_LCNF_mkLetDecl(x_50, x_48, x_53, x_6, x_7, x_8, x_9, x_29);
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_56 = lean_ctor_get(x_54, 0);
x_57 = lean_ctor_get(x_54, 1);
x_58 = lean_ctor_get(x_1, 2);
lean_inc(x_58);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_58);
x_60 = l_Lean_Compiler_LCNF_instInhabitedParam;
x_61 = lean_mk_string_unchecked("sub", 3, 3);
x_62 = lean_ctor_get(x_56, 0);
lean_inc(x_62);
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_62);
x_64 = lean_unsigned_to_nat(2u);
x_65 = lean_mk_empty_array_with_capacity(x_64);
x_66 = lean_array_push(x_65, x_59);
x_67 = lean_st_ref_take(x_7, x_57);
x_68 = !lean_is_exclusive(x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_69 = lean_ctor_get(x_67, 0);
x_70 = lean_ctor_get(x_67, 1);
x_71 = lean_array_get(x_60, x_26, x_32);
lean_dec(x_26);
x_72 = l_Lean_Name_mkStr2(x_30, x_61);
x_73 = lean_array_push(x_66, x_63);
x_74 = lean_ctor_get(x_71, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_71, 1);
lean_inc(x_75);
lean_dec(x_71);
x_76 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_76, 0, x_72);
lean_ctor_set(x_76, 1, x_47);
lean_ctor_set(x_76, 2, x_73);
x_77 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_77, 0, x_74);
lean_ctor_set(x_77, 1, x_75);
lean_ctor_set(x_77, 2, x_48);
lean_ctor_set(x_77, 3, x_76);
x_78 = lean_ctor_get(x_69, 0);
lean_inc(x_78);
lean_inc(x_77);
x_79 = l_Lean_Compiler_LCNF_LCtx_addLetDecl(x_78, x_77);
x_80 = lean_ctor_get(x_69, 1);
lean_inc(x_80);
lean_dec(x_69);
lean_ctor_set(x_67, 1, x_80);
lean_ctor_set(x_67, 0, x_79);
x_81 = lean_st_ref_set(x_7, x_67, x_70);
x_82 = !lean_is_exclusive(x_81);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_81, 1);
x_84 = lean_ctor_get(x_81, 0);
lean_dec(x_84);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_85 = l_Lean_Compiler_LCNF_Code_toMono(x_27, x_5, x_6, x_7, x_8, x_9, x_83);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
x_88 = lean_mk_string_unchecked("false", 5, 5);
x_89 = l_Lean_Name_mkStr2(x_31, x_88);
x_90 = lean_mk_empty_array_with_capacity(x_32);
lean_ctor_set(x_81, 1, x_86);
lean_ctor_set(x_81, 0, x_77);
lean_ctor_set(x_54, 1, x_81);
lean_ctor_set(x_13, 2, x_54);
lean_ctor_set(x_13, 1, x_90);
lean_ctor_set(x_13, 0, x_89);
x_16 = x_13;
x_17 = x_87;
goto block_23;
}
else
{
uint8_t x_91; 
lean_free_object(x_81);
lean_dec(x_77);
lean_free_object(x_54);
lean_dec(x_56);
lean_dec(x_31);
lean_free_object(x_13);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_91 = !lean_is_exclusive(x_85);
if (x_91 == 0)
{
return x_85;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_85, 0);
x_93 = lean_ctor_get(x_85, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_85);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
else
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_ctor_get(x_81, 1);
lean_inc(x_95);
lean_dec(x_81);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_96 = l_Lean_Compiler_LCNF_Code_toMono(x_27, x_5, x_6, x_7, x_8, x_9, x_95);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
lean_dec(x_96);
x_99 = lean_mk_string_unchecked("false", 5, 5);
x_100 = l_Lean_Name_mkStr2(x_31, x_99);
x_101 = lean_mk_empty_array_with_capacity(x_32);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_77);
lean_ctor_set(x_102, 1, x_97);
lean_ctor_set(x_54, 1, x_102);
lean_ctor_set(x_13, 2, x_54);
lean_ctor_set(x_13, 1, x_101);
lean_ctor_set(x_13, 0, x_100);
x_16 = x_13;
x_17 = x_98;
goto block_23;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_77);
lean_free_object(x_54);
lean_dec(x_56);
lean_dec(x_31);
lean_free_object(x_13);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_103 = lean_ctor_get(x_96, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_96, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 lean_ctor_release(x_96, 1);
 x_105 = x_96;
} else {
 lean_dec_ref(x_96);
 x_105 = lean_box(0);
}
if (lean_is_scalar(x_105)) {
 x_106 = lean_alloc_ctor(1, 2, 0);
} else {
 x_106 = x_105;
}
lean_ctor_set(x_106, 0, x_103);
lean_ctor_set(x_106, 1, x_104);
return x_106;
}
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_107 = lean_ctor_get(x_67, 0);
x_108 = lean_ctor_get(x_67, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_67);
x_109 = lean_array_get(x_60, x_26, x_32);
lean_dec(x_26);
x_110 = l_Lean_Name_mkStr2(x_30, x_61);
x_111 = lean_array_push(x_66, x_63);
x_112 = lean_ctor_get(x_109, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_109, 1);
lean_inc(x_113);
lean_dec(x_109);
x_114 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_114, 0, x_110);
lean_ctor_set(x_114, 1, x_47);
lean_ctor_set(x_114, 2, x_111);
x_115 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_115, 0, x_112);
lean_ctor_set(x_115, 1, x_113);
lean_ctor_set(x_115, 2, x_48);
lean_ctor_set(x_115, 3, x_114);
x_116 = lean_ctor_get(x_107, 0);
lean_inc(x_116);
lean_inc(x_115);
x_117 = l_Lean_Compiler_LCNF_LCtx_addLetDecl(x_116, x_115);
x_118 = lean_ctor_get(x_107, 1);
lean_inc(x_118);
lean_dec(x_107);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
x_120 = lean_st_ref_set(x_7, x_119, x_108);
x_121 = lean_ctor_get(x_120, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 x_122 = x_120;
} else {
 lean_dec_ref(x_120);
 x_122 = lean_box(0);
}
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_123 = l_Lean_Compiler_LCNF_Code_toMono(x_27, x_5, x_6, x_7, x_8, x_9, x_121);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
lean_dec(x_123);
x_126 = lean_mk_string_unchecked("false", 5, 5);
x_127 = l_Lean_Name_mkStr2(x_31, x_126);
x_128 = lean_mk_empty_array_with_capacity(x_32);
if (lean_is_scalar(x_122)) {
 x_129 = lean_alloc_ctor(0, 2, 0);
} else {
 x_129 = x_122;
}
lean_ctor_set(x_129, 0, x_115);
lean_ctor_set(x_129, 1, x_124);
lean_ctor_set(x_54, 1, x_129);
lean_ctor_set(x_13, 2, x_54);
lean_ctor_set(x_13, 1, x_128);
lean_ctor_set(x_13, 0, x_127);
x_16 = x_13;
x_17 = x_125;
goto block_23;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
lean_dec(x_122);
lean_dec(x_115);
lean_free_object(x_54);
lean_dec(x_56);
lean_dec(x_31);
lean_free_object(x_13);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_130 = lean_ctor_get(x_123, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_123, 1);
lean_inc(x_131);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 x_132 = x_123;
} else {
 lean_dec_ref(x_123);
 x_132 = lean_box(0);
}
if (lean_is_scalar(x_132)) {
 x_133 = lean_alloc_ctor(1, 2, 0);
} else {
 x_133 = x_132;
}
lean_ctor_set(x_133, 0, x_130);
lean_ctor_set(x_133, 1, x_131);
return x_133;
}
}
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_134 = lean_ctor_get(x_54, 0);
x_135 = lean_ctor_get(x_54, 1);
lean_inc(x_135);
lean_inc(x_134);
lean_dec(x_54);
x_136 = lean_ctor_get(x_1, 2);
lean_inc(x_136);
x_137 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_137, 0, x_136);
x_138 = l_Lean_Compiler_LCNF_instInhabitedParam;
x_139 = lean_mk_string_unchecked("sub", 3, 3);
x_140 = lean_ctor_get(x_134, 0);
lean_inc(x_140);
x_141 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_141, 0, x_140);
x_142 = lean_unsigned_to_nat(2u);
x_143 = lean_mk_empty_array_with_capacity(x_142);
x_144 = lean_array_push(x_143, x_137);
x_145 = lean_st_ref_take(x_7, x_135);
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_145, 1);
lean_inc(x_147);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 lean_ctor_release(x_145, 1);
 x_148 = x_145;
} else {
 lean_dec_ref(x_145);
 x_148 = lean_box(0);
}
x_149 = lean_array_get(x_138, x_26, x_32);
lean_dec(x_26);
x_150 = l_Lean_Name_mkStr2(x_30, x_139);
x_151 = lean_array_push(x_144, x_141);
x_152 = lean_ctor_get(x_149, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_149, 1);
lean_inc(x_153);
lean_dec(x_149);
x_154 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_154, 0, x_150);
lean_ctor_set(x_154, 1, x_47);
lean_ctor_set(x_154, 2, x_151);
x_155 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_155, 0, x_152);
lean_ctor_set(x_155, 1, x_153);
lean_ctor_set(x_155, 2, x_48);
lean_ctor_set(x_155, 3, x_154);
x_156 = lean_ctor_get(x_146, 0);
lean_inc(x_156);
lean_inc(x_155);
x_157 = l_Lean_Compiler_LCNF_LCtx_addLetDecl(x_156, x_155);
x_158 = lean_ctor_get(x_146, 1);
lean_inc(x_158);
lean_dec(x_146);
if (lean_is_scalar(x_148)) {
 x_159 = lean_alloc_ctor(0, 2, 0);
} else {
 x_159 = x_148;
}
lean_ctor_set(x_159, 0, x_157);
lean_ctor_set(x_159, 1, x_158);
x_160 = lean_st_ref_set(x_7, x_159, x_147);
x_161 = lean_ctor_get(x_160, 1);
lean_inc(x_161);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 lean_ctor_release(x_160, 1);
 x_162 = x_160;
} else {
 lean_dec_ref(x_160);
 x_162 = lean_box(0);
}
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_163 = l_Lean_Compiler_LCNF_Code_toMono(x_27, x_5, x_6, x_7, x_8, x_9, x_161);
if (lean_obj_tag(x_163) == 0)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_163, 1);
lean_inc(x_165);
lean_dec(x_163);
x_166 = lean_mk_string_unchecked("false", 5, 5);
x_167 = l_Lean_Name_mkStr2(x_31, x_166);
x_168 = lean_mk_empty_array_with_capacity(x_32);
if (lean_is_scalar(x_162)) {
 x_169 = lean_alloc_ctor(0, 2, 0);
} else {
 x_169 = x_162;
}
lean_ctor_set(x_169, 0, x_155);
lean_ctor_set(x_169, 1, x_164);
x_170 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_170, 0, x_134);
lean_ctor_set(x_170, 1, x_169);
lean_ctor_set(x_13, 2, x_170);
lean_ctor_set(x_13, 1, x_168);
lean_ctor_set(x_13, 0, x_167);
x_16 = x_13;
x_17 = x_165;
goto block_23;
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
lean_dec(x_162);
lean_dec(x_155);
lean_dec(x_134);
lean_dec(x_31);
lean_free_object(x_13);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_171 = lean_ctor_get(x_163, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_163, 1);
lean_inc(x_172);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 lean_ctor_release(x_163, 1);
 x_173 = x_163;
} else {
 lean_dec_ref(x_163);
 x_173 = lean_box(0);
}
if (lean_is_scalar(x_173)) {
 x_174 = lean_alloc_ctor(1, 2, 0);
} else {
 x_174 = x_173;
}
lean_ctor_set(x_174, 0, x_171);
lean_ctor_set(x_174, 1, x_172);
return x_174;
}
}
}
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; uint8_t x_185; 
x_175 = lean_ctor_get(x_13, 0);
x_176 = lean_ctor_get(x_13, 1);
x_177 = lean_ctor_get(x_13, 2);
lean_inc(x_177);
lean_inc(x_176);
lean_inc(x_175);
lean_dec(x_13);
x_178 = l_Lean_Compiler_LCNF_eraseParams___redArg(x_176, x_7, x_10);
x_179 = lean_ctor_get(x_178, 1);
lean_inc(x_179);
lean_dec(x_178);
x_180 = lean_mk_string_unchecked("Nat", 3, 3);
x_181 = lean_mk_string_unchecked("Bool", 4, 4);
x_182 = lean_unsigned_to_nat(0u);
x_183 = lean_mk_string_unchecked("succ", 4, 4);
lean_inc(x_180);
x_184 = l_Lean_Name_mkStr2(x_180, x_183);
x_185 = lean_name_eq(x_175, x_184);
lean_dec(x_184);
lean_dec(x_175);
if (x_185 == 0)
{
lean_object* x_186; 
lean_dec(x_180);
lean_dec(x_176);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_186 = l_Lean_Compiler_LCNF_Code_toMono(x_177, x_5, x_6, x_7, x_8, x_9, x_179);
if (lean_obj_tag(x_186) == 0)
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_187 = lean_ctor_get(x_186, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_186, 1);
lean_inc(x_188);
lean_dec(x_186);
x_189 = lean_mk_string_unchecked("true", 4, 4);
x_190 = l_Lean_Name_mkStr2(x_181, x_189);
x_191 = lean_mk_empty_array_with_capacity(x_182);
x_192 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_192, 0, x_190);
lean_ctor_set(x_192, 1, x_191);
lean_ctor_set(x_192, 2, x_187);
x_16 = x_192;
x_17 = x_188;
goto block_23;
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
lean_dec(x_181);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_193 = lean_ctor_get(x_186, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_186, 1);
lean_inc(x_194);
if (lean_is_exclusive(x_186)) {
 lean_ctor_release(x_186, 0);
 lean_ctor_release(x_186, 1);
 x_195 = x_186;
} else {
 lean_dec_ref(x_186);
 x_195 = lean_box(0);
}
if (lean_is_scalar(x_195)) {
 x_196 = lean_alloc_ctor(1, 2, 0);
} else {
 x_196 = x_195;
}
lean_ctor_set(x_196, 0, x_193);
lean_ctor_set(x_196, 1, x_194);
return x_196;
}
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; 
lean_inc(x_180);
x_197 = l_Lean_Name_mkStr1(x_180);
x_198 = lean_box(0);
x_199 = l_Lean_Expr_const___override(x_197, x_198);
x_200 = lean_mk_string_unchecked("one", 3, 3);
x_201 = l_Lean_Name_mkStr1(x_200);
x_202 = lean_unsigned_to_nat(1u);
x_203 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_203, 0, x_202);
x_204 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_204, 0, x_203);
lean_inc(x_199);
x_205 = l_Lean_Compiler_LCNF_mkLetDecl(x_201, x_199, x_204, x_6, x_7, x_8, x_9, x_179);
x_206 = lean_ctor_get(x_205, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_205, 1);
lean_inc(x_207);
if (lean_is_exclusive(x_205)) {
 lean_ctor_release(x_205, 0);
 lean_ctor_release(x_205, 1);
 x_208 = x_205;
} else {
 lean_dec_ref(x_205);
 x_208 = lean_box(0);
}
x_209 = lean_ctor_get(x_1, 2);
lean_inc(x_209);
x_210 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_210, 0, x_209);
x_211 = l_Lean_Compiler_LCNF_instInhabitedParam;
x_212 = lean_mk_string_unchecked("sub", 3, 3);
x_213 = lean_ctor_get(x_206, 0);
lean_inc(x_213);
x_214 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_214, 0, x_213);
x_215 = lean_unsigned_to_nat(2u);
x_216 = lean_mk_empty_array_with_capacity(x_215);
x_217 = lean_array_push(x_216, x_210);
x_218 = lean_st_ref_take(x_7, x_207);
x_219 = lean_ctor_get(x_218, 0);
lean_inc(x_219);
x_220 = lean_ctor_get(x_218, 1);
lean_inc(x_220);
if (lean_is_exclusive(x_218)) {
 lean_ctor_release(x_218, 0);
 lean_ctor_release(x_218, 1);
 x_221 = x_218;
} else {
 lean_dec_ref(x_218);
 x_221 = lean_box(0);
}
x_222 = lean_array_get(x_211, x_176, x_182);
lean_dec(x_176);
x_223 = l_Lean_Name_mkStr2(x_180, x_212);
x_224 = lean_array_push(x_217, x_214);
x_225 = lean_ctor_get(x_222, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_222, 1);
lean_inc(x_226);
lean_dec(x_222);
x_227 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_227, 0, x_223);
lean_ctor_set(x_227, 1, x_198);
lean_ctor_set(x_227, 2, x_224);
x_228 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_228, 0, x_225);
lean_ctor_set(x_228, 1, x_226);
lean_ctor_set(x_228, 2, x_199);
lean_ctor_set(x_228, 3, x_227);
x_229 = lean_ctor_get(x_219, 0);
lean_inc(x_229);
lean_inc(x_228);
x_230 = l_Lean_Compiler_LCNF_LCtx_addLetDecl(x_229, x_228);
x_231 = lean_ctor_get(x_219, 1);
lean_inc(x_231);
lean_dec(x_219);
if (lean_is_scalar(x_221)) {
 x_232 = lean_alloc_ctor(0, 2, 0);
} else {
 x_232 = x_221;
}
lean_ctor_set(x_232, 0, x_230);
lean_ctor_set(x_232, 1, x_231);
x_233 = lean_st_ref_set(x_7, x_232, x_220);
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
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_236 = l_Lean_Compiler_LCNF_Code_toMono(x_177, x_5, x_6, x_7, x_8, x_9, x_234);
if (lean_obj_tag(x_236) == 0)
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_237 = lean_ctor_get(x_236, 0);
lean_inc(x_237);
x_238 = lean_ctor_get(x_236, 1);
lean_inc(x_238);
lean_dec(x_236);
x_239 = lean_mk_string_unchecked("false", 5, 5);
x_240 = l_Lean_Name_mkStr2(x_181, x_239);
x_241 = lean_mk_empty_array_with_capacity(x_182);
if (lean_is_scalar(x_235)) {
 x_242 = lean_alloc_ctor(0, 2, 0);
} else {
 x_242 = x_235;
}
lean_ctor_set(x_242, 0, x_228);
lean_ctor_set(x_242, 1, x_237);
if (lean_is_scalar(x_208)) {
 x_243 = lean_alloc_ctor(0, 2, 0);
} else {
 x_243 = x_208;
}
lean_ctor_set(x_243, 0, x_206);
lean_ctor_set(x_243, 1, x_242);
x_244 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_244, 0, x_240);
lean_ctor_set(x_244, 1, x_241);
lean_ctor_set(x_244, 2, x_243);
x_16 = x_244;
x_17 = x_238;
goto block_23;
}
else
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
lean_dec(x_235);
lean_dec(x_228);
lean_dec(x_208);
lean_dec(x_206);
lean_dec(x_181);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_245 = lean_ctor_get(x_236, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_236, 1);
lean_inc(x_246);
if (lean_is_exclusive(x_236)) {
 lean_ctor_release(x_236, 0);
 lean_ctor_release(x_236, 1);
 x_247 = x_236;
} else {
 lean_dec_ref(x_236);
 x_247 = lean_box(0);
}
if (lean_is_scalar(x_247)) {
 x_248 = lean_alloc_ctor(1, 2, 0);
} else {
 x_248 = x_247;
}
lean_ctor_set(x_248, 0, x_245);
lean_ctor_set(x_248, 1, x_246);
return x_248;
}
}
}
}
else
{
lean_object* x_249; lean_object* x_250; 
x_249 = lean_ctor_get(x_13, 0);
lean_inc(x_249);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_250 = l_Lean_Compiler_LCNF_Code_toMono(x_249, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_250) == 0)
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; 
x_251 = lean_ctor_get(x_250, 0);
lean_inc(x_251);
x_252 = lean_ctor_get(x_250, 1);
lean_inc(x_252);
lean_dec(x_250);
x_253 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_13, x_251);
x_16 = x_253;
x_17 = x_252;
goto block_23;
}
else
{
uint8_t x_254; 
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_254 = !lean_is_exclusive(x_250);
if (x_254 == 0)
{
return x_250;
}
else
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; 
x_255 = lean_ctor_get(x_250, 0);
x_256 = lean_ctor_get(x_250, 1);
lean_inc(x_256);
lean_inc(x_255);
lean_dec(x_250);
x_257 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_257, 0, x_255);
lean_ctor_set(x_257, 1, x_256);
return x_257;
}
}
}
block_23:
{
lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; 
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_usize_of_nat(x_18);
x_20 = lean_usize_add(x_3, x_19);
x_21 = lean_array_uset(x_15, x_3, x_16);
x_3 = x_20;
x_4 = x_21;
x_10 = x_17;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesNatToMono___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
x_9 = l_Lean_Compiler_LCNF_toMonoType(x_8, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_mk_string_unchecked("Nat", 3, 3);
lean_inc(x_12);
x_13 = l_Lean_Name_mkStr1(x_12);
x_14 = lean_box(0);
x_15 = l_Lean_Expr_const___override(x_13, x_14);
x_16 = lean_mk_string_unchecked("zero", 4, 4);
x_17 = l_Lean_Name_mkStr1(x_16);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = l_Lean_Compiler_LCNF_mkLetDecl(x_17, x_15, x_20, x_3, x_4, x_5, x_6, x_11);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_21, 1);
x_25 = lean_mk_string_unchecked("isZero", 6, 6);
x_26 = l_Lean_Name_mkStr1(x_25);
x_27 = lean_mk_string_unchecked("Bool", 4, 4);
x_28 = l_Lean_Name_mkStr1(x_27);
lean_inc(x_28);
x_29 = l_Lean_Expr_const___override(x_28, x_14);
x_30 = lean_mk_string_unchecked("decEq", 5, 5);
x_31 = l_Lean_Name_mkStr2(x_12, x_30);
x_32 = lean_ctor_get(x_1, 2);
lean_inc(x_32);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = lean_ctor_get(x_23, 0);
lean_inc(x_34);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
x_36 = lean_unsigned_to_nat(2u);
x_37 = lean_mk_empty_array_with_capacity(x_36);
x_38 = lean_array_push(x_37, x_33);
x_39 = lean_array_push(x_38, x_35);
x_40 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_40, 0, x_31);
lean_ctor_set(x_40, 1, x_14);
lean_ctor_set(x_40, 2, x_39);
x_41 = l_Lean_Compiler_LCNF_mkLetDecl(x_26, x_29, x_40, x_3, x_4, x_5, x_6, x_24);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; size_t x_46; size_t x_47; lean_object* x_48; 
x_43 = lean_ctor_get(x_41, 0);
x_44 = lean_ctor_get(x_41, 1);
x_45 = lean_ctor_get(x_1, 3);
lean_inc(x_45);
x_46 = lean_array_size(x_45);
x_47 = lean_usize_of_nat(x_18);
x_48 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_casesNatToMono_spec__0(x_1, x_46, x_47, x_45, x_2, x_3, x_4, x_5, x_6, x_44);
lean_dec(x_1);
if (lean_obj_tag(x_48) == 0)
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_48, 0);
x_51 = lean_ctor_get(x_43, 0);
lean_inc(x_51);
x_52 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_52, 0, x_28);
lean_ctor_set(x_52, 1, x_10);
lean_ctor_set(x_52, 2, x_51);
lean_ctor_set(x_52, 3, x_50);
x_53 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_41, 1, x_53);
lean_ctor_set(x_21, 1, x_41);
lean_ctor_set(x_48, 0, x_21);
return x_48;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_54 = lean_ctor_get(x_48, 0);
x_55 = lean_ctor_get(x_48, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_48);
x_56 = lean_ctor_get(x_43, 0);
lean_inc(x_56);
x_57 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_57, 0, x_28);
lean_ctor_set(x_57, 1, x_10);
lean_ctor_set(x_57, 2, x_56);
lean_ctor_set(x_57, 3, x_54);
x_58 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_41, 1, x_58);
lean_ctor_set(x_21, 1, x_41);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_21);
lean_ctor_set(x_59, 1, x_55);
return x_59;
}
}
else
{
uint8_t x_60; 
lean_free_object(x_41);
lean_dec(x_43);
lean_dec(x_28);
lean_free_object(x_21);
lean_dec(x_23);
lean_dec(x_10);
x_60 = !lean_is_exclusive(x_48);
if (x_60 == 0)
{
return x_48;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_48, 0);
x_62 = lean_ctor_get(x_48, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_48);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; size_t x_67; size_t x_68; lean_object* x_69; 
x_64 = lean_ctor_get(x_41, 0);
x_65 = lean_ctor_get(x_41, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_41);
x_66 = lean_ctor_get(x_1, 3);
lean_inc(x_66);
x_67 = lean_array_size(x_66);
x_68 = lean_usize_of_nat(x_18);
x_69 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_casesNatToMono_spec__0(x_1, x_67, x_68, x_66, x_2, x_3, x_4, x_5, x_6, x_65);
lean_dec(x_1);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_72 = x_69;
} else {
 lean_dec_ref(x_69);
 x_72 = lean_box(0);
}
x_73 = lean_ctor_get(x_64, 0);
lean_inc(x_73);
x_74 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_74, 0, x_28);
lean_ctor_set(x_74, 1, x_10);
lean_ctor_set(x_74, 2, x_73);
lean_ctor_set(x_74, 3, x_70);
x_75 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_75, 0, x_74);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_64);
lean_ctor_set(x_76, 1, x_75);
lean_ctor_set(x_21, 1, x_76);
if (lean_is_scalar(x_72)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_72;
}
lean_ctor_set(x_77, 0, x_21);
lean_ctor_set(x_77, 1, x_71);
return x_77;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_64);
lean_dec(x_28);
lean_free_object(x_21);
lean_dec(x_23);
lean_dec(x_10);
x_78 = lean_ctor_get(x_69, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_69, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_80 = x_69;
} else {
 lean_dec_ref(x_69);
 x_80 = lean_box(0);
}
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(1, 2, 0);
} else {
 x_81 = x_80;
}
lean_ctor_set(x_81, 0, x_78);
lean_ctor_set(x_81, 1, x_79);
return x_81;
}
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; size_t x_105; size_t x_106; lean_object* x_107; 
x_82 = lean_ctor_get(x_21, 0);
x_83 = lean_ctor_get(x_21, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_21);
x_84 = lean_mk_string_unchecked("isZero", 6, 6);
x_85 = l_Lean_Name_mkStr1(x_84);
x_86 = lean_mk_string_unchecked("Bool", 4, 4);
x_87 = l_Lean_Name_mkStr1(x_86);
lean_inc(x_87);
x_88 = l_Lean_Expr_const___override(x_87, x_14);
x_89 = lean_mk_string_unchecked("decEq", 5, 5);
x_90 = l_Lean_Name_mkStr2(x_12, x_89);
x_91 = lean_ctor_get(x_1, 2);
lean_inc(x_91);
x_92 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_92, 0, x_91);
x_93 = lean_ctor_get(x_82, 0);
lean_inc(x_93);
x_94 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_94, 0, x_93);
x_95 = lean_unsigned_to_nat(2u);
x_96 = lean_mk_empty_array_with_capacity(x_95);
x_97 = lean_array_push(x_96, x_92);
x_98 = lean_array_push(x_97, x_94);
x_99 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_99, 0, x_90);
lean_ctor_set(x_99, 1, x_14);
lean_ctor_set(x_99, 2, x_98);
x_100 = l_Lean_Compiler_LCNF_mkLetDecl(x_85, x_88, x_99, x_3, x_4, x_5, x_6, x_83);
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_103 = x_100;
} else {
 lean_dec_ref(x_100);
 x_103 = lean_box(0);
}
x_104 = lean_ctor_get(x_1, 3);
lean_inc(x_104);
x_105 = lean_array_size(x_104);
x_106 = lean_usize_of_nat(x_18);
x_107 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_casesNatToMono_spec__0(x_1, x_105, x_106, x_104, x_2, x_3, x_4, x_5, x_6, x_102);
lean_dec(x_1);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_110 = x_107;
} else {
 lean_dec_ref(x_107);
 x_110 = lean_box(0);
}
x_111 = lean_ctor_get(x_101, 0);
lean_inc(x_111);
x_112 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_112, 0, x_87);
lean_ctor_set(x_112, 1, x_10);
lean_ctor_set(x_112, 2, x_111);
lean_ctor_set(x_112, 3, x_108);
x_113 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_113, 0, x_112);
if (lean_is_scalar(x_103)) {
 x_114 = lean_alloc_ctor(0, 2, 0);
} else {
 x_114 = x_103;
}
lean_ctor_set(x_114, 0, x_101);
lean_ctor_set(x_114, 1, x_113);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_82);
lean_ctor_set(x_115, 1, x_114);
if (lean_is_scalar(x_110)) {
 x_116 = lean_alloc_ctor(0, 2, 0);
} else {
 x_116 = x_110;
}
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_109);
return x_116;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
lean_dec(x_103);
lean_dec(x_101);
lean_dec(x_87);
lean_dec(x_82);
lean_dec(x_10);
x_117 = lean_ctor_get(x_107, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_107, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_119 = x_107;
} else {
 lean_dec_ref(x_107);
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
else
{
uint8_t x_121; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_121 = !lean_is_exclusive(x_9);
if (x_121 == 0)
{
return x_9;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_9, 0);
x_123 = lean_ctor_get(x_9, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_9);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
return x_124;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesNatToMono(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_casesNatToMono___redArg(x_1, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_decToMono_spec__0(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_2, x_1);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_array_uget(x_3, x_2);
x_13 = lean_box(0);
x_14 = lean_array_uset(x_3, x_2, x_13);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_23 = lean_ctor_get(x_12, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_12, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_12, 2);
lean_inc(x_25);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 lean_ctor_release(x_12, 2);
 x_26 = x_12;
} else {
 lean_dec_ref(x_12);
 x_26 = lean_box(0);
}
x_27 = l_Lean_Compiler_LCNF_eraseParams___redArg(x_24, x_6, x_9);
lean_dec(x_24);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_41 = lean_mk_string_unchecked("Decidable", 9, 9);
x_42 = lean_mk_string_unchecked("isTrue", 6, 6);
x_43 = l_Lean_Name_mkStr2(x_41, x_42);
x_44 = lean_name_eq(x_23, x_43);
lean_dec(x_43);
lean_dec(x_23);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_mk_string_unchecked("Bool", 4, 4);
x_46 = lean_mk_string_unchecked("false", 5, 5);
x_47 = l_Lean_Name_mkStr2(x_45, x_46);
x_29 = x_47;
goto block_40;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_mk_string_unchecked("Bool", 4, 4);
x_49 = lean_mk_string_unchecked("true", 4, 4);
x_50 = l_Lean_Name_mkStr2(x_48, x_49);
x_29 = x_50;
goto block_40;
}
block_40:
{
lean_object* x_30; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_30 = l_Lean_Compiler_LCNF_Code_toMono(x_25, x_4, x_5, x_6, x_7, x_8, x_28);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_unsigned_to_nat(0u);
x_34 = lean_mk_empty_array_with_capacity(x_33);
if (lean_is_scalar(x_26)) {
 x_35 = lean_alloc_ctor(0, 3, 0);
} else {
 x_35 = x_26;
}
lean_ctor_set(x_35, 0, x_29);
lean_ctor_set(x_35, 1, x_34);
lean_ctor_set(x_35, 2, x_31);
x_15 = x_35;
x_16 = x_32;
goto block_22;
}
else
{
uint8_t x_36; 
lean_dec(x_29);
lean_dec(x_26);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_36 = !lean_is_exclusive(x_30);
if (x_36 == 0)
{
return x_30;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_30, 0);
x_38 = lean_ctor_get(x_30, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_30);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_12, 0);
lean_inc(x_51);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_52 = l_Lean_Compiler_LCNF_Code_toMono(x_51, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_12, x_53);
x_15 = x_55;
x_16 = x_54;
goto block_22;
}
else
{
uint8_t x_56; 
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_56 = !lean_is_exclusive(x_52);
if (x_56 == 0)
{
return x_52;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_52, 0);
x_58 = lean_ctor_get(x_52, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_52);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
block_22:
{
lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_usize_of_nat(x_17);
x_19 = lean_usize_add(x_2, x_18);
x_20 = lean_array_uset(x_14, x_2, x_15);
x_2 = x_19;
x_3 = x_20;
x_9 = x_16;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_decToMono___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
x_9 = l_Lean_Compiler_LCNF_toMonoType(x_8, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; lean_object* x_14; size_t x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_1, 3);
lean_inc(x_12);
x_13 = lean_array_size(x_12);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_usize_of_nat(x_14);
x_16 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_decToMono_spec__0(x_13, x_15, x_12, x_2, x_3, x_4, x_5, x_6, x_11);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_mk_string_unchecked("Bool", 4, 4);
x_20 = l_Lean_Name_mkStr1(x_19);
x_21 = lean_ctor_get(x_1, 2);
lean_inc(x_21);
lean_dec(x_1);
x_22 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_10);
lean_ctor_set(x_22, 2, x_21);
lean_ctor_set(x_22, 3, x_18);
x_23 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_16, 0, x_23);
return x_16;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_24 = lean_ctor_get(x_16, 0);
x_25 = lean_ctor_get(x_16, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_16);
x_26 = lean_mk_string_unchecked("Bool", 4, 4);
x_27 = l_Lean_Name_mkStr1(x_26);
x_28 = lean_ctor_get(x_1, 2);
lean_inc(x_28);
lean_dec(x_1);
x_29 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_10);
lean_ctor_set(x_29, 2, x_28);
lean_ctor_set(x_29, 3, x_24);
x_30 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_25);
return x_31;
}
}
else
{
uint8_t x_32; 
lean_dec(x_10);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_16);
if (x_32 == 0)
{
return x_16;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_16, 0);
x_34 = lean_ctor_get(x_16, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_16);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
uint8_t x_36; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_9);
if (x_36 == 0)
{
return x_9;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_9, 0);
x_38 = lean_ctor_get(x_9, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_9);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_decToMono(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_decToMono___redArg(x_1, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_FunDeclCore_toMono_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_FunDeclCore_toMono_spec__0___redArg(x_9, x_10, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_5);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_FunDeclCore_toMono_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_FunDeclCore_toMono_spec__0(x_10, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Code_toMono_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Code_toMono_spec__0(x_10, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_trivialStructToMono___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_trivialStructToMono(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesStringToMono___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_casesStringToMono___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesStringToMono___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_casesStringToMono(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloatArrayToMono___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_casesFloatArrayToMono(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesByteArrayToMono___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_casesByteArrayToMono(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesArrayToMono___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_casesArrayToMono___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesArrayToMono___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_casesArrayToMono(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesUIntToMono___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_casesUIntToMono___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesUIntToMono___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_casesUIntToMono(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_casesIntToMono_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_casesIntToMono_spec__0(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_casesNatToMono_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_casesNatToMono_spec__0(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_decToMono_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_decToMono_spec__0(x_10, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___Lean_Compiler_LCNF_Decl_toMono_go_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_apply_7(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_11, 0);
lean_ctor_set(x_2, 0, x_13);
lean_ctor_set(x_11, 0, x_2);
return x_11;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_11, 0);
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_11);
lean_ctor_set(x_2, 0, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_2);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
uint8_t x_17; 
lean_free_object(x_2);
x_17 = !lean_is_exclusive(x_11);
if (x_17 == 0)
{
return x_11;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_11, 0);
x_19 = lean_ctor_get(x_11, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_11);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_2, 0);
lean_inc(x_21);
lean_dec(x_2);
x_22 = lean_apply_7(x_1, x_21, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
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
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_23);
if (lean_is_scalar(x_25)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_25;
}
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_24);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_22, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_22, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_30 = x_22;
} else {
 lean_dec_ref(x_22);
 x_30 = lean_box(0);
}
if (lean_is_scalar(x_30)) {
 x_31 = lean_alloc_ctor(1, 2, 0);
} else {
 x_31 = x_30;
}
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
}
else
{
lean_object* x_32; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_2);
lean_ctor_set(x_32, 1, x_8);
return x_32;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_toMono_go___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_Code_toMono(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_toMono_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
x_9 = l_Lean_Compiler_LCNF_toMonoType(x_8, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; lean_object* x_14; size_t x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_1, 3);
lean_inc(x_12);
x_13 = lean_array_size(x_12);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_usize_of_nat(x_14);
lean_inc(x_6);
lean_inc(x_5);
x_16 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_FunDeclCore_toMono_spec__0___redArg(x_13, x_15, x_12, x_2, x_4, x_5, x_6, x_11);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Decl_toMono_go___lam__0), 7, 0);
x_20 = lean_ctor_get(x_1, 4);
lean_inc(x_20);
lean_inc(x_6);
x_21 = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___Lean_Compiler_LCNF_Decl_toMono_go_spec__0(x_19, x_20, x_2, x_3, x_4, x_5, x_6, x_18);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_ctor_get(x_1, 0);
lean_inc(x_24);
x_25 = lean_box(0);
x_26 = lean_ctor_get_uint8(x_1, sizeof(void*)*6);
x_27 = lean_ctor_get_uint8(x_1, sizeof(void*)*6 + 1);
x_28 = lean_ctor_get(x_1, 5);
lean_inc(x_28);
lean_dec(x_1);
x_29 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_29, 0, x_24);
lean_ctor_set(x_29, 1, x_25);
lean_ctor_set(x_29, 2, x_10);
lean_ctor_set(x_29, 3, x_17);
lean_ctor_set(x_29, 4, x_22);
lean_ctor_set(x_29, 5, x_28);
lean_ctor_set_uint8(x_29, sizeof(void*)*6, x_26);
lean_ctor_set_uint8(x_29, sizeof(void*)*6 + 1, x_27);
lean_inc(x_29);
x_30 = l_Lean_Compiler_LCNF_Decl_saveMono___redArg(x_29, x_6, x_23);
lean_dec(x_6);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_30, 0);
lean_dec(x_32);
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_dec(x_30);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_29);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
else
{
uint8_t x_35; 
lean_dec(x_17);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_21);
if (x_35 == 0)
{
return x_21;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_21, 0);
x_37 = lean_ctor_get(x_21, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_21);
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
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_16);
if (x_39 == 0)
{
return x_16;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_16, 0);
x_41 = lean_ctor_get(x_16, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_16);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_9);
if (x_43 == 0)
{
return x_9;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_9, 0);
x_45 = lean_ctor_get(x_9, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_9);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_toMono(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_box(0);
x_8 = lean_st_mk_ref(x_7, x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_9);
x_11 = l_Lean_Compiler_LCNF_Decl_toMono_go(x_1, x_9, x_2, x_3, x_4, x_5, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_st_ref_get(x_9, x_13);
lean_dec(x_9);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
lean_ctor_set(x_14, 0, x_12);
return x_14;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_12);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
lean_dec(x_9);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_toMono_spec__0(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_2, x_1);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_array_uget(x_3, x_2);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_12 = l_Lean_Compiler_LCNF_Decl_toMono(x_11, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_box(0);
x_16 = lean_array_uset(x_3, x_2, x_15);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_usize_of_nat(x_17);
x_19 = lean_usize_add(x_2, x_18);
x_20 = lean_array_uset(x_16, x_2, x_13);
x_2 = x_19;
x_3 = x_20;
x_8 = x_14;
goto _start;
}
else
{
uint8_t x_22; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_22 = !lean_is_exclusive(x_12);
if (x_22 == 0)
{
return x_12;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_12, 0);
x_24 = lean_ctor_get(x_12, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_12);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toMono___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; lean_object* x_8; size_t x_9; lean_object* x_10; 
x_7 = lean_array_size(x_1);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_usize_of_nat(x_8);
x_10 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_toMono_spec__0(x_7, x_9, x_1, x_2, x_3, x_4, x_5, x_6);
return x_10;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toMono() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_toMono___lam__0), 6, 0);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_box(0);
x_4 = lean_box(1);
x_5 = lean_mk_string_unchecked("toMono", 6, 6);
x_6 = l_Lean_Name_mkStr1(x_5);
x_7 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_6);
lean_ctor_set(x_7, 2, x_1);
x_8 = lean_unbox(x_3);
lean_ctor_set_uint8(x_7, sizeof(void*)*3, x_8);
x_9 = lean_unbox(x_4);
lean_ctor_set_uint8(x_7, sizeof(void*)*3 + 1, x_9);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_toMono_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_toMono_spec__0(x_9, x_10, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ToMono___hyg_4097_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_2 = lean_mk_string_unchecked("Compiler", 8, 8);
x_3 = lean_mk_string_unchecked("toMono", 6, 6);
lean_inc(x_2);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_box(0);
x_7 = lean_mk_string_unchecked("Lean", 4, 4);
lean_inc(x_7);
x_8 = l_Lean_Name_str___override(x_6, x_7);
lean_inc(x_2);
x_9 = l_Lean_Name_str___override(x_8, x_2);
x_10 = lean_mk_string_unchecked("LCNF", 4, 4);
lean_inc(x_10);
x_11 = l_Lean_Name_str___override(x_9, x_10);
x_12 = lean_mk_string_unchecked("initFn", 6, 6);
x_13 = l_Lean_Name_str___override(x_11, x_12);
x_14 = lean_mk_string_unchecked("_@", 2, 2);
x_15 = l_Lean_Name_str___override(x_13, x_14);
x_16 = l_Lean_Name_str___override(x_15, x_7);
x_17 = l_Lean_Name_str___override(x_16, x_2);
x_18 = l_Lean_Name_str___override(x_17, x_10);
x_19 = lean_mk_string_unchecked("ToMono", 6, 6);
x_20 = l_Lean_Name_str___override(x_18, x_19);
x_21 = lean_mk_string_unchecked("_hyg", 4, 4);
x_22 = l_Lean_Name_str___override(x_20, x_21);
x_23 = lean_unsigned_to_nat(4097u);
x_24 = l_Lean_Name_num___override(x_22, x_23);
x_25 = lean_unbox(x_5);
x_26 = l_Lean_registerTraceClass(x_4, x_25, x_24, x_1);
return x_26;
}
}
lean_object* initialize_Lean_Compiler_LCNF_MonoTypes(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_InferType(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_ToMono(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_MonoTypes(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_InferType(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_LCNF_toMono = _init_l_Lean_Compiler_LCNF_toMono();
lean_mark_persistent(l_Lean_Compiler_LCNF_toMono);
if (builtin) {res = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ToMono___hyg_4097_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
