// Lean compiler output
// Module: Lean.Compiler.LCNF.ExplicitRC
// Imports: public import Lean.Compiler.LCNF.CompilerM public import Lean.Compiler.LCNF.PassManager import Lean.Compiler.LCNF.PhaseExt import Lean.Compiler.LCNF.CheckRC import Lean.Compiler.LCNF.PrettyPrinter
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
lean_object* lean_array_get_size(lean_object*);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instBEqFVarId_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_instHashableFVarId_hash___boxed(lean_object*);
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Compiler_LCNF_instInhabitedCode_default__1(uint8_t);
lean_object* lean_panic_fn(lean_object*, lean_object*);
extern lean_object* l_Lean_instEmptyCollectionFVarIdHashSet;
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isPossibleRef(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_instBEqArg_beq___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedParam_default(uint8_t);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_qpartition___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedFVarIdHashSet;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_CtorInfo_type(lean_object*);
uint8_t l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isDefiniteRef(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_checkRC(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
lean_object* l_Lean_Compiler_LCNF_PP_ppLetDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_PP_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Compiler_LCNF_getPurity___redArg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_toLocalContext(lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getImpureSignature_x3f___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedSignature_default(uint8_t);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedFunDecl_default__1(uint8_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(lean_object*, uint8_t, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_instInhabitedDerivedValInfo_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_instInhabitedDerivedValInfo_default___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_instInhabitedDerivedValInfo_default___closed__0_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_instInhabitedDerivedValInfo_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_instInhabitedDerivedValInfo_default___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_instInhabitedDerivedValInfo_default;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_instInhabitedDerivedValInfo;
static const lean_closure_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_visitParam___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqFVarId_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_visitParam___redArg___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_visitParam___redArg___closed__0_value;
static const lean_closure_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_visitParam___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashableFVarId_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_visitParam___redArg___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_visitParam___redArg___closed__1_value;
static const lean_array_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_visitParam___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_visitParam___redArg___closed__2 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_visitParam___redArg___closed__2_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_visitParam___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_visitParam___redArg___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_visitParam___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_visitParam___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_visitParam(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_visitParam___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_addDerivedValue___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_addDerivedValue___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_addDerivedValue___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_addDerivedValue___redArg___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_addDerivedValue___redArg___closed__0_value;
static const lean_closure_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_addDerivedValue___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_addDerivedValue___redArg___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_addDerivedValue___redArg___closed__1_value;
static const lean_closure_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_addDerivedValue___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_addDerivedValue___redArg___closed__2 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_addDerivedValue___redArg___closed__2_value;
static const lean_closure_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_addDerivedValue___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_addDerivedValue___redArg___closed__3 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_addDerivedValue___redArg___closed__3_value;
static const lean_closure_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_addDerivedValue___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_addDerivedValue___redArg___closed__4 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_addDerivedValue___redArg___closed__4_value;
static const lean_closure_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_addDerivedValue___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_addDerivedValue___redArg___closed__5 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_addDerivedValue___redArg___closed__5_value;
static const lean_closure_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_addDerivedValue___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_addDerivedValue___redArg___closed__6 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_addDerivedValue___redArg___closed__6_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_addDerivedValue___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_addDerivedValue___redArg___closed__0_value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_addDerivedValue___redArg___closed__1_value)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_addDerivedValue___redArg___closed__7 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_addDerivedValue___redArg___closed__7_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_addDerivedValue___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_addDerivedValue___redArg___closed__7_value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_addDerivedValue___redArg___closed__2_value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_addDerivedValue___redArg___closed__3_value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_addDerivedValue___redArg___closed__4_value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_addDerivedValue___redArg___closed__5_value)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_addDerivedValue___redArg___closed__8 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_addDerivedValue___redArg___closed__8_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_addDerivedValue___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_addDerivedValue___redArg___closed__8_value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_addDerivedValue___redArg___closed__6_value)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_addDerivedValue___redArg___closed__9 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_addDerivedValue___redArg___closed__9_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_addDerivedValue___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_addDerivedValue___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_addDerivedValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_addDerivedValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_removeFromParent_spec__1_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_removeFromParent_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_removeFromParent_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_removeFromParent_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_removeFromParent_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_removeFromParent_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_removeFromParent_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_removeFromParent_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_removeFromParent_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_removeFromParent_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_removeFromParent_spec__2_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_removeFromParent_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_removeFromParent_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_removeFromParent_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_removeFromParent_spec__3___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_removeFromParent_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_removeFromParent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_removeFromParent___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_removeFromParent_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_removeFromParent_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_removeFromParent_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_removeFromParent_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_removeFromParent_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_removeFromParent_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_removeFromParent_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_removeFromParent_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_removeFromParent_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_removeFromParent_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_removeFromParent_spec__1_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_removeFromParent_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__7___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__7___closed__0;
static const lean_closure_object l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__7___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__7___closed__1 = (const lean_object*)&l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__7___closed__1_value;
static const lean_closure_object l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__7___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__7___closed__2 = (const lean_object*)&l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__7___closed__2_value;
static const lean_closure_object l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__7___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__7___closed__3 = (const lean_object*)&l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__7___closed__3_value;
static const lean_closure_object l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__7___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__7___closed__4 = (const lean_object*)&l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__7___closed__4_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__0_spec__0_spec__3_spec__9___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__0_spec__0_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__0_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__3_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__5___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Array"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode___closed__0_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "getInternal"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode___closed__1_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "get!Internal"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode___closed__2 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode___closed__2_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "uget"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode___closed__3 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode___closed__3_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode___closed__6 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode___closed__6_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 94, .m_capacity = 94, .m_length = 93, .m_data = "_private.Lean.Compiler.LCNF.ExplicitRC.0.Lean.Compiler.LCNF.CollectDerivedValInfo.collectCode"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode___closed__5 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode___closed__5_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "Lean.Compiler.LCNF.ExplicitRC"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode___closed__4 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode___closed__4_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__6(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__0_spec__0_spec__3_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collect_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collect_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collect___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collect___closed__0;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collect___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collect___closed__1;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collect___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collect___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collect(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collect___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_instInhabitedVarInfo_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_instInhabitedVarInfo_default___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_instInhabitedVarInfo_default___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_instInhabitedVarInfo_default = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_instInhabitedVarInfo_default___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_instInhabitedVarInfo = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_instInhabitedVarInfo_default___closed__0_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_instInhabitedLiveVars_default;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_instInhabitedLiveVars;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___lam__0, .m_arity = 5, .m_num_fixed = 2, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_visitParam___redArg___closed__0_value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_visitParam___redArg___closed__1_value)} };
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__0_value;
static const lean_closure_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg___lam__2, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_addDerivedValue___redArg___closed__9_value)} };
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__1_value;
static const lean_closure_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___lam__1, .m_arity = 5, .m_num_fixed = 2, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_addDerivedValue___redArg___closed__9_value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__0_value)} };
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__2 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_erase(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_insertBorrow(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_isAccessible_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_isAccessible_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_isAccessible(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_isAccessible___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_isAccessible_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_isAccessible_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getVarInfo___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getVarInfo___redArg___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getVarInfo___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getVarInfo___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getVarInfo___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getVarInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getVarInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getJpLiveVars___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getJpLiveVars___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getJpLiveVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getJpLiveVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isLive___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isLive___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isLive(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isLive___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowed___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowed___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowed___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isAccessible___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isAccessible___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isAccessible(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isAccessible___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_modifyLive___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_modifyLive___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_modifyLive(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_modifyLive___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withParams___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withParams___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withParams___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withParams___redArg___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withParams___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withParams___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withParams___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetValue_isPersistent(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetValue_isPersistent___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withLetDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withLetDecl___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withLetDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withCtorAlt___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withCtorAlt___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withCtorAlt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withCtorAlt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withCollectLiveVars___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withCollectLiveVars___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withCollectLiveVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withCollectLiveVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendantsAux_spec__1(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendantsAux_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendantsAux_spec__0_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "Std.Data.DHashMap.Internal.AssocList.Basic"};
static const lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendantsAux_spec__0_spec__0___redArg___closed__0 = (const lean_object*)&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendantsAux_spec__0_spec__0___redArg___closed__0_value;
static const lean_string_object l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendantsAux_spec__0_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.DHashMap.Internal.AssocList.get!"};
static const lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendantsAux_spec__0_spec__0___redArg___closed__1 = (const lean_object*)&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendantsAux_spec__0_spec__0___redArg___closed__1_value;
static const lean_string_object l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendantsAux_spec__0_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "key is not present in hash table"};
static const lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendantsAux_spec__0_spec__0___redArg___closed__2 = (const lean_object*)&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendantsAux_spec__0_spec__0___redArg___closed__2_value;
static lean_once_cell_t l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendantsAux_spec__0_spec__0___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendantsAux_spec__0_spec__0___redArg___closed__3;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendantsAux_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendantsAux_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendantsAux_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendantsAux_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendantsAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendantsAux_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendantsAux_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendantsAux_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendantsAux___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendantsAux_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendantsAux_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendantsAux_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendantsAux_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendantsAux_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendantsAux_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendantsAux_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_markLive___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_markLive___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_markLive(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_markLive___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_markDescendantsBorrowed___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_markDescendantsBorrowed___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_markDescendantsBorrowed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_markDescendantsBorrowed___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 72, .m_capacity = 72, .m_length = 71, .m_data = "_private.Lean.Compiler.LCNF.ExplicitRC.0.Lean.Compiler.LCNF.useLetValue"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue___closed__0_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_bindVar___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_bindVar___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_bindVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_bindVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_setRetLiveVars_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_setRetLiveVars_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_setRetLiveVars_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_setRetLiveVars_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_setRetLiveVars___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_setRetLiveVars___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_setRetLiveVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_setRetLiveVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addInc___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addInc___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addInc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addInc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Std.Data.DTreeMap.Internal.Queries"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__0___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__0___redArg___closed__0_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "Std.DTreeMap.Internal.Impl.Const.get!"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__0___redArg___closed__1 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__0___redArg___closed__1_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Key is not present in map"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__0___redArg___closed__2 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__0___redArg___closed__2_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__0___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__0___redArg___closed__3;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__4___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__4___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__4___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__4___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__4___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__5___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt___closed__0_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isFirstOcc_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isFirstOcc_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isFirstOcc(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isFirstOcc___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isFirstOcc_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isFirstOcc_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParamAux_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParamAux_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParamAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParamAux___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParamAux_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParamAux_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParam___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParam___lam__0___closed__0;
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParam___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParam___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParam(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParam___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getNumConsumptions_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getNumConsumptions_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getNumConsumptions(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getNumConsumptions___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getNumConsumptions_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getNumConsumptions_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBefore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBefore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeConsumeAll___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeConsumeAll___lam__0___boxed(lean_object*);
static const lean_closure_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeConsumeAll___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeConsumeAll___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeConsumeAll___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeConsumeAll___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeConsumeAll(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeConsumeAll___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecAfterFullApp_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecAfterFullApp_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecAfterFullApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecAfterFullApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecAfterFullApp_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecAfterFullApp_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecIfNeeded___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecIfNeeded___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecIfNeeded(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecIfNeeded___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_ensureNoBorrow_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_ensureNoBorrow_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_ensureNoBorrow_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_ensureNoBorrow_spec__0___redArg___closed__1;
static lean_once_cell_t l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_ensureNoBorrow_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_ensureNoBorrow_spec__0___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_ensureNoBorrow_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_ensureNoBorrow_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_ensureNoBorrow_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_ensureNoBorrow_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_ensureNoBorrow___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "failed"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_ensureNoBorrow___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_ensureNoBorrow___closed__0_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_ensureNoBorrow___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_ensureNoBorrow___closed__1;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_ensureNoBorrow___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "\nis borrowed but shouldn't be"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_ensureNoBorrow___closed__2 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_ensureNoBorrow___closed__2_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_ensureNoBorrow___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_ensureNoBorrow___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_ensureNoBorrow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_ensureNoBorrow___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "failed: "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = " has "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0___closed__3;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0___closed__5_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__0___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__0(lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__1___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Lean.Compiler.LCNF.Basic"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__0_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "_private.Lean.Compiler.LCNF.Basic.0.Lean.Compiler.LCNF.updateLetImp"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__1_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "ugetBorrowed"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__3 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__3_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "get!InternalBorrowed"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__4 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__4_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "getInternalBorrowed"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__5 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__5_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode___closed__0_value),LEAN_SCALAR_PTR_LITERAL(81, 46, 193, 1, 46, 43, 107, 121)}};
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode___closed__1_value),LEAN_SCALAR_PTR_LITERAL(91, 223, 205, 20, 178, 155, 84, 168)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__6 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__6_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Init.Data.Option.BasicAux"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__7 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__7_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Option.get!"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__8 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__8_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "value is none"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__9 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__9_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__10;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "_private.Lean.Compiler.LCNF.ExplicitRC.0.Lean.Compiler.LCNF.LetDecl.explicitRc"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__11 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__11_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__12;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__4___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__4___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__4(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__0_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__8(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__7(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 76, .m_capacity = 76, .m_length = 75, .m_data = "_private.Lean.Compiler.LCNF.ExplicitRC.0.Lean.Compiler.LCNF.Code.explicitRc"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc___closed__0_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__6(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_runExplicitRc_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_runExplicitRc_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_runExplicitRc_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_runExplicitRc_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_runExplicitRc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_runExplicitRc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_explicitRc___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "explicitRc"};
static const lean_object* l_Lean_Compiler_LCNF_explicitRc___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_explicitRc___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_explicitRc___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_explicitRc___closed__0_value),LEAN_SCALAR_PTR_LITERAL(9, 173, 65, 140, 38, 197, 53, 106)}};
static const lean_object* l_Lean_Compiler_LCNF_explicitRc___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_explicitRc___closed__1_value;
static const lean_closure_object l_Lean_Compiler_LCNF_explicitRc___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_explicitRc___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_explicitRc___closed__2_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_explicitRc___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_explicitRc___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_explicitRc;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Compiler"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(253, 55, 142, 128, 91, 63, 88, 28)}};
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_explicitRc___closed__0_value),LEAN_SCALAR_PTR_LITERAL(31, 132, 102, 171, 122, 154, 149, 18)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(72, 245, 227, 28, 172, 102, 215, 20)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "LCNF"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(225, 25, 15, 1, 146, 18, 87, 58)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "ExplicitRC"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(87, 164, 3, 212, 141, 65, 76, 246)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(234, 211, 142, 143, 107, 33, 215, 207)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(107, 250, 223, 192, 104, 128, 184, 149)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(141, 253, 97, 148, 179, 46, 109, 198)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(184, 97, 91, 211, 31, 209, 125, 32)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(245, 202, 70, 178, 192, 164, 153, 156)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(8, 238, 44, 6, 75, 144, 17, 52)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(225, 123, 124, 125, 95, 169, 195, 145)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(143, 99, 255, 139, 23, 91, 187, 231)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(226, 146, 98, 9, 226, 177, 155, 125)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(152, 80, 138, 101, 161, 95, 63, 48)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2____boxed(lean_object*);
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_instInhabitedDerivedValInfo_default___closed__1(void){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_3_ = l_Lean_instInhabitedFVarIdHashSet;
v___x_4_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_instInhabitedDerivedValInfo_default___closed__0));
v___x_5_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5_, 0, v___x_4_);
lean_ctor_set(v___x_5_, 1, v___x_3_);
return v___x_5_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_instInhabitedDerivedValInfo_default(void){
_start:
{
lean_object* v___x_6_; 
v___x_6_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_instInhabitedDerivedValInfo_default___closed__1, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_instInhabitedDerivedValInfo_default___closed__1_once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_instInhabitedDerivedValInfo_default___closed__1);
return v___x_6_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_instInhabitedDerivedValInfo(void){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_instInhabitedDerivedValInfo_default;
return v___x_7_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_visitParam___redArg___closed__3(void){
_start:
{
lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; 
v___x_12_ = l_Lean_instEmptyCollectionFVarIdHashSet;
v___x_13_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_visitParam___redArg___closed__2));
v___x_14_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_14_, 0, v___x_13_);
lean_ctor_set(v___x_14_, 1, v___x_12_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_visitParam___redArg(lean_object* v_p_15_, lean_object* v_a_16_){
_start:
{
lean_object* v___x_18_; lean_object* v_fst_20_; lean_object* v_snd_21_; lean_object* v_varMap_24_; lean_object* v_borrowedParams_25_; lean_object* v___x_27_; uint8_t v_isShared_28_; uint8_t v_isSharedCheck_44_; 
v___x_18_ = lean_st_ref_take(v_a_16_);
v_varMap_24_ = lean_ctor_get(v___x_18_, 0);
v_borrowedParams_25_ = lean_ctor_get(v___x_18_, 1);
v_isSharedCheck_44_ = !lean_is_exclusive(v___x_18_);
if (v_isSharedCheck_44_ == 0)
{
v___x_27_ = v___x_18_;
v_isShared_28_ = v_isSharedCheck_44_;
goto v_resetjp_26_;
}
else
{
lean_inc(v_borrowedParams_25_);
lean_inc(v_varMap_24_);
lean_dec(v___x_18_);
v___x_27_ = lean_box(0);
v_isShared_28_ = v_isSharedCheck_44_;
goto v_resetjp_26_;
}
v___jp_19_:
{
lean_object* v___x_22_; lean_object* v___x_23_; 
v___x_22_ = lean_st_ref_set(v_a_16_, v_snd_21_);
v___x_23_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_23_, 0, v_fst_20_);
return v___x_23_;
}
v_resetjp_26_:
{
lean_object* v_fvarId_29_; lean_object* v_type_30_; uint8_t v_borrow_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; 
v_fvarId_29_ = lean_ctor_get(v_p_15_, 0);
lean_inc(v_fvarId_29_);
v_type_30_ = lean_ctor_get(v_p_15_, 2);
lean_inc_ref(v_type_30_);
v_borrow_31_ = lean_ctor_get_uint8(v_p_15_, sizeof(void*)*3);
lean_dec_ref(v_p_15_);
v___x_32_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_visitParam___redArg___closed__0));
v___x_33_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_visitParam___redArg___closed__1));
v___x_34_ = lean_box(0);
v___x_35_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_visitParam___redArg___closed__3, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_visitParam___redArg___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_visitParam___redArg___closed__3);
lean_inc(v_fvarId_29_);
v___x_36_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_32_, v___x_33_, v_varMap_24_, v_fvarId_29_, v___x_35_);
if (v_borrow_31_ == 0)
{
lean_dec_ref(v_type_30_);
lean_dec(v_fvarId_29_);
goto v___jp_37_;
}
else
{
uint8_t v___x_41_; 
v___x_41_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isPossibleRef(v_type_30_);
lean_dec_ref(v_type_30_);
if (v___x_41_ == 0)
{
lean_dec(v_fvarId_29_);
goto v___jp_37_;
}
else
{
lean_object* v___x_42_; lean_object* v___x_43_; 
lean_del_object(v___x_27_);
v___x_42_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_32_, v___x_33_, v_borrowedParams_25_, v_fvarId_29_, v___x_34_);
v___x_43_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_43_, 0, v___x_36_);
lean_ctor_set(v___x_43_, 1, v___x_42_);
v_fst_20_ = v___x_34_;
v_snd_21_ = v___x_43_;
goto v___jp_19_;
}
}
v___jp_37_:
{
lean_object* v___x_39_; 
if (v_isShared_28_ == 0)
{
lean_ctor_set(v___x_27_, 0, v___x_36_);
v___x_39_ = v___x_27_;
goto v_reusejp_38_;
}
else
{
lean_object* v_reuseFailAlloc_40_; 
v_reuseFailAlloc_40_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_40_, 0, v___x_36_);
lean_ctor_set(v_reuseFailAlloc_40_, 1, v_borrowedParams_25_);
v___x_39_ = v_reuseFailAlloc_40_;
goto v_reusejp_38_;
}
v_reusejp_38_:
{
v_fst_20_ = v___x_34_;
v_snd_21_ = v___x_39_;
goto v___jp_19_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_visitParam___redArg___boxed(lean_object* v_p_45_, lean_object* v_a_46_, lean_object* v_a_47_){
_start:
{
lean_object* v_res_48_; 
v_res_48_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_visitParam___redArg(v_p_45_, v_a_46_);
lean_dec(v_a_46_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_visitParam(lean_object* v_p_49_, lean_object* v_a_50_, lean_object* v_a_51_, lean_object* v_a_52_, lean_object* v_a_53_, lean_object* v_a_54_){
_start:
{
lean_object* v___x_56_; lean_object* v_fst_58_; lean_object* v_snd_59_; lean_object* v_varMap_62_; lean_object* v_borrowedParams_63_; lean_object* v___x_65_; uint8_t v_isShared_66_; uint8_t v_isSharedCheck_82_; 
v___x_56_ = lean_st_ref_take(v_a_50_);
v_varMap_62_ = lean_ctor_get(v___x_56_, 0);
v_borrowedParams_63_ = lean_ctor_get(v___x_56_, 1);
v_isSharedCheck_82_ = !lean_is_exclusive(v___x_56_);
if (v_isSharedCheck_82_ == 0)
{
v___x_65_ = v___x_56_;
v_isShared_66_ = v_isSharedCheck_82_;
goto v_resetjp_64_;
}
else
{
lean_inc(v_borrowedParams_63_);
lean_inc(v_varMap_62_);
lean_dec(v___x_56_);
v___x_65_ = lean_box(0);
v_isShared_66_ = v_isSharedCheck_82_;
goto v_resetjp_64_;
}
v___jp_57_:
{
lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_60_ = lean_st_ref_set(v_a_50_, v_snd_59_);
v___x_61_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_61_, 0, v_fst_58_);
return v___x_61_;
}
v_resetjp_64_:
{
lean_object* v_fvarId_67_; lean_object* v_type_68_; uint8_t v_borrow_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; 
v_fvarId_67_ = lean_ctor_get(v_p_49_, 0);
lean_inc(v_fvarId_67_);
v_type_68_ = lean_ctor_get(v_p_49_, 2);
lean_inc_ref(v_type_68_);
v_borrow_69_ = lean_ctor_get_uint8(v_p_49_, sizeof(void*)*3);
lean_dec_ref(v_p_49_);
v___x_70_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_visitParam___redArg___closed__0));
v___x_71_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_visitParam___redArg___closed__1));
v___x_72_ = lean_box(0);
v___x_73_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_visitParam___redArg___closed__3, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_visitParam___redArg___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_visitParam___redArg___closed__3);
lean_inc(v_fvarId_67_);
v___x_74_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_70_, v___x_71_, v_varMap_62_, v_fvarId_67_, v___x_73_);
if (v_borrow_69_ == 0)
{
lean_dec_ref(v_type_68_);
lean_dec(v_fvarId_67_);
goto v___jp_75_;
}
else
{
uint8_t v___x_79_; 
v___x_79_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isPossibleRef(v_type_68_);
lean_dec_ref(v_type_68_);
if (v___x_79_ == 0)
{
lean_dec(v_fvarId_67_);
goto v___jp_75_;
}
else
{
lean_object* v___x_80_; lean_object* v___x_81_; 
lean_del_object(v___x_65_);
v___x_80_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_70_, v___x_71_, v_borrowedParams_63_, v_fvarId_67_, v___x_72_);
v___x_81_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_81_, 0, v___x_74_);
lean_ctor_set(v___x_81_, 1, v___x_80_);
v_fst_58_ = v___x_72_;
v_snd_59_ = v___x_81_;
goto v___jp_57_;
}
}
v___jp_75_:
{
lean_object* v___x_77_; 
if (v_isShared_66_ == 0)
{
lean_ctor_set(v___x_65_, 0, v___x_74_);
v___x_77_ = v___x_65_;
goto v_reusejp_76_;
}
else
{
lean_object* v_reuseFailAlloc_78_; 
v_reuseFailAlloc_78_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_78_, 0, v___x_74_);
lean_ctor_set(v_reuseFailAlloc_78_, 1, v_borrowedParams_63_);
v___x_77_ = v_reuseFailAlloc_78_;
goto v_reusejp_76_;
}
v_reusejp_76_:
{
v_fst_58_ = v___x_72_;
v_snd_59_ = v___x_77_;
goto v___jp_57_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_visitParam___boxed(lean_object* v_p_83_, lean_object* v_a_84_, lean_object* v_a_85_, lean_object* v_a_86_, lean_object* v_a_87_, lean_object* v_a_88_, lean_object* v_a_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_visitParam(v_p_83_, v_a_84_, v_a_85_, v_a_86_, v_a_87_, v_a_88_);
lean_dec(v_a_88_);
lean_dec_ref(v_a_87_);
lean_dec(v_a_86_);
lean_dec_ref(v_a_85_);
lean_dec(v_a_84_);
return v_res_90_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_addDerivedValue___redArg___lam__0(lean_object* v___x_91_, lean_object* v___x_92_, lean_object* v_child_93_, lean_object* v_info_94_){
_start:
{
lean_object* v_parents_95_; lean_object* v_children_96_; lean_object* v___x_98_; uint8_t v_isShared_99_; uint8_t v_isSharedCheck_105_; 
v_parents_95_ = lean_ctor_get(v_info_94_, 0);
v_children_96_ = lean_ctor_get(v_info_94_, 1);
v_isSharedCheck_105_ = !lean_is_exclusive(v_info_94_);
if (v_isSharedCheck_105_ == 0)
{
v___x_98_ = v_info_94_;
v_isShared_99_ = v_isSharedCheck_105_;
goto v_resetjp_97_;
}
else
{
lean_inc(v_children_96_);
lean_inc(v_parents_95_);
lean_dec(v_info_94_);
v___x_98_ = lean_box(0);
v_isShared_99_ = v_isSharedCheck_105_;
goto v_resetjp_97_;
}
v_resetjp_97_:
{
lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_103_; 
v___x_100_ = lean_box(0);
v___x_101_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_91_, v___x_92_, v_children_96_, v_child_93_, v___x_100_);
if (v_isShared_99_ == 0)
{
lean_ctor_set(v___x_98_, 1, v___x_101_);
v___x_103_ = v___x_98_;
goto v_reusejp_102_;
}
else
{
lean_object* v_reuseFailAlloc_104_; 
v_reuseFailAlloc_104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_104_, 0, v_parents_95_);
lean_ctor_set(v_reuseFailAlloc_104_, 1, v___x_101_);
v___x_103_ = v_reuseFailAlloc_104_;
goto v_reusejp_102_;
}
v_reusejp_102_:
{
return v___x_103_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_addDerivedValue___redArg___lam__1(lean_object* v___x_106_, lean_object* v___x_107_, lean_object* v___f_108_, lean_object* v_x1_109_, lean_object* v_x2_110_){
_start:
{
lean_object* v___x_111_; 
v___x_111_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___redArg(v___x_106_, v___x_107_, v_x1_109_, v_x2_110_, v___f_108_);
return v___x_111_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_addDerivedValue___redArg(lean_object* v_parents_131_, lean_object* v_child_132_, lean_object* v_a_133_){
_start:
{
lean_object* v___x_135_; lean_object* v_varMap_136_; lean_object* v_borrowedParams_137_; lean_object* v___x_139_; uint8_t v_isShared_140_; uint8_t v_isSharedCheck_167_; 
v___x_135_ = lean_st_ref_take(v_a_133_);
v_varMap_136_ = lean_ctor_get(v___x_135_, 0);
v_borrowedParams_137_ = lean_ctor_get(v___x_135_, 1);
v_isSharedCheck_167_ = !lean_is_exclusive(v___x_135_);
if (v_isSharedCheck_167_ == 0)
{
v___x_139_ = v___x_135_;
v_isShared_140_ = v_isSharedCheck_167_;
goto v_resetjp_138_;
}
else
{
lean_inc(v_borrowedParams_137_);
lean_inc(v_varMap_136_);
lean_dec(v___x_135_);
v___x_139_ = lean_box(0);
v_isShared_140_ = v_isSharedCheck_167_;
goto v_resetjp_138_;
}
v_resetjp_138_:
{
lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___y_146_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; uint8_t v___x_157_; 
v___x_141_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_visitParam___redArg___closed__0));
v___x_142_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_visitParam___redArg___closed__1));
v___x_143_ = l_Lean_instEmptyCollectionFVarIdHashSet;
v___x_144_ = lean_box(0);
v___x_154_ = lean_unsigned_to_nat(0u);
v___x_155_ = lean_array_get_size(v_parents_131_);
v___x_156_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_addDerivedValue___redArg___closed__9));
v___x_157_ = lean_nat_dec_lt(v___x_154_, v___x_155_);
if (v___x_157_ == 0)
{
v___y_146_ = v_varMap_136_;
goto v___jp_145_;
}
else
{
lean_object* v___f_158_; lean_object* v___f_159_; uint8_t v___x_160_; 
lean_inc(v_child_132_);
v___f_158_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_addDerivedValue___redArg___lam__0), 4, 3);
lean_closure_set(v___f_158_, 0, v___x_141_);
lean_closure_set(v___f_158_, 1, v___x_142_);
lean_closure_set(v___f_158_, 2, v_child_132_);
v___f_159_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_addDerivedValue___redArg___lam__1), 5, 3);
lean_closure_set(v___f_159_, 0, v___x_141_);
lean_closure_set(v___f_159_, 1, v___x_142_);
lean_closure_set(v___f_159_, 2, v___f_158_);
v___x_160_ = lean_nat_dec_le(v___x_155_, v___x_155_);
if (v___x_160_ == 0)
{
if (v___x_157_ == 0)
{
lean_dec_ref(v___f_159_);
v___y_146_ = v_varMap_136_;
goto v___jp_145_;
}
else
{
size_t v___x_161_; size_t v___x_162_; lean_object* v___x_163_; 
v___x_161_ = ((size_t)0ULL);
v___x_162_ = lean_usize_of_nat(v___x_155_);
lean_inc_ref(v_parents_131_);
v___x_163_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_156_, v___f_159_, v_parents_131_, v___x_161_, v___x_162_, v_varMap_136_);
v___y_146_ = v___x_163_;
goto v___jp_145_;
}
}
else
{
size_t v___x_164_; size_t v___x_165_; lean_object* v___x_166_; 
v___x_164_ = ((size_t)0ULL);
v___x_165_ = lean_usize_of_nat(v___x_155_);
lean_inc_ref(v_parents_131_);
v___x_166_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_156_, v___f_159_, v_parents_131_, v___x_164_, v___x_165_, v_varMap_136_);
v___y_146_ = v___x_166_;
goto v___jp_145_;
}
}
v___jp_145_:
{
lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_150_; 
v___x_147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_147_, 0, v_parents_131_);
lean_ctor_set(v___x_147_, 1, v___x_143_);
v___x_148_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_141_, v___x_142_, v___y_146_, v_child_132_, v___x_147_);
if (v_isShared_140_ == 0)
{
lean_ctor_set(v___x_139_, 0, v___x_148_);
v___x_150_ = v___x_139_;
goto v_reusejp_149_;
}
else
{
lean_object* v_reuseFailAlloc_153_; 
v_reuseFailAlloc_153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_153_, 0, v___x_148_);
lean_ctor_set(v_reuseFailAlloc_153_, 1, v_borrowedParams_137_);
v___x_150_ = v_reuseFailAlloc_153_;
goto v_reusejp_149_;
}
v_reusejp_149_:
{
lean_object* v___x_151_; lean_object* v___x_152_; 
v___x_151_ = lean_st_ref_set(v_a_133_, v___x_150_);
v___x_152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_152_, 0, v___x_144_);
return v___x_152_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_addDerivedValue___redArg___boxed(lean_object* v_parents_168_, lean_object* v_child_169_, lean_object* v_a_170_, lean_object* v_a_171_){
_start:
{
lean_object* v_res_172_; 
v_res_172_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_addDerivedValue___redArg(v_parents_168_, v_child_169_, v_a_170_);
lean_dec(v_a_170_);
return v_res_172_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_addDerivedValue(lean_object* v_parents_173_, lean_object* v_child_174_, lean_object* v_a_175_, lean_object* v_a_176_, lean_object* v_a_177_, lean_object* v_a_178_, lean_object* v_a_179_){
_start:
{
lean_object* v___x_181_; lean_object* v_varMap_182_; lean_object* v_borrowedParams_183_; lean_object* v___x_185_; uint8_t v_isShared_186_; uint8_t v_isSharedCheck_213_; 
v___x_181_ = lean_st_ref_take(v_a_175_);
v_varMap_182_ = lean_ctor_get(v___x_181_, 0);
v_borrowedParams_183_ = lean_ctor_get(v___x_181_, 1);
v_isSharedCheck_213_ = !lean_is_exclusive(v___x_181_);
if (v_isSharedCheck_213_ == 0)
{
v___x_185_ = v___x_181_;
v_isShared_186_ = v_isSharedCheck_213_;
goto v_resetjp_184_;
}
else
{
lean_inc(v_borrowedParams_183_);
lean_inc(v_varMap_182_);
lean_dec(v___x_181_);
v___x_185_ = lean_box(0);
v_isShared_186_ = v_isSharedCheck_213_;
goto v_resetjp_184_;
}
v_resetjp_184_:
{
lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___y_192_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; uint8_t v___x_203_; 
v___x_187_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_visitParam___redArg___closed__0));
v___x_188_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_visitParam___redArg___closed__1));
v___x_189_ = l_Lean_instEmptyCollectionFVarIdHashSet;
v___x_190_ = lean_box(0);
v___x_200_ = lean_unsigned_to_nat(0u);
v___x_201_ = lean_array_get_size(v_parents_173_);
v___x_202_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_addDerivedValue___redArg___closed__9));
v___x_203_ = lean_nat_dec_lt(v___x_200_, v___x_201_);
if (v___x_203_ == 0)
{
v___y_192_ = v_varMap_182_;
goto v___jp_191_;
}
else
{
lean_object* v___f_204_; lean_object* v___f_205_; uint8_t v___x_206_; 
lean_inc(v_child_174_);
v___f_204_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_addDerivedValue___redArg___lam__0), 4, 3);
lean_closure_set(v___f_204_, 0, v___x_187_);
lean_closure_set(v___f_204_, 1, v___x_188_);
lean_closure_set(v___f_204_, 2, v_child_174_);
v___f_205_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_addDerivedValue___redArg___lam__1), 5, 3);
lean_closure_set(v___f_205_, 0, v___x_187_);
lean_closure_set(v___f_205_, 1, v___x_188_);
lean_closure_set(v___f_205_, 2, v___f_204_);
v___x_206_ = lean_nat_dec_le(v___x_201_, v___x_201_);
if (v___x_206_ == 0)
{
if (v___x_203_ == 0)
{
lean_dec_ref(v___f_205_);
v___y_192_ = v_varMap_182_;
goto v___jp_191_;
}
else
{
size_t v___x_207_; size_t v___x_208_; lean_object* v___x_209_; 
v___x_207_ = ((size_t)0ULL);
v___x_208_ = lean_usize_of_nat(v___x_201_);
lean_inc_ref(v_parents_173_);
v___x_209_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_202_, v___f_205_, v_parents_173_, v___x_207_, v___x_208_, v_varMap_182_);
v___y_192_ = v___x_209_;
goto v___jp_191_;
}
}
else
{
size_t v___x_210_; size_t v___x_211_; lean_object* v___x_212_; 
v___x_210_ = ((size_t)0ULL);
v___x_211_ = lean_usize_of_nat(v___x_201_);
lean_inc_ref(v_parents_173_);
v___x_212_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_202_, v___f_205_, v_parents_173_, v___x_210_, v___x_211_, v_varMap_182_);
v___y_192_ = v___x_212_;
goto v___jp_191_;
}
}
v___jp_191_:
{
lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_196_; 
v___x_193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_193_, 0, v_parents_173_);
lean_ctor_set(v___x_193_, 1, v___x_189_);
v___x_194_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_187_, v___x_188_, v___y_192_, v_child_174_, v___x_193_);
if (v_isShared_186_ == 0)
{
lean_ctor_set(v___x_185_, 0, v___x_194_);
v___x_196_ = v___x_185_;
goto v_reusejp_195_;
}
else
{
lean_object* v_reuseFailAlloc_199_; 
v_reuseFailAlloc_199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_199_, 0, v___x_194_);
lean_ctor_set(v_reuseFailAlloc_199_, 1, v_borrowedParams_183_);
v___x_196_ = v_reuseFailAlloc_199_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
lean_object* v___x_197_; lean_object* v___x_198_; 
v___x_197_ = lean_st_ref_set(v_a_175_, v___x_196_);
v___x_198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_198_, 0, v___x_190_);
return v___x_198_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_addDerivedValue___boxed(lean_object* v_parents_214_, lean_object* v_child_215_, lean_object* v_a_216_, lean_object* v_a_217_, lean_object* v_a_218_, lean_object* v_a_219_, lean_object* v_a_220_, lean_object* v_a_221_){
_start:
{
lean_object* v_res_222_; 
v_res_222_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_addDerivedValue(v_parents_214_, v_child_215_, v_a_216_, v_a_217_, v_a_218_, v_a_219_, v_a_220_);
lean_dec(v_a_220_);
lean_dec_ref(v_a_219_);
lean_dec(v_a_218_);
lean_dec_ref(v_a_217_);
lean_dec(v_a_216_);
return v_res_222_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_removeFromParent_spec__1_spec__3___redArg(lean_object* v_a_223_, lean_object* v_x_224_){
_start:
{
if (lean_obj_tag(v_x_224_) == 0)
{
lean_object* v___x_225_; 
v___x_225_ = lean_box(0);
return v___x_225_;
}
else
{
lean_object* v_key_226_; lean_object* v_value_227_; lean_object* v_tail_228_; uint8_t v___x_229_; 
v_key_226_ = lean_ctor_get(v_x_224_, 0);
v_value_227_ = lean_ctor_get(v_x_224_, 1);
v_tail_228_ = lean_ctor_get(v_x_224_, 2);
v___x_229_ = l_Lean_instBEqFVarId_beq(v_key_226_, v_a_223_);
if (v___x_229_ == 0)
{
v_x_224_ = v_tail_228_;
goto _start;
}
else
{
lean_object* v___x_231_; 
lean_inc(v_value_227_);
v___x_231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_231_, 0, v_value_227_);
return v___x_231_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_removeFromParent_spec__1_spec__3___redArg___boxed(lean_object* v_a_232_, lean_object* v_x_233_){
_start:
{
lean_object* v_res_234_; 
v_res_234_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_removeFromParent_spec__1_spec__3___redArg(v_a_232_, v_x_233_);
lean_dec(v_x_233_);
lean_dec(v_a_232_);
return v_res_234_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_removeFromParent_spec__1___redArg(lean_object* v_m_235_, lean_object* v_a_236_){
_start:
{
lean_object* v_buckets_237_; lean_object* v___x_238_; uint64_t v___x_239_; uint64_t v___x_240_; uint64_t v___x_241_; uint64_t v_fold_242_; uint64_t v___x_243_; uint64_t v___x_244_; uint64_t v___x_245_; size_t v___x_246_; size_t v___x_247_; size_t v___x_248_; size_t v___x_249_; size_t v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; 
v_buckets_237_ = lean_ctor_get(v_m_235_, 1);
v___x_238_ = lean_array_get_size(v_buckets_237_);
v___x_239_ = l_Lean_instHashableFVarId_hash(v_a_236_);
v___x_240_ = 32ULL;
v___x_241_ = lean_uint64_shift_right(v___x_239_, v___x_240_);
v_fold_242_ = lean_uint64_xor(v___x_239_, v___x_241_);
v___x_243_ = 16ULL;
v___x_244_ = lean_uint64_shift_right(v_fold_242_, v___x_243_);
v___x_245_ = lean_uint64_xor(v_fold_242_, v___x_244_);
v___x_246_ = lean_uint64_to_usize(v___x_245_);
v___x_247_ = lean_usize_of_nat(v___x_238_);
v___x_248_ = ((size_t)1ULL);
v___x_249_ = lean_usize_sub(v___x_247_, v___x_248_);
v___x_250_ = lean_usize_land(v___x_246_, v___x_249_);
v___x_251_ = lean_array_uget_borrowed(v_buckets_237_, v___x_250_);
v___x_252_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_removeFromParent_spec__1_spec__3___redArg(v_a_236_, v___x_251_);
return v___x_252_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_removeFromParent_spec__1___redArg___boxed(lean_object* v_m_253_, lean_object* v_a_254_){
_start:
{
lean_object* v_res_255_; 
v_res_255_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_removeFromParent_spec__1___redArg(v_m_253_, v_a_254_);
lean_dec(v_a_254_);
lean_dec_ref(v_m_253_);
return v_res_255_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_removeFromParent_spec__0_spec__0___redArg(lean_object* v_a_256_, lean_object* v_x_257_){
_start:
{
if (lean_obj_tag(v_x_257_) == 0)
{
uint8_t v___x_258_; 
v___x_258_ = 0;
return v___x_258_;
}
else
{
lean_object* v_key_259_; lean_object* v_tail_260_; uint8_t v___x_261_; 
v_key_259_ = lean_ctor_get(v_x_257_, 0);
v_tail_260_ = lean_ctor_get(v_x_257_, 2);
v___x_261_ = l_Lean_instBEqFVarId_beq(v_key_259_, v_a_256_);
if (v___x_261_ == 0)
{
v_x_257_ = v_tail_260_;
goto _start;
}
else
{
return v___x_261_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_removeFromParent_spec__0_spec__0___redArg___boxed(lean_object* v_a_263_, lean_object* v_x_264_){
_start:
{
uint8_t v_res_265_; lean_object* v_r_266_; 
v_res_265_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_removeFromParent_spec__0_spec__0___redArg(v_a_263_, v_x_264_);
lean_dec(v_x_264_);
lean_dec(v_a_263_);
v_r_266_ = lean_box(v_res_265_);
return v_r_266_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_removeFromParent_spec__0_spec__1___redArg(lean_object* v_a_267_, lean_object* v_x_268_){
_start:
{
if (lean_obj_tag(v_x_268_) == 0)
{
return v_x_268_;
}
else
{
lean_object* v_key_269_; lean_object* v_value_270_; lean_object* v_tail_271_; lean_object* v___x_273_; uint8_t v_isShared_274_; uint8_t v_isSharedCheck_280_; 
v_key_269_ = lean_ctor_get(v_x_268_, 0);
v_value_270_ = lean_ctor_get(v_x_268_, 1);
v_tail_271_ = lean_ctor_get(v_x_268_, 2);
v_isSharedCheck_280_ = !lean_is_exclusive(v_x_268_);
if (v_isSharedCheck_280_ == 0)
{
v___x_273_ = v_x_268_;
v_isShared_274_ = v_isSharedCheck_280_;
goto v_resetjp_272_;
}
else
{
lean_inc(v_tail_271_);
lean_inc(v_value_270_);
lean_inc(v_key_269_);
lean_dec(v_x_268_);
v___x_273_ = lean_box(0);
v_isShared_274_ = v_isSharedCheck_280_;
goto v_resetjp_272_;
}
v_resetjp_272_:
{
uint8_t v___x_275_; 
v___x_275_ = l_Lean_instBEqFVarId_beq(v_key_269_, v_a_267_);
if (v___x_275_ == 0)
{
lean_object* v___x_276_; lean_object* v___x_278_; 
v___x_276_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_removeFromParent_spec__0_spec__1___redArg(v_a_267_, v_tail_271_);
if (v_isShared_274_ == 0)
{
lean_ctor_set(v___x_273_, 2, v___x_276_);
v___x_278_ = v___x_273_;
goto v_reusejp_277_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v_key_269_);
lean_ctor_set(v_reuseFailAlloc_279_, 1, v_value_270_);
lean_ctor_set(v_reuseFailAlloc_279_, 2, v___x_276_);
v___x_278_ = v_reuseFailAlloc_279_;
goto v_reusejp_277_;
}
v_reusejp_277_:
{
return v___x_278_;
}
}
else
{
lean_del_object(v___x_273_);
lean_dec(v_value_270_);
lean_dec(v_key_269_);
return v_tail_271_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_removeFromParent_spec__0_spec__1___redArg___boxed(lean_object* v_a_281_, lean_object* v_x_282_){
_start:
{
lean_object* v_res_283_; 
v_res_283_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_removeFromParent_spec__0_spec__1___redArg(v_a_281_, v_x_282_);
lean_dec(v_a_281_);
return v_res_283_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_removeFromParent_spec__0___redArg(lean_object* v_m_284_, lean_object* v_a_285_){
_start:
{
lean_object* v_size_286_; lean_object* v_buckets_287_; lean_object* v___x_288_; uint64_t v___x_289_; uint64_t v___x_290_; uint64_t v___x_291_; uint64_t v_fold_292_; uint64_t v___x_293_; uint64_t v___x_294_; uint64_t v___x_295_; size_t v___x_296_; size_t v___x_297_; size_t v___x_298_; size_t v___x_299_; size_t v___x_300_; lean_object* v_bkt_301_; uint8_t v___x_302_; 
v_size_286_ = lean_ctor_get(v_m_284_, 0);
v_buckets_287_ = lean_ctor_get(v_m_284_, 1);
v___x_288_ = lean_array_get_size(v_buckets_287_);
v___x_289_ = l_Lean_instHashableFVarId_hash(v_a_285_);
v___x_290_ = 32ULL;
v___x_291_ = lean_uint64_shift_right(v___x_289_, v___x_290_);
v_fold_292_ = lean_uint64_xor(v___x_289_, v___x_291_);
v___x_293_ = 16ULL;
v___x_294_ = lean_uint64_shift_right(v_fold_292_, v___x_293_);
v___x_295_ = lean_uint64_xor(v_fold_292_, v___x_294_);
v___x_296_ = lean_uint64_to_usize(v___x_295_);
v___x_297_ = lean_usize_of_nat(v___x_288_);
v___x_298_ = ((size_t)1ULL);
v___x_299_ = lean_usize_sub(v___x_297_, v___x_298_);
v___x_300_ = lean_usize_land(v___x_296_, v___x_299_);
v_bkt_301_ = lean_array_uget_borrowed(v_buckets_287_, v___x_300_);
v___x_302_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_removeFromParent_spec__0_spec__0___redArg(v_a_285_, v_bkt_301_);
if (v___x_302_ == 0)
{
return v_m_284_;
}
else
{
lean_object* v___x_304_; uint8_t v_isShared_305_; uint8_t v_isSharedCheck_315_; 
lean_inc(v_bkt_301_);
lean_inc_ref(v_buckets_287_);
lean_inc(v_size_286_);
v_isSharedCheck_315_ = !lean_is_exclusive(v_m_284_);
if (v_isSharedCheck_315_ == 0)
{
lean_object* v_unused_316_; lean_object* v_unused_317_; 
v_unused_316_ = lean_ctor_get(v_m_284_, 1);
lean_dec(v_unused_316_);
v_unused_317_ = lean_ctor_get(v_m_284_, 0);
lean_dec(v_unused_317_);
v___x_304_ = v_m_284_;
v_isShared_305_ = v_isSharedCheck_315_;
goto v_resetjp_303_;
}
else
{
lean_dec(v_m_284_);
v___x_304_ = lean_box(0);
v_isShared_305_ = v_isSharedCheck_315_;
goto v_resetjp_303_;
}
v_resetjp_303_:
{
lean_object* v___x_306_; lean_object* v_buckets_x27_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_313_; 
v___x_306_ = lean_box(0);
v_buckets_x27_307_ = lean_array_uset(v_buckets_287_, v___x_300_, v___x_306_);
v___x_308_ = lean_unsigned_to_nat(1u);
v___x_309_ = lean_nat_sub(v_size_286_, v___x_308_);
lean_dec(v_size_286_);
v___x_310_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_removeFromParent_spec__0_spec__1___redArg(v_a_285_, v_bkt_301_);
v___x_311_ = lean_array_uset(v_buckets_x27_307_, v___x_300_, v___x_310_);
if (v_isShared_305_ == 0)
{
lean_ctor_set(v___x_304_, 1, v___x_311_);
lean_ctor_set(v___x_304_, 0, v___x_309_);
v___x_313_ = v___x_304_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v___x_309_);
lean_ctor_set(v_reuseFailAlloc_314_, 1, v___x_311_);
v___x_313_ = v_reuseFailAlloc_314_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
return v___x_313_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_removeFromParent_spec__0___redArg___boxed(lean_object* v_m_318_, lean_object* v_a_319_){
_start:
{
lean_object* v_res_320_; 
v_res_320_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_removeFromParent_spec__0___redArg(v_m_318_, v_a_319_);
lean_dec(v_a_319_);
return v_res_320_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_removeFromParent_spec__2_spec__5(lean_object* v_child_321_, lean_object* v_a_322_, lean_object* v_x_323_){
_start:
{
if (lean_obj_tag(v_x_323_) == 0)
{
lean_dec(v_a_322_);
return v_x_323_;
}
else
{
lean_object* v_key_324_; lean_object* v_value_325_; lean_object* v_tail_326_; lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_348_; 
v_key_324_ = lean_ctor_get(v_x_323_, 0);
v_value_325_ = lean_ctor_get(v_x_323_, 1);
v_tail_326_ = lean_ctor_get(v_x_323_, 2);
v_isSharedCheck_348_ = !lean_is_exclusive(v_x_323_);
if (v_isSharedCheck_348_ == 0)
{
v___x_328_ = v_x_323_;
v_isShared_329_ = v_isSharedCheck_348_;
goto v_resetjp_327_;
}
else
{
lean_inc(v_tail_326_);
lean_inc(v_value_325_);
lean_inc(v_key_324_);
lean_dec(v_x_323_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_348_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
uint8_t v___x_330_; 
v___x_330_ = l_Lean_instBEqFVarId_beq(v_key_324_, v_a_322_);
if (v___x_330_ == 0)
{
lean_object* v___x_331_; lean_object* v___x_333_; 
v___x_331_ = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_removeFromParent_spec__2_spec__5(v_child_321_, v_a_322_, v_tail_326_);
if (v_isShared_329_ == 0)
{
lean_ctor_set(v___x_328_, 2, v___x_331_);
v___x_333_ = v___x_328_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v_key_324_);
lean_ctor_set(v_reuseFailAlloc_334_, 1, v_value_325_);
lean_ctor_set(v_reuseFailAlloc_334_, 2, v___x_331_);
v___x_333_ = v_reuseFailAlloc_334_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
return v___x_333_;
}
}
else
{
lean_object* v_parents_335_; lean_object* v_children_336_; lean_object* v___x_338_; uint8_t v_isShared_339_; uint8_t v_isSharedCheck_347_; 
lean_dec(v_key_324_);
v_parents_335_ = lean_ctor_get(v_value_325_, 0);
v_children_336_ = lean_ctor_get(v_value_325_, 1);
v_isSharedCheck_347_ = !lean_is_exclusive(v_value_325_);
if (v_isSharedCheck_347_ == 0)
{
v___x_338_ = v_value_325_;
v_isShared_339_ = v_isSharedCheck_347_;
goto v_resetjp_337_;
}
else
{
lean_inc(v_children_336_);
lean_inc(v_parents_335_);
lean_dec(v_value_325_);
v___x_338_ = lean_box(0);
v_isShared_339_ = v_isSharedCheck_347_;
goto v_resetjp_337_;
}
v_resetjp_337_:
{
lean_object* v___x_340_; lean_object* v___x_342_; 
v___x_340_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_removeFromParent_spec__0___redArg(v_children_336_, v_child_321_);
if (v_isShared_339_ == 0)
{
lean_ctor_set(v___x_338_, 1, v___x_340_);
v___x_342_ = v___x_338_;
goto v_reusejp_341_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v_parents_335_);
lean_ctor_set(v_reuseFailAlloc_346_, 1, v___x_340_);
v___x_342_ = v_reuseFailAlloc_346_;
goto v_reusejp_341_;
}
v_reusejp_341_:
{
lean_object* v___x_344_; 
if (v_isShared_329_ == 0)
{
lean_ctor_set(v___x_328_, 1, v___x_342_);
lean_ctor_set(v___x_328_, 0, v_a_322_);
v___x_344_ = v___x_328_;
goto v_reusejp_343_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_345_, 0, v_a_322_);
lean_ctor_set(v_reuseFailAlloc_345_, 1, v___x_342_);
lean_ctor_set(v_reuseFailAlloc_345_, 2, v_tail_326_);
v___x_344_ = v_reuseFailAlloc_345_;
goto v_reusejp_343_;
}
v_reusejp_343_:
{
return v___x_344_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_removeFromParent_spec__2_spec__5___boxed(lean_object* v_child_349_, lean_object* v_a_350_, lean_object* v_x_351_){
_start:
{
lean_object* v_res_352_; 
v_res_352_ = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_removeFromParent_spec__2_spec__5(v_child_349_, v_a_350_, v_x_351_);
lean_dec(v_child_349_);
return v_res_352_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_removeFromParent_spec__2(lean_object* v_child_353_, lean_object* v_m_354_, lean_object* v_a_355_){
_start:
{
lean_object* v_size_356_; lean_object* v_buckets_357_; lean_object* v___x_358_; uint64_t v___x_359_; uint64_t v___x_360_; uint64_t v___x_361_; uint64_t v_fold_362_; uint64_t v___x_363_; uint64_t v___x_364_; uint64_t v___x_365_; size_t v___x_366_; size_t v___x_367_; size_t v___x_368_; size_t v___x_369_; size_t v___x_370_; lean_object* v_bucket_371_; uint8_t v___x_372_; 
v_size_356_ = lean_ctor_get(v_m_354_, 0);
v_buckets_357_ = lean_ctor_get(v_m_354_, 1);
v___x_358_ = lean_array_get_size(v_buckets_357_);
v___x_359_ = l_Lean_instHashableFVarId_hash(v_a_355_);
v___x_360_ = 32ULL;
v___x_361_ = lean_uint64_shift_right(v___x_359_, v___x_360_);
v_fold_362_ = lean_uint64_xor(v___x_359_, v___x_361_);
v___x_363_ = 16ULL;
v___x_364_ = lean_uint64_shift_right(v_fold_362_, v___x_363_);
v___x_365_ = lean_uint64_xor(v_fold_362_, v___x_364_);
v___x_366_ = lean_uint64_to_usize(v___x_365_);
v___x_367_ = lean_usize_of_nat(v___x_358_);
v___x_368_ = ((size_t)1ULL);
v___x_369_ = lean_usize_sub(v___x_367_, v___x_368_);
v___x_370_ = lean_usize_land(v___x_366_, v___x_369_);
v_bucket_371_ = lean_array_uget_borrowed(v_buckets_357_, v___x_370_);
v___x_372_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_removeFromParent_spec__0_spec__0___redArg(v_a_355_, v_bucket_371_);
if (v___x_372_ == 0)
{
lean_dec(v_a_355_);
return v_m_354_;
}
else
{
lean_object* v___x_374_; uint8_t v_isShared_375_; uint8_t v_isSharedCheck_383_; 
lean_inc(v_bucket_371_);
lean_inc_ref(v_buckets_357_);
lean_inc(v_size_356_);
v_isSharedCheck_383_ = !lean_is_exclusive(v_m_354_);
if (v_isSharedCheck_383_ == 0)
{
lean_object* v_unused_384_; lean_object* v_unused_385_; 
v_unused_384_ = lean_ctor_get(v_m_354_, 1);
lean_dec(v_unused_384_);
v_unused_385_ = lean_ctor_get(v_m_354_, 0);
lean_dec(v_unused_385_);
v___x_374_ = v_m_354_;
v_isShared_375_ = v_isSharedCheck_383_;
goto v_resetjp_373_;
}
else
{
lean_dec(v_m_354_);
v___x_374_ = lean_box(0);
v_isShared_375_ = v_isSharedCheck_383_;
goto v_resetjp_373_;
}
v_resetjp_373_:
{
lean_object* v___x_376_; lean_object* v_buckets_377_; lean_object* v_bucket_378_; lean_object* v___x_379_; lean_object* v___x_381_; 
v___x_376_ = lean_box(0);
v_buckets_377_ = lean_array_uset(v_buckets_357_, v___x_370_, v___x_376_);
v_bucket_378_ = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_removeFromParent_spec__2_spec__5(v_child_353_, v_a_355_, v_bucket_371_);
v___x_379_ = lean_array_uset(v_buckets_377_, v___x_370_, v_bucket_378_);
if (v_isShared_375_ == 0)
{
lean_ctor_set(v___x_374_, 1, v___x_379_);
v___x_381_ = v___x_374_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v_size_356_);
lean_ctor_set(v_reuseFailAlloc_382_, 1, v___x_379_);
v___x_381_ = v_reuseFailAlloc_382_;
goto v_reusejp_380_;
}
v_reusejp_380_:
{
return v___x_381_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_removeFromParent_spec__2___boxed(lean_object* v_child_386_, lean_object* v_m_387_, lean_object* v_a_388_){
_start:
{
lean_object* v_res_389_; 
v_res_389_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_removeFromParent_spec__2(v_child_386_, v_m_387_, v_a_388_);
lean_dec(v_child_386_);
return v_res_389_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_removeFromParent_spec__3___redArg(lean_object* v_child_390_, lean_object* v_as_391_, size_t v_sz_392_, size_t v_i_393_, lean_object* v_b_394_, lean_object* v___y_395_){
_start:
{
uint8_t v___x_397_; 
v___x_397_ = lean_usize_dec_lt(v_i_393_, v_sz_392_);
if (v___x_397_ == 0)
{
lean_object* v___x_398_; 
v___x_398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_398_, 0, v_b_394_);
return v___x_398_;
}
else
{
lean_object* v___x_399_; lean_object* v_varMap_400_; lean_object* v_borrowedParams_401_; lean_object* v___x_403_; uint8_t v_isShared_404_; uint8_t v_isSharedCheck_415_; 
v___x_399_ = lean_st_ref_take(v___y_395_);
v_varMap_400_ = lean_ctor_get(v___x_399_, 0);
v_borrowedParams_401_ = lean_ctor_get(v___x_399_, 1);
v_isSharedCheck_415_ = !lean_is_exclusive(v___x_399_);
if (v_isSharedCheck_415_ == 0)
{
v___x_403_ = v___x_399_;
v_isShared_404_ = v_isSharedCheck_415_;
goto v_resetjp_402_;
}
else
{
lean_inc(v_borrowedParams_401_);
lean_inc(v_varMap_400_);
lean_dec(v___x_399_);
v___x_403_ = lean_box(0);
v_isShared_404_ = v_isSharedCheck_415_;
goto v_resetjp_402_;
}
v_resetjp_402_:
{
lean_object* v_a_405_; lean_object* v___x_406_; lean_object* v___x_408_; 
v_a_405_ = lean_array_uget_borrowed(v_as_391_, v_i_393_);
lean_inc(v_a_405_);
v___x_406_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_removeFromParent_spec__2(v_child_390_, v_varMap_400_, v_a_405_);
if (v_isShared_404_ == 0)
{
lean_ctor_set(v___x_403_, 0, v___x_406_);
v___x_408_ = v___x_403_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_414_; 
v_reuseFailAlloc_414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_414_, 0, v___x_406_);
lean_ctor_set(v_reuseFailAlloc_414_, 1, v_borrowedParams_401_);
v___x_408_ = v_reuseFailAlloc_414_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
lean_object* v___x_409_; lean_object* v___x_410_; size_t v___x_411_; size_t v___x_412_; 
v___x_409_ = lean_st_ref_set(v___y_395_, v___x_408_);
v___x_410_ = lean_box(0);
v___x_411_ = ((size_t)1ULL);
v___x_412_ = lean_usize_add(v_i_393_, v___x_411_);
v_i_393_ = v___x_412_;
v_b_394_ = v___x_410_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_removeFromParent_spec__3___redArg___boxed(lean_object* v_child_416_, lean_object* v_as_417_, lean_object* v_sz_418_, lean_object* v_i_419_, lean_object* v_b_420_, lean_object* v___y_421_, lean_object* v___y_422_){
_start:
{
size_t v_sz_boxed_423_; size_t v_i_boxed_424_; lean_object* v_res_425_; 
v_sz_boxed_423_ = lean_unbox_usize(v_sz_418_);
lean_dec(v_sz_418_);
v_i_boxed_424_ = lean_unbox_usize(v_i_419_);
lean_dec(v_i_419_);
v_res_425_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_removeFromParent_spec__3___redArg(v_child_416_, v_as_417_, v_sz_boxed_423_, v_i_boxed_424_, v_b_420_, v___y_421_);
lean_dec(v___y_421_);
lean_dec_ref(v_as_417_);
lean_dec(v_child_416_);
return v_res_425_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_removeFromParent(lean_object* v_child_426_, lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_){
_start:
{
lean_object* v___x_433_; lean_object* v_varMap_434_; lean_object* v___x_435_; 
v___x_433_ = lean_st_ref_get(v_a_427_);
v_varMap_434_ = lean_ctor_get(v___x_433_, 0);
lean_inc_ref(v_varMap_434_);
lean_dec(v___x_433_);
v___x_435_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_removeFromParent_spec__1___redArg(v_varMap_434_, v_child_426_);
lean_dec_ref(v_varMap_434_);
if (lean_obj_tag(v___x_435_) == 1)
{
lean_object* v_val_436_; lean_object* v_parents_437_; lean_object* v___x_438_; size_t v_sz_439_; size_t v___x_440_; lean_object* v___x_441_; 
v_val_436_ = lean_ctor_get(v___x_435_, 0);
lean_inc(v_val_436_);
lean_dec_ref(v___x_435_);
v_parents_437_ = lean_ctor_get(v_val_436_, 0);
lean_inc_ref(v_parents_437_);
lean_dec(v_val_436_);
v___x_438_ = lean_box(0);
v_sz_439_ = lean_array_size(v_parents_437_);
v___x_440_ = ((size_t)0ULL);
v___x_441_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_removeFromParent_spec__3___redArg(v_child_426_, v_parents_437_, v_sz_439_, v___x_440_, v___x_438_, v_a_427_);
lean_dec_ref(v_parents_437_);
if (lean_obj_tag(v___x_441_) == 0)
{
lean_object* v___x_443_; uint8_t v_isShared_444_; uint8_t v_isSharedCheck_448_; 
v_isSharedCheck_448_ = !lean_is_exclusive(v___x_441_);
if (v_isSharedCheck_448_ == 0)
{
lean_object* v_unused_449_; 
v_unused_449_ = lean_ctor_get(v___x_441_, 0);
lean_dec(v_unused_449_);
v___x_443_ = v___x_441_;
v_isShared_444_ = v_isSharedCheck_448_;
goto v_resetjp_442_;
}
else
{
lean_dec(v___x_441_);
v___x_443_ = lean_box(0);
v_isShared_444_ = v_isSharedCheck_448_;
goto v_resetjp_442_;
}
v_resetjp_442_:
{
lean_object* v___x_446_; 
if (v_isShared_444_ == 0)
{
lean_ctor_set(v___x_443_, 0, v___x_438_);
v___x_446_ = v___x_443_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v___x_438_);
v___x_446_ = v_reuseFailAlloc_447_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
return v___x_446_;
}
}
}
else
{
return v___x_441_;
}
}
else
{
lean_object* v___x_450_; lean_object* v___x_451_; 
lean_dec(v___x_435_);
v___x_450_ = lean_box(0);
v___x_451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_451_, 0, v___x_450_);
return v___x_451_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_removeFromParent___boxed(lean_object* v_child_452_, lean_object* v_a_453_, lean_object* v_a_454_, lean_object* v_a_455_, lean_object* v_a_456_, lean_object* v_a_457_, lean_object* v_a_458_){
_start:
{
lean_object* v_res_459_; 
v_res_459_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_removeFromParent(v_child_452_, v_a_453_, v_a_454_, v_a_455_, v_a_456_, v_a_457_);
lean_dec(v_a_457_);
lean_dec_ref(v_a_456_);
lean_dec(v_a_455_);
lean_dec_ref(v_a_454_);
lean_dec(v_a_453_);
lean_dec(v_child_452_);
return v_res_459_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_removeFromParent_spec__0(lean_object* v_00_u03b2_460_, lean_object* v_m_461_, lean_object* v_a_462_){
_start:
{
lean_object* v___x_463_; 
v___x_463_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_removeFromParent_spec__0___redArg(v_m_461_, v_a_462_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_removeFromParent_spec__0___boxed(lean_object* v_00_u03b2_464_, lean_object* v_m_465_, lean_object* v_a_466_){
_start:
{
lean_object* v_res_467_; 
v_res_467_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_removeFromParent_spec__0(v_00_u03b2_464_, v_m_465_, v_a_466_);
lean_dec(v_a_466_);
return v_res_467_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_removeFromParent_spec__1(lean_object* v_00_u03b2_468_, lean_object* v_m_469_, lean_object* v_a_470_){
_start:
{
lean_object* v___x_471_; 
v___x_471_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_removeFromParent_spec__1___redArg(v_m_469_, v_a_470_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_removeFromParent_spec__1___boxed(lean_object* v_00_u03b2_472_, lean_object* v_m_473_, lean_object* v_a_474_){
_start:
{
lean_object* v_res_475_; 
v_res_475_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_removeFromParent_spec__1(v_00_u03b2_472_, v_m_473_, v_a_474_);
lean_dec(v_a_474_);
lean_dec_ref(v_m_473_);
return v_res_475_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_removeFromParent_spec__3(lean_object* v_child_476_, lean_object* v_as_477_, size_t v_sz_478_, size_t v_i_479_, lean_object* v_b_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_){
_start:
{
lean_object* v___x_487_; 
v___x_487_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_removeFromParent_spec__3___redArg(v_child_476_, v_as_477_, v_sz_478_, v_i_479_, v_b_480_, v___y_481_);
return v___x_487_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_removeFromParent_spec__3___boxed(lean_object* v_child_488_, lean_object* v_as_489_, lean_object* v_sz_490_, lean_object* v_i_491_, lean_object* v_b_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_){
_start:
{
size_t v_sz_boxed_499_; size_t v_i_boxed_500_; lean_object* v_res_501_; 
v_sz_boxed_499_ = lean_unbox_usize(v_sz_490_);
lean_dec(v_sz_490_);
v_i_boxed_500_ = lean_unbox_usize(v_i_491_);
lean_dec(v_i_491_);
v_res_501_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_removeFromParent_spec__3(v_child_488_, v_as_489_, v_sz_boxed_499_, v_i_boxed_500_, v_b_492_, v___y_493_, v___y_494_, v___y_495_, v___y_496_, v___y_497_);
lean_dec(v___y_497_);
lean_dec_ref(v___y_496_);
lean_dec(v___y_495_);
lean_dec_ref(v___y_494_);
lean_dec(v___y_493_);
lean_dec_ref(v_as_489_);
lean_dec(v_child_488_);
return v_res_501_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_removeFromParent_spec__0_spec__0(lean_object* v_00_u03b2_502_, lean_object* v_a_503_, lean_object* v_x_504_){
_start:
{
uint8_t v___x_505_; 
v___x_505_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_removeFromParent_spec__0_spec__0___redArg(v_a_503_, v_x_504_);
return v___x_505_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_removeFromParent_spec__0_spec__0___boxed(lean_object* v_00_u03b2_506_, lean_object* v_a_507_, lean_object* v_x_508_){
_start:
{
uint8_t v_res_509_; lean_object* v_r_510_; 
v_res_509_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_removeFromParent_spec__0_spec__0(v_00_u03b2_506_, v_a_507_, v_x_508_);
lean_dec(v_x_508_);
lean_dec(v_a_507_);
v_r_510_ = lean_box(v_res_509_);
return v_r_510_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_removeFromParent_spec__0_spec__1(lean_object* v_00_u03b2_511_, lean_object* v_a_512_, lean_object* v_x_513_){
_start:
{
lean_object* v___x_514_; 
v___x_514_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_removeFromParent_spec__0_spec__1___redArg(v_a_512_, v_x_513_);
return v___x_514_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_removeFromParent_spec__0_spec__1___boxed(lean_object* v_00_u03b2_515_, lean_object* v_a_516_, lean_object* v_x_517_){
_start:
{
lean_object* v_res_518_; 
v_res_518_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_removeFromParent_spec__0_spec__1(v_00_u03b2_515_, v_a_516_, v_x_517_);
lean_dec(v_a_516_);
return v_res_518_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_removeFromParent_spec__1_spec__3(lean_object* v_00_u03b2_519_, lean_object* v_a_520_, lean_object* v_x_521_){
_start:
{
lean_object* v___x_522_; 
v___x_522_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_removeFromParent_spec__1_spec__3___redArg(v_a_520_, v_x_521_);
return v___x_522_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_removeFromParent_spec__1_spec__3___boxed(lean_object* v_00_u03b2_523_, lean_object* v_a_524_, lean_object* v_x_525_){
_start:
{
lean_object* v_res_526_; 
v_res_526_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_removeFromParent_spec__1_spec__3(v_00_u03b2_523_, v_a_524_, v_x_525_);
lean_dec(v_x_525_);
lean_dec(v_a_524_);
return v_res_526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__2___redArg(lean_object* v_alt_527_, lean_object* v_f_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_){
_start:
{
switch(lean_obj_tag(v_alt_527_))
{
case 0:
{
lean_object* v_code_535_; lean_object* v___x_536_; 
v_code_535_ = lean_ctor_get(v_alt_527_, 2);
lean_inc_ref(v_code_535_);
lean_dec_ref(v_alt_527_);
lean_inc(v___y_533_);
lean_inc_ref(v___y_532_);
lean_inc(v___y_531_);
lean_inc_ref(v___y_530_);
lean_inc(v___y_529_);
v___x_536_ = lean_apply_7(v_f_528_, v_code_535_, v___y_529_, v___y_530_, v___y_531_, v___y_532_, v___y_533_, lean_box(0));
return v___x_536_;
}
case 1:
{
lean_object* v_code_537_; lean_object* v___x_538_; 
v_code_537_ = lean_ctor_get(v_alt_527_, 1);
lean_inc_ref(v_code_537_);
lean_dec_ref(v_alt_527_);
lean_inc(v___y_533_);
lean_inc_ref(v___y_532_);
lean_inc(v___y_531_);
lean_inc_ref(v___y_530_);
lean_inc(v___y_529_);
v___x_538_ = lean_apply_7(v_f_528_, v_code_537_, v___y_529_, v___y_530_, v___y_531_, v___y_532_, v___y_533_, lean_box(0));
return v___x_538_;
}
default: 
{
lean_object* v_code_539_; lean_object* v___x_540_; 
v_code_539_ = lean_ctor_get(v_alt_527_, 0);
lean_inc_ref(v_code_539_);
lean_dec_ref(v_alt_527_);
lean_inc(v___y_533_);
lean_inc_ref(v___y_532_);
lean_inc(v___y_531_);
lean_inc_ref(v___y_530_);
lean_inc(v___y_529_);
v___x_540_ = lean_apply_7(v_f_528_, v_code_539_, v___y_529_, v___y_530_, v___y_531_, v___y_532_, v___y_533_, lean_box(0));
return v___x_540_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__2___redArg___boxed(lean_object* v_alt_541_, lean_object* v_f_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_){
_start:
{
lean_object* v_res_549_; 
v_res_549_ = l_Lean_Compiler_LCNF_Alt_forCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__2___redArg(v_alt_541_, v_f_542_, v___y_543_, v___y_544_, v___y_545_, v___y_546_, v___y_547_);
lean_dec(v___y_547_);
lean_dec_ref(v___y_546_);
lean_dec(v___y_545_);
lean_dec_ref(v___y_544_);
lean_dec(v___y_543_);
return v_res_549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__2(uint8_t v_pu_550_, lean_object* v_alt_551_, lean_object* v_f_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_){
_start:
{
lean_object* v___x_559_; 
v___x_559_ = l_Lean_Compiler_LCNF_Alt_forCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__2___redArg(v_alt_551_, v_f_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_);
return v___x_559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__2___boxed(lean_object* v_pu_560_, lean_object* v_alt_561_, lean_object* v_f_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_){
_start:
{
uint8_t v_pu_boxed_569_; lean_object* v_res_570_; 
v_pu_boxed_569_ = lean_unbox(v_pu_560_);
v_res_570_ = l_Lean_Compiler_LCNF_Alt_forCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__2(v_pu_boxed_569_, v_alt_561_, v_f_562_, v___y_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_);
lean_dec(v___y_567_);
lean_dec_ref(v___y_566_);
lean_dec(v___y_565_);
lean_dec_ref(v___y_564_);
lean_dec(v___y_563_);
return v_res_570_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__7___closed__0(void){
_start:
{
lean_object* v___x_571_; 
v___x_571_ = l_instMonadEIO(lean_box(0));
return v___x_571_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__7(lean_object* v_msg_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_){
_start:
{
lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v_toApplicative_585_; lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_647_; 
v___x_583_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__7___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__7___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__7___closed__0);
v___x_584_ = l_StateRefT_x27_instMonad___redArg(v___x_583_);
v_toApplicative_585_ = lean_ctor_get(v___x_584_, 0);
v_isSharedCheck_647_ = !lean_is_exclusive(v___x_584_);
if (v_isSharedCheck_647_ == 0)
{
lean_object* v_unused_648_; 
v_unused_648_ = lean_ctor_get(v___x_584_, 1);
lean_dec(v_unused_648_);
v___x_587_ = v___x_584_;
v_isShared_588_ = v_isSharedCheck_647_;
goto v_resetjp_586_;
}
else
{
lean_inc(v_toApplicative_585_);
lean_dec(v___x_584_);
v___x_587_ = lean_box(0);
v_isShared_588_ = v_isSharedCheck_647_;
goto v_resetjp_586_;
}
v_resetjp_586_:
{
lean_object* v_toFunctor_589_; lean_object* v_toSeq_590_; lean_object* v_toSeqLeft_591_; lean_object* v_toSeqRight_592_; lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_645_; 
v_toFunctor_589_ = lean_ctor_get(v_toApplicative_585_, 0);
v_toSeq_590_ = lean_ctor_get(v_toApplicative_585_, 2);
v_toSeqLeft_591_ = lean_ctor_get(v_toApplicative_585_, 3);
v_toSeqRight_592_ = lean_ctor_get(v_toApplicative_585_, 4);
v_isSharedCheck_645_ = !lean_is_exclusive(v_toApplicative_585_);
if (v_isSharedCheck_645_ == 0)
{
lean_object* v_unused_646_; 
v_unused_646_ = lean_ctor_get(v_toApplicative_585_, 1);
lean_dec(v_unused_646_);
v___x_594_ = v_toApplicative_585_;
v_isShared_595_ = v_isSharedCheck_645_;
goto v_resetjp_593_;
}
else
{
lean_inc(v_toSeqRight_592_);
lean_inc(v_toSeqLeft_591_);
lean_inc(v_toSeq_590_);
lean_inc(v_toFunctor_589_);
lean_dec(v_toApplicative_585_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_645_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
lean_object* v___f_596_; lean_object* v___f_597_; lean_object* v___f_598_; lean_object* v___f_599_; lean_object* v___x_600_; lean_object* v___f_601_; lean_object* v___f_602_; lean_object* v___f_603_; lean_object* v___x_605_; 
v___f_596_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__7___closed__1));
v___f_597_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__7___closed__2));
lean_inc_ref(v_toFunctor_589_);
v___f_598_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_598_, 0, v_toFunctor_589_);
v___f_599_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_599_, 0, v_toFunctor_589_);
v___x_600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_600_, 0, v___f_598_);
lean_ctor_set(v___x_600_, 1, v___f_599_);
v___f_601_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_601_, 0, v_toSeqRight_592_);
v___f_602_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_602_, 0, v_toSeqLeft_591_);
v___f_603_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_603_, 0, v_toSeq_590_);
if (v_isShared_595_ == 0)
{
lean_ctor_set(v___x_594_, 4, v___f_601_);
lean_ctor_set(v___x_594_, 3, v___f_602_);
lean_ctor_set(v___x_594_, 2, v___f_603_);
lean_ctor_set(v___x_594_, 1, v___f_596_);
lean_ctor_set(v___x_594_, 0, v___x_600_);
v___x_605_ = v___x_594_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v___x_600_);
lean_ctor_set(v_reuseFailAlloc_644_, 1, v___f_596_);
lean_ctor_set(v_reuseFailAlloc_644_, 2, v___f_603_);
lean_ctor_set(v_reuseFailAlloc_644_, 3, v___f_602_);
lean_ctor_set(v_reuseFailAlloc_644_, 4, v___f_601_);
v___x_605_ = v_reuseFailAlloc_644_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
lean_object* v___x_607_; 
if (v_isShared_588_ == 0)
{
lean_ctor_set(v___x_587_, 1, v___f_597_);
lean_ctor_set(v___x_587_, 0, v___x_605_);
v___x_607_ = v___x_587_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v___x_605_);
lean_ctor_set(v_reuseFailAlloc_643_, 1, v___f_597_);
v___x_607_ = v_reuseFailAlloc_643_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
lean_object* v___x_608_; lean_object* v_toApplicative_609_; lean_object* v___x_611_; uint8_t v_isShared_612_; uint8_t v_isSharedCheck_641_; 
v___x_608_ = l_StateRefT_x27_instMonad___redArg(v___x_607_);
v_toApplicative_609_ = lean_ctor_get(v___x_608_, 0);
v_isSharedCheck_641_ = !lean_is_exclusive(v___x_608_);
if (v_isSharedCheck_641_ == 0)
{
lean_object* v_unused_642_; 
v_unused_642_ = lean_ctor_get(v___x_608_, 1);
lean_dec(v_unused_642_);
v___x_611_ = v___x_608_;
v_isShared_612_ = v_isSharedCheck_641_;
goto v_resetjp_610_;
}
else
{
lean_inc(v_toApplicative_609_);
lean_dec(v___x_608_);
v___x_611_ = lean_box(0);
v_isShared_612_ = v_isSharedCheck_641_;
goto v_resetjp_610_;
}
v_resetjp_610_:
{
lean_object* v_toFunctor_613_; lean_object* v_toSeq_614_; lean_object* v_toSeqLeft_615_; lean_object* v_toSeqRight_616_; lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_639_; 
v_toFunctor_613_ = lean_ctor_get(v_toApplicative_609_, 0);
v_toSeq_614_ = lean_ctor_get(v_toApplicative_609_, 2);
v_toSeqLeft_615_ = lean_ctor_get(v_toApplicative_609_, 3);
v_toSeqRight_616_ = lean_ctor_get(v_toApplicative_609_, 4);
v_isSharedCheck_639_ = !lean_is_exclusive(v_toApplicative_609_);
if (v_isSharedCheck_639_ == 0)
{
lean_object* v_unused_640_; 
v_unused_640_ = lean_ctor_get(v_toApplicative_609_, 1);
lean_dec(v_unused_640_);
v___x_618_ = v_toApplicative_609_;
v_isShared_619_ = v_isSharedCheck_639_;
goto v_resetjp_617_;
}
else
{
lean_inc(v_toSeqRight_616_);
lean_inc(v_toSeqLeft_615_);
lean_inc(v_toSeq_614_);
lean_inc(v_toFunctor_613_);
lean_dec(v_toApplicative_609_);
v___x_618_ = lean_box(0);
v_isShared_619_ = v_isSharedCheck_639_;
goto v_resetjp_617_;
}
v_resetjp_617_:
{
lean_object* v___f_620_; lean_object* v___f_621_; lean_object* v___f_622_; lean_object* v___f_623_; lean_object* v___x_624_; lean_object* v___f_625_; lean_object* v___f_626_; lean_object* v___f_627_; lean_object* v___x_629_; 
v___f_620_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__7___closed__3));
v___f_621_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__7___closed__4));
lean_inc_ref(v_toFunctor_613_);
v___f_622_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_622_, 0, v_toFunctor_613_);
v___f_623_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_623_, 0, v_toFunctor_613_);
v___x_624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_624_, 0, v___f_622_);
lean_ctor_set(v___x_624_, 1, v___f_623_);
v___f_625_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_625_, 0, v_toSeqRight_616_);
v___f_626_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_626_, 0, v_toSeqLeft_615_);
v___f_627_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_627_, 0, v_toSeq_614_);
if (v_isShared_619_ == 0)
{
lean_ctor_set(v___x_618_, 4, v___f_625_);
lean_ctor_set(v___x_618_, 3, v___f_626_);
lean_ctor_set(v___x_618_, 2, v___f_627_);
lean_ctor_set(v___x_618_, 1, v___f_620_);
lean_ctor_set(v___x_618_, 0, v___x_624_);
v___x_629_ = v___x_618_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v___x_624_);
lean_ctor_set(v_reuseFailAlloc_638_, 1, v___f_620_);
lean_ctor_set(v_reuseFailAlloc_638_, 2, v___f_627_);
lean_ctor_set(v_reuseFailAlloc_638_, 3, v___f_626_);
lean_ctor_set(v_reuseFailAlloc_638_, 4, v___f_625_);
v___x_629_ = v_reuseFailAlloc_638_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
lean_object* v___x_631_; 
if (v_isShared_612_ == 0)
{
lean_ctor_set(v___x_611_, 1, v___f_621_);
lean_ctor_set(v___x_611_, 0, v___x_629_);
v___x_631_ = v___x_611_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v___x_629_);
lean_ctor_set(v_reuseFailAlloc_637_, 1, v___f_621_);
v___x_631_ = v_reuseFailAlloc_637_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_5420__overap_635_; lean_object* v___x_636_; 
v___x_632_ = l_StateRefT_x27_instMonad___redArg(v___x_631_);
v___x_633_ = lean_box(0);
v___x_634_ = l_instInhabitedOfMonad___redArg(v___x_632_, v___x_633_);
v___x_5420__overap_635_ = lean_panic_fn(v___x_634_, v_msg_576_);
lean_inc(v___y_581_);
lean_inc_ref(v___y_580_);
lean_inc(v___y_579_);
lean_inc_ref(v___y_578_);
lean_inc(v___y_577_);
v___x_636_ = lean_apply_6(v___x_5420__overap_635_, v___y_577_, v___y_578_, v___y_579_, v___y_580_, v___y_581_, lean_box(0));
return v___x_636_;
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__7___boxed(lean_object* v_msg_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_){
_start:
{
lean_object* v_res_656_; 
v_res_656_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__7(v_msg_649_, v___y_650_, v___y_651_, v___y_652_, v___y_653_, v___y_654_);
lean_dec(v___y_654_);
lean_dec_ref(v___y_653_);
lean_dec(v___y_652_);
lean_dec_ref(v___y_651_);
lean_dec(v___y_650_);
return v_res_656_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__0_spec__1___redArg(lean_object* v_a_657_, lean_object* v_b_658_, lean_object* v_x_659_){
_start:
{
if (lean_obj_tag(v_x_659_) == 0)
{
lean_dec(v_b_658_);
lean_dec(v_a_657_);
return v_x_659_;
}
else
{
lean_object* v_key_660_; lean_object* v_value_661_; lean_object* v_tail_662_; lean_object* v___x_664_; uint8_t v_isShared_665_; uint8_t v_isSharedCheck_674_; 
v_key_660_ = lean_ctor_get(v_x_659_, 0);
v_value_661_ = lean_ctor_get(v_x_659_, 1);
v_tail_662_ = lean_ctor_get(v_x_659_, 2);
v_isSharedCheck_674_ = !lean_is_exclusive(v_x_659_);
if (v_isSharedCheck_674_ == 0)
{
v___x_664_ = v_x_659_;
v_isShared_665_ = v_isSharedCheck_674_;
goto v_resetjp_663_;
}
else
{
lean_inc(v_tail_662_);
lean_inc(v_value_661_);
lean_inc(v_key_660_);
lean_dec(v_x_659_);
v___x_664_ = lean_box(0);
v_isShared_665_ = v_isSharedCheck_674_;
goto v_resetjp_663_;
}
v_resetjp_663_:
{
uint8_t v___x_666_; 
v___x_666_ = l_Lean_instBEqFVarId_beq(v_key_660_, v_a_657_);
if (v___x_666_ == 0)
{
lean_object* v___x_667_; lean_object* v___x_669_; 
v___x_667_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__0_spec__1___redArg(v_a_657_, v_b_658_, v_tail_662_);
if (v_isShared_665_ == 0)
{
lean_ctor_set(v___x_664_, 2, v___x_667_);
v___x_669_ = v___x_664_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v_key_660_);
lean_ctor_set(v_reuseFailAlloc_670_, 1, v_value_661_);
lean_ctor_set(v_reuseFailAlloc_670_, 2, v___x_667_);
v___x_669_ = v_reuseFailAlloc_670_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
return v___x_669_;
}
}
else
{
lean_object* v___x_672_; 
lean_dec(v_value_661_);
lean_dec(v_key_660_);
if (v_isShared_665_ == 0)
{
lean_ctor_set(v___x_664_, 1, v_b_658_);
lean_ctor_set(v___x_664_, 0, v_a_657_);
v___x_672_ = v___x_664_;
goto v_reusejp_671_;
}
else
{
lean_object* v_reuseFailAlloc_673_; 
v_reuseFailAlloc_673_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_673_, 0, v_a_657_);
lean_ctor_set(v_reuseFailAlloc_673_, 1, v_b_658_);
lean_ctor_set(v_reuseFailAlloc_673_, 2, v_tail_662_);
v___x_672_ = v_reuseFailAlloc_673_;
goto v_reusejp_671_;
}
v_reusejp_671_:
{
return v___x_672_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__0_spec__0_spec__3_spec__9___redArg(lean_object* v_x_675_, lean_object* v_x_676_){
_start:
{
if (lean_obj_tag(v_x_676_) == 0)
{
return v_x_675_;
}
else
{
lean_object* v_key_677_; lean_object* v_value_678_; lean_object* v_tail_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_702_; 
v_key_677_ = lean_ctor_get(v_x_676_, 0);
v_value_678_ = lean_ctor_get(v_x_676_, 1);
v_tail_679_ = lean_ctor_get(v_x_676_, 2);
v_isSharedCheck_702_ = !lean_is_exclusive(v_x_676_);
if (v_isSharedCheck_702_ == 0)
{
v___x_681_ = v_x_676_;
v_isShared_682_ = v_isSharedCheck_702_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_tail_679_);
lean_inc(v_value_678_);
lean_inc(v_key_677_);
lean_dec(v_x_676_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_702_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
lean_object* v___x_683_; uint64_t v___x_684_; uint64_t v___x_685_; uint64_t v___x_686_; uint64_t v_fold_687_; uint64_t v___x_688_; uint64_t v___x_689_; uint64_t v___x_690_; size_t v___x_691_; size_t v___x_692_; size_t v___x_693_; size_t v___x_694_; size_t v___x_695_; lean_object* v___x_696_; lean_object* v___x_698_; 
v___x_683_ = lean_array_get_size(v_x_675_);
v___x_684_ = l_Lean_instHashableFVarId_hash(v_key_677_);
v___x_685_ = 32ULL;
v___x_686_ = lean_uint64_shift_right(v___x_684_, v___x_685_);
v_fold_687_ = lean_uint64_xor(v___x_684_, v___x_686_);
v___x_688_ = 16ULL;
v___x_689_ = lean_uint64_shift_right(v_fold_687_, v___x_688_);
v___x_690_ = lean_uint64_xor(v_fold_687_, v___x_689_);
v___x_691_ = lean_uint64_to_usize(v___x_690_);
v___x_692_ = lean_usize_of_nat(v___x_683_);
v___x_693_ = ((size_t)1ULL);
v___x_694_ = lean_usize_sub(v___x_692_, v___x_693_);
v___x_695_ = lean_usize_land(v___x_691_, v___x_694_);
v___x_696_ = lean_array_uget_borrowed(v_x_675_, v___x_695_);
lean_inc(v___x_696_);
if (v_isShared_682_ == 0)
{
lean_ctor_set(v___x_681_, 2, v___x_696_);
v___x_698_ = v___x_681_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v_key_677_);
lean_ctor_set(v_reuseFailAlloc_701_, 1, v_value_678_);
lean_ctor_set(v_reuseFailAlloc_701_, 2, v___x_696_);
v___x_698_ = v_reuseFailAlloc_701_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
lean_object* v___x_699_; 
v___x_699_ = lean_array_uset(v_x_675_, v___x_695_, v___x_698_);
v_x_675_ = v___x_699_;
v_x_676_ = v_tail_679_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__0_spec__0_spec__3___redArg(lean_object* v_i_703_, lean_object* v_source_704_, lean_object* v_target_705_){
_start:
{
lean_object* v___x_706_; uint8_t v___x_707_; 
v___x_706_ = lean_array_get_size(v_source_704_);
v___x_707_ = lean_nat_dec_lt(v_i_703_, v___x_706_);
if (v___x_707_ == 0)
{
lean_dec_ref(v_source_704_);
lean_dec(v_i_703_);
return v_target_705_;
}
else
{
lean_object* v_es_708_; lean_object* v___x_709_; lean_object* v_source_710_; lean_object* v_target_711_; lean_object* v___x_712_; lean_object* v___x_713_; 
v_es_708_ = lean_array_fget(v_source_704_, v_i_703_);
v___x_709_ = lean_box(0);
v_source_710_ = lean_array_fset(v_source_704_, v_i_703_, v___x_709_);
v_target_711_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__0_spec__0_spec__3_spec__9___redArg(v_target_705_, v_es_708_);
v___x_712_ = lean_unsigned_to_nat(1u);
v___x_713_ = lean_nat_add(v_i_703_, v___x_712_);
lean_dec(v_i_703_);
v_i_703_ = v___x_713_;
v_source_704_ = v_source_710_;
v_target_705_ = v_target_711_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__0_spec__0___redArg(lean_object* v_data_715_){
_start:
{
lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v_nbuckets_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; 
v___x_716_ = lean_array_get_size(v_data_715_);
v___x_717_ = lean_unsigned_to_nat(2u);
v_nbuckets_718_ = lean_nat_mul(v___x_716_, v___x_717_);
v___x_719_ = lean_unsigned_to_nat(0u);
v___x_720_ = lean_box(0);
v___x_721_ = lean_mk_array(v_nbuckets_718_, v___x_720_);
v___x_722_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__0_spec__0_spec__3___redArg(v___x_719_, v_data_715_, v___x_721_);
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__0___redArg(lean_object* v_m_723_, lean_object* v_a_724_, lean_object* v_b_725_){
_start:
{
lean_object* v_size_726_; lean_object* v_buckets_727_; lean_object* v___x_729_; uint8_t v_isShared_730_; uint8_t v_isSharedCheck_770_; 
v_size_726_ = lean_ctor_get(v_m_723_, 0);
v_buckets_727_ = lean_ctor_get(v_m_723_, 1);
v_isSharedCheck_770_ = !lean_is_exclusive(v_m_723_);
if (v_isSharedCheck_770_ == 0)
{
v___x_729_ = v_m_723_;
v_isShared_730_ = v_isSharedCheck_770_;
goto v_resetjp_728_;
}
else
{
lean_inc(v_buckets_727_);
lean_inc(v_size_726_);
lean_dec(v_m_723_);
v___x_729_ = lean_box(0);
v_isShared_730_ = v_isSharedCheck_770_;
goto v_resetjp_728_;
}
v_resetjp_728_:
{
lean_object* v___x_731_; uint64_t v___x_732_; uint64_t v___x_733_; uint64_t v___x_734_; uint64_t v_fold_735_; uint64_t v___x_736_; uint64_t v___x_737_; uint64_t v___x_738_; size_t v___x_739_; size_t v___x_740_; size_t v___x_741_; size_t v___x_742_; size_t v___x_743_; lean_object* v_bkt_744_; uint8_t v___x_745_; 
v___x_731_ = lean_array_get_size(v_buckets_727_);
v___x_732_ = l_Lean_instHashableFVarId_hash(v_a_724_);
v___x_733_ = 32ULL;
v___x_734_ = lean_uint64_shift_right(v___x_732_, v___x_733_);
v_fold_735_ = lean_uint64_xor(v___x_732_, v___x_734_);
v___x_736_ = 16ULL;
v___x_737_ = lean_uint64_shift_right(v_fold_735_, v___x_736_);
v___x_738_ = lean_uint64_xor(v_fold_735_, v___x_737_);
v___x_739_ = lean_uint64_to_usize(v___x_738_);
v___x_740_ = lean_usize_of_nat(v___x_731_);
v___x_741_ = ((size_t)1ULL);
v___x_742_ = lean_usize_sub(v___x_740_, v___x_741_);
v___x_743_ = lean_usize_land(v___x_739_, v___x_742_);
v_bkt_744_ = lean_array_uget_borrowed(v_buckets_727_, v___x_743_);
v___x_745_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_removeFromParent_spec__0_spec__0___redArg(v_a_724_, v_bkt_744_);
if (v___x_745_ == 0)
{
lean_object* v___x_746_; lean_object* v_size_x27_747_; lean_object* v___x_748_; lean_object* v_buckets_x27_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; uint8_t v___x_755_; 
v___x_746_ = lean_unsigned_to_nat(1u);
v_size_x27_747_ = lean_nat_add(v_size_726_, v___x_746_);
lean_dec(v_size_726_);
lean_inc(v_bkt_744_);
v___x_748_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_748_, 0, v_a_724_);
lean_ctor_set(v___x_748_, 1, v_b_725_);
lean_ctor_set(v___x_748_, 2, v_bkt_744_);
v_buckets_x27_749_ = lean_array_uset(v_buckets_727_, v___x_743_, v___x_748_);
v___x_750_ = lean_unsigned_to_nat(4u);
v___x_751_ = lean_nat_mul(v_size_x27_747_, v___x_750_);
v___x_752_ = lean_unsigned_to_nat(3u);
v___x_753_ = lean_nat_div(v___x_751_, v___x_752_);
lean_dec(v___x_751_);
v___x_754_ = lean_array_get_size(v_buckets_x27_749_);
v___x_755_ = lean_nat_dec_le(v___x_753_, v___x_754_);
lean_dec(v___x_753_);
if (v___x_755_ == 0)
{
lean_object* v_val_756_; lean_object* v___x_758_; 
v_val_756_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__0_spec__0___redArg(v_buckets_x27_749_);
if (v_isShared_730_ == 0)
{
lean_ctor_set(v___x_729_, 1, v_val_756_);
lean_ctor_set(v___x_729_, 0, v_size_x27_747_);
v___x_758_ = v___x_729_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v_size_x27_747_);
lean_ctor_set(v_reuseFailAlloc_759_, 1, v_val_756_);
v___x_758_ = v_reuseFailAlloc_759_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
return v___x_758_;
}
}
else
{
lean_object* v___x_761_; 
if (v_isShared_730_ == 0)
{
lean_ctor_set(v___x_729_, 1, v_buckets_x27_749_);
lean_ctor_set(v___x_729_, 0, v_size_x27_747_);
v___x_761_ = v___x_729_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v_size_x27_747_);
lean_ctor_set(v_reuseFailAlloc_762_, 1, v_buckets_x27_749_);
v___x_761_ = v_reuseFailAlloc_762_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
return v___x_761_;
}
}
}
else
{
lean_object* v___x_763_; lean_object* v_buckets_x27_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_768_; 
lean_inc(v_bkt_744_);
v___x_763_ = lean_box(0);
v_buckets_x27_764_ = lean_array_uset(v_buckets_727_, v___x_743_, v___x_763_);
v___x_765_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__0_spec__1___redArg(v_a_724_, v_b_725_, v_bkt_744_);
v___x_766_ = lean_array_uset(v_buckets_x27_764_, v___x_743_, v___x_765_);
if (v_isShared_730_ == 0)
{
lean_ctor_set(v___x_729_, 1, v___x_766_);
v___x_768_ = v___x_729_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v_size_726_);
lean_ctor_set(v_reuseFailAlloc_769_, 1, v___x_766_);
v___x_768_ = v_reuseFailAlloc_769_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
return v___x_768_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__1___redArg(lean_object* v_m_771_, lean_object* v_a_772_, lean_object* v_b_773_){
_start:
{
lean_object* v_size_774_; lean_object* v_buckets_775_; lean_object* v___x_776_; uint64_t v___x_777_; uint64_t v___x_778_; uint64_t v___x_779_; uint64_t v_fold_780_; uint64_t v___x_781_; uint64_t v___x_782_; uint64_t v___x_783_; size_t v___x_784_; size_t v___x_785_; size_t v___x_786_; size_t v___x_787_; size_t v___x_788_; lean_object* v_bkt_789_; uint8_t v___x_790_; 
v_size_774_ = lean_ctor_get(v_m_771_, 0);
v_buckets_775_ = lean_ctor_get(v_m_771_, 1);
v___x_776_ = lean_array_get_size(v_buckets_775_);
v___x_777_ = l_Lean_instHashableFVarId_hash(v_a_772_);
v___x_778_ = 32ULL;
v___x_779_ = lean_uint64_shift_right(v___x_777_, v___x_778_);
v_fold_780_ = lean_uint64_xor(v___x_777_, v___x_779_);
v___x_781_ = 16ULL;
v___x_782_ = lean_uint64_shift_right(v_fold_780_, v___x_781_);
v___x_783_ = lean_uint64_xor(v_fold_780_, v___x_782_);
v___x_784_ = lean_uint64_to_usize(v___x_783_);
v___x_785_ = lean_usize_of_nat(v___x_776_);
v___x_786_ = ((size_t)1ULL);
v___x_787_ = lean_usize_sub(v___x_785_, v___x_786_);
v___x_788_ = lean_usize_land(v___x_784_, v___x_787_);
v_bkt_789_ = lean_array_uget_borrowed(v_buckets_775_, v___x_788_);
v___x_790_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_removeFromParent_spec__0_spec__0___redArg(v_a_772_, v_bkt_789_);
if (v___x_790_ == 0)
{
lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_811_; 
lean_inc_ref(v_buckets_775_);
lean_inc(v_size_774_);
v_isSharedCheck_811_ = !lean_is_exclusive(v_m_771_);
if (v_isSharedCheck_811_ == 0)
{
lean_object* v_unused_812_; lean_object* v_unused_813_; 
v_unused_812_ = lean_ctor_get(v_m_771_, 1);
lean_dec(v_unused_812_);
v_unused_813_ = lean_ctor_get(v_m_771_, 0);
lean_dec(v_unused_813_);
v___x_792_ = v_m_771_;
v_isShared_793_ = v_isSharedCheck_811_;
goto v_resetjp_791_;
}
else
{
lean_dec(v_m_771_);
v___x_792_ = lean_box(0);
v_isShared_793_ = v_isSharedCheck_811_;
goto v_resetjp_791_;
}
v_resetjp_791_:
{
lean_object* v___x_794_; lean_object* v_size_x27_795_; lean_object* v___x_796_; lean_object* v_buckets_x27_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; uint8_t v___x_803_; 
v___x_794_ = lean_unsigned_to_nat(1u);
v_size_x27_795_ = lean_nat_add(v_size_774_, v___x_794_);
lean_dec(v_size_774_);
lean_inc(v_bkt_789_);
v___x_796_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_796_, 0, v_a_772_);
lean_ctor_set(v___x_796_, 1, v_b_773_);
lean_ctor_set(v___x_796_, 2, v_bkt_789_);
v_buckets_x27_797_ = lean_array_uset(v_buckets_775_, v___x_788_, v___x_796_);
v___x_798_ = lean_unsigned_to_nat(4u);
v___x_799_ = lean_nat_mul(v_size_x27_795_, v___x_798_);
v___x_800_ = lean_unsigned_to_nat(3u);
v___x_801_ = lean_nat_div(v___x_799_, v___x_800_);
lean_dec(v___x_799_);
v___x_802_ = lean_array_get_size(v_buckets_x27_797_);
v___x_803_ = lean_nat_dec_le(v___x_801_, v___x_802_);
lean_dec(v___x_801_);
if (v___x_803_ == 0)
{
lean_object* v_val_804_; lean_object* v___x_806_; 
v_val_804_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__0_spec__0___redArg(v_buckets_x27_797_);
if (v_isShared_793_ == 0)
{
lean_ctor_set(v___x_792_, 1, v_val_804_);
lean_ctor_set(v___x_792_, 0, v_size_x27_795_);
v___x_806_ = v___x_792_;
goto v_reusejp_805_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v_size_x27_795_);
lean_ctor_set(v_reuseFailAlloc_807_, 1, v_val_804_);
v___x_806_ = v_reuseFailAlloc_807_;
goto v_reusejp_805_;
}
v_reusejp_805_:
{
return v___x_806_;
}
}
else
{
lean_object* v___x_809_; 
if (v_isShared_793_ == 0)
{
lean_ctor_set(v___x_792_, 1, v_buckets_x27_797_);
lean_ctor_set(v___x_792_, 0, v_size_x27_795_);
v___x_809_ = v___x_792_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v_size_x27_795_);
lean_ctor_set(v_reuseFailAlloc_810_, 1, v_buckets_x27_797_);
v___x_809_ = v_reuseFailAlloc_810_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
return v___x_809_;
}
}
}
}
else
{
lean_dec(v_b_773_);
lean_dec(v_a_772_);
return v_m_771_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__3_spec__5(lean_object* v___x_814_, lean_object* v_a_815_, lean_object* v_x_816_){
_start:
{
if (lean_obj_tag(v_x_816_) == 0)
{
lean_dec(v_a_815_);
lean_dec(v___x_814_);
return v_x_816_;
}
else
{
lean_object* v_key_817_; lean_object* v_value_818_; lean_object* v_tail_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_842_; 
v_key_817_ = lean_ctor_get(v_x_816_, 0);
v_value_818_ = lean_ctor_get(v_x_816_, 1);
v_tail_819_ = lean_ctor_get(v_x_816_, 2);
v_isSharedCheck_842_ = !lean_is_exclusive(v_x_816_);
if (v_isSharedCheck_842_ == 0)
{
v___x_821_ = v_x_816_;
v_isShared_822_ = v_isSharedCheck_842_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_tail_819_);
lean_inc(v_value_818_);
lean_inc(v_key_817_);
lean_dec(v_x_816_);
v___x_821_ = lean_box(0);
v_isShared_822_ = v_isSharedCheck_842_;
goto v_resetjp_820_;
}
v_resetjp_820_:
{
uint8_t v___x_823_; 
v___x_823_ = l_Lean_instBEqFVarId_beq(v_key_817_, v_a_815_);
if (v___x_823_ == 0)
{
lean_object* v___x_824_; lean_object* v___x_826_; 
v___x_824_ = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__3_spec__5(v___x_814_, v_a_815_, v_tail_819_);
if (v_isShared_822_ == 0)
{
lean_ctor_set(v___x_821_, 2, v___x_824_);
v___x_826_ = v___x_821_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_827_; 
v_reuseFailAlloc_827_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v_key_817_);
lean_ctor_set(v_reuseFailAlloc_827_, 1, v_value_818_);
lean_ctor_set(v_reuseFailAlloc_827_, 2, v___x_824_);
v___x_826_ = v_reuseFailAlloc_827_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
return v___x_826_;
}
}
else
{
lean_object* v_parents_828_; lean_object* v_children_829_; lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_841_; 
lean_dec(v_key_817_);
v_parents_828_ = lean_ctor_get(v_value_818_, 0);
v_children_829_ = lean_ctor_get(v_value_818_, 1);
v_isSharedCheck_841_ = !lean_is_exclusive(v_value_818_);
if (v_isSharedCheck_841_ == 0)
{
v___x_831_ = v_value_818_;
v_isShared_832_ = v_isSharedCheck_841_;
goto v_resetjp_830_;
}
else
{
lean_inc(v_children_829_);
lean_inc(v_parents_828_);
lean_dec(v_value_818_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_841_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_836_; 
v___x_833_ = lean_box(0);
v___x_834_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__1___redArg(v_children_829_, v___x_814_, v___x_833_);
if (v_isShared_832_ == 0)
{
lean_ctor_set(v___x_831_, 1, v___x_834_);
v___x_836_ = v___x_831_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v_parents_828_);
lean_ctor_set(v_reuseFailAlloc_840_, 1, v___x_834_);
v___x_836_ = v_reuseFailAlloc_840_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
lean_object* v___x_838_; 
if (v_isShared_822_ == 0)
{
lean_ctor_set(v___x_821_, 1, v___x_836_);
lean_ctor_set(v___x_821_, 0, v_a_815_);
v___x_838_ = v___x_821_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v_a_815_);
lean_ctor_set(v_reuseFailAlloc_839_, 1, v___x_836_);
lean_ctor_set(v_reuseFailAlloc_839_, 2, v_tail_819_);
v___x_838_ = v_reuseFailAlloc_839_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
return v___x_838_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__3(lean_object* v___x_843_, lean_object* v_m_844_, lean_object* v_a_845_){
_start:
{
lean_object* v_size_846_; lean_object* v_buckets_847_; lean_object* v___x_848_; uint64_t v___x_849_; uint64_t v___x_850_; uint64_t v___x_851_; uint64_t v_fold_852_; uint64_t v___x_853_; uint64_t v___x_854_; uint64_t v___x_855_; size_t v___x_856_; size_t v___x_857_; size_t v___x_858_; size_t v___x_859_; size_t v___x_860_; lean_object* v_bucket_861_; uint8_t v___x_862_; 
v_size_846_ = lean_ctor_get(v_m_844_, 0);
v_buckets_847_ = lean_ctor_get(v_m_844_, 1);
v___x_848_ = lean_array_get_size(v_buckets_847_);
v___x_849_ = l_Lean_instHashableFVarId_hash(v_a_845_);
v___x_850_ = 32ULL;
v___x_851_ = lean_uint64_shift_right(v___x_849_, v___x_850_);
v_fold_852_ = lean_uint64_xor(v___x_849_, v___x_851_);
v___x_853_ = 16ULL;
v___x_854_ = lean_uint64_shift_right(v_fold_852_, v___x_853_);
v___x_855_ = lean_uint64_xor(v_fold_852_, v___x_854_);
v___x_856_ = lean_uint64_to_usize(v___x_855_);
v___x_857_ = lean_usize_of_nat(v___x_848_);
v___x_858_ = ((size_t)1ULL);
v___x_859_ = lean_usize_sub(v___x_857_, v___x_858_);
v___x_860_ = lean_usize_land(v___x_856_, v___x_859_);
v_bucket_861_ = lean_array_uget_borrowed(v_buckets_847_, v___x_860_);
v___x_862_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_removeFromParent_spec__0_spec__0___redArg(v_a_845_, v_bucket_861_);
if (v___x_862_ == 0)
{
lean_dec(v_a_845_);
lean_dec(v___x_843_);
return v_m_844_;
}
else
{
lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_873_; 
lean_inc(v_bucket_861_);
lean_inc_ref(v_buckets_847_);
lean_inc(v_size_846_);
v_isSharedCheck_873_ = !lean_is_exclusive(v_m_844_);
if (v_isSharedCheck_873_ == 0)
{
lean_object* v_unused_874_; lean_object* v_unused_875_; 
v_unused_874_ = lean_ctor_get(v_m_844_, 1);
lean_dec(v_unused_874_);
v_unused_875_ = lean_ctor_get(v_m_844_, 0);
lean_dec(v_unused_875_);
v___x_864_ = v_m_844_;
v_isShared_865_ = v_isSharedCheck_873_;
goto v_resetjp_863_;
}
else
{
lean_dec(v_m_844_);
v___x_864_ = lean_box(0);
v_isShared_865_ = v_isSharedCheck_873_;
goto v_resetjp_863_;
}
v_resetjp_863_:
{
lean_object* v___x_866_; lean_object* v_buckets_867_; lean_object* v_bucket_868_; lean_object* v___x_869_; lean_object* v___x_871_; 
v___x_866_ = lean_box(0);
v_buckets_867_ = lean_array_uset(v_buckets_847_, v___x_860_, v___x_866_);
v_bucket_868_ = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__3_spec__5(v___x_843_, v_a_845_, v_bucket_861_);
v___x_869_ = lean_array_uset(v_buckets_867_, v___x_860_, v_bucket_868_);
if (v_isShared_865_ == 0)
{
lean_ctor_set(v___x_864_, 1, v___x_869_);
v___x_871_ = v___x_864_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v_size_846_);
lean_ctor_set(v_reuseFailAlloc_872_, 1, v___x_869_);
v___x_871_ = v_reuseFailAlloc_872_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
return v___x_871_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__4(lean_object* v___x_876_, lean_object* v_as_877_, size_t v_i_878_, size_t v_stop_879_, lean_object* v_b_880_){
_start:
{
uint8_t v___x_881_; 
v___x_881_ = lean_usize_dec_eq(v_i_878_, v_stop_879_);
if (v___x_881_ == 0)
{
lean_object* v___x_882_; lean_object* v___x_883_; size_t v___x_884_; size_t v___x_885_; 
v___x_882_ = lean_array_uget_borrowed(v_as_877_, v_i_878_);
lean_inc(v___x_882_);
lean_inc(v___x_876_);
v___x_883_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__3(v___x_876_, v_b_880_, v___x_882_);
v___x_884_ = ((size_t)1ULL);
v___x_885_ = lean_usize_add(v_i_878_, v___x_884_);
v_i_878_ = v___x_885_;
v_b_880_ = v___x_883_;
goto _start;
}
else
{
lean_dec(v___x_876_);
return v_b_880_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__4___boxed(lean_object* v___x_887_, lean_object* v_as_888_, lean_object* v_i_889_, lean_object* v_stop_890_, lean_object* v_b_891_){
_start:
{
size_t v_i_boxed_892_; size_t v_stop_boxed_893_; lean_object* v_res_894_; 
v_i_boxed_892_ = lean_unbox_usize(v_i_889_);
lean_dec(v_i_889_);
v_stop_boxed_893_ = lean_unbox_usize(v_stop_890_);
lean_dec(v_stop_890_);
v_res_894_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__4(v___x_887_, v_as_888_, v_i_boxed_892_, v_stop_boxed_893_, v_b_891_);
lean_dec_ref(v_as_888_);
return v_res_894_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__5___redArg(lean_object* v_as_895_, size_t v_i_896_, size_t v_stop_897_, lean_object* v_b_898_, lean_object* v___y_899_){
_start:
{
uint8_t v___x_901_; 
v___x_901_ = lean_usize_dec_eq(v_i_896_, v_stop_897_);
if (v___x_901_ == 0)
{
lean_object* v___x_902_; lean_object* v_fst_904_; lean_object* v_snd_905_; lean_object* v_varMap_910_; lean_object* v_borrowedParams_911_; lean_object* v___x_913_; uint8_t v_isShared_914_; uint8_t v_isSharedCheck_929_; 
v___x_902_ = lean_st_ref_take(v___y_899_);
v_varMap_910_ = lean_ctor_get(v___x_902_, 0);
v_borrowedParams_911_ = lean_ctor_get(v___x_902_, 1);
v_isSharedCheck_929_ = !lean_is_exclusive(v___x_902_);
if (v_isSharedCheck_929_ == 0)
{
v___x_913_ = v___x_902_;
v_isShared_914_ = v_isSharedCheck_929_;
goto v_resetjp_912_;
}
else
{
lean_inc(v_borrowedParams_911_);
lean_inc(v_varMap_910_);
lean_dec(v___x_902_);
v___x_913_ = lean_box(0);
v_isShared_914_ = v_isSharedCheck_929_;
goto v_resetjp_912_;
}
v___jp_903_:
{
lean_object* v___x_906_; size_t v___x_907_; size_t v___x_908_; 
v___x_906_ = lean_st_ref_set(v___y_899_, v_snd_905_);
v___x_907_ = ((size_t)1ULL);
v___x_908_ = lean_usize_add(v_i_896_, v___x_907_);
v_i_896_ = v___x_908_;
v_b_898_ = v_fst_904_;
goto _start;
}
v_resetjp_912_:
{
lean_object* v___x_915_; lean_object* v_fvarId_916_; lean_object* v_type_917_; uint8_t v_borrow_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; 
v___x_915_ = lean_array_uget_borrowed(v_as_895_, v_i_896_);
v_fvarId_916_ = lean_ctor_get(v___x_915_, 0);
v_type_917_ = lean_ctor_get(v___x_915_, 2);
v_borrow_918_ = lean_ctor_get_uint8(v___x_915_, sizeof(void*)*3);
v___x_919_ = lean_box(0);
v___x_920_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_visitParam___redArg___closed__3, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_visitParam___redArg___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_visitParam___redArg___closed__3);
lean_inc(v_fvarId_916_);
v___x_921_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__0___redArg(v_varMap_910_, v_fvarId_916_, v___x_920_);
if (v_borrow_918_ == 0)
{
goto v___jp_922_;
}
else
{
uint8_t v___x_926_; 
v___x_926_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isPossibleRef(v_type_917_);
if (v___x_926_ == 0)
{
goto v___jp_922_;
}
else
{
lean_object* v___x_927_; lean_object* v___x_928_; 
lean_del_object(v___x_913_);
lean_inc(v_fvarId_916_);
v___x_927_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__1___redArg(v_borrowedParams_911_, v_fvarId_916_, v___x_919_);
v___x_928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_928_, 0, v___x_921_);
lean_ctor_set(v___x_928_, 1, v___x_927_);
v_fst_904_ = v___x_919_;
v_snd_905_ = v___x_928_;
goto v___jp_903_;
}
}
v___jp_922_:
{
lean_object* v___x_924_; 
if (v_isShared_914_ == 0)
{
lean_ctor_set(v___x_913_, 0, v___x_921_);
v___x_924_ = v___x_913_;
goto v_reusejp_923_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v___x_921_);
lean_ctor_set(v_reuseFailAlloc_925_, 1, v_borrowedParams_911_);
v___x_924_ = v_reuseFailAlloc_925_;
goto v_reusejp_923_;
}
v_reusejp_923_:
{
v_fst_904_ = v___x_919_;
v_snd_905_ = v___x_924_;
goto v___jp_903_;
}
}
}
}
else
{
lean_object* v___x_930_; 
v___x_930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_930_, 0, v_b_898_);
return v___x_930_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__5___redArg___boxed(lean_object* v_as_931_, lean_object* v_i_932_, lean_object* v_stop_933_, lean_object* v_b_934_, lean_object* v___y_935_, lean_object* v___y_936_){
_start:
{
size_t v_i_boxed_937_; size_t v_stop_boxed_938_; lean_object* v_res_939_; 
v_i_boxed_937_ = lean_unbox_usize(v_i_932_);
lean_dec(v_i_932_);
v_stop_boxed_938_ = lean_unbox_usize(v_stop_933_);
lean_dec(v_stop_933_);
v_res_939_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__5___redArg(v_as_931_, v_i_boxed_937_, v_stop_boxed_938_, v_b_934_, v___y_935_);
lean_dec(v___y_935_);
lean_dec_ref(v_as_931_);
return v_res_939_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode___closed__7(void){
_start:
{
lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; 
v___x_947_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode___closed__6));
v___x_948_ = lean_unsigned_to_nat(59u);
v___x_949_ = lean_unsigned_to_nat(127u);
v___x_950_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode___closed__5));
v___x_951_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode___closed__4));
v___x_952_ = l_mkPanicMessageWithDecl(v___x_951_, v___x_950_, v___x_949_, v___x_948_, v___x_947_);
return v___x_952_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode(lean_object* v_code_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_){
_start:
{
switch(lean_obj_tag(v_code_953_))
{
case 0:
{
lean_object* v_decl_960_; lean_object* v_k_961_; lean_object* v___x_963_; uint8_t v_isShared_964_; uint8_t v_isSharedCheck_1129_; 
v_decl_960_ = lean_ctor_get(v_code_953_, 0);
v_k_961_ = lean_ctor_get(v_code_953_, 1);
v_isSharedCheck_1129_ = !lean_is_exclusive(v_code_953_);
if (v_isSharedCheck_1129_ == 0)
{
v___x_963_ = v_code_953_;
v_isShared_964_ = v_isSharedCheck_1129_;
goto v_resetjp_962_;
}
else
{
lean_inc(v_k_961_);
lean_inc(v_decl_960_);
lean_dec(v_code_953_);
v___x_963_ = lean_box(0);
v_isShared_964_ = v_isSharedCheck_1129_;
goto v_resetjp_962_;
}
v_resetjp_962_:
{
lean_object* v_borrowedParams_966_; lean_object* v___y_967_; lean_object* v___y_968_; lean_object* v___y_969_; lean_object* v___y_970_; lean_object* v___y_971_; lean_object* v___y_972_; lean_object* v___y_973_; lean_object* v___y_974_; lean_object* v___y_975_; lean_object* v___y_984_; lean_object* v_borrowedParams_985_; lean_object* v___y_986_; lean_object* v___y_987_; lean_object* v___y_988_; lean_object* v___y_989_; lean_object* v___y_990_; lean_object* v___y_991_; lean_object* v___y_992_; lean_object* v___y_993_; lean_object* v_fvarId_999_; lean_object* v_value_1000_; lean_object* v_args_1002_; lean_object* v___y_1003_; lean_object* v___y_1004_; lean_object* v___y_1005_; lean_object* v___y_1006_; lean_object* v___y_1007_; lean_object* v_arr_1030_; lean_object* v___y_1031_; lean_object* v___y_1032_; lean_object* v___y_1033_; lean_object* v___y_1034_; lean_object* v___y_1035_; 
v_fvarId_999_ = lean_ctor_get(v_decl_960_, 0);
lean_inc(v_fvarId_999_);
v_value_1000_ = lean_ctor_get(v_decl_960_, 3);
lean_inc(v_value_1000_);
lean_dec_ref(v_decl_960_);
switch(lean_obj_tag(v_value_1000_))
{
case 6:
{
lean_object* v_var_1050_; lean_object* v___x_1052_; uint8_t v_isShared_1053_; uint8_t v_isSharedCheck_1086_; 
lean_del_object(v___x_963_);
v_var_1050_ = lean_ctor_get(v_value_1000_, 1);
v_isSharedCheck_1086_ = !lean_is_exclusive(v_value_1000_);
if (v_isSharedCheck_1086_ == 0)
{
lean_object* v_unused_1087_; 
v_unused_1087_ = lean_ctor_get(v_value_1000_, 0);
lean_dec(v_unused_1087_);
v___x_1052_ = v_value_1000_;
v_isShared_1053_ = v_isSharedCheck_1086_;
goto v_resetjp_1051_;
}
else
{
lean_inc(v_var_1050_);
lean_dec(v_value_1000_);
v___x_1052_ = lean_box(0);
v_isShared_1053_ = v_isSharedCheck_1086_;
goto v_resetjp_1051_;
}
v_resetjp_1051_:
{
lean_object* v___x_1054_; lean_object* v_varMap_1055_; lean_object* v_borrowedParams_1056_; lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1085_; 
v___x_1054_ = lean_st_ref_take(v_a_954_);
v_varMap_1055_ = lean_ctor_get(v___x_1054_, 0);
v_borrowedParams_1056_ = lean_ctor_get(v___x_1054_, 1);
v_isSharedCheck_1085_ = !lean_is_exclusive(v___x_1054_);
if (v_isSharedCheck_1085_ == 0)
{
v___x_1058_ = v___x_1054_;
v_isShared_1059_ = v_isSharedCheck_1085_;
goto v_resetjp_1057_;
}
else
{
lean_inc(v_borrowedParams_1056_);
lean_inc(v_varMap_1055_);
lean_dec(v___x_1054_);
v___x_1058_ = lean_box(0);
v_isShared_1059_ = v_isSharedCheck_1085_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___y_1065_; lean_object* v___x_1075_; lean_object* v___x_1076_; uint8_t v___x_1077_; 
v___x_1060_ = l_Lean_instEmptyCollectionFVarIdHashSet;
v___x_1061_ = lean_unsigned_to_nat(1u);
v___x_1062_ = lean_mk_empty_array_with_capacity(v___x_1061_);
v___x_1063_ = lean_array_push(v___x_1062_, v_var_1050_);
v___x_1075_ = lean_unsigned_to_nat(0u);
v___x_1076_ = lean_array_get_size(v___x_1063_);
v___x_1077_ = lean_nat_dec_lt(v___x_1075_, v___x_1076_);
if (v___x_1077_ == 0)
{
v___y_1065_ = v_varMap_1055_;
goto v___jp_1064_;
}
else
{
uint8_t v___x_1078_; 
v___x_1078_ = lean_nat_dec_le(v___x_1076_, v___x_1076_);
if (v___x_1078_ == 0)
{
if (v___x_1077_ == 0)
{
v___y_1065_ = v_varMap_1055_;
goto v___jp_1064_;
}
else
{
size_t v___x_1079_; size_t v___x_1080_; lean_object* v___x_1081_; 
v___x_1079_ = ((size_t)0ULL);
v___x_1080_ = lean_usize_of_nat(v___x_1076_);
lean_inc(v_fvarId_999_);
v___x_1081_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__4(v_fvarId_999_, v___x_1063_, v___x_1079_, v___x_1080_, v_varMap_1055_);
v___y_1065_ = v___x_1081_;
goto v___jp_1064_;
}
}
else
{
size_t v___x_1082_; size_t v___x_1083_; lean_object* v___x_1084_; 
v___x_1082_ = ((size_t)0ULL);
v___x_1083_ = lean_usize_of_nat(v___x_1076_);
lean_inc(v_fvarId_999_);
v___x_1084_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__4(v_fvarId_999_, v___x_1063_, v___x_1082_, v___x_1083_, v_varMap_1055_);
v___y_1065_ = v___x_1084_;
goto v___jp_1064_;
}
}
v___jp_1064_:
{
lean_object* v___x_1067_; 
if (v_isShared_1053_ == 0)
{
lean_ctor_set_tag(v___x_1052_, 0);
lean_ctor_set(v___x_1052_, 1, v___x_1060_);
lean_ctor_set(v___x_1052_, 0, v___x_1063_);
v___x_1067_ = v___x_1052_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v___x_1063_);
lean_ctor_set(v_reuseFailAlloc_1074_, 1, v___x_1060_);
v___x_1067_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
lean_object* v___x_1068_; lean_object* v___x_1070_; 
v___x_1068_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__0___redArg(v___y_1065_, v_fvarId_999_, v___x_1067_);
if (v_isShared_1059_ == 0)
{
lean_ctor_set(v___x_1058_, 0, v___x_1068_);
v___x_1070_ = v___x_1058_;
goto v_reusejp_1069_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v___x_1068_);
lean_ctor_set(v_reuseFailAlloc_1073_, 1, v_borrowedParams_1056_);
v___x_1070_ = v_reuseFailAlloc_1073_;
goto v_reusejp_1069_;
}
v_reusejp_1069_:
{
lean_object* v___x_1071_; 
v___x_1071_ = lean_st_ref_set(v_a_954_, v___x_1070_);
v_code_953_ = v_k_961_;
goto _start;
}
}
}
}
}
}
case 9:
{
lean_object* v_fn_1088_; lean_object* v_args_1089_; lean_object* v_arr_1091_; lean_object* v___y_1092_; lean_object* v___y_1093_; lean_object* v___y_1094_; lean_object* v___y_1095_; lean_object* v___y_1096_; 
v_fn_1088_ = lean_ctor_get(v_value_1000_, 0);
lean_inc(v_fn_1088_);
v_args_1089_ = lean_ctor_get(v_value_1000_, 1);
lean_inc_ref(v_args_1089_);
lean_dec_ref(v_value_1000_);
if (lean_obj_tag(v_fn_1088_) == 1)
{
lean_object* v_pre_1102_; 
v_pre_1102_ = lean_ctor_get(v_fn_1088_, 0);
lean_inc(v_pre_1102_);
if (lean_obj_tag(v_pre_1102_) == 1)
{
lean_object* v_pre_1103_; 
v_pre_1103_ = lean_ctor_get(v_pre_1102_, 0);
if (lean_obj_tag(v_pre_1103_) == 0)
{
lean_object* v_str_1104_; lean_object* v_str_1105_; lean_object* v___x_1106_; uint8_t v___x_1107_; 
v_str_1104_ = lean_ctor_get(v_fn_1088_, 1);
lean_inc_ref(v_str_1104_);
lean_dec_ref(v_fn_1088_);
v_str_1105_ = lean_ctor_get(v_pre_1102_, 1);
lean_inc_ref(v_str_1105_);
lean_dec_ref(v_pre_1102_);
v___x_1106_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode___closed__0));
v___x_1107_ = lean_string_dec_eq(v_str_1105_, v___x_1106_);
lean_dec_ref(v_str_1105_);
if (v___x_1107_ == 0)
{
lean_dec_ref(v_str_1104_);
lean_dec_ref(v_args_1089_);
lean_dec(v_fvarId_999_);
lean_del_object(v___x_963_);
v_code_953_ = v_k_961_;
goto _start;
}
else
{
lean_object* v___x_1109_; uint8_t v___x_1110_; 
v___x_1109_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode___closed__1));
v___x_1110_ = lean_string_dec_eq(v_str_1104_, v___x_1109_);
if (v___x_1110_ == 0)
{
lean_object* v___x_1111_; uint8_t v___x_1112_; 
v___x_1111_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode___closed__2));
v___x_1112_ = lean_string_dec_eq(v_str_1104_, v___x_1111_);
if (v___x_1112_ == 0)
{
lean_object* v___x_1113_; uint8_t v___x_1114_; 
lean_del_object(v___x_963_);
v___x_1113_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode___closed__3));
v___x_1114_ = lean_string_dec_eq(v_str_1104_, v___x_1113_);
lean_dec_ref(v_str_1104_);
if (v___x_1114_ == 0)
{
lean_dec_ref(v_args_1089_);
lean_dec(v_fvarId_999_);
v_code_953_ = v_k_961_;
goto _start;
}
else
{
v_args_1002_ = v_args_1089_;
v___y_1003_ = v_a_954_;
v___y_1004_ = v_a_955_;
v___y_1005_ = v_a_956_;
v___y_1006_ = v_a_957_;
v___y_1007_ = v_a_958_;
goto v___jp_1001_;
}
}
else
{
lean_object* v_arr_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; 
lean_dec_ref(v_str_1104_);
v_arr_1116_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_visitParam___redArg___closed__2));
v___x_1117_ = lean_box(0);
v___x_1118_ = lean_unsigned_to_nat(1u);
v___x_1119_ = lean_array_get_borrowed(v___x_1117_, v_args_1089_, v___x_1118_);
if (lean_obj_tag(v___x_1119_) == 1)
{
lean_object* v_fvarId_1120_; lean_object* v_arr_1121_; 
v_fvarId_1120_ = lean_ctor_get(v___x_1119_, 0);
lean_inc(v_fvarId_1120_);
v_arr_1121_ = lean_array_push(v_arr_1116_, v_fvarId_1120_);
v_arr_1091_ = v_arr_1121_;
v___y_1092_ = v_a_954_;
v___y_1093_ = v_a_955_;
v___y_1094_ = v_a_956_;
v___y_1095_ = v_a_957_;
v___y_1096_ = v_a_958_;
goto v___jp_1090_;
}
else
{
v_arr_1091_ = v_arr_1116_;
v___y_1092_ = v_a_954_;
v___y_1093_ = v_a_955_;
v___y_1094_ = v_a_956_;
v___y_1095_ = v_a_957_;
v___y_1096_ = v_a_958_;
goto v___jp_1090_;
}
}
}
else
{
lean_dec_ref(v_str_1104_);
lean_del_object(v___x_963_);
v_args_1002_ = v_args_1089_;
v___y_1003_ = v_a_954_;
v___y_1004_ = v_a_955_;
v___y_1005_ = v_a_956_;
v___y_1006_ = v_a_957_;
v___y_1007_ = v_a_958_;
goto v___jp_1001_;
}
}
}
else
{
lean_dec_ref(v_pre_1102_);
lean_dec_ref(v_fn_1088_);
lean_dec_ref(v_args_1089_);
lean_dec(v_fvarId_999_);
lean_del_object(v___x_963_);
v_code_953_ = v_k_961_;
goto _start;
}
}
else
{
lean_dec(v_pre_1102_);
lean_dec_ref(v_fn_1088_);
lean_dec_ref(v_args_1089_);
lean_dec(v_fvarId_999_);
lean_del_object(v___x_963_);
v_code_953_ = v_k_961_;
goto _start;
}
}
else
{
lean_dec_ref(v_args_1089_);
lean_dec(v_fn_1088_);
lean_dec(v_fvarId_999_);
lean_del_object(v___x_963_);
v_code_953_ = v_k_961_;
goto _start;
}
v___jp_1090_:
{
lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; 
v___x_1097_ = lean_box(0);
v___x_1098_ = lean_unsigned_to_nat(2u);
v___x_1099_ = lean_array_get(v___x_1097_, v_args_1089_, v___x_1098_);
lean_dec_ref(v_args_1089_);
if (lean_obj_tag(v___x_1099_) == 1)
{
lean_object* v_fvarId_1100_; lean_object* v_arr_1101_; 
v_fvarId_1100_ = lean_ctor_get(v___x_1099_, 0);
lean_inc(v_fvarId_1100_);
lean_dec_ref(v___x_1099_);
v_arr_1101_ = lean_array_push(v_arr_1091_, v_fvarId_1100_);
v_arr_1030_ = v_arr_1101_;
v___y_1031_ = v___y_1092_;
v___y_1032_ = v___y_1093_;
v___y_1033_ = v___y_1094_;
v___y_1034_ = v___y_1095_;
v___y_1035_ = v___y_1096_;
goto v___jp_1029_;
}
else
{
lean_dec(v___x_1099_);
v_arr_1030_ = v_arr_1091_;
v___y_1031_ = v___y_1092_;
v___y_1032_ = v___y_1093_;
v___y_1033_ = v___y_1094_;
v___y_1034_ = v___y_1095_;
v___y_1035_ = v___y_1096_;
goto v___jp_1029_;
}
}
}
case 11:
{
lean_object* v_var_1125_; lean_object* v___x_1126_; 
lean_dec(v_fvarId_999_);
lean_del_object(v___x_963_);
v_var_1125_ = lean_ctor_get(v_value_1000_, 1);
lean_inc(v_var_1125_);
lean_dec_ref(v_value_1000_);
v___x_1126_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_removeFromParent(v_var_1125_, v_a_954_, v_a_955_, v_a_956_, v_a_957_, v_a_958_);
lean_dec(v_var_1125_);
if (lean_obj_tag(v___x_1126_) == 0)
{
lean_dec_ref(v___x_1126_);
v_code_953_ = v_k_961_;
goto _start;
}
else
{
lean_dec_ref(v_k_961_);
return v___x_1126_;
}
}
default: 
{
lean_dec(v_value_1000_);
lean_dec(v_fvarId_999_);
lean_del_object(v___x_963_);
v_code_953_ = v_k_961_;
goto _start;
}
}
v___jp_965_:
{
lean_object* v___x_977_; 
if (v_isShared_964_ == 0)
{
lean_ctor_set(v___x_963_, 1, v___y_967_);
lean_ctor_set(v___x_963_, 0, v___y_968_);
v___x_977_ = v___x_963_;
goto v_reusejp_976_;
}
else
{
lean_object* v_reuseFailAlloc_982_; 
v_reuseFailAlloc_982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_982_, 0, v___y_968_);
lean_ctor_set(v_reuseFailAlloc_982_, 1, v___y_967_);
v___x_977_ = v_reuseFailAlloc_982_;
goto v_reusejp_976_;
}
v_reusejp_976_:
{
lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; 
v___x_978_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__0___redArg(v___y_975_, v___y_970_, v___x_977_);
v___x_979_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_979_, 0, v___x_978_);
lean_ctor_set(v___x_979_, 1, v_borrowedParams_966_);
v___x_980_ = lean_st_ref_set(v___y_973_, v___x_979_);
v_code_953_ = v_k_961_;
v_a_954_ = v___y_973_;
v_a_955_ = v___y_971_;
v_a_956_ = v___y_969_;
v_a_957_ = v___y_972_;
v_a_958_ = v___y_974_;
goto _start;
}
}
v___jp_983_:
{
lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; 
v___x_994_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_994_, 0, v___y_986_);
lean_ctor_set(v___x_994_, 1, v___y_991_);
v___x_995_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__0___redArg(v___y_993_, v___y_992_, v___x_994_);
v___x_996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_996_, 0, v___x_995_);
lean_ctor_set(v___x_996_, 1, v_borrowedParams_985_);
v___x_997_ = lean_st_ref_set(v___y_987_, v___x_996_);
v_code_953_ = v_k_961_;
v_a_954_ = v___y_987_;
v_a_955_ = v___y_984_;
v_a_956_ = v___y_989_;
v_a_957_ = v___y_988_;
v_a_958_ = v___y_990_;
goto _start;
}
v___jp_1001_:
{
lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; 
v___x_1008_ = lean_box(0);
v___x_1009_ = lean_unsigned_to_nat(1u);
v___x_1010_ = lean_array_get(v___x_1008_, v_args_1002_, v___x_1009_);
lean_dec_ref(v_args_1002_);
if (lean_obj_tag(v___x_1010_) == 1)
{
lean_object* v_fvarId_1011_; lean_object* v___x_1012_; lean_object* v_varMap_1013_; lean_object* v_borrowedParams_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; uint8_t v___x_1020_; 
v_fvarId_1011_ = lean_ctor_get(v___x_1010_, 0);
lean_inc(v_fvarId_1011_);
lean_dec_ref(v___x_1010_);
v___x_1012_ = lean_st_ref_take(v___y_1003_);
v_varMap_1013_ = lean_ctor_get(v___x_1012_, 0);
lean_inc_ref(v_varMap_1013_);
v_borrowedParams_1014_ = lean_ctor_get(v___x_1012_, 1);
lean_inc_ref(v_borrowedParams_1014_);
lean_dec(v___x_1012_);
v___x_1015_ = l_Lean_instEmptyCollectionFVarIdHashSet;
v___x_1016_ = lean_mk_empty_array_with_capacity(v___x_1009_);
v___x_1017_ = lean_array_push(v___x_1016_, v_fvarId_1011_);
v___x_1018_ = lean_unsigned_to_nat(0u);
v___x_1019_ = lean_array_get_size(v___x_1017_);
v___x_1020_ = lean_nat_dec_lt(v___x_1018_, v___x_1019_);
if (v___x_1020_ == 0)
{
v___y_984_ = v___y_1004_;
v_borrowedParams_985_ = v_borrowedParams_1014_;
v___y_986_ = v___x_1017_;
v___y_987_ = v___y_1003_;
v___y_988_ = v___y_1006_;
v___y_989_ = v___y_1005_;
v___y_990_ = v___y_1007_;
v___y_991_ = v___x_1015_;
v___y_992_ = v_fvarId_999_;
v___y_993_ = v_varMap_1013_;
goto v___jp_983_;
}
else
{
uint8_t v___x_1021_; 
v___x_1021_ = lean_nat_dec_le(v___x_1019_, v___x_1019_);
if (v___x_1021_ == 0)
{
if (v___x_1020_ == 0)
{
v___y_984_ = v___y_1004_;
v_borrowedParams_985_ = v_borrowedParams_1014_;
v___y_986_ = v___x_1017_;
v___y_987_ = v___y_1003_;
v___y_988_ = v___y_1006_;
v___y_989_ = v___y_1005_;
v___y_990_ = v___y_1007_;
v___y_991_ = v___x_1015_;
v___y_992_ = v_fvarId_999_;
v___y_993_ = v_varMap_1013_;
goto v___jp_983_;
}
else
{
size_t v___x_1022_; size_t v___x_1023_; lean_object* v___x_1024_; 
v___x_1022_ = ((size_t)0ULL);
v___x_1023_ = lean_usize_of_nat(v___x_1019_);
lean_inc(v_fvarId_999_);
v___x_1024_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__4(v_fvarId_999_, v___x_1017_, v___x_1022_, v___x_1023_, v_varMap_1013_);
v___y_984_ = v___y_1004_;
v_borrowedParams_985_ = v_borrowedParams_1014_;
v___y_986_ = v___x_1017_;
v___y_987_ = v___y_1003_;
v___y_988_ = v___y_1006_;
v___y_989_ = v___y_1005_;
v___y_990_ = v___y_1007_;
v___y_991_ = v___x_1015_;
v___y_992_ = v_fvarId_999_;
v___y_993_ = v___x_1024_;
goto v___jp_983_;
}
}
else
{
size_t v___x_1025_; size_t v___x_1026_; lean_object* v___x_1027_; 
v___x_1025_ = ((size_t)0ULL);
v___x_1026_ = lean_usize_of_nat(v___x_1019_);
lean_inc(v_fvarId_999_);
v___x_1027_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__4(v_fvarId_999_, v___x_1017_, v___x_1025_, v___x_1026_, v_varMap_1013_);
v___y_984_ = v___y_1004_;
v_borrowedParams_985_ = v_borrowedParams_1014_;
v___y_986_ = v___x_1017_;
v___y_987_ = v___y_1003_;
v___y_988_ = v___y_1006_;
v___y_989_ = v___y_1005_;
v___y_990_ = v___y_1007_;
v___y_991_ = v___x_1015_;
v___y_992_ = v_fvarId_999_;
v___y_993_ = v___x_1027_;
goto v___jp_983_;
}
}
}
else
{
lean_dec(v___x_1010_);
lean_dec(v_fvarId_999_);
v_code_953_ = v_k_961_;
v_a_954_ = v___y_1003_;
v_a_955_ = v___y_1004_;
v_a_956_ = v___y_1005_;
v_a_957_ = v___y_1006_;
v_a_958_ = v___y_1007_;
goto _start;
}
}
v___jp_1029_:
{
lean_object* v___x_1036_; lean_object* v_varMap_1037_; lean_object* v_borrowedParams_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; uint8_t v___x_1042_; 
v___x_1036_ = lean_st_ref_take(v___y_1031_);
v_varMap_1037_ = lean_ctor_get(v___x_1036_, 0);
lean_inc_ref(v_varMap_1037_);
v_borrowedParams_1038_ = lean_ctor_get(v___x_1036_, 1);
lean_inc_ref(v_borrowedParams_1038_);
lean_dec(v___x_1036_);
v___x_1039_ = l_Lean_instEmptyCollectionFVarIdHashSet;
v___x_1040_ = lean_unsigned_to_nat(0u);
v___x_1041_ = lean_array_get_size(v_arr_1030_);
v___x_1042_ = lean_nat_dec_lt(v___x_1040_, v___x_1041_);
if (v___x_1042_ == 0)
{
v_borrowedParams_966_ = v_borrowedParams_1038_;
v___y_967_ = v___x_1039_;
v___y_968_ = v_arr_1030_;
v___y_969_ = v___y_1033_;
v___y_970_ = v_fvarId_999_;
v___y_971_ = v___y_1032_;
v___y_972_ = v___y_1034_;
v___y_973_ = v___y_1031_;
v___y_974_ = v___y_1035_;
v___y_975_ = v_varMap_1037_;
goto v___jp_965_;
}
else
{
uint8_t v___x_1043_; 
v___x_1043_ = lean_nat_dec_le(v___x_1041_, v___x_1041_);
if (v___x_1043_ == 0)
{
if (v___x_1042_ == 0)
{
v_borrowedParams_966_ = v_borrowedParams_1038_;
v___y_967_ = v___x_1039_;
v___y_968_ = v_arr_1030_;
v___y_969_ = v___y_1033_;
v___y_970_ = v_fvarId_999_;
v___y_971_ = v___y_1032_;
v___y_972_ = v___y_1034_;
v___y_973_ = v___y_1031_;
v___y_974_ = v___y_1035_;
v___y_975_ = v_varMap_1037_;
goto v___jp_965_;
}
else
{
size_t v___x_1044_; size_t v___x_1045_; lean_object* v___x_1046_; 
v___x_1044_ = ((size_t)0ULL);
v___x_1045_ = lean_usize_of_nat(v___x_1041_);
lean_inc(v_fvarId_999_);
v___x_1046_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__4(v_fvarId_999_, v_arr_1030_, v___x_1044_, v___x_1045_, v_varMap_1037_);
v_borrowedParams_966_ = v_borrowedParams_1038_;
v___y_967_ = v___x_1039_;
v___y_968_ = v_arr_1030_;
v___y_969_ = v___y_1033_;
v___y_970_ = v_fvarId_999_;
v___y_971_ = v___y_1032_;
v___y_972_ = v___y_1034_;
v___y_973_ = v___y_1031_;
v___y_974_ = v___y_1035_;
v___y_975_ = v___x_1046_;
goto v___jp_965_;
}
}
else
{
size_t v___x_1047_; size_t v___x_1048_; lean_object* v___x_1049_; 
v___x_1047_ = ((size_t)0ULL);
v___x_1048_ = lean_usize_of_nat(v___x_1041_);
lean_inc(v_fvarId_999_);
v___x_1049_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__4(v_fvarId_999_, v_arr_1030_, v___x_1047_, v___x_1048_, v_varMap_1037_);
v_borrowedParams_966_ = v_borrowedParams_1038_;
v___y_967_ = v___x_1039_;
v___y_968_ = v_arr_1030_;
v___y_969_ = v___y_1033_;
v___y_970_ = v_fvarId_999_;
v___y_971_ = v___y_1032_;
v___y_972_ = v___y_1034_;
v___y_973_ = v___y_1031_;
v___y_974_ = v___y_1035_;
v___y_975_ = v___x_1049_;
goto v___jp_965_;
}
}
}
}
}
case 2:
{
lean_object* v_decl_1130_; lean_object* v_k_1131_; lean_object* v_params_1132_; lean_object* v_value_1133_; lean_object* v___y_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; uint8_t v___x_1141_; 
v_decl_1130_ = lean_ctor_get(v_code_953_, 0);
lean_inc_ref(v_decl_1130_);
v_k_1131_ = lean_ctor_get(v_code_953_, 1);
lean_inc_ref(v_k_1131_);
lean_dec_ref(v_code_953_);
v_params_1132_ = lean_ctor_get(v_decl_1130_, 2);
lean_inc_ref(v_params_1132_);
v_value_1133_ = lean_ctor_get(v_decl_1130_, 4);
lean_inc_ref(v_value_1133_);
lean_dec_ref(v_decl_1130_);
v___x_1139_ = lean_unsigned_to_nat(0u);
v___x_1140_ = lean_array_get_size(v_params_1132_);
v___x_1141_ = lean_nat_dec_lt(v___x_1139_, v___x_1140_);
if (v___x_1141_ == 0)
{
lean_dec_ref(v_params_1132_);
goto v___jp_1134_;
}
else
{
lean_object* v___x_1142_; uint8_t v___x_1143_; 
v___x_1142_ = lean_box(0);
v___x_1143_ = lean_nat_dec_le(v___x_1140_, v___x_1140_);
if (v___x_1143_ == 0)
{
if (v___x_1141_ == 0)
{
lean_dec_ref(v_params_1132_);
goto v___jp_1134_;
}
else
{
size_t v___x_1144_; size_t v___x_1145_; lean_object* v___x_1146_; 
v___x_1144_ = ((size_t)0ULL);
v___x_1145_ = lean_usize_of_nat(v___x_1140_);
v___x_1146_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__5___redArg(v_params_1132_, v___x_1144_, v___x_1145_, v___x_1142_, v_a_954_);
lean_dec_ref(v_params_1132_);
v___y_1138_ = v___x_1146_;
goto v___jp_1137_;
}
}
else
{
size_t v___x_1147_; size_t v___x_1148_; lean_object* v___x_1149_; 
v___x_1147_ = ((size_t)0ULL);
v___x_1148_ = lean_usize_of_nat(v___x_1140_);
v___x_1149_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__5___redArg(v_params_1132_, v___x_1147_, v___x_1148_, v___x_1142_, v_a_954_);
lean_dec_ref(v_params_1132_);
v___y_1138_ = v___x_1149_;
goto v___jp_1137_;
}
}
v___jp_1134_:
{
lean_object* v___x_1135_; 
v___x_1135_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode(v_value_1133_, v_a_954_, v_a_955_, v_a_956_, v_a_957_, v_a_958_);
if (lean_obj_tag(v___x_1135_) == 0)
{
lean_dec_ref(v___x_1135_);
v_code_953_ = v_k_1131_;
goto _start;
}
else
{
lean_dec_ref(v_k_1131_);
return v___x_1135_;
}
}
v___jp_1137_:
{
if (lean_obj_tag(v___y_1138_) == 0)
{
lean_dec_ref(v___y_1138_);
goto v___jp_1134_;
}
else
{
lean_dec_ref(v_value_1133_);
lean_dec_ref(v_k_1131_);
return v___y_1138_;
}
}
}
case 3:
{
lean_object* v___x_1150_; lean_object* v___x_1151_; 
lean_dec_ref(v_code_953_);
v___x_1150_ = lean_box(0);
v___x_1151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1151_, 0, v___x_1150_);
return v___x_1151_;
}
case 4:
{
lean_object* v_cases_1152_; lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1174_; 
v_cases_1152_ = lean_ctor_get(v_code_953_, 0);
v_isSharedCheck_1174_ = !lean_is_exclusive(v_code_953_);
if (v_isSharedCheck_1174_ == 0)
{
v___x_1154_ = v_code_953_;
v_isShared_1155_ = v_isSharedCheck_1174_;
goto v_resetjp_1153_;
}
else
{
lean_inc(v_cases_1152_);
lean_dec(v_code_953_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1174_;
goto v_resetjp_1153_;
}
v_resetjp_1153_:
{
lean_object* v_alts_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; uint8_t v___x_1160_; 
v_alts_1156_ = lean_ctor_get(v_cases_1152_, 3);
lean_inc_ref(v_alts_1156_);
lean_dec_ref(v_cases_1152_);
v___x_1157_ = lean_unsigned_to_nat(0u);
v___x_1158_ = lean_array_get_size(v_alts_1156_);
v___x_1159_ = lean_box(0);
v___x_1160_ = lean_nat_dec_lt(v___x_1157_, v___x_1158_);
if (v___x_1160_ == 0)
{
lean_object* v___x_1162_; 
lean_dec_ref(v_alts_1156_);
if (v_isShared_1155_ == 0)
{
lean_ctor_set_tag(v___x_1154_, 0);
lean_ctor_set(v___x_1154_, 0, v___x_1159_);
v___x_1162_ = v___x_1154_;
goto v_reusejp_1161_;
}
else
{
lean_object* v_reuseFailAlloc_1163_; 
v_reuseFailAlloc_1163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1163_, 0, v___x_1159_);
v___x_1162_ = v_reuseFailAlloc_1163_;
goto v_reusejp_1161_;
}
v_reusejp_1161_:
{
return v___x_1162_;
}
}
else
{
uint8_t v___x_1164_; 
v___x_1164_ = lean_nat_dec_le(v___x_1158_, v___x_1158_);
if (v___x_1164_ == 0)
{
if (v___x_1160_ == 0)
{
lean_object* v___x_1166_; 
lean_dec_ref(v_alts_1156_);
if (v_isShared_1155_ == 0)
{
lean_ctor_set_tag(v___x_1154_, 0);
lean_ctor_set(v___x_1154_, 0, v___x_1159_);
v___x_1166_ = v___x_1154_;
goto v_reusejp_1165_;
}
else
{
lean_object* v_reuseFailAlloc_1167_; 
v_reuseFailAlloc_1167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1167_, 0, v___x_1159_);
v___x_1166_ = v_reuseFailAlloc_1167_;
goto v_reusejp_1165_;
}
v_reusejp_1165_:
{
return v___x_1166_;
}
}
else
{
size_t v___x_1168_; size_t v___x_1169_; lean_object* v___x_1170_; 
lean_del_object(v___x_1154_);
v___x_1168_ = ((size_t)0ULL);
v___x_1169_ = lean_usize_of_nat(v___x_1158_);
v___x_1170_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__6(v_alts_1156_, v___x_1168_, v___x_1169_, v___x_1159_, v_a_954_, v_a_955_, v_a_956_, v_a_957_, v_a_958_);
lean_dec_ref(v_alts_1156_);
return v___x_1170_;
}
}
else
{
size_t v___x_1171_; size_t v___x_1172_; lean_object* v___x_1173_; 
lean_del_object(v___x_1154_);
v___x_1171_ = ((size_t)0ULL);
v___x_1172_ = lean_usize_of_nat(v___x_1158_);
v___x_1173_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__6(v_alts_1156_, v___x_1171_, v___x_1172_, v___x_1159_, v_a_954_, v_a_955_, v_a_956_, v_a_957_, v_a_958_);
lean_dec_ref(v_alts_1156_);
return v___x_1173_;
}
}
}
}
case 5:
{
lean_object* v___x_1176_; uint8_t v_isShared_1177_; uint8_t v_isSharedCheck_1182_; 
v_isSharedCheck_1182_ = !lean_is_exclusive(v_code_953_);
if (v_isSharedCheck_1182_ == 0)
{
lean_object* v_unused_1183_; 
v_unused_1183_ = lean_ctor_get(v_code_953_, 0);
lean_dec(v_unused_1183_);
v___x_1176_ = v_code_953_;
v_isShared_1177_ = v_isSharedCheck_1182_;
goto v_resetjp_1175_;
}
else
{
lean_dec(v_code_953_);
v___x_1176_ = lean_box(0);
v_isShared_1177_ = v_isSharedCheck_1182_;
goto v_resetjp_1175_;
}
v_resetjp_1175_:
{
lean_object* v___x_1178_; lean_object* v___x_1180_; 
v___x_1178_ = lean_box(0);
if (v_isShared_1177_ == 0)
{
lean_ctor_set_tag(v___x_1176_, 0);
lean_ctor_set(v___x_1176_, 0, v___x_1178_);
v___x_1180_ = v___x_1176_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v___x_1178_);
v___x_1180_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1179_;
}
v_reusejp_1179_:
{
return v___x_1180_;
}
}
}
case 6:
{
lean_object* v___x_1185_; uint8_t v_isShared_1186_; uint8_t v_isSharedCheck_1191_; 
v_isSharedCheck_1191_ = !lean_is_exclusive(v_code_953_);
if (v_isSharedCheck_1191_ == 0)
{
lean_object* v_unused_1192_; 
v_unused_1192_ = lean_ctor_get(v_code_953_, 0);
lean_dec(v_unused_1192_);
v___x_1185_ = v_code_953_;
v_isShared_1186_ = v_isSharedCheck_1191_;
goto v_resetjp_1184_;
}
else
{
lean_dec(v_code_953_);
v___x_1185_ = lean_box(0);
v_isShared_1186_ = v_isSharedCheck_1191_;
goto v_resetjp_1184_;
}
v_resetjp_1184_:
{
lean_object* v___x_1187_; lean_object* v___x_1189_; 
v___x_1187_ = lean_box(0);
if (v_isShared_1186_ == 0)
{
lean_ctor_set_tag(v___x_1185_, 0);
lean_ctor_set(v___x_1185_, 0, v___x_1187_);
v___x_1189_ = v___x_1185_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v___x_1187_);
v___x_1189_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
return v___x_1189_;
}
}
}
case 8:
{
lean_object* v_k_1193_; 
v_k_1193_ = lean_ctor_get(v_code_953_, 3);
lean_inc_ref(v_k_1193_);
lean_dec_ref(v_code_953_);
v_code_953_ = v_k_1193_;
goto _start;
}
case 9:
{
lean_object* v_k_1195_; 
v_k_1195_ = lean_ctor_get(v_code_953_, 5);
lean_inc_ref(v_k_1195_);
lean_dec_ref(v_code_953_);
v_code_953_ = v_k_1195_;
goto _start;
}
default: 
{
lean_object* v___x_1197_; lean_object* v___x_1198_; 
lean_dec_ref(v_code_953_);
v___x_1197_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode___closed__7, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode___closed__7_once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode___closed__7);
v___x_1198_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__7(v___x_1197_, v_a_954_, v_a_955_, v_a_956_, v_a_957_, v_a_958_);
return v___x_1198_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode___boxed(lean_object* v_code_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_, lean_object* v_a_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_){
_start:
{
lean_object* v_res_1206_; 
v_res_1206_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode(v_code_1199_, v_a_1200_, v_a_1201_, v_a_1202_, v_a_1203_, v_a_1204_);
lean_dec(v_a_1204_);
lean_dec_ref(v_a_1203_);
lean_dec(v_a_1202_);
lean_dec_ref(v_a_1201_);
lean_dec(v_a_1200_);
return v_res_1206_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__6(lean_object* v_as_1207_, size_t v_i_1208_, size_t v_stop_1209_, lean_object* v_b_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_){
_start:
{
uint8_t v___x_1217_; 
v___x_1217_ = lean_usize_dec_eq(v_i_1208_, v_stop_1209_);
if (v___x_1217_ == 0)
{
lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; 
v___x_1218_ = lean_array_uget_borrowed(v_as_1207_, v_i_1208_);
v___x_1219_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode___boxed), 7, 0);
lean_inc(v___x_1218_);
v___x_1220_ = l_Lean_Compiler_LCNF_Alt_forCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__2___redArg(v___x_1218_, v___x_1219_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_, v___y_1215_);
if (lean_obj_tag(v___x_1220_) == 0)
{
lean_object* v_a_1221_; size_t v___x_1222_; size_t v___x_1223_; 
v_a_1221_ = lean_ctor_get(v___x_1220_, 0);
lean_inc(v_a_1221_);
lean_dec_ref(v___x_1220_);
v___x_1222_ = ((size_t)1ULL);
v___x_1223_ = lean_usize_add(v_i_1208_, v___x_1222_);
v_i_1208_ = v___x_1223_;
v_b_1210_ = v_a_1221_;
goto _start;
}
else
{
return v___x_1220_;
}
}
else
{
lean_object* v___x_1225_; 
v___x_1225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1225_, 0, v_b_1210_);
return v___x_1225_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__6___boxed(lean_object* v_as_1226_, lean_object* v_i_1227_, lean_object* v_stop_1228_, lean_object* v_b_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_){
_start:
{
size_t v_i_boxed_1236_; size_t v_stop_boxed_1237_; lean_object* v_res_1238_; 
v_i_boxed_1236_ = lean_unbox_usize(v_i_1227_);
lean_dec(v_i_1227_);
v_stop_boxed_1237_ = lean_unbox_usize(v_stop_1228_);
lean_dec(v_stop_1228_);
v_res_1238_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__6(v_as_1226_, v_i_boxed_1236_, v_stop_boxed_1237_, v_b_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_);
lean_dec(v___y_1234_);
lean_dec_ref(v___y_1233_);
lean_dec(v___y_1232_);
lean_dec_ref(v___y_1231_);
lean_dec(v___y_1230_);
lean_dec_ref(v_as_1226_);
return v_res_1238_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__0(lean_object* v_00_u03b2_1239_, lean_object* v_m_1240_, lean_object* v_a_1241_, lean_object* v_b_1242_){
_start:
{
lean_object* v___x_1243_; 
v___x_1243_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__0___redArg(v_m_1240_, v_a_1241_, v_b_1242_);
return v___x_1243_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__1(lean_object* v_00_u03b2_1244_, lean_object* v_m_1245_, lean_object* v_a_1246_, lean_object* v_b_1247_){
_start:
{
lean_object* v___x_1248_; 
v___x_1248_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__1___redArg(v_m_1245_, v_a_1246_, v_b_1247_);
return v___x_1248_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__5(lean_object* v_as_1249_, size_t v_i_1250_, size_t v_stop_1251_, lean_object* v_b_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_){
_start:
{
lean_object* v___x_1259_; 
v___x_1259_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__5___redArg(v_as_1249_, v_i_1250_, v_stop_1251_, v_b_1252_, v___y_1253_);
return v___x_1259_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__5___boxed(lean_object* v_as_1260_, lean_object* v_i_1261_, lean_object* v_stop_1262_, lean_object* v_b_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_){
_start:
{
size_t v_i_boxed_1270_; size_t v_stop_boxed_1271_; lean_object* v_res_1272_; 
v_i_boxed_1270_ = lean_unbox_usize(v_i_1261_);
lean_dec(v_i_1261_);
v_stop_boxed_1271_ = lean_unbox_usize(v_stop_1262_);
lean_dec(v_stop_1262_);
v_res_1272_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__5(v_as_1260_, v_i_boxed_1270_, v_stop_boxed_1271_, v_b_1263_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_);
lean_dec(v___y_1268_);
lean_dec_ref(v___y_1267_);
lean_dec(v___y_1266_);
lean_dec_ref(v___y_1265_);
lean_dec(v___y_1264_);
lean_dec_ref(v_as_1260_);
return v_res_1272_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__0_spec__0(lean_object* v_00_u03b2_1273_, lean_object* v_data_1274_){
_start:
{
lean_object* v___x_1275_; 
v___x_1275_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__0_spec__0___redArg(v_data_1274_);
return v___x_1275_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__0_spec__1(lean_object* v_00_u03b2_1276_, lean_object* v_a_1277_, lean_object* v_b_1278_, lean_object* v_x_1279_){
_start:
{
lean_object* v___x_1280_; 
v___x_1280_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__0_spec__1___redArg(v_a_1277_, v_b_1278_, v_x_1279_);
return v___x_1280_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_1281_, lean_object* v_i_1282_, lean_object* v_source_1283_, lean_object* v_target_1284_){
_start:
{
lean_object* v___x_1285_; 
v___x_1285_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__0_spec__0_spec__3___redArg(v_i_1282_, v_source_1283_, v_target_1284_);
return v___x_1285_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__0_spec__0_spec__3_spec__9(lean_object* v_00_u03b2_1286_, lean_object* v_x_1287_, lean_object* v_x_1288_){
_start:
{
lean_object* v___x_1289_; 
v___x_1289_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__0_spec__0_spec__3_spec__9___redArg(v_x_1287_, v_x_1288_);
return v___x_1289_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collect_go(lean_object* v_ps_1290_, lean_object* v_code_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_){
_start:
{
lean_object* v___y_1299_; lean_object* v___x_1301_; lean_object* v___x_1302_; uint8_t v___x_1303_; 
v___x_1301_ = lean_unsigned_to_nat(0u);
v___x_1302_ = lean_array_get_size(v_ps_1290_);
v___x_1303_ = lean_nat_dec_lt(v___x_1301_, v___x_1302_);
if (v___x_1303_ == 0)
{
lean_object* v___x_1304_; 
v___x_1304_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode(v_code_1291_, v_a_1292_, v_a_1293_, v_a_1294_, v_a_1295_, v_a_1296_);
return v___x_1304_;
}
else
{
lean_object* v___x_1305_; uint8_t v___x_1306_; 
v___x_1305_ = lean_box(0);
v___x_1306_ = lean_nat_dec_le(v___x_1302_, v___x_1302_);
if (v___x_1306_ == 0)
{
if (v___x_1303_ == 0)
{
lean_object* v___x_1307_; 
v___x_1307_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode(v_code_1291_, v_a_1292_, v_a_1293_, v_a_1294_, v_a_1295_, v_a_1296_);
return v___x_1307_;
}
else
{
size_t v___x_1308_; size_t v___x_1309_; lean_object* v___x_1310_; 
v___x_1308_ = ((size_t)0ULL);
v___x_1309_ = lean_usize_of_nat(v___x_1302_);
v___x_1310_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__5___redArg(v_ps_1290_, v___x_1308_, v___x_1309_, v___x_1305_, v_a_1292_);
v___y_1299_ = v___x_1310_;
goto v___jp_1298_;
}
}
else
{
size_t v___x_1311_; size_t v___x_1312_; lean_object* v___x_1313_; 
v___x_1311_ = ((size_t)0ULL);
v___x_1312_ = lean_usize_of_nat(v___x_1302_);
v___x_1313_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__5___redArg(v_ps_1290_, v___x_1311_, v___x_1312_, v___x_1305_, v_a_1292_);
v___y_1299_ = v___x_1313_;
goto v___jp_1298_;
}
}
v___jp_1298_:
{
if (lean_obj_tag(v___y_1299_) == 0)
{
lean_object* v___x_1300_; 
lean_dec_ref(v___y_1299_);
v___x_1300_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode(v_code_1291_, v_a_1292_, v_a_1293_, v_a_1294_, v_a_1295_, v_a_1296_);
return v___x_1300_;
}
else
{
lean_dec_ref(v_code_1291_);
return v___y_1299_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collect_go___boxed(lean_object* v_ps_1314_, lean_object* v_code_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_, lean_object* v_a_1318_, lean_object* v_a_1319_, lean_object* v_a_1320_, lean_object* v_a_1321_){
_start:
{
lean_object* v_res_1322_; 
v_res_1322_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collect_go(v_ps_1314_, v_code_1315_, v_a_1316_, v_a_1317_, v_a_1318_, v_a_1319_, v_a_1320_);
lean_dec(v_a_1320_);
lean_dec_ref(v_a_1319_);
lean_dec(v_a_1318_);
lean_dec_ref(v_a_1317_);
lean_dec(v_a_1316_);
lean_dec_ref(v_ps_1314_);
return v_res_1322_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collect___closed__0(void){
_start:
{
lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; 
v___x_1323_ = lean_box(0);
v___x_1324_ = lean_unsigned_to_nat(16u);
v___x_1325_ = lean_mk_array(v___x_1324_, v___x_1323_);
return v___x_1325_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collect___closed__1(void){
_start:
{
lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; 
v___x_1326_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collect___closed__0, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collect___closed__0_once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collect___closed__0);
v___x_1327_ = lean_unsigned_to_nat(0u);
v___x_1328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1328_, 0, v___x_1327_);
lean_ctor_set(v___x_1328_, 1, v___x_1326_);
return v___x_1328_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collect___closed__2(void){
_start:
{
lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; 
v___x_1329_ = l_Lean_instEmptyCollectionFVarIdHashSet;
v___x_1330_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collect___closed__1, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collect___closed__1_once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collect___closed__1);
v___x_1331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1331_, 0, v___x_1330_);
lean_ctor_set(v___x_1331_, 1, v___x_1329_);
return v___x_1331_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collect(lean_object* v_ps_1332_, lean_object* v_code_1333_, lean_object* v_a_1334_, lean_object* v_a_1335_, lean_object* v_a_1336_, lean_object* v_a_1337_){
_start:
{
lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; 
v___x_1339_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collect___closed__2, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collect___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collect___closed__2);
v___x_1340_ = lean_st_mk_ref(v___x_1339_);
v___x_1341_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collect_go(v_ps_1332_, v_code_1333_, v___x_1340_, v_a_1334_, v_a_1335_, v_a_1336_, v_a_1337_);
if (lean_obj_tag(v___x_1341_) == 0)
{
lean_object* v___x_1343_; uint8_t v_isShared_1344_; uint8_t v_isSharedCheck_1358_; 
v_isSharedCheck_1358_ = !lean_is_exclusive(v___x_1341_);
if (v_isSharedCheck_1358_ == 0)
{
lean_object* v_unused_1359_; 
v_unused_1359_ = lean_ctor_get(v___x_1341_, 0);
lean_dec(v_unused_1359_);
v___x_1343_ = v___x_1341_;
v_isShared_1344_ = v_isSharedCheck_1358_;
goto v_resetjp_1342_;
}
else
{
lean_dec(v___x_1341_);
v___x_1343_ = lean_box(0);
v_isShared_1344_ = v_isSharedCheck_1358_;
goto v_resetjp_1342_;
}
v_resetjp_1342_:
{
lean_object* v___x_1345_; lean_object* v_varMap_1346_; lean_object* v_borrowedParams_1347_; lean_object* v___x_1349_; uint8_t v_isShared_1350_; uint8_t v_isSharedCheck_1357_; 
v___x_1345_ = lean_st_ref_get(v___x_1340_);
lean_dec(v___x_1340_);
v_varMap_1346_ = lean_ctor_get(v___x_1345_, 0);
v_borrowedParams_1347_ = lean_ctor_get(v___x_1345_, 1);
v_isSharedCheck_1357_ = !lean_is_exclusive(v___x_1345_);
if (v_isSharedCheck_1357_ == 0)
{
v___x_1349_ = v___x_1345_;
v_isShared_1350_ = v_isSharedCheck_1357_;
goto v_resetjp_1348_;
}
else
{
lean_inc(v_borrowedParams_1347_);
lean_inc(v_varMap_1346_);
lean_dec(v___x_1345_);
v___x_1349_ = lean_box(0);
v_isShared_1350_ = v_isSharedCheck_1357_;
goto v_resetjp_1348_;
}
v_resetjp_1348_:
{
lean_object* v___x_1352_; 
if (v_isShared_1350_ == 0)
{
v___x_1352_ = v___x_1349_;
goto v_reusejp_1351_;
}
else
{
lean_object* v_reuseFailAlloc_1356_; 
v_reuseFailAlloc_1356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v_varMap_1346_);
lean_ctor_set(v_reuseFailAlloc_1356_, 1, v_borrowedParams_1347_);
v___x_1352_ = v_reuseFailAlloc_1356_;
goto v_reusejp_1351_;
}
v_reusejp_1351_:
{
lean_object* v___x_1354_; 
if (v_isShared_1344_ == 0)
{
lean_ctor_set(v___x_1343_, 0, v___x_1352_);
v___x_1354_ = v___x_1343_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1355_; 
v_reuseFailAlloc_1355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1355_, 0, v___x_1352_);
v___x_1354_ = v_reuseFailAlloc_1355_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
return v___x_1354_;
}
}
}
}
}
else
{
lean_object* v_a_1360_; lean_object* v___x_1362_; uint8_t v_isShared_1363_; uint8_t v_isSharedCheck_1367_; 
lean_dec(v___x_1340_);
v_a_1360_ = lean_ctor_get(v___x_1341_, 0);
v_isSharedCheck_1367_ = !lean_is_exclusive(v___x_1341_);
if (v_isSharedCheck_1367_ == 0)
{
v___x_1362_ = v___x_1341_;
v_isShared_1363_ = v_isSharedCheck_1367_;
goto v_resetjp_1361_;
}
else
{
lean_inc(v_a_1360_);
lean_dec(v___x_1341_);
v___x_1362_ = lean_box(0);
v_isShared_1363_ = v_isSharedCheck_1367_;
goto v_resetjp_1361_;
}
v_resetjp_1361_:
{
lean_object* v___x_1365_; 
if (v_isShared_1363_ == 0)
{
v___x_1365_ = v___x_1362_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v_a_1360_);
v___x_1365_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
return v___x_1365_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collect___boxed(lean_object* v_ps_1368_, lean_object* v_code_1369_, lean_object* v_a_1370_, lean_object* v_a_1371_, lean_object* v_a_1372_, lean_object* v_a_1373_, lean_object* v_a_1374_){
_start:
{
lean_object* v_res_1375_; 
v_res_1375_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collect(v_ps_1368_, v_code_1369_, v_a_1370_, v_a_1371_, v_a_1372_, v_a_1373_);
lean_dec(v_a_1373_);
lean_dec_ref(v_a_1372_);
lean_dec(v_a_1371_);
lean_dec_ref(v_a_1370_);
lean_dec_ref(v_ps_1368_);
return v_res_1375_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__0(void){
_start:
{
lean_object* v___x_1381_; lean_object* v___x_1382_; 
v___x_1381_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collect___closed__1, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collect___closed__1_once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collect___closed__1);
v___x_1382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1382_, 0, v___x_1381_);
lean_ctor_set(v___x_1382_, 1, v___x_1381_);
return v___x_1382_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_instInhabitedLiveVars_default(void){
_start:
{
lean_object* v___x_1383_; 
v___x_1383_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__0, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__0_once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__0);
return v___x_1383_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_instInhabitedLiveVars(void){
_start:
{
lean_object* v___x_1384_; 
v___x_1384_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_instInhabitedLiveVars_default;
return v___x_1384_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___lam__0(lean_object* v___x_1385_, lean_object* v___x_1386_, lean_object* v_a_1387_, lean_object* v_b_1388_, lean_object* v_acc_1389_){
_start:
{
lean_object* v_r_1390_; lean_object* v___x_1391_; 
v_r_1390_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_1385_, v___x_1386_, v_acc_1389_, v_a_1387_, v_b_1388_);
v___x_1391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1391_, 0, v_r_1390_);
return v___x_1391_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___lam__1(lean_object* v___x_1392_, lean_object* v___f_1393_, lean_object* v_a_1394_, lean_object* v_x_1395_, lean_object* v___y_1396_){
_start:
{
lean_object* v___x_1397_; 
v___x_1397_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v___x_1392_, v___f_1393_, v_a_1394_, v___y_1396_);
return v___x_1397_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union(lean_object* v_liveVars1_1406_, lean_object* v_liveVars2_1407_){
_start:
{
lean_object* v_vars_1408_; lean_object* v_vars_1409_; lean_object* v_borrows_1410_; lean_object* v_borrows_1411_; lean_object* v___x_1413_; uint8_t v_isShared_1414_; uint8_t v_isSharedCheck_1447_; 
v_vars_1408_ = lean_ctor_get(v_liveVars1_1406_, 0);
lean_inc_ref(v_vars_1408_);
v_vars_1409_ = lean_ctor_get(v_liveVars2_1407_, 0);
lean_inc_ref(v_vars_1409_);
v_borrows_1410_ = lean_ctor_get(v_liveVars1_1406_, 1);
lean_inc_ref(v_borrows_1410_);
lean_dec_ref(v_liveVars1_1406_);
v_borrows_1411_ = lean_ctor_get(v_liveVars2_1407_, 1);
v_isSharedCheck_1447_ = !lean_is_exclusive(v_liveVars2_1407_);
if (v_isSharedCheck_1447_ == 0)
{
lean_object* v_unused_1448_; 
v_unused_1448_ = lean_ctor_get(v_liveVars2_1407_, 0);
lean_dec(v_unused_1448_);
v___x_1413_ = v_liveVars2_1407_;
v_isShared_1414_ = v_isSharedCheck_1447_;
goto v_resetjp_1412_;
}
else
{
lean_inc(v_borrows_1411_);
lean_dec(v_liveVars2_1407_);
v___x_1413_ = lean_box(0);
v_isShared_1414_ = v_isSharedCheck_1447_;
goto v_resetjp_1412_;
}
v_resetjp_1412_:
{
lean_object* v_size_1415_; lean_object* v_buckets_1416_; lean_object* v_size_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___y_1421_; uint8_t v___x_1439_; 
v_size_1415_ = lean_ctor_get(v_vars_1408_, 0);
v_buckets_1416_ = lean_ctor_get(v_vars_1408_, 1);
v_size_1417_ = lean_ctor_get(v_vars_1409_, 0);
v___x_1418_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_visitParam___redArg___closed__0));
v___x_1419_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_visitParam___redArg___closed__1));
v___x_1439_ = lean_nat_dec_le(v_size_1415_, v_size_1417_);
if (v___x_1439_ == 0)
{
lean_object* v___f_1440_; lean_object* v___x_1441_; 
v___f_1440_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__1));
v___x_1441_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_1440_, v___x_1418_, v___x_1419_, v_vars_1408_, v_vars_1409_);
v___y_1421_ = v___x_1441_;
goto v___jp_1420_;
}
else
{
lean_object* v___x_1442_; lean_object* v___f_1443_; size_t v_sz_1444_; size_t v___x_1445_; lean_object* v___x_1446_; 
lean_inc_ref(v_buckets_1416_);
lean_dec_ref(v_vars_1408_);
v___x_1442_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_addDerivedValue___redArg___closed__9));
v___f_1443_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__2));
v_sz_1444_ = lean_array_size(v_buckets_1416_);
v___x_1445_ = ((size_t)0ULL);
v___x_1446_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1442_, v_buckets_1416_, v___f_1443_, v_sz_1444_, v___x_1445_, v_vars_1409_);
v___y_1421_ = v___x_1446_;
goto v___jp_1420_;
}
v___jp_1420_:
{
lean_object* v_size_1422_; lean_object* v_buckets_1423_; lean_object* v_size_1424_; uint8_t v___x_1425_; 
v_size_1422_ = lean_ctor_get(v_borrows_1410_, 0);
v_buckets_1423_ = lean_ctor_get(v_borrows_1410_, 1);
v_size_1424_ = lean_ctor_get(v_borrows_1411_, 0);
v___x_1425_ = lean_nat_dec_le(v_size_1422_, v_size_1424_);
if (v___x_1425_ == 0)
{
lean_object* v___f_1426_; lean_object* v___x_1427_; lean_object* v___x_1429_; 
v___f_1426_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__1));
v___x_1427_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_1426_, v___x_1418_, v___x_1419_, v_borrows_1410_, v_borrows_1411_);
if (v_isShared_1414_ == 0)
{
lean_ctor_set(v___x_1413_, 1, v___x_1427_);
lean_ctor_set(v___x_1413_, 0, v___y_1421_);
v___x_1429_ = v___x_1413_;
goto v_reusejp_1428_;
}
else
{
lean_object* v_reuseFailAlloc_1430_; 
v_reuseFailAlloc_1430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1430_, 0, v___y_1421_);
lean_ctor_set(v_reuseFailAlloc_1430_, 1, v___x_1427_);
v___x_1429_ = v_reuseFailAlloc_1430_;
goto v_reusejp_1428_;
}
v_reusejp_1428_:
{
return v___x_1429_;
}
}
else
{
lean_object* v___x_1431_; lean_object* v___f_1432_; size_t v_sz_1433_; size_t v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1437_; 
lean_inc_ref(v_buckets_1423_);
lean_dec_ref(v_borrows_1410_);
v___x_1431_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_addDerivedValue___redArg___closed__9));
v___f_1432_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__2));
v_sz_1433_ = lean_array_size(v_buckets_1423_);
v___x_1434_ = ((size_t)0ULL);
v___x_1435_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1431_, v_buckets_1423_, v___f_1432_, v_sz_1433_, v___x_1434_, v_borrows_1411_);
if (v_isShared_1414_ == 0)
{
lean_ctor_set(v___x_1413_, 1, v___x_1435_);
lean_ctor_set(v___x_1413_, 0, v___y_1421_);
v___x_1437_ = v___x_1413_;
goto v_reusejp_1436_;
}
else
{
lean_object* v_reuseFailAlloc_1438_; 
v_reuseFailAlloc_1438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1438_, 0, v___y_1421_);
lean_ctor_set(v_reuseFailAlloc_1438_, 1, v___x_1435_);
v___x_1437_ = v_reuseFailAlloc_1438_;
goto v_reusejp_1436_;
}
v_reusejp_1436_:
{
return v___x_1437_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_erase(lean_object* v_liveVars_1449_, lean_object* v_fvarId_1450_){
_start:
{
lean_object* v_vars_1451_; lean_object* v_borrows_1452_; lean_object* v___x_1454_; uint8_t v_isShared_1455_; uint8_t v_isSharedCheck_1463_; 
v_vars_1451_ = lean_ctor_get(v_liveVars_1449_, 0);
v_borrows_1452_ = lean_ctor_get(v_liveVars_1449_, 1);
v_isSharedCheck_1463_ = !lean_is_exclusive(v_liveVars_1449_);
if (v_isSharedCheck_1463_ == 0)
{
v___x_1454_ = v_liveVars_1449_;
v_isShared_1455_ = v_isSharedCheck_1463_;
goto v_resetjp_1453_;
}
else
{
lean_inc(v_borrows_1452_);
lean_inc(v_vars_1451_);
lean_dec(v_liveVars_1449_);
v___x_1454_ = lean_box(0);
v_isShared_1455_ = v_isSharedCheck_1463_;
goto v_resetjp_1453_;
}
v_resetjp_1453_:
{
lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v_vars_1458_; lean_object* v_borrows_1459_; lean_object* v___x_1461_; 
v___x_1456_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_visitParam___redArg___closed__0));
v___x_1457_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_visitParam___redArg___closed__1));
lean_inc(v_fvarId_1450_);
v_vars_1458_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v___x_1456_, v___x_1457_, v_vars_1451_, v_fvarId_1450_);
v_borrows_1459_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v___x_1456_, v___x_1457_, v_borrows_1452_, v_fvarId_1450_);
if (v_isShared_1455_ == 0)
{
lean_ctor_set(v___x_1454_, 1, v_borrows_1459_);
lean_ctor_set(v___x_1454_, 0, v_vars_1458_);
v___x_1461_ = v___x_1454_;
goto v_reusejp_1460_;
}
else
{
lean_object* v_reuseFailAlloc_1462_; 
v_reuseFailAlloc_1462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1462_, 0, v_vars_1458_);
lean_ctor_set(v_reuseFailAlloc_1462_, 1, v_borrows_1459_);
v___x_1461_ = v_reuseFailAlloc_1462_;
goto v_reusejp_1460_;
}
v_reusejp_1460_:
{
return v___x_1461_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_insertBorrow(lean_object* v_liveVars_1464_, lean_object* v_fvarId_1465_){
_start:
{
lean_object* v_vars_1466_; lean_object* v_borrows_1467_; lean_object* v___x_1469_; uint8_t v_isShared_1470_; uint8_t v_isSharedCheck_1478_; 
v_vars_1466_ = lean_ctor_get(v_liveVars_1464_, 0);
v_borrows_1467_ = lean_ctor_get(v_liveVars_1464_, 1);
v_isSharedCheck_1478_ = !lean_is_exclusive(v_liveVars_1464_);
if (v_isSharedCheck_1478_ == 0)
{
v___x_1469_ = v_liveVars_1464_;
v_isShared_1470_ = v_isSharedCheck_1478_;
goto v_resetjp_1468_;
}
else
{
lean_inc(v_borrows_1467_);
lean_inc(v_vars_1466_);
lean_dec(v_liveVars_1464_);
v___x_1469_ = lean_box(0);
v_isShared_1470_ = v_isSharedCheck_1478_;
goto v_resetjp_1468_;
}
v_resetjp_1468_:
{
lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1476_; 
v___x_1471_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_visitParam___redArg___closed__0));
v___x_1472_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_visitParam___redArg___closed__1));
v___x_1473_ = lean_box(0);
v___x_1474_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_1471_, v___x_1472_, v_borrows_1467_, v_fvarId_1465_, v___x_1473_);
if (v_isShared_1470_ == 0)
{
lean_ctor_set(v___x_1469_, 1, v___x_1474_);
v___x_1476_ = v___x_1469_;
goto v_reusejp_1475_;
}
else
{
lean_object* v_reuseFailAlloc_1477_; 
v_reuseFailAlloc_1477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1477_, 0, v_vars_1466_);
lean_ctor_set(v_reuseFailAlloc_1477_, 1, v___x_1474_);
v___x_1476_ = v_reuseFailAlloc_1477_;
goto v_reusejp_1475_;
}
v_reusejp_1475_:
{
return v___x_1476_;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_isAccessible_spec__0___redArg(lean_object* v_m_1479_, lean_object* v_a_1480_){
_start:
{
lean_object* v_buckets_1481_; lean_object* v___x_1482_; uint64_t v___x_1483_; uint64_t v___x_1484_; uint64_t v___x_1485_; uint64_t v_fold_1486_; uint64_t v___x_1487_; uint64_t v___x_1488_; uint64_t v___x_1489_; size_t v___x_1490_; size_t v___x_1491_; size_t v___x_1492_; size_t v___x_1493_; size_t v___x_1494_; lean_object* v___x_1495_; uint8_t v___x_1496_; 
v_buckets_1481_ = lean_ctor_get(v_m_1479_, 1);
v___x_1482_ = lean_array_get_size(v_buckets_1481_);
v___x_1483_ = l_Lean_instHashableFVarId_hash(v_a_1480_);
v___x_1484_ = 32ULL;
v___x_1485_ = lean_uint64_shift_right(v___x_1483_, v___x_1484_);
v_fold_1486_ = lean_uint64_xor(v___x_1483_, v___x_1485_);
v___x_1487_ = 16ULL;
v___x_1488_ = lean_uint64_shift_right(v_fold_1486_, v___x_1487_);
v___x_1489_ = lean_uint64_xor(v_fold_1486_, v___x_1488_);
v___x_1490_ = lean_uint64_to_usize(v___x_1489_);
v___x_1491_ = lean_usize_of_nat(v___x_1482_);
v___x_1492_ = ((size_t)1ULL);
v___x_1493_ = lean_usize_sub(v___x_1491_, v___x_1492_);
v___x_1494_ = lean_usize_land(v___x_1490_, v___x_1493_);
v___x_1495_ = lean_array_uget_borrowed(v_buckets_1481_, v___x_1494_);
v___x_1496_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_removeFromParent_spec__0_spec__0___redArg(v_a_1480_, v___x_1495_);
return v___x_1496_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_isAccessible_spec__0___redArg___boxed(lean_object* v_m_1497_, lean_object* v_a_1498_){
_start:
{
uint8_t v_res_1499_; lean_object* v_r_1500_; 
v_res_1499_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_isAccessible_spec__0___redArg(v_m_1497_, v_a_1498_);
lean_dec(v_a_1498_);
lean_dec_ref(v_m_1497_);
v_r_1500_ = lean_box(v_res_1499_);
return v_r_1500_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_isAccessible(lean_object* v_liveVars_1501_, lean_object* v_fvarId_1502_){
_start:
{
lean_object* v_vars_1503_; lean_object* v_borrows_1504_; uint8_t v___x_1505_; 
v_vars_1503_ = lean_ctor_get(v_liveVars_1501_, 0);
v_borrows_1504_ = lean_ctor_get(v_liveVars_1501_, 1);
v___x_1505_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_isAccessible_spec__0___redArg(v_vars_1503_, v_fvarId_1502_);
if (v___x_1505_ == 0)
{
uint8_t v___x_1506_; 
v___x_1506_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_isAccessible_spec__0___redArg(v_borrows_1504_, v_fvarId_1502_);
return v___x_1506_;
}
else
{
return v___x_1505_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_isAccessible___boxed(lean_object* v_liveVars_1507_, lean_object* v_fvarId_1508_){
_start:
{
uint8_t v_res_1509_; lean_object* v_r_1510_; 
v_res_1509_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_isAccessible(v_liveVars_1507_, v_fvarId_1508_);
lean_dec(v_fvarId_1508_);
lean_dec_ref(v_liveVars_1507_);
v_r_1510_ = lean_box(v_res_1509_);
return v_r_1510_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_isAccessible_spec__0(lean_object* v_00_u03b2_1511_, lean_object* v_m_1512_, lean_object* v_a_1513_){
_start:
{
uint8_t v___x_1514_; 
v___x_1514_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_isAccessible_spec__0___redArg(v_m_1512_, v_a_1513_);
return v___x_1514_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_isAccessible_spec__0___boxed(lean_object* v_00_u03b2_1515_, lean_object* v_m_1516_, lean_object* v_a_1517_){
_start:
{
uint8_t v_res_1518_; lean_object* v_r_1519_; 
v_res_1518_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_isAccessible_spec__0(v_00_u03b2_1515_, v_m_1516_, v_a_1517_);
lean_dec(v_a_1517_);
lean_dec_ref(v_m_1516_);
v_r_1519_ = lean_box(v_res_1518_);
return v_r_1519_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getVarInfo___redArg(lean_object* v_fvarId_1521_, lean_object* v_a_1522_){
_start:
{
lean_object* v_varMap_1524_; lean_object* v___f_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; 
v_varMap_1524_ = lean_ctor_get(v_a_1522_, 2);
lean_inc(v_varMap_1524_);
lean_dec_ref(v_a_1522_);
v___f_1525_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getVarInfo___redArg___closed__0));
v___x_1526_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_instInhabitedVarInfo_default));
v___x_1527_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(v___f_1525_, v___x_1526_, v_varMap_1524_, v_fvarId_1521_);
v___x_1528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1528_, 0, v___x_1527_);
return v___x_1528_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getVarInfo___redArg___boxed(lean_object* v_fvarId_1529_, lean_object* v_a_1530_, lean_object* v_a_1531_){
_start:
{
lean_object* v_res_1532_; 
v_res_1532_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getVarInfo___redArg(v_fvarId_1529_, v_a_1530_);
return v_res_1532_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getVarInfo(lean_object* v_fvarId_1533_, lean_object* v_a_1534_, lean_object* v_a_1535_, lean_object* v_a_1536_, lean_object* v_a_1537_, lean_object* v_a_1538_, lean_object* v_a_1539_){
_start:
{
lean_object* v_varMap_1541_; lean_object* v___f_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; 
v_varMap_1541_ = lean_ctor_get(v_a_1534_, 2);
lean_inc(v_varMap_1541_);
lean_dec_ref(v_a_1534_);
v___f_1542_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getVarInfo___redArg___closed__0));
v___x_1543_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_instInhabitedVarInfo_default));
v___x_1544_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(v___f_1542_, v___x_1543_, v_varMap_1541_, v_fvarId_1533_);
v___x_1545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1545_, 0, v___x_1544_);
return v___x_1545_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getVarInfo___boxed(lean_object* v_fvarId_1546_, lean_object* v_a_1547_, lean_object* v_a_1548_, lean_object* v_a_1549_, lean_object* v_a_1550_, lean_object* v_a_1551_, lean_object* v_a_1552_, lean_object* v_a_1553_){
_start:
{
lean_object* v_res_1554_; 
v_res_1554_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getVarInfo(v_fvarId_1546_, v_a_1547_, v_a_1548_, v_a_1549_, v_a_1550_, v_a_1551_, v_a_1552_);
lean_dec(v_a_1552_);
lean_dec_ref(v_a_1551_);
lean_dec(v_a_1550_);
lean_dec_ref(v_a_1549_);
lean_dec(v_a_1548_);
return v_res_1554_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getJpLiveVars___redArg(lean_object* v_fvarId_1555_, lean_object* v_a_1556_){
_start:
{
lean_object* v_jpLiveVarMap_1558_; lean_object* v___f_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; 
v_jpLiveVarMap_1558_ = lean_ctor_get(v_a_1556_, 3);
lean_inc(v_jpLiveVarMap_1558_);
lean_dec_ref(v_a_1556_);
v___f_1559_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getVarInfo___redArg___closed__0));
v___x_1560_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_instInhabitedLiveVars_default;
v___x_1561_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(v___f_1559_, v___x_1560_, v_jpLiveVarMap_1558_, v_fvarId_1555_);
v___x_1562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1562_, 0, v___x_1561_);
return v___x_1562_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getJpLiveVars___redArg___boxed(lean_object* v_fvarId_1563_, lean_object* v_a_1564_, lean_object* v_a_1565_){
_start:
{
lean_object* v_res_1566_; 
v_res_1566_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getJpLiveVars___redArg(v_fvarId_1563_, v_a_1564_);
return v_res_1566_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getJpLiveVars(lean_object* v_fvarId_1567_, lean_object* v_a_1568_, lean_object* v_a_1569_, lean_object* v_a_1570_, lean_object* v_a_1571_, lean_object* v_a_1572_, lean_object* v_a_1573_){
_start:
{
lean_object* v_jpLiveVarMap_1575_; lean_object* v___f_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; 
v_jpLiveVarMap_1575_ = lean_ctor_get(v_a_1568_, 3);
lean_inc(v_jpLiveVarMap_1575_);
lean_dec_ref(v_a_1568_);
v___f_1576_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getVarInfo___redArg___closed__0));
v___x_1577_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_instInhabitedLiveVars_default;
v___x_1578_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(v___f_1576_, v___x_1577_, v_jpLiveVarMap_1575_, v_fvarId_1567_);
v___x_1579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1579_, 0, v___x_1578_);
return v___x_1579_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getJpLiveVars___boxed(lean_object* v_fvarId_1580_, lean_object* v_a_1581_, lean_object* v_a_1582_, lean_object* v_a_1583_, lean_object* v_a_1584_, lean_object* v_a_1585_, lean_object* v_a_1586_, lean_object* v_a_1587_){
_start:
{
lean_object* v_res_1588_; 
v_res_1588_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getJpLiveVars(v_fvarId_1580_, v_a_1581_, v_a_1582_, v_a_1583_, v_a_1584_, v_a_1585_, v_a_1586_);
lean_dec(v_a_1586_);
lean_dec_ref(v_a_1585_);
lean_dec(v_a_1584_);
lean_dec_ref(v_a_1583_);
lean_dec(v_a_1582_);
return v_res_1588_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isLive___redArg(lean_object* v_fvarId_1589_, lean_object* v_a_1590_){
_start:
{
lean_object* v___x_1592_; lean_object* v_vars_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; uint8_t v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; 
v___x_1592_ = lean_st_ref_get(v_a_1590_);
v_vars_1593_ = lean_ctor_get(v___x_1592_, 0);
lean_inc_ref(v_vars_1593_);
lean_dec(v___x_1592_);
v___x_1594_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_visitParam___redArg___closed__0));
v___x_1595_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_visitParam___redArg___closed__1));
v___x_1596_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___x_1594_, v___x_1595_, v_vars_1593_, v_fvarId_1589_);
lean_dec_ref(v_vars_1593_);
v___x_1597_ = lean_box(v___x_1596_);
v___x_1598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1598_, 0, v___x_1597_);
return v___x_1598_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isLive___redArg___boxed(lean_object* v_fvarId_1599_, lean_object* v_a_1600_, lean_object* v_a_1601_){
_start:
{
lean_object* v_res_1602_; 
v_res_1602_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isLive___redArg(v_fvarId_1599_, v_a_1600_);
lean_dec(v_a_1600_);
return v_res_1602_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isLive(lean_object* v_fvarId_1603_, lean_object* v_a_1604_, lean_object* v_a_1605_, lean_object* v_a_1606_, lean_object* v_a_1607_, lean_object* v_a_1608_, lean_object* v_a_1609_){
_start:
{
lean_object* v___x_1611_; lean_object* v_vars_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; uint8_t v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; 
v___x_1611_ = lean_st_ref_get(v_a_1605_);
v_vars_1612_ = lean_ctor_get(v___x_1611_, 0);
lean_inc_ref(v_vars_1612_);
lean_dec(v___x_1611_);
v___x_1613_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_visitParam___redArg___closed__0));
v___x_1614_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_visitParam___redArg___closed__1));
v___x_1615_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___x_1613_, v___x_1614_, v_vars_1612_, v_fvarId_1603_);
lean_dec_ref(v_vars_1612_);
v___x_1616_ = lean_box(v___x_1615_);
v___x_1617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1617_, 0, v___x_1616_);
return v___x_1617_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isLive___boxed(lean_object* v_fvarId_1618_, lean_object* v_a_1619_, lean_object* v_a_1620_, lean_object* v_a_1621_, lean_object* v_a_1622_, lean_object* v_a_1623_, lean_object* v_a_1624_, lean_object* v_a_1625_){
_start:
{
lean_object* v_res_1626_; 
v_res_1626_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isLive(v_fvarId_1618_, v_a_1619_, v_a_1620_, v_a_1621_, v_a_1622_, v_a_1623_, v_a_1624_);
lean_dec(v_a_1624_);
lean_dec_ref(v_a_1623_);
lean_dec(v_a_1622_);
lean_dec_ref(v_a_1621_);
lean_dec(v_a_1620_);
lean_dec_ref(v_a_1619_);
return v_res_1626_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowed___redArg(lean_object* v_fvarId_1627_, lean_object* v_a_1628_){
_start:
{
lean_object* v___x_1630_; lean_object* v_borrows_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; uint8_t v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; 
v___x_1630_ = lean_st_ref_get(v_a_1628_);
v_borrows_1631_ = lean_ctor_get(v___x_1630_, 1);
lean_inc_ref(v_borrows_1631_);
lean_dec(v___x_1630_);
v___x_1632_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_visitParam___redArg___closed__0));
v___x_1633_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_visitParam___redArg___closed__1));
v___x_1634_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___x_1632_, v___x_1633_, v_borrows_1631_, v_fvarId_1627_);
lean_dec_ref(v_borrows_1631_);
v___x_1635_ = lean_box(v___x_1634_);
v___x_1636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1636_, 0, v___x_1635_);
return v___x_1636_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowed___redArg___boxed(lean_object* v_fvarId_1637_, lean_object* v_a_1638_, lean_object* v_a_1639_){
_start:
{
lean_object* v_res_1640_; 
v_res_1640_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowed___redArg(v_fvarId_1637_, v_a_1638_);
lean_dec(v_a_1638_);
return v_res_1640_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowed(lean_object* v_fvarId_1641_, lean_object* v_a_1642_, lean_object* v_a_1643_, lean_object* v_a_1644_, lean_object* v_a_1645_, lean_object* v_a_1646_, lean_object* v_a_1647_){
_start:
{
lean_object* v___x_1649_; lean_object* v_borrows_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; uint8_t v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; 
v___x_1649_ = lean_st_ref_get(v_a_1643_);
v_borrows_1650_ = lean_ctor_get(v___x_1649_, 1);
lean_inc_ref(v_borrows_1650_);
lean_dec(v___x_1649_);
v___x_1651_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_visitParam___redArg___closed__0));
v___x_1652_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_visitParam___redArg___closed__1));
v___x_1653_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___x_1651_, v___x_1652_, v_borrows_1650_, v_fvarId_1641_);
lean_dec_ref(v_borrows_1650_);
v___x_1654_ = lean_box(v___x_1653_);
v___x_1655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1655_, 0, v___x_1654_);
return v___x_1655_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowed___boxed(lean_object* v_fvarId_1656_, lean_object* v_a_1657_, lean_object* v_a_1658_, lean_object* v_a_1659_, lean_object* v_a_1660_, lean_object* v_a_1661_, lean_object* v_a_1662_, lean_object* v_a_1663_){
_start:
{
lean_object* v_res_1664_; 
v_res_1664_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowed(v_fvarId_1656_, v_a_1657_, v_a_1658_, v_a_1659_, v_a_1660_, v_a_1661_, v_a_1662_);
lean_dec(v_a_1662_);
lean_dec_ref(v_a_1661_);
lean_dec(v_a_1660_);
lean_dec_ref(v_a_1659_);
lean_dec(v_a_1658_);
lean_dec_ref(v_a_1657_);
return v_res_1664_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isAccessible___redArg(lean_object* v_fvarId_1665_, lean_object* v_a_1666_){
_start:
{
lean_object* v___x_1668_; uint8_t v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; 
v___x_1668_ = lean_st_ref_get(v_a_1666_);
v___x_1669_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_isAccessible(v___x_1668_, v_fvarId_1665_);
lean_dec(v___x_1668_);
v___x_1670_ = lean_box(v___x_1669_);
v___x_1671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1671_, 0, v___x_1670_);
return v___x_1671_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isAccessible___redArg___boxed(lean_object* v_fvarId_1672_, lean_object* v_a_1673_, lean_object* v_a_1674_){
_start:
{
lean_object* v_res_1675_; 
v_res_1675_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isAccessible___redArg(v_fvarId_1672_, v_a_1673_);
lean_dec(v_a_1673_);
lean_dec(v_fvarId_1672_);
return v_res_1675_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isAccessible(lean_object* v_fvarId_1676_, lean_object* v_a_1677_, lean_object* v_a_1678_, lean_object* v_a_1679_, lean_object* v_a_1680_, lean_object* v_a_1681_, lean_object* v_a_1682_){
_start:
{
lean_object* v___x_1684_; uint8_t v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; 
v___x_1684_ = lean_st_ref_get(v_a_1678_);
v___x_1685_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_isAccessible(v___x_1684_, v_fvarId_1676_);
lean_dec(v___x_1684_);
v___x_1686_ = lean_box(v___x_1685_);
v___x_1687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1687_, 0, v___x_1686_);
return v___x_1687_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isAccessible___boxed(lean_object* v_fvarId_1688_, lean_object* v_a_1689_, lean_object* v_a_1690_, lean_object* v_a_1691_, lean_object* v_a_1692_, lean_object* v_a_1693_, lean_object* v_a_1694_, lean_object* v_a_1695_){
_start:
{
lean_object* v_res_1696_; 
v_res_1696_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isAccessible(v_fvarId_1688_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_, v_a_1693_, v_a_1694_);
lean_dec(v_a_1694_);
lean_dec_ref(v_a_1693_);
lean_dec(v_a_1692_);
lean_dec_ref(v_a_1691_);
lean_dec(v_a_1690_);
lean_dec_ref(v_a_1689_);
lean_dec(v_fvarId_1688_);
return v_res_1696_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_modifyLive___redArg(lean_object* v_f_1697_, lean_object* v_a_1698_){
_start:
{
lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; 
v___x_1700_ = lean_st_ref_take(v_a_1698_);
v___x_1701_ = lean_apply_1(v_f_1697_, v___x_1700_);
v___x_1702_ = lean_st_ref_set(v_a_1698_, v___x_1701_);
v___x_1703_ = lean_box(0);
v___x_1704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1704_, 0, v___x_1703_);
return v___x_1704_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_modifyLive___redArg___boxed(lean_object* v_f_1705_, lean_object* v_a_1706_, lean_object* v_a_1707_){
_start:
{
lean_object* v_res_1708_; 
v_res_1708_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_modifyLive___redArg(v_f_1705_, v_a_1706_);
lean_dec(v_a_1706_);
return v_res_1708_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_modifyLive(lean_object* v_f_1709_, lean_object* v_a_1710_, lean_object* v_a_1711_, lean_object* v_a_1712_, lean_object* v_a_1713_, lean_object* v_a_1714_, lean_object* v_a_1715_){
_start:
{
lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; 
v___x_1717_ = lean_st_ref_take(v_a_1711_);
v___x_1718_ = lean_apply_1(v_f_1709_, v___x_1717_);
v___x_1719_ = lean_st_ref_set(v_a_1711_, v___x_1718_);
v___x_1720_ = lean_box(0);
v___x_1721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1721_, 0, v___x_1720_);
return v___x_1721_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_modifyLive___boxed(lean_object* v_f_1722_, lean_object* v_a_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_){
_start:
{
lean_object* v_res_1730_; 
v_res_1730_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_modifyLive(v_f_1722_, v_a_1723_, v_a_1724_, v_a_1725_, v_a_1726_, v_a_1727_, v_a_1728_);
lean_dec(v_a_1728_);
lean_dec_ref(v_a_1727_);
lean_dec(v_a_1726_);
lean_dec_ref(v_a_1725_);
lean_dec(v_a_1724_);
lean_dec_ref(v_a_1723_);
return v_res_1730_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withParams___redArg___lam__0(lean_object* v_x1_1731_, lean_object* v_x2_1732_){
_start:
{
lean_object* v_borrowedParams_1733_; lean_object* v_derivedValMap_1734_; lean_object* v_varMap_1735_; lean_object* v_jpLiveVarMap_1736_; lean_object* v_idx_1737_; lean_object* v___x_1739_; uint8_t v_isShared_1740_; uint8_t v_isSharedCheck_1753_; 
v_borrowedParams_1733_ = lean_ctor_get(v_x1_1731_, 0);
v_derivedValMap_1734_ = lean_ctor_get(v_x1_1731_, 1);
v_varMap_1735_ = lean_ctor_get(v_x1_1731_, 2);
v_jpLiveVarMap_1736_ = lean_ctor_get(v_x1_1731_, 3);
v_idx_1737_ = lean_ctor_get(v_x1_1731_, 4);
v_isSharedCheck_1753_ = !lean_is_exclusive(v_x1_1731_);
if (v_isSharedCheck_1753_ == 0)
{
v___x_1739_ = v_x1_1731_;
v_isShared_1740_ = v_isSharedCheck_1753_;
goto v_resetjp_1738_;
}
else
{
lean_inc(v_idx_1737_);
lean_inc(v_jpLiveVarMap_1736_);
lean_inc(v_varMap_1735_);
lean_inc(v_derivedValMap_1734_);
lean_inc(v_borrowedParams_1733_);
lean_dec(v_x1_1731_);
v___x_1739_ = lean_box(0);
v_isShared_1740_ = v_isSharedCheck_1753_;
goto v_resetjp_1738_;
}
v_resetjp_1738_:
{
lean_object* v_fvarId_1741_; lean_object* v_type_1742_; uint8_t v___x_1743_; uint8_t v___x_1744_; uint8_t v___x_1745_; lean_object* v___x_1746_; lean_object* v_varMap_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1751_; 
v_fvarId_1741_ = lean_ctor_get(v_x2_1732_, 0);
lean_inc(v_fvarId_1741_);
v_type_1742_ = lean_ctor_get(v_x2_1732_, 2);
lean_inc_ref(v_type_1742_);
lean_dec_ref(v_x2_1732_);
v___x_1743_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isPossibleRef(v_type_1742_);
v___x_1744_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isDefiniteRef(v_type_1742_);
lean_dec_ref(v_type_1742_);
v___x_1745_ = 0;
lean_inc(v_idx_1737_);
v___x_1746_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_1746_, 0, v_idx_1737_);
lean_ctor_set_uint8(v___x_1746_, sizeof(void*)*1, v___x_1743_);
lean_ctor_set_uint8(v___x_1746_, sizeof(void*)*1 + 1, v___x_1744_);
lean_ctor_set_uint8(v___x_1746_, sizeof(void*)*1 + 2, v___x_1745_);
v_varMap_1747_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_1741_, v___x_1746_, v_varMap_1735_);
v___x_1748_ = lean_unsigned_to_nat(1u);
v___x_1749_ = lean_nat_add(v_idx_1737_, v___x_1748_);
lean_dec(v_idx_1737_);
if (v_isShared_1740_ == 0)
{
lean_ctor_set(v___x_1739_, 4, v___x_1749_);
lean_ctor_set(v___x_1739_, 2, v_varMap_1747_);
v___x_1751_ = v___x_1739_;
goto v_reusejp_1750_;
}
else
{
lean_object* v_reuseFailAlloc_1752_; 
v_reuseFailAlloc_1752_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1752_, 0, v_borrowedParams_1733_);
lean_ctor_set(v_reuseFailAlloc_1752_, 1, v_derivedValMap_1734_);
lean_ctor_set(v_reuseFailAlloc_1752_, 2, v_varMap_1747_);
lean_ctor_set(v_reuseFailAlloc_1752_, 3, v_jpLiveVarMap_1736_);
lean_ctor_set(v_reuseFailAlloc_1752_, 4, v___x_1749_);
v___x_1751_ = v_reuseFailAlloc_1752_;
goto v_reusejp_1750_;
}
v_reusejp_1750_:
{
return v___x_1751_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withParams___redArg(lean_object* v_ps_1755_, lean_object* v_x_1756_, lean_object* v_a_1757_, lean_object* v_a_1758_, lean_object* v_a_1759_, lean_object* v_a_1760_, lean_object* v_a_1761_, lean_object* v_a_1762_){
_start:
{
lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; uint8_t v___x_1767_; 
v___x_1764_ = lean_unsigned_to_nat(0u);
v___x_1765_ = lean_array_get_size(v_ps_1755_);
v___x_1766_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_addDerivedValue___redArg___closed__9));
v___x_1767_ = lean_nat_dec_lt(v___x_1764_, v___x_1765_);
if (v___x_1767_ == 0)
{
lean_object* v___x_1768_; 
lean_dec_ref(v_ps_1755_);
lean_inc(v_a_1762_);
lean_inc_ref(v_a_1761_);
lean_inc(v_a_1760_);
lean_inc_ref(v_a_1759_);
lean_inc(v_a_1758_);
lean_inc_ref(v_a_1757_);
v___x_1768_ = lean_apply_7(v_x_1756_, v_a_1757_, v_a_1758_, v_a_1759_, v_a_1760_, v_a_1761_, v_a_1762_, lean_box(0));
return v___x_1768_;
}
else
{
lean_object* v___f_1769_; uint8_t v___x_1770_; 
v___f_1769_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withParams___redArg___closed__0));
v___x_1770_ = lean_nat_dec_le(v___x_1765_, v___x_1765_);
if (v___x_1770_ == 0)
{
if (v___x_1767_ == 0)
{
lean_object* v___x_1771_; 
lean_dec_ref(v_ps_1755_);
lean_inc(v_a_1762_);
lean_inc_ref(v_a_1761_);
lean_inc(v_a_1760_);
lean_inc_ref(v_a_1759_);
lean_inc(v_a_1758_);
lean_inc_ref(v_a_1757_);
v___x_1771_ = lean_apply_7(v_x_1756_, v_a_1757_, v_a_1758_, v_a_1759_, v_a_1760_, v_a_1761_, v_a_1762_, lean_box(0));
return v___x_1771_;
}
else
{
size_t v___x_1772_; size_t v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; 
v___x_1772_ = ((size_t)0ULL);
v___x_1773_ = lean_usize_of_nat(v___x_1765_);
lean_inc_ref(v_a_1757_);
v___x_1774_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1766_, v___f_1769_, v_ps_1755_, v___x_1772_, v___x_1773_, v_a_1757_);
lean_inc(v_a_1762_);
lean_inc_ref(v_a_1761_);
lean_inc(v_a_1760_);
lean_inc_ref(v_a_1759_);
lean_inc(v_a_1758_);
v___x_1775_ = lean_apply_7(v_x_1756_, v___x_1774_, v_a_1758_, v_a_1759_, v_a_1760_, v_a_1761_, v_a_1762_, lean_box(0));
return v___x_1775_;
}
}
else
{
size_t v___x_1776_; size_t v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; 
v___x_1776_ = ((size_t)0ULL);
v___x_1777_ = lean_usize_of_nat(v___x_1765_);
lean_inc_ref(v_a_1757_);
v___x_1778_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1766_, v___f_1769_, v_ps_1755_, v___x_1776_, v___x_1777_, v_a_1757_);
lean_inc(v_a_1762_);
lean_inc_ref(v_a_1761_);
lean_inc(v_a_1760_);
lean_inc_ref(v_a_1759_);
lean_inc(v_a_1758_);
v___x_1779_ = lean_apply_7(v_x_1756_, v___x_1778_, v_a_1758_, v_a_1759_, v_a_1760_, v_a_1761_, v_a_1762_, lean_box(0));
return v___x_1779_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withParams___redArg___boxed(lean_object* v_ps_1780_, lean_object* v_x_1781_, lean_object* v_a_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_, lean_object* v_a_1787_, lean_object* v_a_1788_){
_start:
{
lean_object* v_res_1789_; 
v_res_1789_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withParams___redArg(v_ps_1780_, v_x_1781_, v_a_1782_, v_a_1783_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_);
lean_dec(v_a_1787_);
lean_dec_ref(v_a_1786_);
lean_dec(v_a_1785_);
lean_dec_ref(v_a_1784_);
lean_dec(v_a_1783_);
lean_dec_ref(v_a_1782_);
return v_res_1789_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withParams(lean_object* v_00_u03b1_1790_, lean_object* v_ps_1791_, lean_object* v_x_1792_, lean_object* v_a_1793_, lean_object* v_a_1794_, lean_object* v_a_1795_, lean_object* v_a_1796_, lean_object* v_a_1797_, lean_object* v_a_1798_){
_start:
{
lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; uint8_t v___x_1803_; 
v___x_1800_ = lean_unsigned_to_nat(0u);
v___x_1801_ = lean_array_get_size(v_ps_1791_);
v___x_1802_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_addDerivedValue___redArg___closed__9));
v___x_1803_ = lean_nat_dec_lt(v___x_1800_, v___x_1801_);
if (v___x_1803_ == 0)
{
lean_object* v___x_1804_; 
lean_dec_ref(v_ps_1791_);
lean_inc(v_a_1798_);
lean_inc_ref(v_a_1797_);
lean_inc(v_a_1796_);
lean_inc_ref(v_a_1795_);
lean_inc(v_a_1794_);
lean_inc_ref(v_a_1793_);
v___x_1804_ = lean_apply_7(v_x_1792_, v_a_1793_, v_a_1794_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_, lean_box(0));
return v___x_1804_;
}
else
{
lean_object* v___f_1805_; uint8_t v___x_1806_; 
v___f_1805_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withParams___redArg___closed__0));
v___x_1806_ = lean_nat_dec_le(v___x_1801_, v___x_1801_);
if (v___x_1806_ == 0)
{
if (v___x_1803_ == 0)
{
lean_object* v___x_1807_; 
lean_dec_ref(v_ps_1791_);
lean_inc(v_a_1798_);
lean_inc_ref(v_a_1797_);
lean_inc(v_a_1796_);
lean_inc_ref(v_a_1795_);
lean_inc(v_a_1794_);
lean_inc_ref(v_a_1793_);
v___x_1807_ = lean_apply_7(v_x_1792_, v_a_1793_, v_a_1794_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_, lean_box(0));
return v___x_1807_;
}
else
{
size_t v___x_1808_; size_t v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; 
v___x_1808_ = ((size_t)0ULL);
v___x_1809_ = lean_usize_of_nat(v___x_1801_);
lean_inc_ref(v_a_1793_);
v___x_1810_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1802_, v___f_1805_, v_ps_1791_, v___x_1808_, v___x_1809_, v_a_1793_);
lean_inc(v_a_1798_);
lean_inc_ref(v_a_1797_);
lean_inc(v_a_1796_);
lean_inc_ref(v_a_1795_);
lean_inc(v_a_1794_);
v___x_1811_ = lean_apply_7(v_x_1792_, v___x_1810_, v_a_1794_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_, lean_box(0));
return v___x_1811_;
}
}
else
{
size_t v___x_1812_; size_t v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; 
v___x_1812_ = ((size_t)0ULL);
v___x_1813_ = lean_usize_of_nat(v___x_1801_);
lean_inc_ref(v_a_1793_);
v___x_1814_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1802_, v___f_1805_, v_ps_1791_, v___x_1812_, v___x_1813_, v_a_1793_);
lean_inc(v_a_1798_);
lean_inc_ref(v_a_1797_);
lean_inc(v_a_1796_);
lean_inc_ref(v_a_1795_);
lean_inc(v_a_1794_);
v___x_1815_ = lean_apply_7(v_x_1792_, v___x_1814_, v_a_1794_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_, lean_box(0));
return v___x_1815_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withParams___boxed(lean_object* v_00_u03b1_1816_, lean_object* v_ps_1817_, lean_object* v_x_1818_, lean_object* v_a_1819_, lean_object* v_a_1820_, lean_object* v_a_1821_, lean_object* v_a_1822_, lean_object* v_a_1823_, lean_object* v_a_1824_, lean_object* v_a_1825_){
_start:
{
lean_object* v_res_1826_; 
v_res_1826_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withParams(v_00_u03b1_1816_, v_ps_1817_, v_x_1818_, v_a_1819_, v_a_1820_, v_a_1821_, v_a_1822_, v_a_1823_, v_a_1824_);
lean_dec(v_a_1824_);
lean_dec_ref(v_a_1823_);
lean_dec(v_a_1822_);
lean_dec_ref(v_a_1821_);
lean_dec(v_a_1820_);
lean_dec_ref(v_a_1819_);
return v_res_1826_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetValue_isPersistent(lean_object* v_val_1827_){
_start:
{
if (lean_obj_tag(v_val_1827_) == 9)
{
lean_object* v_args_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; uint8_t v___x_1831_; 
v_args_1828_ = lean_ctor_get(v_val_1827_, 1);
v___x_1829_ = lean_array_get_size(v_args_1828_);
v___x_1830_ = lean_unsigned_to_nat(0u);
v___x_1831_ = lean_nat_dec_eq(v___x_1829_, v___x_1830_);
return v___x_1831_;
}
else
{
uint8_t v___x_1832_; 
v___x_1832_ = 0;
return v___x_1832_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetValue_isPersistent___boxed(lean_object* v_val_1833_){
_start:
{
uint8_t v_res_1834_; lean_object* v_r_1835_; 
v_res_1834_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetValue_isPersistent(v_val_1833_);
lean_dec(v_val_1833_);
v_r_1835_ = lean_box(v_res_1834_);
return v_r_1835_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withLetDecl___redArg(lean_object* v_decl_1836_, lean_object* v_x_1837_, lean_object* v_a_1838_, lean_object* v_a_1839_, lean_object* v_a_1840_, lean_object* v_a_1841_, lean_object* v_a_1842_, lean_object* v_a_1843_){
_start:
{
lean_object* v_fvarId_1845_; lean_object* v_type_1846_; lean_object* v_value_1847_; lean_object* v_borrowedParams_1848_; lean_object* v_derivedValMap_1849_; lean_object* v_varMap_1850_; lean_object* v_jpLiveVarMap_1851_; lean_object* v_idx_1852_; uint8_t v___x_1853_; uint8_t v___x_1854_; uint8_t v___x_1855_; lean_object* v_varInfo_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; 
v_fvarId_1845_ = lean_ctor_get(v_decl_1836_, 0);
lean_inc(v_fvarId_1845_);
v_type_1846_ = lean_ctor_get(v_decl_1836_, 2);
lean_inc_ref(v_type_1846_);
v_value_1847_ = lean_ctor_get(v_decl_1836_, 3);
lean_inc(v_value_1847_);
lean_dec_ref(v_decl_1836_);
v_borrowedParams_1848_ = lean_ctor_get(v_a_1838_, 0);
lean_inc_ref(v_borrowedParams_1848_);
v_derivedValMap_1849_ = lean_ctor_get(v_a_1838_, 1);
lean_inc_ref(v_derivedValMap_1849_);
v_varMap_1850_ = lean_ctor_get(v_a_1838_, 2);
lean_inc(v_varMap_1850_);
v_jpLiveVarMap_1851_ = lean_ctor_get(v_a_1838_, 3);
lean_inc(v_jpLiveVarMap_1851_);
v_idx_1852_ = lean_ctor_get(v_a_1838_, 4);
lean_inc(v_idx_1852_);
lean_dec_ref(v_a_1838_);
v___x_1853_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isPossibleRef(v_type_1846_);
v___x_1854_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isDefiniteRef(v_type_1846_);
lean_dec_ref(v_type_1846_);
v___x_1855_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetValue_isPersistent(v_value_1847_);
lean_dec(v_value_1847_);
lean_inc(v_idx_1852_);
v_varInfo_1856_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v_varInfo_1856_, 0, v_idx_1852_);
lean_ctor_set_uint8(v_varInfo_1856_, sizeof(void*)*1, v___x_1853_);
lean_ctor_set_uint8(v_varInfo_1856_, sizeof(void*)*1 + 1, v___x_1854_);
lean_ctor_set_uint8(v_varInfo_1856_, sizeof(void*)*1 + 2, v___x_1855_);
v___x_1857_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_1845_, v_varInfo_1856_, v_varMap_1850_);
v___x_1858_ = lean_unsigned_to_nat(1u);
v___x_1859_ = lean_nat_add(v_idx_1852_, v___x_1858_);
lean_dec(v_idx_1852_);
v___x_1860_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1860_, 0, v_borrowedParams_1848_);
lean_ctor_set(v___x_1860_, 1, v_derivedValMap_1849_);
lean_ctor_set(v___x_1860_, 2, v___x_1857_);
lean_ctor_set(v___x_1860_, 3, v_jpLiveVarMap_1851_);
lean_ctor_set(v___x_1860_, 4, v___x_1859_);
lean_inc(v_a_1843_);
lean_inc_ref(v_a_1842_);
lean_inc(v_a_1841_);
lean_inc_ref(v_a_1840_);
lean_inc(v_a_1839_);
v___x_1861_ = lean_apply_7(v_x_1837_, v___x_1860_, v_a_1839_, v_a_1840_, v_a_1841_, v_a_1842_, v_a_1843_, lean_box(0));
return v___x_1861_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withLetDecl___redArg___boxed(lean_object* v_decl_1862_, lean_object* v_x_1863_, lean_object* v_a_1864_, lean_object* v_a_1865_, lean_object* v_a_1866_, lean_object* v_a_1867_, lean_object* v_a_1868_, lean_object* v_a_1869_, lean_object* v_a_1870_){
_start:
{
lean_object* v_res_1871_; 
v_res_1871_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withLetDecl___redArg(v_decl_1862_, v_x_1863_, v_a_1864_, v_a_1865_, v_a_1866_, v_a_1867_, v_a_1868_, v_a_1869_);
lean_dec(v_a_1869_);
lean_dec_ref(v_a_1868_);
lean_dec(v_a_1867_);
lean_dec_ref(v_a_1866_);
lean_dec(v_a_1865_);
return v_res_1871_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withLetDecl(lean_object* v_00_u03b1_1872_, lean_object* v_decl_1873_, lean_object* v_x_1874_, lean_object* v_a_1875_, lean_object* v_a_1876_, lean_object* v_a_1877_, lean_object* v_a_1878_, lean_object* v_a_1879_, lean_object* v_a_1880_){
_start:
{
lean_object* v_fvarId_1882_; lean_object* v_type_1883_; lean_object* v_value_1884_; lean_object* v_borrowedParams_1885_; lean_object* v_derivedValMap_1886_; lean_object* v_varMap_1887_; lean_object* v_jpLiveVarMap_1888_; lean_object* v_idx_1889_; uint8_t v___x_1890_; uint8_t v___x_1891_; uint8_t v___x_1892_; lean_object* v_varInfo_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; 
v_fvarId_1882_ = lean_ctor_get(v_decl_1873_, 0);
lean_inc(v_fvarId_1882_);
v_type_1883_ = lean_ctor_get(v_decl_1873_, 2);
lean_inc_ref(v_type_1883_);
v_value_1884_ = lean_ctor_get(v_decl_1873_, 3);
lean_inc(v_value_1884_);
lean_dec_ref(v_decl_1873_);
v_borrowedParams_1885_ = lean_ctor_get(v_a_1875_, 0);
lean_inc_ref(v_borrowedParams_1885_);
v_derivedValMap_1886_ = lean_ctor_get(v_a_1875_, 1);
lean_inc_ref(v_derivedValMap_1886_);
v_varMap_1887_ = lean_ctor_get(v_a_1875_, 2);
lean_inc(v_varMap_1887_);
v_jpLiveVarMap_1888_ = lean_ctor_get(v_a_1875_, 3);
lean_inc(v_jpLiveVarMap_1888_);
v_idx_1889_ = lean_ctor_get(v_a_1875_, 4);
lean_inc(v_idx_1889_);
lean_dec_ref(v_a_1875_);
v___x_1890_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isPossibleRef(v_type_1883_);
v___x_1891_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isDefiniteRef(v_type_1883_);
lean_dec_ref(v_type_1883_);
v___x_1892_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetValue_isPersistent(v_value_1884_);
lean_dec(v_value_1884_);
lean_inc(v_idx_1889_);
v_varInfo_1893_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v_varInfo_1893_, 0, v_idx_1889_);
lean_ctor_set_uint8(v_varInfo_1893_, sizeof(void*)*1, v___x_1890_);
lean_ctor_set_uint8(v_varInfo_1893_, sizeof(void*)*1 + 1, v___x_1891_);
lean_ctor_set_uint8(v_varInfo_1893_, sizeof(void*)*1 + 2, v___x_1892_);
v___x_1894_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_1882_, v_varInfo_1893_, v_varMap_1887_);
v___x_1895_ = lean_unsigned_to_nat(1u);
v___x_1896_ = lean_nat_add(v_idx_1889_, v___x_1895_);
lean_dec(v_idx_1889_);
v___x_1897_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1897_, 0, v_borrowedParams_1885_);
lean_ctor_set(v___x_1897_, 1, v_derivedValMap_1886_);
lean_ctor_set(v___x_1897_, 2, v___x_1894_);
lean_ctor_set(v___x_1897_, 3, v_jpLiveVarMap_1888_);
lean_ctor_set(v___x_1897_, 4, v___x_1896_);
lean_inc(v_a_1880_);
lean_inc_ref(v_a_1879_);
lean_inc(v_a_1878_);
lean_inc_ref(v_a_1877_);
lean_inc(v_a_1876_);
v___x_1898_ = lean_apply_7(v_x_1874_, v___x_1897_, v_a_1876_, v_a_1877_, v_a_1878_, v_a_1879_, v_a_1880_, lean_box(0));
return v___x_1898_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withLetDecl___boxed(lean_object* v_00_u03b1_1899_, lean_object* v_decl_1900_, lean_object* v_x_1901_, lean_object* v_a_1902_, lean_object* v_a_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_, lean_object* v_a_1906_, lean_object* v_a_1907_, lean_object* v_a_1908_){
_start:
{
lean_object* v_res_1909_; 
v_res_1909_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withLetDecl(v_00_u03b1_1899_, v_decl_1900_, v_x_1901_, v_a_1902_, v_a_1903_, v_a_1904_, v_a_1905_, v_a_1906_, v_a_1907_);
lean_dec(v_a_1907_);
lean_dec_ref(v_a_1906_);
lean_dec(v_a_1905_);
lean_dec_ref(v_a_1904_);
lean_dec(v_a_1903_);
return v_res_1909_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withCtorAlt___redArg(lean_object* v_discr_1910_, lean_object* v_c_1911_, lean_object* v_x_1912_, lean_object* v_a_1913_, lean_object* v_a_1914_, lean_object* v_a_1915_, lean_object* v_a_1916_, lean_object* v_a_1917_, lean_object* v_a_1918_){
_start:
{
lean_object* v_borrowedParams_1920_; lean_object* v_derivedValMap_1921_; lean_object* v_varMap_1922_; lean_object* v_jpLiveVarMap_1923_; lean_object* v_idx_1924_; lean_object* v___y_1926_; lean_object* v___f_1931_; lean_object* v___x_1932_; 
v_borrowedParams_1920_ = lean_ctor_get(v_a_1913_, 0);
lean_inc_ref(v_borrowedParams_1920_);
v_derivedValMap_1921_ = lean_ctor_get(v_a_1913_, 1);
lean_inc_ref(v_derivedValMap_1921_);
v_varMap_1922_ = lean_ctor_get(v_a_1913_, 2);
lean_inc(v_varMap_1922_);
v_jpLiveVarMap_1923_ = lean_ctor_get(v_a_1913_, 3);
lean_inc(v_jpLiveVarMap_1923_);
v_idx_1924_ = lean_ctor_get(v_a_1913_, 4);
lean_inc(v_idx_1924_);
lean_dec_ref(v_a_1913_);
v___f_1931_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getVarInfo___redArg___closed__0));
lean_inc(v_discr_1910_);
lean_inc(v_varMap_1922_);
v___x_1932_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v___f_1931_, v_varMap_1922_, v_discr_1910_);
if (lean_obj_tag(v___x_1932_) == 0)
{
lean_dec(v_discr_1910_);
v___y_1926_ = v_varMap_1922_;
goto v___jp_1925_;
}
else
{
lean_object* v_val_1933_; uint8_t v_persistent_1934_; lean_object* v___x_1936_; uint8_t v_isShared_1937_; uint8_t v_isSharedCheck_1947_; 
v_val_1933_ = lean_ctor_get(v___x_1932_, 0);
lean_inc(v_val_1933_);
lean_dec_ref(v___x_1932_);
v_persistent_1934_ = lean_ctor_get_uint8(v_val_1933_, sizeof(void*)*1 + 2);
v_isSharedCheck_1947_ = !lean_is_exclusive(v_val_1933_);
if (v_isSharedCheck_1947_ == 0)
{
lean_object* v_unused_1948_; 
v_unused_1948_ = lean_ctor_get(v_val_1933_, 0);
lean_dec(v_unused_1948_);
v___x_1936_ = v_val_1933_;
v_isShared_1937_ = v_isSharedCheck_1947_;
goto v_resetjp_1935_;
}
else
{
lean_dec(v_val_1933_);
v___x_1936_ = lean_box(0);
v_isShared_1937_ = v_isSharedCheck_1947_;
goto v_resetjp_1935_;
}
v_resetjp_1935_:
{
lean_object* v___x_1938_; uint8_t v___x_1939_; uint8_t v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1944_; 
v___x_1938_ = l_Lean_Compiler_LCNF_CtorInfo_type(v_c_1911_);
v___x_1939_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isPossibleRef(v___x_1938_);
v___x_1940_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isDefiniteRef(v___x_1938_);
lean_dec_ref(v___x_1938_);
v___x_1941_ = lean_unsigned_to_nat(1u);
v___x_1942_ = lean_nat_add(v_idx_1924_, v___x_1941_);
if (v_isShared_1937_ == 0)
{
lean_ctor_set(v___x_1936_, 0, v___x_1942_);
v___x_1944_ = v___x_1936_;
goto v_reusejp_1943_;
}
else
{
lean_object* v_reuseFailAlloc_1946_; 
v_reuseFailAlloc_1946_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v_reuseFailAlloc_1946_, 0, v___x_1942_);
lean_ctor_set_uint8(v_reuseFailAlloc_1946_, sizeof(void*)*1 + 2, v_persistent_1934_);
v___x_1944_ = v_reuseFailAlloc_1946_;
goto v_reusejp_1943_;
}
v_reusejp_1943_:
{
lean_object* v___x_1945_; 
lean_ctor_set_uint8(v___x_1944_, sizeof(void*)*1, v___x_1939_);
lean_ctor_set_uint8(v___x_1944_, sizeof(void*)*1 + 1, v___x_1940_);
v___x_1945_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_discr_1910_, v___x_1944_, v_varMap_1922_);
v___y_1926_ = v___x_1945_;
goto v___jp_1925_;
}
}
}
v___jp_1925_:
{
lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; 
v___x_1927_ = lean_unsigned_to_nat(1u);
v___x_1928_ = lean_nat_add(v_idx_1924_, v___x_1927_);
lean_dec(v_idx_1924_);
v___x_1929_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1929_, 0, v_borrowedParams_1920_);
lean_ctor_set(v___x_1929_, 1, v_derivedValMap_1921_);
lean_ctor_set(v___x_1929_, 2, v___y_1926_);
lean_ctor_set(v___x_1929_, 3, v_jpLiveVarMap_1923_);
lean_ctor_set(v___x_1929_, 4, v___x_1928_);
lean_inc(v_a_1918_);
lean_inc_ref(v_a_1917_);
lean_inc(v_a_1916_);
lean_inc_ref(v_a_1915_);
lean_inc(v_a_1914_);
v___x_1930_ = lean_apply_7(v_x_1912_, v___x_1929_, v_a_1914_, v_a_1915_, v_a_1916_, v_a_1917_, v_a_1918_, lean_box(0));
return v___x_1930_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withCtorAlt___redArg___boxed(lean_object* v_discr_1949_, lean_object* v_c_1950_, lean_object* v_x_1951_, lean_object* v_a_1952_, lean_object* v_a_1953_, lean_object* v_a_1954_, lean_object* v_a_1955_, lean_object* v_a_1956_, lean_object* v_a_1957_, lean_object* v_a_1958_){
_start:
{
lean_object* v_res_1959_; 
v_res_1959_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withCtorAlt___redArg(v_discr_1949_, v_c_1950_, v_x_1951_, v_a_1952_, v_a_1953_, v_a_1954_, v_a_1955_, v_a_1956_, v_a_1957_);
lean_dec(v_a_1957_);
lean_dec_ref(v_a_1956_);
lean_dec(v_a_1955_);
lean_dec_ref(v_a_1954_);
lean_dec(v_a_1953_);
lean_dec_ref(v_c_1950_);
return v_res_1959_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withCtorAlt(lean_object* v_00_u03b1_1960_, lean_object* v_discr_1961_, lean_object* v_c_1962_, lean_object* v_x_1963_, lean_object* v_a_1964_, lean_object* v_a_1965_, lean_object* v_a_1966_, lean_object* v_a_1967_, lean_object* v_a_1968_, lean_object* v_a_1969_){
_start:
{
lean_object* v_borrowedParams_1971_; lean_object* v_derivedValMap_1972_; lean_object* v_varMap_1973_; lean_object* v_jpLiveVarMap_1974_; lean_object* v_idx_1975_; lean_object* v___y_1977_; lean_object* v___f_1982_; lean_object* v___x_1983_; 
v_borrowedParams_1971_ = lean_ctor_get(v_a_1964_, 0);
lean_inc_ref(v_borrowedParams_1971_);
v_derivedValMap_1972_ = lean_ctor_get(v_a_1964_, 1);
lean_inc_ref(v_derivedValMap_1972_);
v_varMap_1973_ = lean_ctor_get(v_a_1964_, 2);
lean_inc(v_varMap_1973_);
v_jpLiveVarMap_1974_ = lean_ctor_get(v_a_1964_, 3);
lean_inc(v_jpLiveVarMap_1974_);
v_idx_1975_ = lean_ctor_get(v_a_1964_, 4);
lean_inc(v_idx_1975_);
lean_dec_ref(v_a_1964_);
v___f_1982_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getVarInfo___redArg___closed__0));
lean_inc(v_discr_1961_);
lean_inc(v_varMap_1973_);
v___x_1983_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v___f_1982_, v_varMap_1973_, v_discr_1961_);
if (lean_obj_tag(v___x_1983_) == 0)
{
lean_dec(v_discr_1961_);
v___y_1977_ = v_varMap_1973_;
goto v___jp_1976_;
}
else
{
lean_object* v_val_1984_; uint8_t v_persistent_1985_; lean_object* v___x_1987_; uint8_t v_isShared_1988_; uint8_t v_isSharedCheck_1998_; 
v_val_1984_ = lean_ctor_get(v___x_1983_, 0);
lean_inc(v_val_1984_);
lean_dec_ref(v___x_1983_);
v_persistent_1985_ = lean_ctor_get_uint8(v_val_1984_, sizeof(void*)*1 + 2);
v_isSharedCheck_1998_ = !lean_is_exclusive(v_val_1984_);
if (v_isSharedCheck_1998_ == 0)
{
lean_object* v_unused_1999_; 
v_unused_1999_ = lean_ctor_get(v_val_1984_, 0);
lean_dec(v_unused_1999_);
v___x_1987_ = v_val_1984_;
v_isShared_1988_ = v_isSharedCheck_1998_;
goto v_resetjp_1986_;
}
else
{
lean_dec(v_val_1984_);
v___x_1987_ = lean_box(0);
v_isShared_1988_ = v_isSharedCheck_1998_;
goto v_resetjp_1986_;
}
v_resetjp_1986_:
{
lean_object* v___x_1989_; uint8_t v___x_1990_; uint8_t v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1995_; 
v___x_1989_ = l_Lean_Compiler_LCNF_CtorInfo_type(v_c_1962_);
v___x_1990_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isPossibleRef(v___x_1989_);
v___x_1991_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isDefiniteRef(v___x_1989_);
lean_dec_ref(v___x_1989_);
v___x_1992_ = lean_unsigned_to_nat(1u);
v___x_1993_ = lean_nat_add(v_idx_1975_, v___x_1992_);
if (v_isShared_1988_ == 0)
{
lean_ctor_set(v___x_1987_, 0, v___x_1993_);
v___x_1995_ = v___x_1987_;
goto v_reusejp_1994_;
}
else
{
lean_object* v_reuseFailAlloc_1997_; 
v_reuseFailAlloc_1997_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v_reuseFailAlloc_1997_, 0, v___x_1993_);
lean_ctor_set_uint8(v_reuseFailAlloc_1997_, sizeof(void*)*1 + 2, v_persistent_1985_);
v___x_1995_ = v_reuseFailAlloc_1997_;
goto v_reusejp_1994_;
}
v_reusejp_1994_:
{
lean_object* v___x_1996_; 
lean_ctor_set_uint8(v___x_1995_, sizeof(void*)*1, v___x_1990_);
lean_ctor_set_uint8(v___x_1995_, sizeof(void*)*1 + 1, v___x_1991_);
v___x_1996_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_discr_1961_, v___x_1995_, v_varMap_1973_);
v___y_1977_ = v___x_1996_;
goto v___jp_1976_;
}
}
}
v___jp_1976_:
{
lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; 
v___x_1978_ = lean_unsigned_to_nat(1u);
v___x_1979_ = lean_nat_add(v_idx_1975_, v___x_1978_);
lean_dec(v_idx_1975_);
v___x_1980_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1980_, 0, v_borrowedParams_1971_);
lean_ctor_set(v___x_1980_, 1, v_derivedValMap_1972_);
lean_ctor_set(v___x_1980_, 2, v___y_1977_);
lean_ctor_set(v___x_1980_, 3, v_jpLiveVarMap_1974_);
lean_ctor_set(v___x_1980_, 4, v___x_1979_);
lean_inc(v_a_1969_);
lean_inc_ref(v_a_1968_);
lean_inc(v_a_1967_);
lean_inc_ref(v_a_1966_);
lean_inc(v_a_1965_);
v___x_1981_ = lean_apply_7(v_x_1963_, v___x_1980_, v_a_1965_, v_a_1966_, v_a_1967_, v_a_1968_, v_a_1969_, lean_box(0));
return v___x_1981_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withCtorAlt___boxed(lean_object* v_00_u03b1_2000_, lean_object* v_discr_2001_, lean_object* v_c_2002_, lean_object* v_x_2003_, lean_object* v_a_2004_, lean_object* v_a_2005_, lean_object* v_a_2006_, lean_object* v_a_2007_, lean_object* v_a_2008_, lean_object* v_a_2009_, lean_object* v_a_2010_){
_start:
{
lean_object* v_res_2011_; 
v_res_2011_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withCtorAlt(v_00_u03b1_2000_, v_discr_2001_, v_c_2002_, v_x_2003_, v_a_2004_, v_a_2005_, v_a_2006_, v_a_2007_, v_a_2008_, v_a_2009_);
lean_dec(v_a_2009_);
lean_dec_ref(v_a_2008_);
lean_dec(v_a_2007_);
lean_dec_ref(v_a_2006_);
lean_dec(v_a_2005_);
lean_dec_ref(v_c_2002_);
return v_res_2011_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withCollectLiveVars___redArg(lean_object* v_x_2012_, lean_object* v_a_2013_, lean_object* v_a_2014_, lean_object* v_a_2015_, lean_object* v_a_2016_, lean_object* v_a_2017_, lean_object* v_a_2018_){
_start:
{
lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; 
v___x_2020_ = lean_st_ref_get(v_a_2014_);
v___x_2021_ = lean_st_ref_take(v_a_2014_);
lean_dec(v___x_2021_);
v___x_2022_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__0, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__0_once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__0);
v___x_2023_ = lean_st_ref_set(v_a_2014_, v___x_2022_);
lean_inc(v_a_2018_);
lean_inc_ref(v_a_2017_);
lean_inc(v_a_2016_);
lean_inc_ref(v_a_2015_);
lean_inc(v_a_2014_);
lean_inc_ref(v_a_2013_);
v___x_2024_ = lean_apply_7(v_x_2012_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_, v_a_2018_, lean_box(0));
if (lean_obj_tag(v___x_2024_) == 0)
{
lean_object* v_a_2025_; lean_object* v___x_2027_; uint8_t v_isShared_2028_; uint8_t v_isSharedCheck_2036_; 
v_a_2025_ = lean_ctor_get(v___x_2024_, 0);
v_isSharedCheck_2036_ = !lean_is_exclusive(v___x_2024_);
if (v_isSharedCheck_2036_ == 0)
{
v___x_2027_ = v___x_2024_;
v_isShared_2028_ = v_isSharedCheck_2036_;
goto v_resetjp_2026_;
}
else
{
lean_inc(v_a_2025_);
lean_dec(v___x_2024_);
v___x_2027_ = lean_box(0);
v_isShared_2028_ = v_isSharedCheck_2036_;
goto v_resetjp_2026_;
}
v_resetjp_2026_:
{
lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2034_; 
v___x_2029_ = lean_st_ref_get(v_a_2014_);
v___x_2030_ = lean_st_ref_take(v_a_2014_);
lean_dec(v___x_2030_);
v___x_2031_ = lean_st_ref_set(v_a_2014_, v___x_2020_);
v___x_2032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2032_, 0, v_a_2025_);
lean_ctor_set(v___x_2032_, 1, v___x_2029_);
if (v_isShared_2028_ == 0)
{
lean_ctor_set(v___x_2027_, 0, v___x_2032_);
v___x_2034_ = v___x_2027_;
goto v_reusejp_2033_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v___x_2032_);
v___x_2034_ = v_reuseFailAlloc_2035_;
goto v_reusejp_2033_;
}
v_reusejp_2033_:
{
return v___x_2034_;
}
}
}
else
{
lean_object* v_a_2037_; lean_object* v___x_2039_; uint8_t v_isShared_2040_; uint8_t v_isSharedCheck_2044_; 
lean_dec(v___x_2020_);
v_a_2037_ = lean_ctor_get(v___x_2024_, 0);
v_isSharedCheck_2044_ = !lean_is_exclusive(v___x_2024_);
if (v_isSharedCheck_2044_ == 0)
{
v___x_2039_ = v___x_2024_;
v_isShared_2040_ = v_isSharedCheck_2044_;
goto v_resetjp_2038_;
}
else
{
lean_inc(v_a_2037_);
lean_dec(v___x_2024_);
v___x_2039_ = lean_box(0);
v_isShared_2040_ = v_isSharedCheck_2044_;
goto v_resetjp_2038_;
}
v_resetjp_2038_:
{
lean_object* v___x_2042_; 
if (v_isShared_2040_ == 0)
{
v___x_2042_ = v___x_2039_;
goto v_reusejp_2041_;
}
else
{
lean_object* v_reuseFailAlloc_2043_; 
v_reuseFailAlloc_2043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2043_, 0, v_a_2037_);
v___x_2042_ = v_reuseFailAlloc_2043_;
goto v_reusejp_2041_;
}
v_reusejp_2041_:
{
return v___x_2042_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withCollectLiveVars___redArg___boxed(lean_object* v_x_2045_, lean_object* v_a_2046_, lean_object* v_a_2047_, lean_object* v_a_2048_, lean_object* v_a_2049_, lean_object* v_a_2050_, lean_object* v_a_2051_, lean_object* v_a_2052_){
_start:
{
lean_object* v_res_2053_; 
v_res_2053_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withCollectLiveVars___redArg(v_x_2045_, v_a_2046_, v_a_2047_, v_a_2048_, v_a_2049_, v_a_2050_, v_a_2051_);
lean_dec(v_a_2051_);
lean_dec_ref(v_a_2050_);
lean_dec(v_a_2049_);
lean_dec_ref(v_a_2048_);
lean_dec(v_a_2047_);
lean_dec_ref(v_a_2046_);
return v_res_2053_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withCollectLiveVars(lean_object* v_00_u03b1_2054_, lean_object* v_x_2055_, lean_object* v_a_2056_, lean_object* v_a_2057_, lean_object* v_a_2058_, lean_object* v_a_2059_, lean_object* v_a_2060_, lean_object* v_a_2061_){
_start:
{
lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; 
v___x_2063_ = lean_st_ref_get(v_a_2057_);
v___x_2064_ = lean_st_ref_take(v_a_2057_);
lean_dec(v___x_2064_);
v___x_2065_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__0, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__0_once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__0);
v___x_2066_ = lean_st_ref_set(v_a_2057_, v___x_2065_);
lean_inc(v_a_2061_);
lean_inc_ref(v_a_2060_);
lean_inc(v_a_2059_);
lean_inc_ref(v_a_2058_);
lean_inc(v_a_2057_);
lean_inc_ref(v_a_2056_);
v___x_2067_ = lean_apply_7(v_x_2055_, v_a_2056_, v_a_2057_, v_a_2058_, v_a_2059_, v_a_2060_, v_a_2061_, lean_box(0));
if (lean_obj_tag(v___x_2067_) == 0)
{
lean_object* v_a_2068_; lean_object* v___x_2070_; uint8_t v_isShared_2071_; uint8_t v_isSharedCheck_2079_; 
v_a_2068_ = lean_ctor_get(v___x_2067_, 0);
v_isSharedCheck_2079_ = !lean_is_exclusive(v___x_2067_);
if (v_isSharedCheck_2079_ == 0)
{
v___x_2070_ = v___x_2067_;
v_isShared_2071_ = v_isSharedCheck_2079_;
goto v_resetjp_2069_;
}
else
{
lean_inc(v_a_2068_);
lean_dec(v___x_2067_);
v___x_2070_ = lean_box(0);
v_isShared_2071_ = v_isSharedCheck_2079_;
goto v_resetjp_2069_;
}
v_resetjp_2069_:
{
lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2077_; 
v___x_2072_ = lean_st_ref_get(v_a_2057_);
v___x_2073_ = lean_st_ref_take(v_a_2057_);
lean_dec(v___x_2073_);
v___x_2074_ = lean_st_ref_set(v_a_2057_, v___x_2063_);
v___x_2075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2075_, 0, v_a_2068_);
lean_ctor_set(v___x_2075_, 1, v___x_2072_);
if (v_isShared_2071_ == 0)
{
lean_ctor_set(v___x_2070_, 0, v___x_2075_);
v___x_2077_ = v___x_2070_;
goto v_reusejp_2076_;
}
else
{
lean_object* v_reuseFailAlloc_2078_; 
v_reuseFailAlloc_2078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2078_, 0, v___x_2075_);
v___x_2077_ = v_reuseFailAlloc_2078_;
goto v_reusejp_2076_;
}
v_reusejp_2076_:
{
return v___x_2077_;
}
}
}
else
{
lean_object* v_a_2080_; lean_object* v___x_2082_; uint8_t v_isShared_2083_; uint8_t v_isSharedCheck_2087_; 
lean_dec(v___x_2063_);
v_a_2080_ = lean_ctor_get(v___x_2067_, 0);
v_isSharedCheck_2087_ = !lean_is_exclusive(v___x_2067_);
if (v_isSharedCheck_2087_ == 0)
{
v___x_2082_ = v___x_2067_;
v_isShared_2083_ = v_isSharedCheck_2087_;
goto v_resetjp_2081_;
}
else
{
lean_inc(v_a_2080_);
lean_dec(v___x_2067_);
v___x_2082_ = lean_box(0);
v_isShared_2083_ = v_isSharedCheck_2087_;
goto v_resetjp_2081_;
}
v_resetjp_2081_:
{
lean_object* v___x_2085_; 
if (v_isShared_2083_ == 0)
{
v___x_2085_ = v___x_2082_;
goto v_reusejp_2084_;
}
else
{
lean_object* v_reuseFailAlloc_2086_; 
v_reuseFailAlloc_2086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2086_, 0, v_a_2080_);
v___x_2085_ = v_reuseFailAlloc_2086_;
goto v_reusejp_2084_;
}
v_reusejp_2084_:
{
return v___x_2085_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withCollectLiveVars___boxed(lean_object* v_00_u03b1_2088_, lean_object* v_x_2089_, lean_object* v_a_2090_, lean_object* v_a_2091_, lean_object* v_a_2092_, lean_object* v_a_2093_, lean_object* v_a_2094_, lean_object* v_a_2095_, lean_object* v_a_2096_){
_start:
{
lean_object* v_res_2097_; 
v_res_2097_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withCollectLiveVars(v_00_u03b1_2088_, v_x_2089_, v_a_2090_, v_a_2091_, v_a_2092_, v_a_2093_, v_a_2094_, v_a_2095_);
lean_dec(v_a_2095_);
lean_dec_ref(v_a_2094_);
lean_dec(v_a_2093_);
lean_dec_ref(v_a_2092_);
lean_dec(v_a_2091_);
lean_dec_ref(v_a_2090_);
return v_res_2097_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendantsAux_spec__1(lean_object* v_x1_2098_, lean_object* v_as_2099_, size_t v_i_2100_, size_t v_stop_2101_){
_start:
{
uint8_t v___x_2102_; 
v___x_2102_ = lean_usize_dec_eq(v_i_2100_, v_stop_2101_);
if (v___x_2102_ == 0)
{
uint8_t v___x_2103_; lean_object* v___x_2104_; uint8_t v___x_2105_; 
v___x_2103_ = 1;
v___x_2104_ = lean_array_uget_borrowed(v_as_2099_, v_i_2100_);
v___x_2105_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_isAccessible(v_x1_2098_, v___x_2104_);
if (v___x_2105_ == 0)
{
return v___x_2103_;
}
else
{
if (v___x_2102_ == 0)
{
size_t v___x_2106_; size_t v___x_2107_; 
v___x_2106_ = ((size_t)1ULL);
v___x_2107_ = lean_usize_add(v_i_2100_, v___x_2106_);
v_i_2100_ = v___x_2107_;
goto _start;
}
else
{
return v___x_2103_;
}
}
}
else
{
uint8_t v___x_2109_; 
v___x_2109_ = 0;
return v___x_2109_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendantsAux_spec__1___boxed(lean_object* v_x1_2110_, lean_object* v_as_2111_, lean_object* v_i_2112_, lean_object* v_stop_2113_){
_start:
{
size_t v_i_boxed_2114_; size_t v_stop_boxed_2115_; uint8_t v_res_2116_; lean_object* v_r_2117_; 
v_i_boxed_2114_ = lean_unbox_usize(v_i_2112_);
lean_dec(v_i_2112_);
v_stop_boxed_2115_ = lean_unbox_usize(v_stop_2113_);
lean_dec(v_stop_2113_);
v_res_2116_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendantsAux_spec__1(v_x1_2110_, v_as_2111_, v_i_boxed_2114_, v_stop_boxed_2115_);
lean_dec_ref(v_as_2111_);
lean_dec_ref(v_x1_2110_);
v_r_2117_ = lean_box(v_res_2116_);
return v_r_2117_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendantsAux_spec__0_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; 
v___x_2121_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendantsAux_spec__0_spec__0___redArg___closed__2));
v___x_2122_ = lean_unsigned_to_nat(11u);
v___x_2123_ = lean_unsigned_to_nat(163u);
v___x_2124_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendantsAux_spec__0_spec__0___redArg___closed__1));
v___x_2125_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendantsAux_spec__0_spec__0___redArg___closed__0));
v___x_2126_ = l_mkPanicMessageWithDecl(v___x_2125_, v___x_2124_, v___x_2123_, v___x_2122_, v___x_2121_);
return v___x_2126_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendantsAux_spec__0_spec__0___redArg(lean_object* v_inst_2127_, lean_object* v_a_2128_, lean_object* v_x_2129_){
_start:
{
if (lean_obj_tag(v_x_2129_) == 0)
{
lean_object* v___x_2130_; lean_object* v___x_2131_; 
v___x_2130_ = lean_obj_once(&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendantsAux_spec__0_spec__0___redArg___closed__3, &l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendantsAux_spec__0_spec__0___redArg___closed__3_once, _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendantsAux_spec__0_spec__0___redArg___closed__3);
v___x_2131_ = lean_panic_fn(v_inst_2127_, v___x_2130_);
return v___x_2131_;
}
else
{
lean_object* v_key_2132_; lean_object* v_value_2133_; lean_object* v_tail_2134_; uint8_t v___x_2135_; 
v_key_2132_ = lean_ctor_get(v_x_2129_, 0);
v_value_2133_ = lean_ctor_get(v_x_2129_, 1);
v_tail_2134_ = lean_ctor_get(v_x_2129_, 2);
v___x_2135_ = l_Lean_instBEqFVarId_beq(v_key_2132_, v_a_2128_);
if (v___x_2135_ == 0)
{
v_x_2129_ = v_tail_2134_;
goto _start;
}
else
{
lean_dec(v_inst_2127_);
lean_inc(v_value_2133_);
return v_value_2133_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendantsAux_spec__0_spec__0___redArg___boxed(lean_object* v_inst_2137_, lean_object* v_a_2138_, lean_object* v_x_2139_){
_start:
{
lean_object* v_res_2140_; 
v_res_2140_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendantsAux_spec__0_spec__0___redArg(v_inst_2137_, v_a_2138_, v_x_2139_);
lean_dec(v_x_2139_);
lean_dec(v_a_2138_);
return v_res_2140_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendantsAux_spec__0___redArg(lean_object* v_inst_2141_, lean_object* v_m_2142_, lean_object* v_a_2143_){
_start:
{
lean_object* v_buckets_2144_; lean_object* v___x_2145_; uint64_t v___x_2146_; uint64_t v___x_2147_; uint64_t v___x_2148_; uint64_t v_fold_2149_; uint64_t v___x_2150_; uint64_t v___x_2151_; uint64_t v___x_2152_; size_t v___x_2153_; size_t v___x_2154_; size_t v___x_2155_; size_t v___x_2156_; size_t v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; 
v_buckets_2144_ = lean_ctor_get(v_m_2142_, 1);
v___x_2145_ = lean_array_get_size(v_buckets_2144_);
v___x_2146_ = l_Lean_instHashableFVarId_hash(v_a_2143_);
v___x_2147_ = 32ULL;
v___x_2148_ = lean_uint64_shift_right(v___x_2146_, v___x_2147_);
v_fold_2149_ = lean_uint64_xor(v___x_2146_, v___x_2148_);
v___x_2150_ = 16ULL;
v___x_2151_ = lean_uint64_shift_right(v_fold_2149_, v___x_2150_);
v___x_2152_ = lean_uint64_xor(v_fold_2149_, v___x_2151_);
v___x_2153_ = lean_uint64_to_usize(v___x_2152_);
v___x_2154_ = lean_usize_of_nat(v___x_2145_);
v___x_2155_ = ((size_t)1ULL);
v___x_2156_ = lean_usize_sub(v___x_2154_, v___x_2155_);
v___x_2157_ = lean_usize_land(v___x_2153_, v___x_2156_);
v___x_2158_ = lean_array_uget_borrowed(v_buckets_2144_, v___x_2157_);
v___x_2159_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendantsAux_spec__0_spec__0___redArg(v_inst_2141_, v_a_2143_, v___x_2158_);
return v___x_2159_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendantsAux_spec__0___redArg___boxed(lean_object* v_inst_2160_, lean_object* v_m_2161_, lean_object* v_a_2162_){
_start:
{
lean_object* v_res_2163_; 
v_res_2163_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendantsAux_spec__0___redArg(v_inst_2160_, v_m_2161_, v_a_2162_);
lean_dec(v_a_2162_);
lean_dec_ref(v_m_2161_);
return v_res_2163_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendantsAux(lean_object* v_info_2164_, lean_object* v_derivedValMap_2165_, lean_object* v_liveVars_2166_){
_start:
{
lean_object* v_children_2167_; lean_object* v_buckets_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; uint8_t v___x_2171_; 
v_children_2167_ = lean_ctor_get(v_info_2164_, 1);
v_buckets_2168_ = lean_ctor_get(v_children_2167_, 1);
v___x_2169_ = lean_unsigned_to_nat(0u);
v___x_2170_ = lean_array_get_size(v_buckets_2168_);
v___x_2171_ = lean_nat_dec_lt(v___x_2169_, v___x_2170_);
if (v___x_2171_ == 0)
{
return v_liveVars_2166_;
}
else
{
uint8_t v___x_2172_; 
v___x_2172_ = lean_nat_dec_le(v___x_2170_, v___x_2170_);
if (v___x_2172_ == 0)
{
if (v___x_2171_ == 0)
{
return v_liveVars_2166_;
}
else
{
size_t v___x_2173_; size_t v___x_2174_; lean_object* v___x_2175_; 
v___x_2173_ = ((size_t)0ULL);
v___x_2174_ = lean_usize_of_nat(v___x_2170_);
v___x_2175_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendantsAux_spec__3(v_derivedValMap_2165_, v_buckets_2168_, v___x_2173_, v___x_2174_, v_liveVars_2166_);
return v___x_2175_;
}
}
else
{
size_t v___x_2176_; size_t v___x_2177_; lean_object* v___x_2178_; 
v___x_2176_ = ((size_t)0ULL);
v___x_2177_ = lean_usize_of_nat(v___x_2170_);
v___x_2178_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendantsAux_spec__3(v_derivedValMap_2165_, v_buckets_2168_, v___x_2176_, v___x_2177_, v_liveVars_2166_);
return v___x_2178_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendantsAux_spec__2(lean_object* v_derivedValMap_2179_, lean_object* v_x_2180_, lean_object* v_x_2181_){
_start:
{
if (lean_obj_tag(v_x_2181_) == 0)
{
return v_x_2180_;
}
else
{
lean_object* v_key_2182_; lean_object* v_tail_2183_; lean_object* v___x_2184_; lean_object* v_info_2185_; lean_object* v_parents_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; uint8_t v___x_2208_; 
v_key_2182_ = lean_ctor_get(v_x_2181_, 0);
lean_inc(v_key_2182_);
v_tail_2183_ = lean_ctor_get(v_x_2181_, 2);
lean_inc(v_tail_2183_);
lean_dec_ref(v_x_2181_);
v___x_2184_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_instInhabitedDerivedValInfo_default;
v_info_2185_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendantsAux_spec__0___redArg(v___x_2184_, v_derivedValMap_2179_, v_key_2182_);
v_parents_2205_ = lean_ctor_get(v_info_2185_, 0);
lean_inc_ref(v_parents_2205_);
v___x_2206_ = lean_unsigned_to_nat(0u);
v___x_2207_ = lean_array_get_size(v_parents_2205_);
v___x_2208_ = lean_nat_dec_lt(v___x_2206_, v___x_2207_);
if (v___x_2208_ == 0)
{
lean_dec_ref(v_parents_2205_);
goto v___jp_2186_;
}
else
{
if (v___x_2208_ == 0)
{
lean_dec_ref(v_parents_2205_);
goto v___jp_2186_;
}
else
{
size_t v___x_2209_; size_t v___x_2210_; uint8_t v___x_2211_; 
v___x_2209_ = ((size_t)0ULL);
v___x_2210_ = lean_usize_of_nat(v___x_2207_);
v___x_2211_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendantsAux_spec__1(v_x_2180_, v_parents_2205_, v___x_2209_, v___x_2210_);
lean_dec_ref(v_parents_2205_);
if (v___x_2211_ == 0)
{
goto v___jp_2186_;
}
else
{
lean_object* v___x_2212_; 
lean_dec(v_key_2182_);
v___x_2212_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendantsAux(v_info_2185_, v_derivedValMap_2179_, v_x_2180_);
lean_dec(v_info_2185_);
v_x_2180_ = v___x_2212_;
v_x_2181_ = v_tail_2183_;
goto _start;
}
}
}
v___jp_2186_:
{
lean_object* v_vars_2187_; lean_object* v_borrows_2188_; uint8_t v___x_2189_; 
v_vars_2187_ = lean_ctor_get(v_x_2180_, 0);
v_borrows_2188_ = lean_ctor_get(v_x_2180_, 1);
v___x_2189_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_isAccessible_spec__0___redArg(v_vars_2187_, v_key_2182_);
if (v___x_2189_ == 0)
{
lean_object* v___x_2191_; uint8_t v_isShared_2192_; uint8_t v_isSharedCheck_2200_; 
lean_inc_ref(v_borrows_2188_);
lean_inc_ref(v_vars_2187_);
v_isSharedCheck_2200_ = !lean_is_exclusive(v_x_2180_);
if (v_isSharedCheck_2200_ == 0)
{
lean_object* v_unused_2201_; lean_object* v_unused_2202_; 
v_unused_2201_ = lean_ctor_get(v_x_2180_, 1);
lean_dec(v_unused_2201_);
v_unused_2202_ = lean_ctor_get(v_x_2180_, 0);
lean_dec(v_unused_2202_);
v___x_2191_ = v_x_2180_;
v_isShared_2192_ = v_isSharedCheck_2200_;
goto v_resetjp_2190_;
}
else
{
lean_dec(v_x_2180_);
v___x_2191_ = lean_box(0);
v_isShared_2192_ = v_isSharedCheck_2200_;
goto v_resetjp_2190_;
}
v_resetjp_2190_:
{
lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2196_; 
v___x_2193_ = lean_box(0);
v___x_2194_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__1___redArg(v_borrows_2188_, v_key_2182_, v___x_2193_);
if (v_isShared_2192_ == 0)
{
lean_ctor_set(v___x_2191_, 1, v___x_2194_);
v___x_2196_ = v___x_2191_;
goto v_reusejp_2195_;
}
else
{
lean_object* v_reuseFailAlloc_2199_; 
v_reuseFailAlloc_2199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2199_, 0, v_vars_2187_);
lean_ctor_set(v_reuseFailAlloc_2199_, 1, v___x_2194_);
v___x_2196_ = v_reuseFailAlloc_2199_;
goto v_reusejp_2195_;
}
v_reusejp_2195_:
{
lean_object* v___x_2197_; 
v___x_2197_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendantsAux(v_info_2185_, v_derivedValMap_2179_, v___x_2196_);
lean_dec(v_info_2185_);
v_x_2180_ = v___x_2197_;
v_x_2181_ = v_tail_2183_;
goto _start;
}
}
}
else
{
lean_object* v___x_2203_; 
lean_dec(v_key_2182_);
v___x_2203_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendantsAux(v_info_2185_, v_derivedValMap_2179_, v_x_2180_);
lean_dec(v_info_2185_);
v_x_2180_ = v___x_2203_;
v_x_2181_ = v_tail_2183_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendantsAux_spec__3(lean_object* v_derivedValMap_2214_, lean_object* v_as_2215_, size_t v_i_2216_, size_t v_stop_2217_, lean_object* v_b_2218_){
_start:
{
uint8_t v___x_2219_; 
v___x_2219_ = lean_usize_dec_eq(v_i_2216_, v_stop_2217_);
if (v___x_2219_ == 0)
{
lean_object* v___x_2220_; lean_object* v___x_2221_; size_t v___x_2222_; size_t v___x_2223_; 
v___x_2220_ = lean_array_uget_borrowed(v_as_2215_, v_i_2216_);
lean_inc(v___x_2220_);
v___x_2221_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendantsAux_spec__2(v_derivedValMap_2214_, v_b_2218_, v___x_2220_);
v___x_2222_ = ((size_t)1ULL);
v___x_2223_ = lean_usize_add(v_i_2216_, v___x_2222_);
v_i_2216_ = v___x_2223_;
v_b_2218_ = v___x_2221_;
goto _start;
}
else
{
return v_b_2218_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendantsAux_spec__3___boxed(lean_object* v_derivedValMap_2225_, lean_object* v_as_2226_, lean_object* v_i_2227_, lean_object* v_stop_2228_, lean_object* v_b_2229_){
_start:
{
size_t v_i_boxed_2230_; size_t v_stop_boxed_2231_; lean_object* v_res_2232_; 
v_i_boxed_2230_ = lean_unbox_usize(v_i_2227_);
lean_dec(v_i_2227_);
v_stop_boxed_2231_ = lean_unbox_usize(v_stop_2228_);
lean_dec(v_stop_2228_);
v_res_2232_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendantsAux_spec__3(v_derivedValMap_2225_, v_as_2226_, v_i_boxed_2230_, v_stop_boxed_2231_, v_b_2229_);
lean_dec_ref(v_as_2226_);
lean_dec_ref(v_derivedValMap_2225_);
return v_res_2232_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendantsAux___boxed(lean_object* v_info_2233_, lean_object* v_derivedValMap_2234_, lean_object* v_liveVars_2235_){
_start:
{
lean_object* v_res_2236_; 
v_res_2236_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendantsAux(v_info_2233_, v_derivedValMap_2234_, v_liveVars_2235_);
lean_dec_ref(v_derivedValMap_2234_);
lean_dec_ref(v_info_2233_);
return v_res_2236_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendantsAux_spec__2___boxed(lean_object* v_derivedValMap_2237_, lean_object* v_x_2238_, lean_object* v_x_2239_){
_start:
{
lean_object* v_res_2240_; 
v_res_2240_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendantsAux_spec__2(v_derivedValMap_2237_, v_x_2238_, v_x_2239_);
lean_dec_ref(v_derivedValMap_2237_);
return v_res_2240_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendantsAux_spec__0(lean_object* v_00_u03b2_2241_, lean_object* v_inst_2242_, lean_object* v_m_2243_, lean_object* v_a_2244_){
_start:
{
lean_object* v___x_2245_; 
v___x_2245_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendantsAux_spec__0___redArg(v_inst_2242_, v_m_2243_, v_a_2244_);
return v___x_2245_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendantsAux_spec__0___boxed(lean_object* v_00_u03b2_2246_, lean_object* v_inst_2247_, lean_object* v_m_2248_, lean_object* v_a_2249_){
_start:
{
lean_object* v_res_2250_; 
v_res_2250_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendantsAux_spec__0(v_00_u03b2_2246_, v_inst_2247_, v_m_2248_, v_a_2249_);
lean_dec(v_a_2249_);
lean_dec_ref(v_m_2248_);
return v_res_2250_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendantsAux_spec__0_spec__0_spec__1___redArg(lean_object* v_inst_2251_, lean_object* v_msg_2252_){
_start:
{
lean_object* v___x_2253_; 
v___x_2253_ = lean_panic_fn(v_inst_2251_, v_msg_2252_);
return v___x_2253_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendantsAux_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2254_, lean_object* v_inst_2255_, lean_object* v_msg_2256_){
_start:
{
lean_object* v___x_2257_; 
v___x_2257_ = lean_panic_fn(v_inst_2255_, v_msg_2256_);
return v___x_2257_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendantsAux_spec__0_spec__0(lean_object* v_00_u03b2_2258_, lean_object* v_inst_2259_, lean_object* v_a_2260_, lean_object* v_x_2261_){
_start:
{
lean_object* v___x_2262_; 
v___x_2262_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendantsAux_spec__0_spec__0___redArg(v_inst_2259_, v_a_2260_, v_x_2261_);
return v___x_2262_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendantsAux_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2263_, lean_object* v_inst_2264_, lean_object* v_a_2265_, lean_object* v_x_2266_){
_start:
{
lean_object* v_res_2267_; 
v_res_2267_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendantsAux_spec__0_spec__0(v_00_u03b2_2263_, v_inst_2264_, v_a_2265_, v_x_2266_);
lean_dec(v_x_2266_);
lean_dec(v_a_2265_);
return v_res_2267_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants(lean_object* v_fvarId_2268_, lean_object* v_derivedValMap_2269_, lean_object* v_liveVars_2270_){
_start:
{
lean_object* v___x_2271_; 
v___x_2271_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_removeFromParent_spec__1___redArg(v_derivedValMap_2269_, v_fvarId_2268_);
if (lean_obj_tag(v___x_2271_) == 1)
{
lean_object* v_val_2272_; lean_object* v___x_2273_; 
v_val_2272_ = lean_ctor_get(v___x_2271_, 0);
lean_inc(v_val_2272_);
lean_dec_ref(v___x_2271_);
v___x_2273_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendantsAux(v_val_2272_, v_derivedValMap_2269_, v_liveVars_2270_);
lean_dec(v_val_2272_);
return v___x_2273_;
}
else
{
lean_dec(v___x_2271_);
return v_liveVars_2270_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___boxed(lean_object* v_fvarId_2274_, lean_object* v_derivedValMap_2275_, lean_object* v_liveVars_2276_){
_start:
{
lean_object* v_res_2277_; 
v_res_2277_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants(v_fvarId_2274_, v_derivedValMap_2275_, v_liveVars_2276_);
lean_dec_ref(v_derivedValMap_2275_);
lean_dec(v_fvarId_2274_);
return v_res_2277_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_markLive___redArg(lean_object* v_fvarId_2278_, lean_object* v_a_2279_){
_start:
{
lean_object* v___x_2281_; lean_object* v_vars_2282_; lean_object* v_borrows_2283_; lean_object* v___x_2285_; uint8_t v_isShared_2286_; uint8_t v_isSharedCheck_2294_; 
v___x_2281_ = lean_st_ref_take(v_a_2279_);
v_vars_2282_ = lean_ctor_get(v___x_2281_, 0);
v_borrows_2283_ = lean_ctor_get(v___x_2281_, 1);
v_isSharedCheck_2294_ = !lean_is_exclusive(v___x_2281_);
if (v_isSharedCheck_2294_ == 0)
{
v___x_2285_ = v___x_2281_;
v_isShared_2286_ = v_isSharedCheck_2294_;
goto v_resetjp_2284_;
}
else
{
lean_inc(v_borrows_2283_);
lean_inc(v_vars_2282_);
lean_dec(v___x_2281_);
v___x_2285_ = lean_box(0);
v_isShared_2286_ = v_isSharedCheck_2294_;
goto v_resetjp_2284_;
}
v_resetjp_2284_:
{
lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2290_; 
v___x_2287_ = lean_box(0);
v___x_2288_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__1___redArg(v_vars_2282_, v_fvarId_2278_, v___x_2287_);
if (v_isShared_2286_ == 0)
{
lean_ctor_set(v___x_2285_, 0, v___x_2288_);
v___x_2290_ = v___x_2285_;
goto v_reusejp_2289_;
}
else
{
lean_object* v_reuseFailAlloc_2293_; 
v_reuseFailAlloc_2293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2293_, 0, v___x_2288_);
lean_ctor_set(v_reuseFailAlloc_2293_, 1, v_borrows_2283_);
v___x_2290_ = v_reuseFailAlloc_2293_;
goto v_reusejp_2289_;
}
v_reusejp_2289_:
{
lean_object* v___x_2291_; lean_object* v___x_2292_; 
v___x_2291_ = lean_st_ref_set(v_a_2279_, v___x_2290_);
v___x_2292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2292_, 0, v___x_2287_);
return v___x_2292_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_markLive___redArg___boxed(lean_object* v_fvarId_2295_, lean_object* v_a_2296_, lean_object* v_a_2297_){
_start:
{
lean_object* v_res_2298_; 
v_res_2298_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_markLive___redArg(v_fvarId_2295_, v_a_2296_);
lean_dec(v_a_2296_);
return v_res_2298_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_markLive(lean_object* v_fvarId_2299_, lean_object* v_a_2300_, lean_object* v_a_2301_, lean_object* v_a_2302_, lean_object* v_a_2303_, lean_object* v_a_2304_, lean_object* v_a_2305_){
_start:
{
lean_object* v___x_2307_; 
v___x_2307_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_markLive___redArg(v_fvarId_2299_, v_a_2301_);
return v___x_2307_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_markLive___boxed(lean_object* v_fvarId_2308_, lean_object* v_a_2309_, lean_object* v_a_2310_, lean_object* v_a_2311_, lean_object* v_a_2312_, lean_object* v_a_2313_, lean_object* v_a_2314_, lean_object* v_a_2315_){
_start:
{
lean_object* v_res_2316_; 
v_res_2316_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_markLive(v_fvarId_2308_, v_a_2309_, v_a_2310_, v_a_2311_, v_a_2312_, v_a_2313_, v_a_2314_);
lean_dec(v_a_2314_);
lean_dec_ref(v_a_2313_);
lean_dec(v_a_2312_);
lean_dec_ref(v_a_2311_);
lean_dec(v_a_2310_);
lean_dec_ref(v_a_2309_);
return v_res_2316_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_markDescendantsBorrowed___redArg(lean_object* v_fvarId_2317_, lean_object* v_a_2318_, lean_object* v_a_2319_){
_start:
{
lean_object* v___x_2321_; lean_object* v_derivedValMap_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; 
v___x_2321_ = lean_st_ref_take(v_a_2319_);
v_derivedValMap_2322_ = lean_ctor_get(v_a_2318_, 1);
v___x_2323_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants(v_fvarId_2317_, v_derivedValMap_2322_, v___x_2321_);
v___x_2324_ = lean_st_ref_set(v_a_2319_, v___x_2323_);
v___x_2325_ = lean_box(0);
v___x_2326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2326_, 0, v___x_2325_);
return v___x_2326_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_markDescendantsBorrowed___redArg___boxed(lean_object* v_fvarId_2327_, lean_object* v_a_2328_, lean_object* v_a_2329_, lean_object* v_a_2330_){
_start:
{
lean_object* v_res_2331_; 
v_res_2331_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_markDescendantsBorrowed___redArg(v_fvarId_2327_, v_a_2328_, v_a_2329_);
lean_dec(v_a_2329_);
lean_dec_ref(v_a_2328_);
lean_dec(v_fvarId_2327_);
return v_res_2331_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_markDescendantsBorrowed(lean_object* v_fvarId_2332_, lean_object* v_a_2333_, lean_object* v_a_2334_, lean_object* v_a_2335_, lean_object* v_a_2336_, lean_object* v_a_2337_, lean_object* v_a_2338_){
_start:
{
lean_object* v___x_2340_; 
v___x_2340_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_markDescendantsBorrowed___redArg(v_fvarId_2332_, v_a_2333_, v_a_2334_);
return v___x_2340_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_markDescendantsBorrowed___boxed(lean_object* v_fvarId_2341_, lean_object* v_a_2342_, lean_object* v_a_2343_, lean_object* v_a_2344_, lean_object* v_a_2345_, lean_object* v_a_2346_, lean_object* v_a_2347_, lean_object* v_a_2348_){
_start:
{
lean_object* v_res_2349_; 
v_res_2349_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_markDescendantsBorrowed(v_fvarId_2341_, v_a_2342_, v_a_2343_, v_a_2344_, v_a_2345_, v_a_2346_, v_a_2347_);
lean_dec(v_a_2347_);
lean_dec_ref(v_a_2346_);
lean_dec(v_a_2345_);
lean_dec_ref(v_a_2344_);
lean_dec(v_a_2343_);
lean_dec_ref(v_a_2342_);
lean_dec(v_fvarId_2341_);
return v_res_2349_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___redArg(lean_object* v_fvarId_2350_, lean_object* v_a_2351_, lean_object* v_a_2352_){
_start:
{
lean_object* v___x_2354_; lean_object* v_vars_2355_; uint8_t v___x_2356_; 
v___x_2354_ = lean_st_ref_get(v_a_2352_);
v_vars_2355_ = lean_ctor_get(v___x_2354_, 0);
lean_inc_ref(v_vars_2355_);
lean_dec(v___x_2354_);
v___x_2356_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_isAccessible_spec__0___redArg(v_vars_2355_, v_fvarId_2350_);
lean_dec_ref(v_vars_2355_);
if (v___x_2356_ == 0)
{
lean_object* v___x_2357_; lean_object* v___x_2358_; 
lean_inc(v_fvarId_2350_);
v___x_2357_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_markLive___redArg(v_fvarId_2350_, v_a_2352_);
lean_dec_ref(v___x_2357_);
v___x_2358_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_markDescendantsBorrowed___redArg(v_fvarId_2350_, v_a_2351_, v_a_2352_);
lean_dec(v_fvarId_2350_);
return v___x_2358_;
}
else
{
lean_object* v___x_2359_; lean_object* v___x_2360_; 
lean_dec(v_fvarId_2350_);
v___x_2359_ = lean_box(0);
v___x_2360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2360_, 0, v___x_2359_);
return v___x_2360_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___redArg___boxed(lean_object* v_fvarId_2361_, lean_object* v_a_2362_, lean_object* v_a_2363_, lean_object* v_a_2364_){
_start:
{
lean_object* v_res_2365_; 
v_res_2365_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___redArg(v_fvarId_2361_, v_a_2362_, v_a_2363_);
lean_dec(v_a_2363_);
lean_dec_ref(v_a_2362_);
return v_res_2365_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar(lean_object* v_fvarId_2366_, lean_object* v_a_2367_, lean_object* v_a_2368_, lean_object* v_a_2369_, lean_object* v_a_2370_, lean_object* v_a_2371_, lean_object* v_a_2372_){
_start:
{
lean_object* v___x_2374_; 
v___x_2374_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___redArg(v_fvarId_2366_, v_a_2367_, v_a_2368_);
return v___x_2374_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___boxed(lean_object* v_fvarId_2375_, lean_object* v_a_2376_, lean_object* v_a_2377_, lean_object* v_a_2378_, lean_object* v_a_2379_, lean_object* v_a_2380_, lean_object* v_a_2381_, lean_object* v_a_2382_){
_start:
{
lean_object* v_res_2383_; 
v_res_2383_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar(v_fvarId_2375_, v_a_2376_, v_a_2377_, v_a_2378_, v_a_2379_, v_a_2380_, v_a_2381_);
lean_dec(v_a_2381_);
lean_dec_ref(v_a_2380_);
lean_dec(v_a_2379_);
lean_dec_ref(v_a_2378_);
lean_dec(v_a_2377_);
lean_dec_ref(v_a_2376_);
return v_res_2383_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__0_spec__0___redArg(lean_object* v_as_2384_, size_t v_i_2385_, size_t v_stop_2386_, lean_object* v_b_2387_, lean_object* v___y_2388_){
_start:
{
lean_object* v_a_2391_; uint8_t v___x_2395_; 
v___x_2395_ = lean_usize_dec_eq(v_i_2385_, v_stop_2386_);
if (v___x_2395_ == 0)
{
lean_object* v___x_2396_; 
v___x_2396_ = lean_array_uget_borrowed(v_as_2384_, v_i_2385_);
if (lean_obj_tag(v___x_2396_) == 0)
{
v_a_2391_ = v_b_2387_;
goto v___jp_2390_;
}
else
{
lean_object* v_fvarId_2397_; lean_object* v___x_2398_; lean_object* v_vars_2399_; uint8_t v___x_2400_; 
v_fvarId_2397_ = lean_ctor_get(v___x_2396_, 0);
v___x_2398_ = lean_st_ref_get(v___y_2388_);
v_vars_2399_ = lean_ctor_get(v___x_2398_, 0);
lean_inc_ref(v_vars_2399_);
lean_dec(v___x_2398_);
v___x_2400_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_isAccessible_spec__0___redArg(v_vars_2399_, v_fvarId_2397_);
lean_dec_ref(v_vars_2399_);
if (v___x_2400_ == 0)
{
lean_object* v___x_2401_; 
lean_inc(v_fvarId_2397_);
v___x_2401_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_markLive___redArg(v_fvarId_2397_, v___y_2388_);
if (lean_obj_tag(v___x_2401_) == 0)
{
lean_object* v___x_2402_; 
lean_dec_ref(v___x_2401_);
lean_inc(v_fvarId_2397_);
v___x_2402_ = lean_array_push(v_b_2387_, v_fvarId_2397_);
v_a_2391_ = v___x_2402_;
goto v___jp_2390_;
}
else
{
lean_object* v_a_2403_; lean_object* v___x_2405_; uint8_t v_isShared_2406_; uint8_t v_isSharedCheck_2410_; 
lean_dec_ref(v_b_2387_);
v_a_2403_ = lean_ctor_get(v___x_2401_, 0);
v_isSharedCheck_2410_ = !lean_is_exclusive(v___x_2401_);
if (v_isSharedCheck_2410_ == 0)
{
v___x_2405_ = v___x_2401_;
v_isShared_2406_ = v_isSharedCheck_2410_;
goto v_resetjp_2404_;
}
else
{
lean_inc(v_a_2403_);
lean_dec(v___x_2401_);
v___x_2405_ = lean_box(0);
v_isShared_2406_ = v_isSharedCheck_2410_;
goto v_resetjp_2404_;
}
v_resetjp_2404_:
{
lean_object* v___x_2408_; 
if (v_isShared_2406_ == 0)
{
v___x_2408_ = v___x_2405_;
goto v_reusejp_2407_;
}
else
{
lean_object* v_reuseFailAlloc_2409_; 
v_reuseFailAlloc_2409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2409_, 0, v_a_2403_);
v___x_2408_ = v_reuseFailAlloc_2409_;
goto v_reusejp_2407_;
}
v_reusejp_2407_:
{
return v___x_2408_;
}
}
}
}
else
{
v_a_2391_ = v_b_2387_;
goto v___jp_2390_;
}
}
}
else
{
lean_object* v___x_2411_; 
v___x_2411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2411_, 0, v_b_2387_);
return v___x_2411_;
}
v___jp_2390_:
{
size_t v___x_2392_; size_t v___x_2393_; 
v___x_2392_ = ((size_t)1ULL);
v___x_2393_ = lean_usize_add(v_i_2385_, v___x_2392_);
v_i_2385_ = v___x_2393_;
v_b_2387_ = v_a_2391_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__0_spec__0___redArg___boxed(lean_object* v_as_2412_, lean_object* v_i_2413_, lean_object* v_stop_2414_, lean_object* v_b_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_){
_start:
{
size_t v_i_boxed_2418_; size_t v_stop_boxed_2419_; lean_object* v_res_2420_; 
v_i_boxed_2418_ = lean_unbox_usize(v_i_2413_);
lean_dec(v_i_2413_);
v_stop_boxed_2419_ = lean_unbox_usize(v_stop_2414_);
lean_dec(v_stop_2414_);
v_res_2420_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__0_spec__0___redArg(v_as_2412_, v_i_boxed_2418_, v_stop_boxed_2419_, v_b_2415_, v___y_2416_);
lean_dec(v___y_2416_);
lean_dec_ref(v_as_2412_);
return v_res_2420_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__0(lean_object* v_as_2421_, lean_object* v_start_2422_, lean_object* v_stop_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_){
_start:
{
lean_object* v___x_2431_; uint8_t v___x_2432_; 
v___x_2431_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_visitParam___redArg___closed__2));
v___x_2432_ = lean_nat_dec_lt(v_start_2422_, v_stop_2423_);
if (v___x_2432_ == 0)
{
lean_object* v___x_2433_; 
v___x_2433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2433_, 0, v___x_2431_);
return v___x_2433_;
}
else
{
lean_object* v___x_2434_; uint8_t v___x_2435_; 
v___x_2434_ = lean_array_get_size(v_as_2421_);
v___x_2435_ = lean_nat_dec_le(v_stop_2423_, v___x_2434_);
if (v___x_2435_ == 0)
{
uint8_t v___x_2436_; 
v___x_2436_ = lean_nat_dec_lt(v_start_2422_, v___x_2434_);
if (v___x_2436_ == 0)
{
lean_object* v___x_2437_; 
v___x_2437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2437_, 0, v___x_2431_);
return v___x_2437_;
}
else
{
size_t v___x_2438_; size_t v___x_2439_; lean_object* v___x_2440_; 
v___x_2438_ = lean_usize_of_nat(v_start_2422_);
v___x_2439_ = lean_usize_of_nat(v___x_2434_);
v___x_2440_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__0_spec__0___redArg(v_as_2421_, v___x_2438_, v___x_2439_, v___x_2431_, v___y_2425_);
return v___x_2440_;
}
}
else
{
size_t v___x_2441_; size_t v___x_2442_; lean_object* v___x_2443_; 
v___x_2441_ = lean_usize_of_nat(v_start_2422_);
v___x_2442_ = lean_usize_of_nat(v_stop_2423_);
v___x_2443_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__0_spec__0___redArg(v_as_2421_, v___x_2441_, v___x_2442_, v___x_2431_, v___y_2425_);
return v___x_2443_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__0___boxed(lean_object* v_as_2444_, lean_object* v_start_2445_, lean_object* v_stop_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_){
_start:
{
lean_object* v_res_2454_; 
v_res_2454_ = l_Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__0(v_as_2444_, v_start_2445_, v_stop_2446_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_);
lean_dec(v___y_2452_);
lean_dec_ref(v___y_2451_);
lean_dec(v___y_2450_);
lean_dec_ref(v___y_2449_);
lean_dec(v___y_2448_);
lean_dec_ref(v___y_2447_);
lean_dec(v_stop_2446_);
lean_dec(v_start_2445_);
lean_dec_ref(v_as_2444_);
return v_res_2454_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1___redArg(lean_object* v_as_2455_, size_t v_i_2456_, size_t v_stop_2457_, lean_object* v_b_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_){
_start:
{
uint8_t v___x_2462_; 
v___x_2462_ = lean_usize_dec_eq(v_i_2456_, v_stop_2457_);
if (v___x_2462_ == 0)
{
lean_object* v___x_2463_; lean_object* v___x_2464_; 
v___x_2463_ = lean_array_uget_borrowed(v_as_2455_, v_i_2456_);
v___x_2464_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_markDescendantsBorrowed___redArg(v___x_2463_, v___y_2459_, v___y_2460_);
if (lean_obj_tag(v___x_2464_) == 0)
{
lean_object* v_a_2465_; size_t v___x_2466_; size_t v___x_2467_; 
v_a_2465_ = lean_ctor_get(v___x_2464_, 0);
lean_inc(v_a_2465_);
lean_dec_ref(v___x_2464_);
v___x_2466_ = ((size_t)1ULL);
v___x_2467_ = lean_usize_add(v_i_2456_, v___x_2466_);
v_i_2456_ = v___x_2467_;
v_b_2458_ = v_a_2465_;
goto _start;
}
else
{
return v___x_2464_;
}
}
else
{
lean_object* v___x_2469_; 
v___x_2469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2469_, 0, v_b_2458_);
return v___x_2469_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1___redArg___boxed(lean_object* v_as_2470_, lean_object* v_i_2471_, lean_object* v_stop_2472_, lean_object* v_b_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_){
_start:
{
size_t v_i_boxed_2477_; size_t v_stop_boxed_2478_; lean_object* v_res_2479_; 
v_i_boxed_2477_ = lean_unbox_usize(v_i_2471_);
lean_dec(v_i_2471_);
v_stop_boxed_2478_ = lean_unbox_usize(v_stop_2472_);
lean_dec(v_stop_2472_);
v_res_2479_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1___redArg(v_as_2470_, v_i_boxed_2477_, v_stop_boxed_2478_, v_b_2473_, v___y_2474_, v___y_2475_);
lean_dec(v___y_2475_);
lean_dec_ref(v___y_2474_);
lean_dec_ref(v_as_2470_);
return v_res_2479_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs(lean_object* v_args_2480_, lean_object* v_a_2481_, lean_object* v_a_2482_, lean_object* v_a_2483_, lean_object* v_a_2484_, lean_object* v_a_2485_, lean_object* v_a_2486_){
_start:
{
lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; 
v___x_2488_ = lean_unsigned_to_nat(0u);
v___x_2489_ = lean_array_get_size(v_args_2480_);
v___x_2490_ = l_Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__0(v_args_2480_, v___x_2488_, v___x_2489_, v_a_2481_, v_a_2482_, v_a_2483_, v_a_2484_, v_a_2485_, v_a_2486_);
if (lean_obj_tag(v___x_2490_) == 0)
{
lean_object* v_a_2491_; lean_object* v___x_2493_; uint8_t v_isShared_2494_; uint8_t v_isSharedCheck_2511_; 
v_a_2491_ = lean_ctor_get(v___x_2490_, 0);
v_isSharedCheck_2511_ = !lean_is_exclusive(v___x_2490_);
if (v_isSharedCheck_2511_ == 0)
{
v___x_2493_ = v___x_2490_;
v_isShared_2494_ = v_isSharedCheck_2511_;
goto v_resetjp_2492_;
}
else
{
lean_inc(v_a_2491_);
lean_dec(v___x_2490_);
v___x_2493_ = lean_box(0);
v_isShared_2494_ = v_isSharedCheck_2511_;
goto v_resetjp_2492_;
}
v_resetjp_2492_:
{
lean_object* v___x_2495_; lean_object* v___x_2496_; uint8_t v___x_2497_; 
v___x_2495_ = lean_array_get_size(v_a_2491_);
v___x_2496_ = lean_box(0);
v___x_2497_ = lean_nat_dec_lt(v___x_2488_, v___x_2495_);
if (v___x_2497_ == 0)
{
lean_object* v___x_2499_; 
lean_dec(v_a_2491_);
if (v_isShared_2494_ == 0)
{
lean_ctor_set(v___x_2493_, 0, v___x_2496_);
v___x_2499_ = v___x_2493_;
goto v_reusejp_2498_;
}
else
{
lean_object* v_reuseFailAlloc_2500_; 
v_reuseFailAlloc_2500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2500_, 0, v___x_2496_);
v___x_2499_ = v_reuseFailAlloc_2500_;
goto v_reusejp_2498_;
}
v_reusejp_2498_:
{
return v___x_2499_;
}
}
else
{
uint8_t v___x_2501_; 
v___x_2501_ = lean_nat_dec_le(v___x_2495_, v___x_2495_);
if (v___x_2501_ == 0)
{
if (v___x_2497_ == 0)
{
lean_object* v___x_2503_; 
lean_dec(v_a_2491_);
if (v_isShared_2494_ == 0)
{
lean_ctor_set(v___x_2493_, 0, v___x_2496_);
v___x_2503_ = v___x_2493_;
goto v_reusejp_2502_;
}
else
{
lean_object* v_reuseFailAlloc_2504_; 
v_reuseFailAlloc_2504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2504_, 0, v___x_2496_);
v___x_2503_ = v_reuseFailAlloc_2504_;
goto v_reusejp_2502_;
}
v_reusejp_2502_:
{
return v___x_2503_;
}
}
else
{
size_t v___x_2505_; size_t v___x_2506_; lean_object* v___x_2507_; 
lean_del_object(v___x_2493_);
v___x_2505_ = ((size_t)0ULL);
v___x_2506_ = lean_usize_of_nat(v___x_2495_);
v___x_2507_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1___redArg(v_a_2491_, v___x_2505_, v___x_2506_, v___x_2496_, v_a_2481_, v_a_2482_);
lean_dec(v_a_2491_);
return v___x_2507_;
}
}
else
{
size_t v___x_2508_; size_t v___x_2509_; lean_object* v___x_2510_; 
lean_del_object(v___x_2493_);
v___x_2508_ = ((size_t)0ULL);
v___x_2509_ = lean_usize_of_nat(v___x_2495_);
v___x_2510_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1___redArg(v_a_2491_, v___x_2508_, v___x_2509_, v___x_2496_, v_a_2481_, v_a_2482_);
lean_dec(v_a_2491_);
return v___x_2510_;
}
}
}
}
else
{
lean_object* v_a_2512_; lean_object* v___x_2514_; uint8_t v_isShared_2515_; uint8_t v_isSharedCheck_2519_; 
v_a_2512_ = lean_ctor_get(v___x_2490_, 0);
v_isSharedCheck_2519_ = !lean_is_exclusive(v___x_2490_);
if (v_isSharedCheck_2519_ == 0)
{
v___x_2514_ = v___x_2490_;
v_isShared_2515_ = v_isSharedCheck_2519_;
goto v_resetjp_2513_;
}
else
{
lean_inc(v_a_2512_);
lean_dec(v___x_2490_);
v___x_2514_ = lean_box(0);
v_isShared_2515_ = v_isSharedCheck_2519_;
goto v_resetjp_2513_;
}
v_resetjp_2513_:
{
lean_object* v___x_2517_; 
if (v_isShared_2515_ == 0)
{
v___x_2517_ = v___x_2514_;
goto v_reusejp_2516_;
}
else
{
lean_object* v_reuseFailAlloc_2518_; 
v_reuseFailAlloc_2518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2518_, 0, v_a_2512_);
v___x_2517_ = v_reuseFailAlloc_2518_;
goto v_reusejp_2516_;
}
v_reusejp_2516_:
{
return v___x_2517_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs___boxed(lean_object* v_args_2520_, lean_object* v_a_2521_, lean_object* v_a_2522_, lean_object* v_a_2523_, lean_object* v_a_2524_, lean_object* v_a_2525_, lean_object* v_a_2526_, lean_object* v_a_2527_){
_start:
{
lean_object* v_res_2528_; 
v_res_2528_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs(v_args_2520_, v_a_2521_, v_a_2522_, v_a_2523_, v_a_2524_, v_a_2525_, v_a_2526_);
lean_dec(v_a_2526_);
lean_dec_ref(v_a_2525_);
lean_dec(v_a_2524_);
lean_dec_ref(v_a_2523_);
lean_dec(v_a_2522_);
lean_dec_ref(v_a_2521_);
lean_dec_ref(v_args_2520_);
return v_res_2528_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1(lean_object* v_as_2529_, size_t v_i_2530_, size_t v_stop_2531_, lean_object* v_b_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_){
_start:
{
lean_object* v___x_2540_; 
v___x_2540_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1___redArg(v_as_2529_, v_i_2530_, v_stop_2531_, v_b_2532_, v___y_2533_, v___y_2534_);
return v___x_2540_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1___boxed(lean_object* v_as_2541_, lean_object* v_i_2542_, lean_object* v_stop_2543_, lean_object* v_b_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_){
_start:
{
size_t v_i_boxed_2552_; size_t v_stop_boxed_2553_; lean_object* v_res_2554_; 
v_i_boxed_2552_ = lean_unbox_usize(v_i_2542_);
lean_dec(v_i_2542_);
v_stop_boxed_2553_ = lean_unbox_usize(v_stop_2543_);
lean_dec(v_stop_2543_);
v_res_2554_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1(v_as_2541_, v_i_boxed_2552_, v_stop_boxed_2553_, v_b_2544_, v___y_2545_, v___y_2546_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_);
lean_dec(v___y_2550_);
lean_dec_ref(v___y_2549_);
lean_dec(v___y_2548_);
lean_dec_ref(v___y_2547_);
lean_dec(v___y_2546_);
lean_dec_ref(v___y_2545_);
lean_dec_ref(v_as_2541_);
return v_res_2554_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__0_spec__0(lean_object* v_as_2555_, size_t v_i_2556_, size_t v_stop_2557_, lean_object* v_b_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_){
_start:
{
lean_object* v___x_2566_; 
v___x_2566_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__0_spec__0___redArg(v_as_2555_, v_i_2556_, v_stop_2557_, v_b_2558_, v___y_2560_);
return v___x_2566_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__0_spec__0___boxed(lean_object* v_as_2567_, lean_object* v_i_2568_, lean_object* v_stop_2569_, lean_object* v_b_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_){
_start:
{
size_t v_i_boxed_2578_; size_t v_stop_boxed_2579_; lean_object* v_res_2580_; 
v_i_boxed_2578_ = lean_unbox_usize(v_i_2568_);
lean_dec(v_i_2568_);
v_stop_boxed_2579_ = lean_unbox_usize(v_stop_2569_);
lean_dec(v_stop_2569_);
v_res_2580_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__0_spec__0(v_as_2567_, v_i_boxed_2578_, v_stop_boxed_2579_, v_b_2570_, v___y_2571_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_);
lean_dec(v___y_2576_);
lean_dec_ref(v___y_2575_);
lean_dec(v___y_2574_);
lean_dec_ref(v___y_2573_);
lean_dec(v___y_2572_);
lean_dec_ref(v___y_2571_);
lean_dec_ref(v_as_2567_);
return v_res_2580_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0(lean_object* v_msg_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_){
_start:
{
lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v_toApplicative_2591_; lean_object* v___x_2593_; uint8_t v_isShared_2594_; uint8_t v_isSharedCheck_2654_; 
v___x_2589_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__7___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__7___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__7___closed__0);
v___x_2590_ = l_StateRefT_x27_instMonad___redArg(v___x_2589_);
v_toApplicative_2591_ = lean_ctor_get(v___x_2590_, 0);
v_isSharedCheck_2654_ = !lean_is_exclusive(v___x_2590_);
if (v_isSharedCheck_2654_ == 0)
{
lean_object* v_unused_2655_; 
v_unused_2655_ = lean_ctor_get(v___x_2590_, 1);
lean_dec(v_unused_2655_);
v___x_2593_ = v___x_2590_;
v_isShared_2594_ = v_isSharedCheck_2654_;
goto v_resetjp_2592_;
}
else
{
lean_inc(v_toApplicative_2591_);
lean_dec(v___x_2590_);
v___x_2593_ = lean_box(0);
v_isShared_2594_ = v_isSharedCheck_2654_;
goto v_resetjp_2592_;
}
v_resetjp_2592_:
{
lean_object* v_toFunctor_2595_; lean_object* v_toSeq_2596_; lean_object* v_toSeqLeft_2597_; lean_object* v_toSeqRight_2598_; lean_object* v___x_2600_; uint8_t v_isShared_2601_; uint8_t v_isSharedCheck_2652_; 
v_toFunctor_2595_ = lean_ctor_get(v_toApplicative_2591_, 0);
v_toSeq_2596_ = lean_ctor_get(v_toApplicative_2591_, 2);
v_toSeqLeft_2597_ = lean_ctor_get(v_toApplicative_2591_, 3);
v_toSeqRight_2598_ = lean_ctor_get(v_toApplicative_2591_, 4);
v_isSharedCheck_2652_ = !lean_is_exclusive(v_toApplicative_2591_);
if (v_isSharedCheck_2652_ == 0)
{
lean_object* v_unused_2653_; 
v_unused_2653_ = lean_ctor_get(v_toApplicative_2591_, 1);
lean_dec(v_unused_2653_);
v___x_2600_ = v_toApplicative_2591_;
v_isShared_2601_ = v_isSharedCheck_2652_;
goto v_resetjp_2599_;
}
else
{
lean_inc(v_toSeqRight_2598_);
lean_inc(v_toSeqLeft_2597_);
lean_inc(v_toSeq_2596_);
lean_inc(v_toFunctor_2595_);
lean_dec(v_toApplicative_2591_);
v___x_2600_ = lean_box(0);
v_isShared_2601_ = v_isSharedCheck_2652_;
goto v_resetjp_2599_;
}
v_resetjp_2599_:
{
lean_object* v___f_2602_; lean_object* v___f_2603_; lean_object* v___f_2604_; lean_object* v___f_2605_; lean_object* v___x_2606_; lean_object* v___f_2607_; lean_object* v___f_2608_; lean_object* v___f_2609_; lean_object* v___x_2611_; 
v___f_2602_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__7___closed__1));
v___f_2603_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__7___closed__2));
lean_inc_ref(v_toFunctor_2595_);
v___f_2604_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2604_, 0, v_toFunctor_2595_);
v___f_2605_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2605_, 0, v_toFunctor_2595_);
v___x_2606_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2606_, 0, v___f_2604_);
lean_ctor_set(v___x_2606_, 1, v___f_2605_);
v___f_2607_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2607_, 0, v_toSeqRight_2598_);
v___f_2608_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2608_, 0, v_toSeqLeft_2597_);
v___f_2609_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2609_, 0, v_toSeq_2596_);
if (v_isShared_2601_ == 0)
{
lean_ctor_set(v___x_2600_, 4, v___f_2607_);
lean_ctor_set(v___x_2600_, 3, v___f_2608_);
lean_ctor_set(v___x_2600_, 2, v___f_2609_);
lean_ctor_set(v___x_2600_, 1, v___f_2602_);
lean_ctor_set(v___x_2600_, 0, v___x_2606_);
v___x_2611_ = v___x_2600_;
goto v_reusejp_2610_;
}
else
{
lean_object* v_reuseFailAlloc_2651_; 
v_reuseFailAlloc_2651_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2651_, 0, v___x_2606_);
lean_ctor_set(v_reuseFailAlloc_2651_, 1, v___f_2602_);
lean_ctor_set(v_reuseFailAlloc_2651_, 2, v___f_2609_);
lean_ctor_set(v_reuseFailAlloc_2651_, 3, v___f_2608_);
lean_ctor_set(v_reuseFailAlloc_2651_, 4, v___f_2607_);
v___x_2611_ = v_reuseFailAlloc_2651_;
goto v_reusejp_2610_;
}
v_reusejp_2610_:
{
lean_object* v___x_2613_; 
if (v_isShared_2594_ == 0)
{
lean_ctor_set(v___x_2593_, 1, v___f_2603_);
lean_ctor_set(v___x_2593_, 0, v___x_2611_);
v___x_2613_ = v___x_2593_;
goto v_reusejp_2612_;
}
else
{
lean_object* v_reuseFailAlloc_2650_; 
v_reuseFailAlloc_2650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2650_, 0, v___x_2611_);
lean_ctor_set(v_reuseFailAlloc_2650_, 1, v___f_2603_);
v___x_2613_ = v_reuseFailAlloc_2650_;
goto v_reusejp_2612_;
}
v_reusejp_2612_:
{
lean_object* v___x_2614_; lean_object* v_toApplicative_2615_; lean_object* v___x_2617_; uint8_t v_isShared_2618_; uint8_t v_isSharedCheck_2648_; 
v___x_2614_ = l_StateRefT_x27_instMonad___redArg(v___x_2613_);
v_toApplicative_2615_ = lean_ctor_get(v___x_2614_, 0);
v_isSharedCheck_2648_ = !lean_is_exclusive(v___x_2614_);
if (v_isSharedCheck_2648_ == 0)
{
lean_object* v_unused_2649_; 
v_unused_2649_ = lean_ctor_get(v___x_2614_, 1);
lean_dec(v_unused_2649_);
v___x_2617_ = v___x_2614_;
v_isShared_2618_ = v_isSharedCheck_2648_;
goto v_resetjp_2616_;
}
else
{
lean_inc(v_toApplicative_2615_);
lean_dec(v___x_2614_);
v___x_2617_ = lean_box(0);
v_isShared_2618_ = v_isSharedCheck_2648_;
goto v_resetjp_2616_;
}
v_resetjp_2616_:
{
lean_object* v_toFunctor_2619_; lean_object* v_toSeq_2620_; lean_object* v_toSeqLeft_2621_; lean_object* v_toSeqRight_2622_; lean_object* v___x_2624_; uint8_t v_isShared_2625_; uint8_t v_isSharedCheck_2646_; 
v_toFunctor_2619_ = lean_ctor_get(v_toApplicative_2615_, 0);
v_toSeq_2620_ = lean_ctor_get(v_toApplicative_2615_, 2);
v_toSeqLeft_2621_ = lean_ctor_get(v_toApplicative_2615_, 3);
v_toSeqRight_2622_ = lean_ctor_get(v_toApplicative_2615_, 4);
v_isSharedCheck_2646_ = !lean_is_exclusive(v_toApplicative_2615_);
if (v_isSharedCheck_2646_ == 0)
{
lean_object* v_unused_2647_; 
v_unused_2647_ = lean_ctor_get(v_toApplicative_2615_, 1);
lean_dec(v_unused_2647_);
v___x_2624_ = v_toApplicative_2615_;
v_isShared_2625_ = v_isSharedCheck_2646_;
goto v_resetjp_2623_;
}
else
{
lean_inc(v_toSeqRight_2622_);
lean_inc(v_toSeqLeft_2621_);
lean_inc(v_toSeq_2620_);
lean_inc(v_toFunctor_2619_);
lean_dec(v_toApplicative_2615_);
v___x_2624_ = lean_box(0);
v_isShared_2625_ = v_isSharedCheck_2646_;
goto v_resetjp_2623_;
}
v_resetjp_2623_:
{
lean_object* v___f_2626_; lean_object* v___f_2627_; lean_object* v___f_2628_; lean_object* v___f_2629_; lean_object* v___x_2630_; lean_object* v___f_2631_; lean_object* v___f_2632_; lean_object* v___f_2633_; lean_object* v___x_2635_; 
v___f_2626_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__7___closed__3));
v___f_2627_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__7___closed__4));
lean_inc_ref(v_toFunctor_2619_);
v___f_2628_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2628_, 0, v_toFunctor_2619_);
v___f_2629_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2629_, 0, v_toFunctor_2619_);
v___x_2630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2630_, 0, v___f_2628_);
lean_ctor_set(v___x_2630_, 1, v___f_2629_);
v___f_2631_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2631_, 0, v_toSeqRight_2622_);
v___f_2632_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2632_, 0, v_toSeqLeft_2621_);
v___f_2633_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2633_, 0, v_toSeq_2620_);
if (v_isShared_2625_ == 0)
{
lean_ctor_set(v___x_2624_, 4, v___f_2631_);
lean_ctor_set(v___x_2624_, 3, v___f_2632_);
lean_ctor_set(v___x_2624_, 2, v___f_2633_);
lean_ctor_set(v___x_2624_, 1, v___f_2626_);
lean_ctor_set(v___x_2624_, 0, v___x_2630_);
v___x_2635_ = v___x_2624_;
goto v_reusejp_2634_;
}
else
{
lean_object* v_reuseFailAlloc_2645_; 
v_reuseFailAlloc_2645_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2645_, 0, v___x_2630_);
lean_ctor_set(v_reuseFailAlloc_2645_, 1, v___f_2626_);
lean_ctor_set(v_reuseFailAlloc_2645_, 2, v___f_2633_);
lean_ctor_set(v_reuseFailAlloc_2645_, 3, v___f_2632_);
lean_ctor_set(v_reuseFailAlloc_2645_, 4, v___f_2631_);
v___x_2635_ = v_reuseFailAlloc_2645_;
goto v_reusejp_2634_;
}
v_reusejp_2634_:
{
lean_object* v___x_2637_; 
if (v_isShared_2618_ == 0)
{
lean_ctor_set(v___x_2617_, 1, v___f_2627_);
lean_ctor_set(v___x_2617_, 0, v___x_2635_);
v___x_2637_ = v___x_2617_;
goto v_reusejp_2636_;
}
else
{
lean_object* v_reuseFailAlloc_2644_; 
v_reuseFailAlloc_2644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2644_, 0, v___x_2635_);
lean_ctor_set(v_reuseFailAlloc_2644_, 1, v___f_2627_);
v___x_2637_ = v_reuseFailAlloc_2644_;
goto v_reusejp_2636_;
}
v_reusejp_2636_:
{
lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___f_2641_; lean_object* v___x_1590__overap_2642_; lean_object* v___x_2643_; 
v___x_2638_ = l_StateRefT_x27_instMonad___redArg(v___x_2637_);
v___x_2639_ = lean_box(0);
v___x_2640_ = l_instInhabitedOfMonad___redArg(v___x_2638_, v___x_2639_);
v___f_2641_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2641_, 0, v___x_2640_);
v___x_1590__overap_2642_ = lean_panic_fn(v___f_2641_, v_msg_2581_);
lean_inc(v___y_2587_);
lean_inc_ref(v___y_2586_);
lean_inc(v___y_2585_);
lean_inc_ref(v___y_2584_);
lean_inc(v___y_2583_);
lean_inc_ref(v___y_2582_);
v___x_2643_ = lean_apply_7(v___x_1590__overap_2642_, v___y_2582_, v___y_2583_, v___y_2584_, v___y_2585_, v___y_2586_, v___y_2587_, lean_box(0));
return v___x_2643_;
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0___boxed(lean_object* v_msg_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_){
_start:
{
lean_object* v_res_2664_; 
v_res_2664_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0(v_msg_2656_, v___y_2657_, v___y_2658_, v___y_2659_, v___y_2660_, v___y_2661_, v___y_2662_);
lean_dec(v___y_2662_);
lean_dec_ref(v___y_2661_);
lean_dec(v___y_2660_);
lean_dec_ref(v___y_2659_);
lean_dec(v___y_2658_);
lean_dec_ref(v___y_2657_);
return v_res_2664_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue___closed__1(void){
_start:
{
lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; 
v___x_2666_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode___closed__6));
v___x_2667_ = lean_unsigned_to_nat(20u);
v___x_2668_ = lean_unsigned_to_nat(364u);
v___x_2669_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue___closed__0));
v___x_2670_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode___closed__4));
v___x_2671_ = l_mkPanicMessageWithDecl(v___x_2670_, v___x_2669_, v___x_2668_, v___x_2667_, v___x_2666_);
return v___x_2671_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue(lean_object* v_value_2672_, lean_object* v_a_2673_, lean_object* v_a_2674_, lean_object* v_a_2675_, lean_object* v_a_2676_, lean_object* v_a_2677_, lean_object* v_a_2678_){
_start:
{
switch(lean_obj_tag(v_value_2672_))
{
case 0:
{
lean_object* v___x_2681_; uint8_t v_isShared_2682_; uint8_t v_isSharedCheck_2687_; 
v_isSharedCheck_2687_ = !lean_is_exclusive(v_value_2672_);
if (v_isSharedCheck_2687_ == 0)
{
lean_object* v_unused_2688_; 
v_unused_2688_ = lean_ctor_get(v_value_2672_, 0);
lean_dec(v_unused_2688_);
v___x_2681_ = v_value_2672_;
v_isShared_2682_ = v_isSharedCheck_2687_;
goto v_resetjp_2680_;
}
else
{
lean_dec(v_value_2672_);
v___x_2681_ = lean_box(0);
v_isShared_2682_ = v_isSharedCheck_2687_;
goto v_resetjp_2680_;
}
v_resetjp_2680_:
{
lean_object* v___x_2683_; lean_object* v___x_2685_; 
v___x_2683_ = lean_box(0);
if (v_isShared_2682_ == 0)
{
lean_ctor_set(v___x_2681_, 0, v___x_2683_);
v___x_2685_ = v___x_2681_;
goto v_reusejp_2684_;
}
else
{
lean_object* v_reuseFailAlloc_2686_; 
v_reuseFailAlloc_2686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2686_, 0, v___x_2683_);
v___x_2685_ = v_reuseFailAlloc_2686_;
goto v_reusejp_2684_;
}
v_reusejp_2684_:
{
return v___x_2685_;
}
}
}
case 1:
{
lean_object* v___x_2689_; lean_object* v___x_2690_; 
v___x_2689_ = lean_box(0);
v___x_2690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2690_, 0, v___x_2689_);
return v___x_2690_;
}
case 4:
{
lean_object* v_fvarId_2691_; lean_object* v_args_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; 
v_fvarId_2691_ = lean_ctor_get(v_value_2672_, 0);
lean_inc(v_fvarId_2691_);
v_args_2692_ = lean_ctor_get(v_value_2672_, 1);
lean_inc_ref(v_args_2692_);
lean_dec_ref(v_value_2672_);
v___x_2693_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___redArg(v_fvarId_2691_, v_a_2673_, v_a_2674_);
lean_dec_ref(v___x_2693_);
v___x_2694_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs(v_args_2692_, v_a_2673_, v_a_2674_, v_a_2675_, v_a_2676_, v_a_2677_, v_a_2678_);
lean_dec_ref(v_args_2692_);
return v___x_2694_;
}
case 5:
{
lean_object* v_args_2695_; lean_object* v___x_2696_; 
v_args_2695_ = lean_ctor_get(v_value_2672_, 1);
lean_inc_ref(v_args_2695_);
lean_dec_ref(v_value_2672_);
v___x_2696_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs(v_args_2695_, v_a_2673_, v_a_2674_, v_a_2675_, v_a_2676_, v_a_2677_, v_a_2678_);
lean_dec_ref(v_args_2695_);
return v___x_2696_;
}
case 8:
{
lean_object* v_var_2697_; lean_object* v___x_2698_; 
v_var_2697_ = lean_ctor_get(v_value_2672_, 2);
lean_inc(v_var_2697_);
lean_dec_ref(v_value_2672_);
v___x_2698_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___redArg(v_var_2697_, v_a_2673_, v_a_2674_);
return v___x_2698_;
}
case 9:
{
lean_object* v_args_2699_; lean_object* v___x_2700_; 
v_args_2699_ = lean_ctor_get(v_value_2672_, 1);
lean_inc_ref(v_args_2699_);
lean_dec_ref(v_value_2672_);
v___x_2700_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs(v_args_2699_, v_a_2673_, v_a_2674_, v_a_2675_, v_a_2676_, v_a_2677_, v_a_2678_);
lean_dec_ref(v_args_2699_);
return v___x_2700_;
}
case 10:
{
lean_object* v_args_2701_; lean_object* v___x_2702_; 
v_args_2701_ = lean_ctor_get(v_value_2672_, 1);
lean_inc_ref(v_args_2701_);
lean_dec_ref(v_value_2672_);
v___x_2702_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs(v_args_2701_, v_a_2673_, v_a_2674_, v_a_2675_, v_a_2676_, v_a_2677_, v_a_2678_);
lean_dec_ref(v_args_2701_);
return v___x_2702_;
}
case 12:
{
lean_object* v_var_2703_; lean_object* v_args_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; 
v_var_2703_ = lean_ctor_get(v_value_2672_, 0);
lean_inc(v_var_2703_);
v_args_2704_ = lean_ctor_get(v_value_2672_, 2);
lean_inc_ref(v_args_2704_);
lean_dec_ref(v_value_2672_);
v___x_2705_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___redArg(v_var_2703_, v_a_2673_, v_a_2674_);
lean_dec_ref(v___x_2705_);
v___x_2706_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs(v_args_2704_, v_a_2673_, v_a_2674_, v_a_2675_, v_a_2676_, v_a_2677_, v_a_2678_);
lean_dec_ref(v_args_2704_);
return v___x_2706_;
}
case 14:
{
lean_object* v_fvarId_2707_; lean_object* v___x_2708_; 
v_fvarId_2707_ = lean_ctor_get(v_value_2672_, 0);
lean_inc(v_fvarId_2707_);
lean_dec_ref(v_value_2672_);
v___x_2708_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___redArg(v_fvarId_2707_, v_a_2673_, v_a_2674_);
return v___x_2708_;
}
case 15:
{
lean_object* v___x_2709_; lean_object* v___x_2710_; 
lean_dec_ref(v_value_2672_);
v___x_2709_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue___closed__1, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue___closed__1_once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue___closed__1);
v___x_2710_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0(v___x_2709_, v_a_2673_, v_a_2674_, v_a_2675_, v_a_2676_, v_a_2677_, v_a_2678_);
return v___x_2710_;
}
default: 
{
lean_object* v_var_2711_; lean_object* v___x_2712_; 
v_var_2711_ = lean_ctor_get(v_value_2672_, 1);
lean_inc(v_var_2711_);
lean_dec(v_value_2672_);
v___x_2712_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___redArg(v_var_2711_, v_a_2673_, v_a_2674_);
return v___x_2712_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue___boxed(lean_object* v_value_2713_, lean_object* v_a_2714_, lean_object* v_a_2715_, lean_object* v_a_2716_, lean_object* v_a_2717_, lean_object* v_a_2718_, lean_object* v_a_2719_, lean_object* v_a_2720_){
_start:
{
lean_object* v_res_2721_; 
v_res_2721_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue(v_value_2713_, v_a_2714_, v_a_2715_, v_a_2716_, v_a_2717_, v_a_2718_, v_a_2719_);
lean_dec(v_a_2719_);
lean_dec_ref(v_a_2718_);
lean_dec(v_a_2717_);
lean_dec_ref(v_a_2716_);
lean_dec(v_a_2715_);
lean_dec_ref(v_a_2714_);
return v_res_2721_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_bindVar___redArg(lean_object* v_fvarId_2722_, lean_object* v_a_2723_){
_start:
{
lean_object* v___x_2725_; lean_object* v_vars_2726_; lean_object* v_borrows_2727_; lean_object* v___x_2729_; uint8_t v_isShared_2730_; uint8_t v_isSharedCheck_2741_; 
v___x_2725_ = lean_st_ref_take(v_a_2723_);
v_vars_2726_ = lean_ctor_get(v___x_2725_, 0);
v_borrows_2727_ = lean_ctor_get(v___x_2725_, 1);
v_isSharedCheck_2741_ = !lean_is_exclusive(v___x_2725_);
if (v_isSharedCheck_2741_ == 0)
{
v___x_2729_ = v___x_2725_;
v_isShared_2730_ = v_isSharedCheck_2741_;
goto v_resetjp_2728_;
}
else
{
lean_inc(v_borrows_2727_);
lean_inc(v_vars_2726_);
lean_dec(v___x_2725_);
v___x_2729_ = lean_box(0);
v_isShared_2730_ = v_isSharedCheck_2741_;
goto v_resetjp_2728_;
}
v_resetjp_2728_:
{
lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v_vars_2733_; lean_object* v_borrows_2734_; lean_object* v___x_2736_; 
v___x_2731_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_visitParam___redArg___closed__0));
v___x_2732_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_visitParam___redArg___closed__1));
lean_inc(v_fvarId_2722_);
v_vars_2733_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v___x_2731_, v___x_2732_, v_vars_2726_, v_fvarId_2722_);
v_borrows_2734_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v___x_2731_, v___x_2732_, v_borrows_2727_, v_fvarId_2722_);
if (v_isShared_2730_ == 0)
{
lean_ctor_set(v___x_2729_, 1, v_borrows_2734_);
lean_ctor_set(v___x_2729_, 0, v_vars_2733_);
v___x_2736_ = v___x_2729_;
goto v_reusejp_2735_;
}
else
{
lean_object* v_reuseFailAlloc_2740_; 
v_reuseFailAlloc_2740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2740_, 0, v_vars_2733_);
lean_ctor_set(v_reuseFailAlloc_2740_, 1, v_borrows_2734_);
v___x_2736_ = v_reuseFailAlloc_2740_;
goto v_reusejp_2735_;
}
v_reusejp_2735_:
{
lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; 
v___x_2737_ = lean_st_ref_set(v_a_2723_, v___x_2736_);
v___x_2738_ = lean_box(0);
v___x_2739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2739_, 0, v___x_2738_);
return v___x_2739_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_bindVar___redArg___boxed(lean_object* v_fvarId_2742_, lean_object* v_a_2743_, lean_object* v_a_2744_){
_start:
{
lean_object* v_res_2745_; 
v_res_2745_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_bindVar___redArg(v_fvarId_2742_, v_a_2743_);
lean_dec(v_a_2743_);
return v_res_2745_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_bindVar(lean_object* v_fvarId_2746_, lean_object* v_a_2747_, lean_object* v_a_2748_, lean_object* v_a_2749_, lean_object* v_a_2750_, lean_object* v_a_2751_, lean_object* v_a_2752_){
_start:
{
lean_object* v___x_2754_; lean_object* v_vars_2755_; lean_object* v_borrows_2756_; lean_object* v___x_2758_; uint8_t v_isShared_2759_; uint8_t v_isSharedCheck_2770_; 
v___x_2754_ = lean_st_ref_take(v_a_2748_);
v_vars_2755_ = lean_ctor_get(v___x_2754_, 0);
v_borrows_2756_ = lean_ctor_get(v___x_2754_, 1);
v_isSharedCheck_2770_ = !lean_is_exclusive(v___x_2754_);
if (v_isSharedCheck_2770_ == 0)
{
v___x_2758_ = v___x_2754_;
v_isShared_2759_ = v_isSharedCheck_2770_;
goto v_resetjp_2757_;
}
else
{
lean_inc(v_borrows_2756_);
lean_inc(v_vars_2755_);
lean_dec(v___x_2754_);
v___x_2758_ = lean_box(0);
v_isShared_2759_ = v_isSharedCheck_2770_;
goto v_resetjp_2757_;
}
v_resetjp_2757_:
{
lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v_vars_2762_; lean_object* v_borrows_2763_; lean_object* v___x_2765_; 
v___x_2760_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_visitParam___redArg___closed__0));
v___x_2761_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_visitParam___redArg___closed__1));
lean_inc(v_fvarId_2746_);
v_vars_2762_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v___x_2760_, v___x_2761_, v_vars_2755_, v_fvarId_2746_);
v_borrows_2763_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v___x_2760_, v___x_2761_, v_borrows_2756_, v_fvarId_2746_);
if (v_isShared_2759_ == 0)
{
lean_ctor_set(v___x_2758_, 1, v_borrows_2763_);
lean_ctor_set(v___x_2758_, 0, v_vars_2762_);
v___x_2765_ = v___x_2758_;
goto v_reusejp_2764_;
}
else
{
lean_object* v_reuseFailAlloc_2769_; 
v_reuseFailAlloc_2769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2769_, 0, v_vars_2762_);
lean_ctor_set(v_reuseFailAlloc_2769_, 1, v_borrows_2763_);
v___x_2765_ = v_reuseFailAlloc_2769_;
goto v_reusejp_2764_;
}
v_reusejp_2764_:
{
lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; 
v___x_2766_ = lean_st_ref_set(v_a_2748_, v___x_2765_);
v___x_2767_ = lean_box(0);
v___x_2768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2768_, 0, v___x_2767_);
return v___x_2768_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_bindVar___boxed(lean_object* v_fvarId_2771_, lean_object* v_a_2772_, lean_object* v_a_2773_, lean_object* v_a_2774_, lean_object* v_a_2775_, lean_object* v_a_2776_, lean_object* v_a_2777_, lean_object* v_a_2778_){
_start:
{
lean_object* v_res_2779_; 
v_res_2779_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_bindVar(v_fvarId_2771_, v_a_2772_, v_a_2773_, v_a_2774_, v_a_2775_, v_a_2776_, v_a_2777_);
lean_dec(v_a_2777_);
lean_dec_ref(v_a_2776_);
lean_dec(v_a_2775_);
lean_dec_ref(v_a_2774_);
lean_dec(v_a_2773_);
lean_dec_ref(v_a_2772_);
return v_res_2779_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_setRetLiveVars_spec__0(lean_object* v___x_2780_, lean_object* v_x_2781_, lean_object* v_x_2782_){
_start:
{
if (lean_obj_tag(v_x_2782_) == 0)
{
return v_x_2781_;
}
else
{
lean_object* v_key_2783_; lean_object* v_tail_2784_; lean_object* v_vars_2785_; lean_object* v_borrows_2786_; lean_object* v___x_2788_; uint8_t v_isShared_2789_; uint8_t v_isSharedCheck_2797_; 
v_key_2783_ = lean_ctor_get(v_x_2782_, 0);
lean_inc(v_key_2783_);
v_tail_2784_ = lean_ctor_get(v_x_2782_, 2);
lean_inc(v_tail_2784_);
lean_dec_ref(v_x_2782_);
v_vars_2785_ = lean_ctor_get(v_x_2781_, 0);
v_borrows_2786_ = lean_ctor_get(v_x_2781_, 1);
v_isSharedCheck_2797_ = !lean_is_exclusive(v_x_2781_);
if (v_isSharedCheck_2797_ == 0)
{
v___x_2788_ = v_x_2781_;
v_isShared_2789_ = v_isSharedCheck_2797_;
goto v_resetjp_2787_;
}
else
{
lean_inc(v_borrows_2786_);
lean_inc(v_vars_2785_);
lean_dec(v_x_2781_);
v___x_2788_ = lean_box(0);
v_isShared_2789_ = v_isSharedCheck_2797_;
goto v_resetjp_2787_;
}
v_resetjp_2787_:
{
lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2793_; 
v___x_2790_ = lean_box(0);
lean_inc(v_key_2783_);
v___x_2791_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__1___redArg(v_borrows_2786_, v_key_2783_, v___x_2790_);
if (v_isShared_2789_ == 0)
{
lean_ctor_set(v___x_2788_, 1, v___x_2791_);
v___x_2793_ = v___x_2788_;
goto v_reusejp_2792_;
}
else
{
lean_object* v_reuseFailAlloc_2796_; 
v_reuseFailAlloc_2796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2796_, 0, v_vars_2785_);
lean_ctor_set(v_reuseFailAlloc_2796_, 1, v___x_2791_);
v___x_2793_ = v_reuseFailAlloc_2796_;
goto v_reusejp_2792_;
}
v_reusejp_2792_:
{
lean_object* v___x_2794_; 
v___x_2794_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants(v_key_2783_, v___x_2780_, v___x_2793_);
lean_dec(v_key_2783_);
v_x_2781_ = v___x_2794_;
v_x_2782_ = v_tail_2784_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_setRetLiveVars_spec__0___boxed(lean_object* v___x_2798_, lean_object* v_x_2799_, lean_object* v_x_2800_){
_start:
{
lean_object* v_res_2801_; 
v_res_2801_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_setRetLiveVars_spec__0(v___x_2798_, v_x_2799_, v_x_2800_);
lean_dec_ref(v___x_2798_);
return v_res_2801_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_setRetLiveVars_spec__1(lean_object* v___x_2802_, lean_object* v_as_2803_, size_t v_i_2804_, size_t v_stop_2805_, lean_object* v_b_2806_){
_start:
{
uint8_t v___x_2807_; 
v___x_2807_ = lean_usize_dec_eq(v_i_2804_, v_stop_2805_);
if (v___x_2807_ == 0)
{
lean_object* v___x_2808_; lean_object* v___x_2809_; size_t v___x_2810_; size_t v___x_2811_; 
v___x_2808_ = lean_array_uget_borrowed(v_as_2803_, v_i_2804_);
lean_inc(v___x_2808_);
v___x_2809_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_setRetLiveVars_spec__0(v___x_2802_, v_b_2806_, v___x_2808_);
v___x_2810_ = ((size_t)1ULL);
v___x_2811_ = lean_usize_add(v_i_2804_, v___x_2810_);
v_i_2804_ = v___x_2811_;
v_b_2806_ = v___x_2809_;
goto _start;
}
else
{
return v_b_2806_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_setRetLiveVars_spec__1___boxed(lean_object* v___x_2813_, lean_object* v_as_2814_, lean_object* v_i_2815_, lean_object* v_stop_2816_, lean_object* v_b_2817_){
_start:
{
size_t v_i_boxed_2818_; size_t v_stop_boxed_2819_; lean_object* v_res_2820_; 
v_i_boxed_2818_ = lean_unbox_usize(v_i_2815_);
lean_dec(v_i_2815_);
v_stop_boxed_2819_ = lean_unbox_usize(v_stop_2816_);
lean_dec(v_stop_2816_);
v_res_2820_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_setRetLiveVars_spec__1(v___x_2813_, v_as_2814_, v_i_boxed_2818_, v_stop_boxed_2819_, v_b_2817_);
lean_dec_ref(v_as_2814_);
lean_dec_ref(v___x_2813_);
return v_res_2820_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_setRetLiveVars___redArg(lean_object* v_a_2821_, lean_object* v_a_2822_){
_start:
{
lean_object* v___y_2825_; lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v_borrowedParams_2832_; lean_object* v_derivedValMap_2833_; lean_object* v_buckets_2834_; lean_object* v___x_2835_; uint8_t v___x_2836_; 
v___x_2830_ = lean_unsigned_to_nat(0u);
v___x_2831_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__0, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__0_once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__0);
v_borrowedParams_2832_ = lean_ctor_get(v_a_2821_, 0);
v_derivedValMap_2833_ = lean_ctor_get(v_a_2821_, 1);
v_buckets_2834_ = lean_ctor_get(v_borrowedParams_2832_, 1);
v___x_2835_ = lean_array_get_size(v_buckets_2834_);
v___x_2836_ = lean_nat_dec_lt(v___x_2830_, v___x_2835_);
if (v___x_2836_ == 0)
{
v___y_2825_ = v___x_2831_;
goto v___jp_2824_;
}
else
{
uint8_t v___x_2837_; 
v___x_2837_ = lean_nat_dec_le(v___x_2835_, v___x_2835_);
if (v___x_2837_ == 0)
{
if (v___x_2836_ == 0)
{
v___y_2825_ = v___x_2831_;
goto v___jp_2824_;
}
else
{
size_t v___x_2838_; size_t v___x_2839_; lean_object* v___x_2840_; 
v___x_2838_ = ((size_t)0ULL);
v___x_2839_ = lean_usize_of_nat(v___x_2835_);
v___x_2840_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_setRetLiveVars_spec__1(v_derivedValMap_2833_, v_buckets_2834_, v___x_2838_, v___x_2839_, v___x_2831_);
v___y_2825_ = v___x_2840_;
goto v___jp_2824_;
}
}
else
{
size_t v___x_2841_; size_t v___x_2842_; lean_object* v___x_2843_; 
v___x_2841_ = ((size_t)0ULL);
v___x_2842_ = lean_usize_of_nat(v___x_2835_);
v___x_2843_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_setRetLiveVars_spec__1(v_derivedValMap_2833_, v_buckets_2834_, v___x_2841_, v___x_2842_, v___x_2831_);
v___y_2825_ = v___x_2843_;
goto v___jp_2824_;
}
}
v___jp_2824_:
{
lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; 
v___x_2826_ = lean_st_ref_take(v_a_2822_);
lean_dec(v___x_2826_);
v___x_2827_ = lean_st_ref_set(v_a_2822_, v___y_2825_);
v___x_2828_ = lean_box(0);
v___x_2829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2829_, 0, v___x_2828_);
return v___x_2829_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_setRetLiveVars___redArg___boxed(lean_object* v_a_2844_, lean_object* v_a_2845_, lean_object* v_a_2846_){
_start:
{
lean_object* v_res_2847_; 
v_res_2847_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_setRetLiveVars___redArg(v_a_2844_, v_a_2845_);
lean_dec(v_a_2845_);
lean_dec_ref(v_a_2844_);
return v_res_2847_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_setRetLiveVars(lean_object* v_a_2848_, lean_object* v_a_2849_, lean_object* v_a_2850_, lean_object* v_a_2851_, lean_object* v_a_2852_, lean_object* v_a_2853_){
_start:
{
lean_object* v___x_2855_; 
v___x_2855_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_setRetLiveVars___redArg(v_a_2848_, v_a_2849_);
return v___x_2855_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_setRetLiveVars___boxed(lean_object* v_a_2856_, lean_object* v_a_2857_, lean_object* v_a_2858_, lean_object* v_a_2859_, lean_object* v_a_2860_, lean_object* v_a_2861_, lean_object* v_a_2862_){
_start:
{
lean_object* v_res_2863_; 
v_res_2863_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_setRetLiveVars(v_a_2856_, v_a_2857_, v_a_2858_, v_a_2859_, v_a_2860_, v_a_2861_);
lean_dec(v_a_2861_);
lean_dec_ref(v_a_2860_);
lean_dec(v_a_2859_);
lean_dec_ref(v_a_2858_);
lean_dec(v_a_2857_);
lean_dec_ref(v_a_2856_);
return v_res_2863_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addInc___redArg(lean_object* v_fvarId_2864_, lean_object* v_k_2865_, lean_object* v_n_2866_, lean_object* v_a_2867_){
_start:
{
lean_object* v___x_2869_; uint8_t v___x_2870_; 
v___x_2869_ = lean_unsigned_to_nat(0u);
v___x_2870_ = lean_nat_dec_eq(v_n_2866_, v___x_2869_);
if (v___x_2870_ == 0)
{
lean_object* v_varMap_2871_; lean_object* v___f_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; uint8_t v___y_2876_; uint8_t v_isDefiniteRef_2880_; 
v_varMap_2871_ = lean_ctor_get(v_a_2867_, 2);
lean_inc(v_varMap_2871_);
lean_dec_ref(v_a_2867_);
v___f_2872_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getVarInfo___redArg___closed__0));
v___x_2873_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_instInhabitedVarInfo_default));
lean_inc(v_fvarId_2864_);
v___x_2874_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(v___f_2872_, v___x_2873_, v_varMap_2871_, v_fvarId_2864_);
v_isDefiniteRef_2880_ = lean_ctor_get_uint8(v___x_2874_, sizeof(void*)*1 + 1);
if (v_isDefiniteRef_2880_ == 0)
{
uint8_t v___x_2881_; 
v___x_2881_ = 1;
v___y_2876_ = v___x_2881_;
goto v___jp_2875_;
}
else
{
v___y_2876_ = v___x_2870_;
goto v___jp_2875_;
}
v___jp_2875_:
{
uint8_t v_persistent_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; 
v_persistent_2877_ = lean_ctor_get_uint8(v___x_2874_, sizeof(void*)*1 + 2);
lean_dec(v___x_2874_);
v___x_2878_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v___x_2878_, 0, v_fvarId_2864_);
lean_ctor_set(v___x_2878_, 1, v_n_2866_);
lean_ctor_set(v___x_2878_, 2, v_k_2865_);
lean_ctor_set_uint8(v___x_2878_, sizeof(void*)*3, v___y_2876_);
lean_ctor_set_uint8(v___x_2878_, sizeof(void*)*3 + 1, v_persistent_2877_);
v___x_2879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2879_, 0, v___x_2878_);
return v___x_2879_;
}
}
else
{
lean_object* v___x_2882_; 
lean_dec_ref(v_a_2867_);
lean_dec(v_n_2866_);
lean_dec(v_fvarId_2864_);
v___x_2882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2882_, 0, v_k_2865_);
return v___x_2882_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addInc___redArg___boxed(lean_object* v_fvarId_2883_, lean_object* v_k_2884_, lean_object* v_n_2885_, lean_object* v_a_2886_, lean_object* v_a_2887_){
_start:
{
lean_object* v_res_2888_; 
v_res_2888_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addInc___redArg(v_fvarId_2883_, v_k_2884_, v_n_2885_, v_a_2886_);
return v_res_2888_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addInc(lean_object* v_fvarId_2889_, lean_object* v_k_2890_, lean_object* v_n_2891_, lean_object* v_a_2892_, lean_object* v_a_2893_, lean_object* v_a_2894_, lean_object* v_a_2895_, lean_object* v_a_2896_, lean_object* v_a_2897_){
_start:
{
lean_object* v___x_2899_; uint8_t v___x_2900_; 
v___x_2899_ = lean_unsigned_to_nat(0u);
v___x_2900_ = lean_nat_dec_eq(v_n_2891_, v___x_2899_);
if (v___x_2900_ == 0)
{
lean_object* v_varMap_2901_; lean_object* v___f_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; uint8_t v___y_2906_; uint8_t v_isDefiniteRef_2910_; 
v_varMap_2901_ = lean_ctor_get(v_a_2892_, 2);
lean_inc(v_varMap_2901_);
lean_dec_ref(v_a_2892_);
v___f_2902_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getVarInfo___redArg___closed__0));
v___x_2903_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_instInhabitedVarInfo_default));
lean_inc(v_fvarId_2889_);
v___x_2904_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(v___f_2902_, v___x_2903_, v_varMap_2901_, v_fvarId_2889_);
v_isDefiniteRef_2910_ = lean_ctor_get_uint8(v___x_2904_, sizeof(void*)*1 + 1);
if (v_isDefiniteRef_2910_ == 0)
{
uint8_t v___x_2911_; 
v___x_2911_ = 1;
v___y_2906_ = v___x_2911_;
goto v___jp_2905_;
}
else
{
v___y_2906_ = v___x_2900_;
goto v___jp_2905_;
}
v___jp_2905_:
{
uint8_t v_persistent_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; 
v_persistent_2907_ = lean_ctor_get_uint8(v___x_2904_, sizeof(void*)*1 + 2);
lean_dec(v___x_2904_);
v___x_2908_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v___x_2908_, 0, v_fvarId_2889_);
lean_ctor_set(v___x_2908_, 1, v_n_2891_);
lean_ctor_set(v___x_2908_, 2, v_k_2890_);
lean_ctor_set_uint8(v___x_2908_, sizeof(void*)*3, v___y_2906_);
lean_ctor_set_uint8(v___x_2908_, sizeof(void*)*3 + 1, v_persistent_2907_);
v___x_2909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2909_, 0, v___x_2908_);
return v___x_2909_;
}
}
else
{
lean_object* v___x_2912_; 
lean_dec_ref(v_a_2892_);
lean_dec(v_n_2891_);
lean_dec(v_fvarId_2889_);
v___x_2912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2912_, 0, v_k_2890_);
return v___x_2912_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addInc___boxed(lean_object* v_fvarId_2913_, lean_object* v_k_2914_, lean_object* v_n_2915_, lean_object* v_a_2916_, lean_object* v_a_2917_, lean_object* v_a_2918_, lean_object* v_a_2919_, lean_object* v_a_2920_, lean_object* v_a_2921_, lean_object* v_a_2922_){
_start:
{
lean_object* v_res_2923_; 
v_res_2923_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addInc(v_fvarId_2913_, v_k_2914_, v_n_2915_, v_a_2916_, v_a_2917_, v_a_2918_, v_a_2919_, v_a_2920_, v_a_2921_);
lean_dec(v_a_2921_);
lean_dec_ref(v_a_2920_);
lean_dec(v_a_2919_);
lean_dec_ref(v_a_2918_);
lean_dec(v_a_2917_);
return v_res_2923_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec___redArg(lean_object* v_fvarId_2924_, lean_object* v_k_2925_, lean_object* v_a_2926_){
_start:
{
lean_object* v_varMap_2928_; lean_object* v___f_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; uint8_t v_isDefiniteRef_2932_; lean_object* v___x_2933_; uint8_t v___y_2935_; 
v_varMap_2928_ = lean_ctor_get(v_a_2926_, 2);
lean_inc(v_varMap_2928_);
lean_dec_ref(v_a_2926_);
v___f_2929_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getVarInfo___redArg___closed__0));
v___x_2930_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_instInhabitedVarInfo_default));
lean_inc(v_fvarId_2924_);
v___x_2931_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(v___f_2929_, v___x_2930_, v_varMap_2928_, v_fvarId_2924_);
v_isDefiniteRef_2932_ = lean_ctor_get_uint8(v___x_2931_, sizeof(void*)*1 + 1);
v___x_2933_ = lean_unsigned_to_nat(1u);
if (v_isDefiniteRef_2932_ == 0)
{
uint8_t v___x_2939_; 
v___x_2939_ = 1;
v___y_2935_ = v___x_2939_;
goto v___jp_2934_;
}
else
{
uint8_t v___x_2940_; 
v___x_2940_ = 0;
v___y_2935_ = v___x_2940_;
goto v___jp_2934_;
}
v___jp_2934_:
{
uint8_t v_persistent_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; 
v_persistent_2936_ = lean_ctor_get_uint8(v___x_2931_, sizeof(void*)*1 + 2);
lean_dec(v___x_2931_);
v___x_2937_ = lean_alloc_ctor(12, 3, 2);
lean_ctor_set(v___x_2937_, 0, v_fvarId_2924_);
lean_ctor_set(v___x_2937_, 1, v___x_2933_);
lean_ctor_set(v___x_2937_, 2, v_k_2925_);
lean_ctor_set_uint8(v___x_2937_, sizeof(void*)*3, v___y_2935_);
lean_ctor_set_uint8(v___x_2937_, sizeof(void*)*3 + 1, v_persistent_2936_);
v___x_2938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2938_, 0, v___x_2937_);
return v___x_2938_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec___redArg___boxed(lean_object* v_fvarId_2941_, lean_object* v_k_2942_, lean_object* v_a_2943_, lean_object* v_a_2944_){
_start:
{
lean_object* v_res_2945_; 
v_res_2945_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec___redArg(v_fvarId_2941_, v_k_2942_, v_a_2943_);
return v_res_2945_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec(lean_object* v_fvarId_2946_, lean_object* v_k_2947_, lean_object* v_a_2948_, lean_object* v_a_2949_, lean_object* v_a_2950_, lean_object* v_a_2951_, lean_object* v_a_2952_, lean_object* v_a_2953_){
_start:
{
lean_object* v_varMap_2955_; lean_object* v___f_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; uint8_t v_isDefiniteRef_2959_; lean_object* v___x_2960_; uint8_t v___y_2962_; 
v_varMap_2955_ = lean_ctor_get(v_a_2948_, 2);
lean_inc(v_varMap_2955_);
lean_dec_ref(v_a_2948_);
v___f_2956_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getVarInfo___redArg___closed__0));
v___x_2957_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_instInhabitedVarInfo_default));
lean_inc(v_fvarId_2946_);
v___x_2958_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(v___f_2956_, v___x_2957_, v_varMap_2955_, v_fvarId_2946_);
v_isDefiniteRef_2959_ = lean_ctor_get_uint8(v___x_2958_, sizeof(void*)*1 + 1);
v___x_2960_ = lean_unsigned_to_nat(1u);
if (v_isDefiniteRef_2959_ == 0)
{
uint8_t v___x_2966_; 
v___x_2966_ = 1;
v___y_2962_ = v___x_2966_;
goto v___jp_2961_;
}
else
{
uint8_t v___x_2967_; 
v___x_2967_ = 0;
v___y_2962_ = v___x_2967_;
goto v___jp_2961_;
}
v___jp_2961_:
{
uint8_t v_persistent_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; 
v_persistent_2963_ = lean_ctor_get_uint8(v___x_2958_, sizeof(void*)*1 + 2);
lean_dec(v___x_2958_);
v___x_2964_ = lean_alloc_ctor(12, 3, 2);
lean_ctor_set(v___x_2964_, 0, v_fvarId_2946_);
lean_ctor_set(v___x_2964_, 1, v___x_2960_);
lean_ctor_set(v___x_2964_, 2, v_k_2947_);
lean_ctor_set_uint8(v___x_2964_, sizeof(void*)*3, v___y_2962_);
lean_ctor_set_uint8(v___x_2964_, sizeof(void*)*3 + 1, v_persistent_2963_);
v___x_2965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2965_, 0, v___x_2964_);
return v___x_2965_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec___boxed(lean_object* v_fvarId_2968_, lean_object* v_k_2969_, lean_object* v_a_2970_, lean_object* v_a_2971_, lean_object* v_a_2972_, lean_object* v_a_2973_, lean_object* v_a_2974_, lean_object* v_a_2975_, lean_object* v_a_2976_){
_start:
{
lean_object* v_res_2977_; 
v_res_2977_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec(v_fvarId_2968_, v_k_2969_, v_a_2970_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_, v_a_2975_);
lean_dec(v_a_2975_);
lean_dec_ref(v_a_2974_);
lean_dec(v_a_2973_);
lean_dec_ref(v_a_2972_);
lean_dec(v_a_2971_);
return v_res_2977_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; 
v___x_2981_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__0___redArg___closed__2));
v___x_2982_ = lean_unsigned_to_nat(13u);
v___x_2983_ = lean_unsigned_to_nat(227u);
v___x_2984_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__0___redArg___closed__1));
v___x_2985_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__0___redArg___closed__0));
v___x_2986_ = l_mkPanicMessageWithDecl(v___x_2985_, v___x_2984_, v___x_2983_, v___x_2982_, v___x_2981_);
return v___x_2986_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__0___redArg(lean_object* v_inst_2987_, lean_object* v_t_2988_, lean_object* v_k_2989_){
_start:
{
if (lean_obj_tag(v_t_2988_) == 0)
{
lean_object* v_k_2990_; lean_object* v_v_2991_; lean_object* v_l_2992_; lean_object* v_r_2993_; uint8_t v___x_2994_; 
v_k_2990_ = lean_ctor_get(v_t_2988_, 1);
v_v_2991_ = lean_ctor_get(v_t_2988_, 2);
v_l_2992_ = lean_ctor_get(v_t_2988_, 3);
v_r_2993_ = lean_ctor_get(v_t_2988_, 4);
v___x_2994_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2989_, v_k_2990_);
switch(v___x_2994_)
{
case 0:
{
v_t_2988_ = v_l_2992_;
goto _start;
}
case 1:
{
lean_dec(v_inst_2987_);
lean_inc(v_v_2991_);
return v_v_2991_;
}
default: 
{
v_t_2988_ = v_r_2993_;
goto _start;
}
}
}
else
{
lean_object* v___x_2997_; lean_object* v___x_2998_; 
v___x_2997_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__0___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__0___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__0___redArg___closed__3);
v___x_2998_ = lean_panic_fn(v_inst_2987_, v___x_2997_);
return v___x_2998_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__0___redArg___boxed(lean_object* v_inst_2999_, lean_object* v_t_3000_, lean_object* v_k_3001_){
_start:
{
lean_object* v_res_3002_; 
v_res_3002_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__0___redArg(v_inst_2999_, v_t_3000_, v_k_3001_);
lean_dec(v_k_3001_);
lean_dec(v_t_3000_);
return v_res_3002_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3___redArg(lean_object* v_as_3003_, size_t v_i_3004_, size_t v_stop_3005_, lean_object* v_b_3006_, lean_object* v___y_3007_){
_start:
{
uint8_t v___x_3009_; 
v___x_3009_ = lean_usize_dec_eq(v_i_3004_, v_stop_3005_);
if (v___x_3009_ == 0)
{
lean_object* v___x_3010_; lean_object* v_fst_3011_; lean_object* v_varMap_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; uint8_t v_isDefiniteRef_3015_; lean_object* v___x_3016_; uint8_t v___y_3018_; 
v___x_3010_ = lean_array_uget_borrowed(v_as_3003_, v_i_3004_);
v_fst_3011_ = lean_ctor_get(v___x_3010_, 0);
v_varMap_3012_ = lean_ctor_get(v___y_3007_, 2);
v___x_3013_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_instInhabitedVarInfo_default));
v___x_3014_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__0___redArg(v___x_3013_, v_varMap_3012_, v_fst_3011_);
v_isDefiniteRef_3015_ = lean_ctor_get_uint8(v___x_3014_, sizeof(void*)*1 + 1);
v___x_3016_ = lean_unsigned_to_nat(1u);
if (v_isDefiniteRef_3015_ == 0)
{
uint8_t v___x_3024_; 
v___x_3024_ = 1;
v___y_3018_ = v___x_3024_;
goto v___jp_3017_;
}
else
{
v___y_3018_ = v___x_3009_;
goto v___jp_3017_;
}
v___jp_3017_:
{
uint8_t v_persistent_3019_; lean_object* v___x_3020_; size_t v___x_3021_; size_t v___x_3022_; 
v_persistent_3019_ = lean_ctor_get_uint8(v___x_3014_, sizeof(void*)*1 + 2);
lean_dec(v___x_3014_);
lean_inc(v_fst_3011_);
v___x_3020_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v___x_3020_, 0, v_fst_3011_);
lean_ctor_set(v___x_3020_, 1, v___x_3016_);
lean_ctor_set(v___x_3020_, 2, v_b_3006_);
lean_ctor_set_uint8(v___x_3020_, sizeof(void*)*3, v___y_3018_);
lean_ctor_set_uint8(v___x_3020_, sizeof(void*)*3 + 1, v_persistent_3019_);
v___x_3021_ = ((size_t)1ULL);
v___x_3022_ = lean_usize_add(v_i_3004_, v___x_3021_);
v_i_3004_ = v___x_3022_;
v_b_3006_ = v___x_3020_;
goto _start;
}
}
else
{
lean_object* v___x_3025_; 
v___x_3025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3025_, 0, v_b_3006_);
return v___x_3025_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3___redArg___boxed(lean_object* v_as_3026_, lean_object* v_i_3027_, lean_object* v_stop_3028_, lean_object* v_b_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_){
_start:
{
size_t v_i_boxed_3032_; size_t v_stop_boxed_3033_; lean_object* v_res_3034_; 
v_i_boxed_3032_ = lean_unbox_usize(v_i_3027_);
lean_dec(v_i_3027_);
v_stop_boxed_3033_ = lean_unbox_usize(v_stop_3028_);
lean_dec(v_stop_3028_);
v_res_3034_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3___redArg(v_as_3026_, v_i_boxed_3032_, v_stop_boxed_3033_, v_b_3029_, v___y_3030_);
lean_dec_ref(v___y_3030_);
lean_dec_ref(v_as_3026_);
return v_res_3034_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__4___redArg___lam__0(lean_object* v_x_3035_, lean_object* v_x_3036_){
_start:
{
lean_object* v_snd_3037_; lean_object* v_snd_3038_; uint8_t v___x_3039_; 
v_snd_3037_ = lean_ctor_get(v_x_3035_, 1);
v_snd_3038_ = lean_ctor_get(v_x_3036_, 1);
v___x_3039_ = lean_nat_dec_lt(v_snd_3037_, v_snd_3038_);
return v___x_3039_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__4___redArg___lam__0___boxed(lean_object* v_x_3040_, lean_object* v_x_3041_){
_start:
{
uint8_t v_res_3042_; lean_object* v_r_3043_; 
v_res_3042_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__4___redArg___lam__0(v_x_3040_, v_x_3041_);
lean_dec_ref(v_x_3041_);
lean_dec_ref(v_x_3040_);
v_r_3043_ = lean_box(v_res_3042_);
return v_r_3043_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__4___redArg(lean_object* v_as_3045_, lean_object* v_lo_3046_, lean_object* v_hi_3047_){
_start:
{
uint8_t v___x_3048_; 
v___x_3048_ = lean_nat_dec_lt(v_lo_3046_, v_hi_3047_);
if (v___x_3048_ == 0)
{
lean_dec(v_lo_3046_);
return v_as_3045_;
}
else
{
lean_object* v___f_3049_; lean_object* v___x_3050_; lean_object* v_fst_3051_; lean_object* v_snd_3052_; uint8_t v___x_3053_; 
v___f_3049_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__4___redArg___closed__0));
lean_inc(v_lo_3046_);
v___x_3050_ = l_Array_qpartition___redArg(v_as_3045_, v___f_3049_, v_lo_3046_, v_hi_3047_);
v_fst_3051_ = lean_ctor_get(v___x_3050_, 0);
lean_inc(v_fst_3051_);
v_snd_3052_ = lean_ctor_get(v___x_3050_, 1);
lean_inc(v_snd_3052_);
lean_dec_ref(v___x_3050_);
v___x_3053_ = lean_nat_dec_le(v_hi_3047_, v_fst_3051_);
if (v___x_3053_ == 0)
{
lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; 
v___x_3054_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__4___redArg(v_snd_3052_, v_lo_3046_, v_fst_3051_);
v___x_3055_ = lean_unsigned_to_nat(1u);
v___x_3056_ = lean_nat_add(v_fst_3051_, v___x_3055_);
lean_dec(v_fst_3051_);
v_as_3045_ = v___x_3054_;
v_lo_3046_ = v___x_3056_;
goto _start;
}
else
{
lean_dec(v_fst_3051_);
lean_dec(v_lo_3046_);
return v_snd_3052_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__4___redArg___boxed(lean_object* v_as_3058_, lean_object* v_lo_3059_, lean_object* v_hi_3060_){
_start:
{
lean_object* v_res_3061_; 
v_res_3061_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__4___redArg(v_as_3058_, v_lo_3059_, v_hi_3060_);
lean_dec(v_hi_3060_);
return v_res_3061_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__5___redArg(lean_object* v_as_3062_, size_t v_i_3063_, size_t v_stop_3064_, lean_object* v_b_3065_, lean_object* v___y_3066_){
_start:
{
uint8_t v___x_3068_; 
v___x_3068_ = lean_usize_dec_eq(v_i_3063_, v_stop_3064_);
if (v___x_3068_ == 0)
{
lean_object* v___x_3069_; lean_object* v_fst_3070_; lean_object* v_varMap_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; uint8_t v_isDefiniteRef_3074_; lean_object* v___x_3075_; uint8_t v___y_3077_; 
v___x_3069_ = lean_array_uget_borrowed(v_as_3062_, v_i_3063_);
v_fst_3070_ = lean_ctor_get(v___x_3069_, 0);
v_varMap_3071_ = lean_ctor_get(v___y_3066_, 2);
v___x_3072_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_instInhabitedVarInfo_default));
v___x_3073_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__0___redArg(v___x_3072_, v_varMap_3071_, v_fst_3070_);
v_isDefiniteRef_3074_ = lean_ctor_get_uint8(v___x_3073_, sizeof(void*)*1 + 1);
v___x_3075_ = lean_unsigned_to_nat(1u);
if (v_isDefiniteRef_3074_ == 0)
{
uint8_t v___x_3083_; 
v___x_3083_ = 1;
v___y_3077_ = v___x_3083_;
goto v___jp_3076_;
}
else
{
v___y_3077_ = v___x_3068_;
goto v___jp_3076_;
}
v___jp_3076_:
{
uint8_t v_persistent_3078_; lean_object* v___x_3079_; size_t v___x_3080_; size_t v___x_3081_; 
v_persistent_3078_ = lean_ctor_get_uint8(v___x_3073_, sizeof(void*)*1 + 2);
lean_dec(v___x_3073_);
lean_inc(v_fst_3070_);
v___x_3079_ = lean_alloc_ctor(12, 3, 2);
lean_ctor_set(v___x_3079_, 0, v_fst_3070_);
lean_ctor_set(v___x_3079_, 1, v___x_3075_);
lean_ctor_set(v___x_3079_, 2, v_b_3065_);
lean_ctor_set_uint8(v___x_3079_, sizeof(void*)*3, v___y_3077_);
lean_ctor_set_uint8(v___x_3079_, sizeof(void*)*3 + 1, v_persistent_3078_);
v___x_3080_ = ((size_t)1ULL);
v___x_3081_ = lean_usize_add(v_i_3063_, v___x_3080_);
v_i_3063_ = v___x_3081_;
v_b_3065_ = v___x_3079_;
goto _start;
}
}
else
{
lean_object* v___x_3084_; 
v___x_3084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3084_, 0, v_b_3065_);
return v___x_3084_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__5___redArg___boxed(lean_object* v_as_3085_, lean_object* v_i_3086_, lean_object* v_stop_3087_, lean_object* v_b_3088_, lean_object* v___y_3089_, lean_object* v___y_3090_){
_start:
{
size_t v_i_boxed_3091_; size_t v_stop_boxed_3092_; lean_object* v_res_3093_; 
v_i_boxed_3091_ = lean_unbox_usize(v_i_3086_);
lean_dec(v_i_3086_);
v_stop_boxed_3092_ = lean_unbox_usize(v_stop_3087_);
lean_dec(v_stop_3087_);
v_res_3093_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__5___redArg(v_as_3085_, v_i_boxed_3091_, v_stop_boxed_3092_, v_b_3088_, v___y_3089_);
lean_dec_ref(v___y_3089_);
lean_dec_ref(v_as_3085_);
return v_res_3093_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__1___redArg(lean_object* v_altLiveVars_3094_, lean_object* v_a_3095_, lean_object* v_a_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_){
_start:
{
if (lean_obj_tag(v_a_3095_) == 0)
{
lean_object* v___x_3100_; lean_object* v___x_3101_; 
v___x_3100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3100_, 0, v_a_3096_);
v___x_3101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3101_, 0, v___x_3100_);
return v___x_3101_;
}
else
{
lean_object* v_key_3102_; lean_object* v_tail_3103_; lean_object* v_fst_3104_; lean_object* v_snd_3105_; lean_object* v___x_3107_; uint8_t v_isShared_3108_; uint8_t v_isSharedCheck_3152_; 
v_key_3102_ = lean_ctor_get(v_a_3095_, 0);
v_tail_3103_ = lean_ctor_get(v_a_3095_, 2);
v_fst_3104_ = lean_ctor_get(v_a_3096_, 0);
v_snd_3105_ = lean_ctor_get(v_a_3096_, 1);
v_isSharedCheck_3152_ = !lean_is_exclusive(v_a_3096_);
if (v_isSharedCheck_3152_ == 0)
{
v___x_3107_ = v_a_3096_;
v_isShared_3108_ = v_isSharedCheck_3152_;
goto v_resetjp_3106_;
}
else
{
lean_inc(v_snd_3105_);
lean_inc(v_fst_3104_);
lean_dec(v_a_3096_);
v___x_3107_ = lean_box(0);
v_isShared_3108_ = v_isSharedCheck_3152_;
goto v_resetjp_3106_;
}
v_resetjp_3106_:
{
lean_object* v_varMap_3109_; lean_object* v_vars_3110_; lean_object* v_borrows_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; uint8_t v___x_3114_; 
v_varMap_3109_ = lean_ctor_get(v___y_3097_, 2);
v_vars_3110_ = lean_ctor_get(v_altLiveVars_3094_, 0);
v_borrows_3111_ = lean_ctor_get(v_altLiveVars_3094_, 1);
v___x_3112_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_instInhabitedVarInfo_default));
v___x_3113_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__0___redArg(v___x_3112_, v_varMap_3109_, v_key_3102_);
v___x_3114_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_isAccessible_spec__0___redArg(v_vars_3110_, v_key_3102_);
if (v___x_3114_ == 0)
{
lean_object* v___x_3115_; uint8_t v_isPossibleRef_3121_; 
v___x_3115_ = lean_st_ref_get(v___y_3098_);
v_isPossibleRef_3121_ = lean_ctor_get_uint8(v___x_3113_, sizeof(void*)*1);
if (v_isPossibleRef_3121_ == 0)
{
lean_dec(v___x_3115_);
lean_dec(v___x_3113_);
goto v___jp_3116_;
}
else
{
lean_object* v_idx_3122_; lean_object* v_borrows_3123_; lean_object* v___x_3125_; uint8_t v_isShared_3126_; uint8_t v_isSharedCheck_3134_; 
v_idx_3122_ = lean_ctor_get(v___x_3113_, 0);
lean_inc(v_idx_3122_);
lean_dec(v___x_3113_);
v_borrows_3123_ = lean_ctor_get(v___x_3115_, 1);
v_isSharedCheck_3134_ = !lean_is_exclusive(v___x_3115_);
if (v_isSharedCheck_3134_ == 0)
{
lean_object* v_unused_3135_; 
v_unused_3135_ = lean_ctor_get(v___x_3115_, 0);
lean_dec(v_unused_3135_);
v___x_3125_ = v___x_3115_;
v_isShared_3126_ = v_isSharedCheck_3134_;
goto v_resetjp_3124_;
}
else
{
lean_inc(v_borrows_3123_);
lean_dec(v___x_3115_);
v___x_3125_ = lean_box(0);
v_isShared_3126_ = v_isSharedCheck_3134_;
goto v_resetjp_3124_;
}
v_resetjp_3124_:
{
uint8_t v___x_3127_; 
v___x_3127_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_isAccessible_spec__0___redArg(v_borrows_3123_, v_key_3102_);
lean_dec_ref(v_borrows_3123_);
if (v___x_3127_ == 0)
{
lean_object* v___x_3129_; 
lean_del_object(v___x_3107_);
lean_inc(v_key_3102_);
if (v_isShared_3126_ == 0)
{
lean_ctor_set(v___x_3125_, 1, v_idx_3122_);
lean_ctor_set(v___x_3125_, 0, v_key_3102_);
v___x_3129_ = v___x_3125_;
goto v_reusejp_3128_;
}
else
{
lean_object* v_reuseFailAlloc_3133_; 
v_reuseFailAlloc_3133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3133_, 0, v_key_3102_);
lean_ctor_set(v_reuseFailAlloc_3133_, 1, v_idx_3122_);
v___x_3129_ = v_reuseFailAlloc_3133_;
goto v_reusejp_3128_;
}
v_reusejp_3128_:
{
lean_object* v___x_3130_; lean_object* v___x_3131_; 
v___x_3130_ = lean_array_push(v_snd_3105_, v___x_3129_);
v___x_3131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3131_, 0, v_fst_3104_);
lean_ctor_set(v___x_3131_, 1, v___x_3130_);
v_a_3095_ = v_tail_3103_;
v_a_3096_ = v___x_3131_;
goto _start;
}
}
else
{
lean_del_object(v___x_3125_);
lean_dec(v_idx_3122_);
goto v___jp_3116_;
}
}
}
v___jp_3116_:
{
lean_object* v___x_3118_; 
if (v_isShared_3108_ == 0)
{
v___x_3118_ = v___x_3107_;
goto v_reusejp_3117_;
}
else
{
lean_object* v_reuseFailAlloc_3120_; 
v_reuseFailAlloc_3120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3120_, 0, v_fst_3104_);
lean_ctor_set(v_reuseFailAlloc_3120_, 1, v_snd_3105_);
v___x_3118_ = v_reuseFailAlloc_3120_;
goto v_reusejp_3117_;
}
v_reusejp_3117_:
{
v_a_3095_ = v_tail_3103_;
v_a_3096_ = v___x_3118_;
goto _start;
}
}
}
else
{
lean_object* v___x_3136_; uint8_t v___y_3143_; lean_object* v_borrows_3149_; uint8_t v___x_3150_; 
v___x_3136_ = lean_st_ref_get(v___y_3098_);
v_borrows_3149_ = lean_ctor_get(v___x_3136_, 1);
lean_inc_ref(v_borrows_3149_);
lean_dec(v___x_3136_);
v___x_3150_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_isAccessible_spec__0___redArg(v_borrows_3149_, v_key_3102_);
lean_dec_ref(v_borrows_3149_);
if (v___x_3150_ == 0)
{
v___y_3143_ = v___x_3150_;
goto v___jp_3142_;
}
else
{
uint8_t v___x_3151_; 
v___x_3151_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_isAccessible_spec__0___redArg(v_borrows_3111_, v_key_3102_);
if (v___x_3151_ == 0)
{
v___y_3143_ = v___x_3150_;
goto v___jp_3142_;
}
else
{
lean_dec(v___x_3113_);
goto v___jp_3137_;
}
}
v___jp_3137_:
{
lean_object* v___x_3139_; 
if (v_isShared_3108_ == 0)
{
v___x_3139_ = v___x_3107_;
goto v_reusejp_3138_;
}
else
{
lean_object* v_reuseFailAlloc_3141_; 
v_reuseFailAlloc_3141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3141_, 0, v_fst_3104_);
lean_ctor_set(v_reuseFailAlloc_3141_, 1, v_snd_3105_);
v___x_3139_ = v_reuseFailAlloc_3141_;
goto v_reusejp_3138_;
}
v_reusejp_3138_:
{
v_a_3095_ = v_tail_3103_;
v_a_3096_ = v___x_3139_;
goto _start;
}
}
v___jp_3142_:
{
if (v___y_3143_ == 0)
{
lean_dec(v___x_3113_);
goto v___jp_3137_;
}
else
{
lean_object* v_idx_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; 
lean_del_object(v___x_3107_);
v_idx_3144_ = lean_ctor_get(v___x_3113_, 0);
lean_inc(v_idx_3144_);
lean_dec(v___x_3113_);
lean_inc(v_key_3102_);
v___x_3145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3145_, 0, v_key_3102_);
lean_ctor_set(v___x_3145_, 1, v_idx_3144_);
v___x_3146_ = lean_array_push(v_fst_3104_, v___x_3145_);
v___x_3147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3147_, 0, v___x_3146_);
lean_ctor_set(v___x_3147_, 1, v_snd_3105_);
v_a_3095_ = v_tail_3103_;
v_a_3096_ = v___x_3147_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__1___redArg___boxed(lean_object* v_altLiveVars_3153_, lean_object* v_a_3154_, lean_object* v_a_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_){
_start:
{
lean_object* v_res_3159_; 
v_res_3159_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__1___redArg(v_altLiveVars_3153_, v_a_3154_, v_a_3155_, v___y_3156_, v___y_3157_);
lean_dec(v___y_3157_);
lean_dec_ref(v___y_3156_);
lean_dec(v_a_3154_);
lean_dec_ref(v_altLiveVars_3153_);
return v_res_3159_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__2(lean_object* v_altLiveVars_3160_, lean_object* v_as_3161_, size_t v_sz_3162_, size_t v_i_3163_, lean_object* v_b_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_){
_start:
{
uint8_t v___x_3172_; 
v___x_3172_ = lean_usize_dec_lt(v_i_3163_, v_sz_3162_);
if (v___x_3172_ == 0)
{
lean_object* v___x_3173_; 
v___x_3173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3173_, 0, v_b_3164_);
return v___x_3173_;
}
else
{
lean_object* v_a_3174_; lean_object* v___x_3175_; 
v_a_3174_ = lean_array_uget_borrowed(v_as_3161_, v_i_3163_);
v___x_3175_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__1___redArg(v_altLiveVars_3160_, v_a_3174_, v_b_3164_, v___y_3165_, v___y_3166_);
if (lean_obj_tag(v___x_3175_) == 0)
{
lean_object* v_a_3176_; lean_object* v___x_3178_; uint8_t v_isShared_3179_; uint8_t v_isSharedCheck_3188_; 
v_a_3176_ = lean_ctor_get(v___x_3175_, 0);
v_isSharedCheck_3188_ = !lean_is_exclusive(v___x_3175_);
if (v_isSharedCheck_3188_ == 0)
{
v___x_3178_ = v___x_3175_;
v_isShared_3179_ = v_isSharedCheck_3188_;
goto v_resetjp_3177_;
}
else
{
lean_inc(v_a_3176_);
lean_dec(v___x_3175_);
v___x_3178_ = lean_box(0);
v_isShared_3179_ = v_isSharedCheck_3188_;
goto v_resetjp_3177_;
}
v_resetjp_3177_:
{
if (lean_obj_tag(v_a_3176_) == 0)
{
lean_object* v_a_3180_; lean_object* v___x_3182_; 
v_a_3180_ = lean_ctor_get(v_a_3176_, 0);
lean_inc(v_a_3180_);
lean_dec_ref(v_a_3176_);
if (v_isShared_3179_ == 0)
{
lean_ctor_set(v___x_3178_, 0, v_a_3180_);
v___x_3182_ = v___x_3178_;
goto v_reusejp_3181_;
}
else
{
lean_object* v_reuseFailAlloc_3183_; 
v_reuseFailAlloc_3183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3183_, 0, v_a_3180_);
v___x_3182_ = v_reuseFailAlloc_3183_;
goto v_reusejp_3181_;
}
v_reusejp_3181_:
{
return v___x_3182_;
}
}
else
{
lean_object* v_a_3184_; size_t v___x_3185_; size_t v___x_3186_; 
lean_del_object(v___x_3178_);
v_a_3184_ = lean_ctor_get(v_a_3176_, 0);
lean_inc(v_a_3184_);
lean_dec_ref(v_a_3176_);
v___x_3185_ = ((size_t)1ULL);
v___x_3186_ = lean_usize_add(v_i_3163_, v___x_3185_);
v_i_3163_ = v___x_3186_;
v_b_3164_ = v_a_3184_;
goto _start;
}
}
}
else
{
lean_object* v_a_3189_; lean_object* v___x_3191_; uint8_t v_isShared_3192_; uint8_t v_isSharedCheck_3196_; 
v_a_3189_ = lean_ctor_get(v___x_3175_, 0);
v_isSharedCheck_3196_ = !lean_is_exclusive(v___x_3175_);
if (v_isSharedCheck_3196_ == 0)
{
v___x_3191_ = v___x_3175_;
v_isShared_3192_ = v_isSharedCheck_3196_;
goto v_resetjp_3190_;
}
else
{
lean_inc(v_a_3189_);
lean_dec(v___x_3175_);
v___x_3191_ = lean_box(0);
v_isShared_3192_ = v_isSharedCheck_3196_;
goto v_resetjp_3190_;
}
v_resetjp_3190_:
{
lean_object* v___x_3194_; 
if (v_isShared_3192_ == 0)
{
v___x_3194_ = v___x_3191_;
goto v_reusejp_3193_;
}
else
{
lean_object* v_reuseFailAlloc_3195_; 
v_reuseFailAlloc_3195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3195_, 0, v_a_3189_);
v___x_3194_ = v_reuseFailAlloc_3195_;
goto v_reusejp_3193_;
}
v_reusejp_3193_:
{
return v___x_3194_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__2___boxed(lean_object* v_altLiveVars_3197_, lean_object* v_as_3198_, lean_object* v_sz_3199_, lean_object* v_i_3200_, lean_object* v_b_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_){
_start:
{
size_t v_sz_boxed_3209_; size_t v_i_boxed_3210_; lean_object* v_res_3211_; 
v_sz_boxed_3209_ = lean_unbox_usize(v_sz_3199_);
lean_dec(v_sz_3199_);
v_i_boxed_3210_ = lean_unbox_usize(v_i_3200_);
lean_dec(v_i_3200_);
v_res_3211_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__2(v_altLiveVars_3197_, v_as_3198_, v_sz_boxed_3209_, v_i_boxed_3210_, v_b_3201_, v___y_3202_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_, v___y_3207_);
lean_dec(v___y_3207_);
lean_dec_ref(v___y_3206_);
lean_dec(v___y_3205_);
lean_dec_ref(v___y_3204_);
lean_dec(v___y_3203_);
lean_dec_ref(v___y_3202_);
lean_dec_ref(v_as_3198_);
lean_dec_ref(v_altLiveVars_3197_);
return v_res_3211_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt___closed__1(void){
_start:
{
lean_object* v_incs_3214_; lean_object* v___x_3215_; 
v_incs_3214_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt___closed__0));
v___x_3215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3215_, 0, v_incs_3214_);
lean_ctor_set(v___x_3215_, 1, v_incs_3214_);
return v___x_3215_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt(lean_object* v_altLiveVars_3216_, lean_object* v_k_3217_, lean_object* v_a_3218_, lean_object* v_a_3219_, lean_object* v_a_3220_, lean_object* v_a_3221_, lean_object* v_a_3222_, lean_object* v_a_3223_){
_start:
{
lean_object* v___x_3225_; lean_object* v_vars_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v_buckets_3229_; size_t v_sz_3230_; size_t v___x_3231_; lean_object* v___y_3233_; lean_object* v___y_3234_; lean_object* v___y_3235_; lean_object* v___x_3243_; 
v___x_3225_ = lean_st_ref_get(v_a_3219_);
v_vars_3226_ = lean_ctor_get(v___x_3225_, 0);
lean_inc_ref(v_vars_3226_);
lean_dec(v___x_3225_);
v___x_3227_ = lean_unsigned_to_nat(0u);
v___x_3228_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt___closed__1, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt___closed__1_once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt___closed__1);
v_buckets_3229_ = lean_ctor_get(v_vars_3226_, 1);
lean_inc_ref(v_buckets_3229_);
lean_dec_ref(v_vars_3226_);
v_sz_3230_ = lean_array_size(v_buckets_3229_);
v___x_3231_ = ((size_t)0ULL);
v___x_3243_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__2(v_altLiveVars_3216_, v_buckets_3229_, v_sz_3230_, v___x_3231_, v___x_3228_, v_a_3218_, v_a_3219_, v_a_3220_, v_a_3221_, v_a_3222_, v_a_3223_);
lean_dec_ref(v_buckets_3229_);
if (lean_obj_tag(v___x_3243_) == 0)
{
lean_object* v_a_3244_; lean_object* v___x_3246_; uint8_t v_isShared_3247_; uint8_t v_isSharedCheck_3301_; 
v_a_3244_ = lean_ctor_get(v___x_3243_, 0);
v_isSharedCheck_3301_ = !lean_is_exclusive(v___x_3243_);
if (v_isSharedCheck_3301_ == 0)
{
v___x_3246_ = v___x_3243_;
v_isShared_3247_ = v_isSharedCheck_3301_;
goto v_resetjp_3245_;
}
else
{
lean_inc(v_a_3244_);
lean_dec(v___x_3243_);
v___x_3246_ = lean_box(0);
v_isShared_3247_ = v_isSharedCheck_3301_;
goto v_resetjp_3245_;
}
v_resetjp_3245_:
{
lean_object* v_fst_3248_; lean_object* v_snd_3249_; lean_object* v___y_3251_; lean_object* v___y_3252_; lean_object* v___y_3253_; lean_object* v___y_3254_; lean_object* v___y_3255_; lean_object* v___y_3258_; lean_object* v___y_3259_; lean_object* v___y_3260_; lean_object* v___y_3261_; lean_object* v___y_3262_; lean_object* v___x_3264_; lean_object* v___y_3266_; lean_object* v_a_3267_; lean_object* v___y_3273_; lean_object* v___y_3276_; lean_object* v___y_3291_; lean_object* v___y_3292_; lean_object* v___x_3294_; uint8_t v___x_3295_; 
v_fst_3248_ = lean_ctor_get(v_a_3244_, 0);
lean_inc(v_fst_3248_);
v_snd_3249_ = lean_ctor_get(v_a_3244_, 1);
lean_inc(v_snd_3249_);
lean_dec(v_a_3244_);
v___x_3264_ = lean_unsigned_to_nat(1u);
v___x_3294_ = lean_array_get_size(v_snd_3249_);
v___x_3295_ = lean_nat_dec_eq(v___x_3294_, v___x_3227_);
if (v___x_3295_ == 0)
{
lean_object* v___x_3296_; lean_object* v___y_3298_; uint8_t v___x_3300_; 
v___x_3296_ = lean_nat_sub(v___x_3294_, v___x_3264_);
v___x_3300_ = lean_nat_dec_le(v___x_3227_, v___x_3296_);
if (v___x_3300_ == 0)
{
lean_inc(v___x_3296_);
v___y_3298_ = v___x_3296_;
goto v___jp_3297_;
}
else
{
v___y_3298_ = v___x_3227_;
goto v___jp_3297_;
}
v___jp_3297_:
{
uint8_t v___x_3299_; 
v___x_3299_ = lean_nat_dec_le(v___y_3298_, v___x_3296_);
if (v___x_3299_ == 0)
{
lean_dec(v___x_3296_);
lean_inc(v___y_3298_);
v___y_3291_ = v___y_3298_;
v___y_3292_ = v___y_3298_;
goto v___jp_3290_;
}
else
{
v___y_3291_ = v___y_3298_;
v___y_3292_ = v___x_3296_;
goto v___jp_3290_;
}
}
}
else
{
v___y_3276_ = v_snd_3249_;
goto v___jp_3275_;
}
v___jp_3250_:
{
lean_object* v___x_3256_; 
lean_dec(v___y_3254_);
v___x_3256_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__4___redArg(v_fst_3248_, v___y_3253_, v___y_3255_);
lean_dec(v___y_3255_);
v___y_3233_ = v___y_3251_;
v___y_3234_ = v___y_3252_;
v___y_3235_ = v___x_3256_;
goto v___jp_3232_;
}
v___jp_3257_:
{
uint8_t v___x_3263_; 
v___x_3263_ = lean_nat_dec_le(v___y_3262_, v___y_3258_);
if (v___x_3263_ == 0)
{
lean_dec(v___y_3258_);
lean_inc(v___y_3262_);
v___y_3251_ = v___y_3259_;
v___y_3252_ = v___y_3260_;
v___y_3253_ = v___y_3262_;
v___y_3254_ = v___y_3261_;
v___y_3255_ = v___y_3262_;
goto v___jp_3250_;
}
else
{
v___y_3251_ = v___y_3259_;
v___y_3252_ = v___y_3260_;
v___y_3253_ = v___y_3262_;
v___y_3254_ = v___y_3261_;
v___y_3255_ = v___y_3258_;
goto v___jp_3250_;
}
}
v___jp_3265_:
{
lean_object* v___x_3268_; uint8_t v___x_3269_; 
v___x_3268_ = lean_array_get_size(v_fst_3248_);
v___x_3269_ = lean_nat_dec_eq(v___x_3268_, v___x_3227_);
if (v___x_3269_ == 0)
{
lean_object* v___x_3270_; uint8_t v___x_3271_; 
v___x_3270_ = lean_nat_sub(v___x_3268_, v___x_3264_);
v___x_3271_ = lean_nat_dec_le(v___x_3227_, v___x_3270_);
if (v___x_3271_ == 0)
{
lean_inc(v___x_3270_);
v___y_3258_ = v___x_3270_;
v___y_3259_ = v___y_3266_;
v___y_3260_ = v_a_3267_;
v___y_3261_ = v___x_3268_;
v___y_3262_ = v___x_3270_;
goto v___jp_3257_;
}
else
{
v___y_3258_ = v___x_3270_;
v___y_3259_ = v___y_3266_;
v___y_3260_ = v_a_3267_;
v___y_3261_ = v___x_3268_;
v___y_3262_ = v___x_3227_;
goto v___jp_3257_;
}
}
else
{
v___y_3233_ = v___y_3266_;
v___y_3234_ = v_a_3267_;
v___y_3235_ = v_fst_3248_;
goto v___jp_3232_;
}
}
v___jp_3272_:
{
if (lean_obj_tag(v___y_3273_) == 0)
{
lean_object* v_a_3274_; 
v_a_3274_ = lean_ctor_get(v___y_3273_, 0);
lean_inc(v_a_3274_);
v___y_3266_ = v___y_3273_;
v_a_3267_ = v_a_3274_;
goto v___jp_3265_;
}
else
{
lean_dec(v_fst_3248_);
return v___y_3273_;
}
}
v___jp_3275_:
{
lean_object* v___x_3277_; uint8_t v___x_3278_; 
v___x_3277_ = lean_array_get_size(v___y_3276_);
v___x_3278_ = lean_nat_dec_lt(v___x_3227_, v___x_3277_);
if (v___x_3278_ == 0)
{
lean_object* v___x_3280_; 
lean_dec_ref(v___y_3276_);
lean_inc_ref(v_k_3217_);
if (v_isShared_3247_ == 0)
{
lean_ctor_set(v___x_3246_, 0, v_k_3217_);
v___x_3280_ = v___x_3246_;
goto v_reusejp_3279_;
}
else
{
lean_object* v_reuseFailAlloc_3281_; 
v_reuseFailAlloc_3281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3281_, 0, v_k_3217_);
v___x_3280_ = v_reuseFailAlloc_3281_;
goto v_reusejp_3279_;
}
v_reusejp_3279_:
{
v___y_3266_ = v___x_3280_;
v_a_3267_ = v_k_3217_;
goto v___jp_3265_;
}
}
else
{
uint8_t v___x_3282_; 
v___x_3282_ = lean_nat_dec_le(v___x_3277_, v___x_3277_);
if (v___x_3282_ == 0)
{
if (v___x_3278_ == 0)
{
lean_object* v___x_3284_; 
lean_dec_ref(v___y_3276_);
lean_inc_ref(v_k_3217_);
if (v_isShared_3247_ == 0)
{
lean_ctor_set(v___x_3246_, 0, v_k_3217_);
v___x_3284_ = v___x_3246_;
goto v_reusejp_3283_;
}
else
{
lean_object* v_reuseFailAlloc_3285_; 
v_reuseFailAlloc_3285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3285_, 0, v_k_3217_);
v___x_3284_ = v_reuseFailAlloc_3285_;
goto v_reusejp_3283_;
}
v_reusejp_3283_:
{
v___y_3266_ = v___x_3284_;
v_a_3267_ = v_k_3217_;
goto v___jp_3265_;
}
}
else
{
size_t v___x_3286_; lean_object* v___x_3287_; 
lean_del_object(v___x_3246_);
v___x_3286_ = lean_usize_of_nat(v___x_3277_);
v___x_3287_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__5___redArg(v___y_3276_, v___x_3231_, v___x_3286_, v_k_3217_, v_a_3218_);
lean_dec_ref(v___y_3276_);
v___y_3273_ = v___x_3287_;
goto v___jp_3272_;
}
}
else
{
size_t v___x_3288_; lean_object* v___x_3289_; 
lean_del_object(v___x_3246_);
v___x_3288_ = lean_usize_of_nat(v___x_3277_);
v___x_3289_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__5___redArg(v___y_3276_, v___x_3231_, v___x_3288_, v_k_3217_, v_a_3218_);
lean_dec_ref(v___y_3276_);
v___y_3273_ = v___x_3289_;
goto v___jp_3272_;
}
}
}
v___jp_3290_:
{
lean_object* v___x_3293_; 
v___x_3293_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__4___redArg(v_snd_3249_, v___y_3291_, v___y_3292_);
lean_dec(v___y_3292_);
v___y_3276_ = v___x_3293_;
goto v___jp_3275_;
}
}
}
else
{
lean_object* v_a_3302_; lean_object* v___x_3304_; uint8_t v_isShared_3305_; uint8_t v_isSharedCheck_3309_; 
lean_dec_ref(v_k_3217_);
v_a_3302_ = lean_ctor_get(v___x_3243_, 0);
v_isSharedCheck_3309_ = !lean_is_exclusive(v___x_3243_);
if (v_isSharedCheck_3309_ == 0)
{
v___x_3304_ = v___x_3243_;
v_isShared_3305_ = v_isSharedCheck_3309_;
goto v_resetjp_3303_;
}
else
{
lean_inc(v_a_3302_);
lean_dec(v___x_3243_);
v___x_3304_ = lean_box(0);
v_isShared_3305_ = v_isSharedCheck_3309_;
goto v_resetjp_3303_;
}
v_resetjp_3303_:
{
lean_object* v___x_3307_; 
if (v_isShared_3305_ == 0)
{
v___x_3307_ = v___x_3304_;
goto v_reusejp_3306_;
}
else
{
lean_object* v_reuseFailAlloc_3308_; 
v_reuseFailAlloc_3308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3308_, 0, v_a_3302_);
v___x_3307_ = v_reuseFailAlloc_3308_;
goto v_reusejp_3306_;
}
v_reusejp_3306_:
{
return v___x_3307_;
}
}
}
v___jp_3232_:
{
lean_object* v___x_3236_; uint8_t v___x_3237_; 
v___x_3236_ = lean_array_get_size(v___y_3235_);
v___x_3237_ = lean_nat_dec_lt(v___x_3227_, v___x_3236_);
if (v___x_3237_ == 0)
{
lean_dec_ref(v___y_3235_);
lean_dec_ref(v___y_3234_);
return v___y_3233_;
}
else
{
uint8_t v___x_3238_; 
v___x_3238_ = lean_nat_dec_le(v___x_3236_, v___x_3236_);
if (v___x_3238_ == 0)
{
if (v___x_3237_ == 0)
{
lean_dec_ref(v___y_3235_);
lean_dec_ref(v___y_3234_);
return v___y_3233_;
}
else
{
size_t v___x_3239_; lean_object* v___x_3240_; 
lean_dec_ref(v___y_3233_);
v___x_3239_ = lean_usize_of_nat(v___x_3236_);
v___x_3240_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3___redArg(v___y_3235_, v___x_3231_, v___x_3239_, v___y_3234_, v_a_3218_);
lean_dec_ref(v___y_3235_);
return v___x_3240_;
}
}
else
{
size_t v___x_3241_; lean_object* v___x_3242_; 
lean_dec_ref(v___y_3233_);
v___x_3241_ = lean_usize_of_nat(v___x_3236_);
v___x_3242_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3___redArg(v___y_3235_, v___x_3231_, v___x_3241_, v___y_3234_, v_a_3218_);
lean_dec_ref(v___y_3235_);
return v___x_3242_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt___boxed(lean_object* v_altLiveVars_3310_, lean_object* v_k_3311_, lean_object* v_a_3312_, lean_object* v_a_3313_, lean_object* v_a_3314_, lean_object* v_a_3315_, lean_object* v_a_3316_, lean_object* v_a_3317_, lean_object* v_a_3318_){
_start:
{
lean_object* v_res_3319_; 
v_res_3319_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt(v_altLiveVars_3310_, v_k_3311_, v_a_3312_, v_a_3313_, v_a_3314_, v_a_3315_, v_a_3316_, v_a_3317_);
lean_dec(v_a_3317_);
lean_dec_ref(v_a_3316_);
lean_dec(v_a_3315_);
lean_dec_ref(v_a_3314_);
lean_dec(v_a_3313_);
lean_dec_ref(v_a_3312_);
lean_dec_ref(v_altLiveVars_3310_);
return v_res_3319_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__0(lean_object* v_00_u03b4_3320_, lean_object* v_inst_3321_, lean_object* v_t_3322_, lean_object* v_k_3323_){
_start:
{
lean_object* v___x_3324_; 
v___x_3324_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__0___redArg(v_inst_3321_, v_t_3322_, v_k_3323_);
return v___x_3324_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__0___boxed(lean_object* v_00_u03b4_3325_, lean_object* v_inst_3326_, lean_object* v_t_3327_, lean_object* v_k_3328_){
_start:
{
lean_object* v_res_3329_; 
v_res_3329_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__0(v_00_u03b4_3325_, v_inst_3326_, v_t_3327_, v_k_3328_);
lean_dec(v_k_3328_);
lean_dec(v_t_3327_);
return v_res_3329_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__1(lean_object* v_altLiveVars_3330_, lean_object* v_a_3331_, lean_object* v_a_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_){
_start:
{
lean_object* v___x_3340_; 
v___x_3340_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__1___redArg(v_altLiveVars_3330_, v_a_3331_, v_a_3332_, v___y_3333_, v___y_3334_);
return v___x_3340_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__1___boxed(lean_object* v_altLiveVars_3341_, lean_object* v_a_3342_, lean_object* v_a_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_, lean_object* v___y_3350_){
_start:
{
lean_object* v_res_3351_; 
v_res_3351_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__1(v_altLiveVars_3341_, v_a_3342_, v_a_3343_, v___y_3344_, v___y_3345_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_);
lean_dec(v___y_3349_);
lean_dec_ref(v___y_3348_);
lean_dec(v___y_3347_);
lean_dec_ref(v___y_3346_);
lean_dec(v___y_3345_);
lean_dec_ref(v___y_3344_);
lean_dec(v_a_3342_);
lean_dec_ref(v_altLiveVars_3341_);
return v_res_3351_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3(lean_object* v_as_3352_, size_t v_i_3353_, size_t v_stop_3354_, lean_object* v_b_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_, lean_object* v___y_3360_, lean_object* v___y_3361_){
_start:
{
lean_object* v___x_3363_; 
v___x_3363_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3___redArg(v_as_3352_, v_i_3353_, v_stop_3354_, v_b_3355_, v___y_3356_);
return v___x_3363_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3___boxed(lean_object* v_as_3364_, lean_object* v_i_3365_, lean_object* v_stop_3366_, lean_object* v_b_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_, lean_object* v___y_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_){
_start:
{
size_t v_i_boxed_3375_; size_t v_stop_boxed_3376_; lean_object* v_res_3377_; 
v_i_boxed_3375_ = lean_unbox_usize(v_i_3365_);
lean_dec(v_i_3365_);
v_stop_boxed_3376_ = lean_unbox_usize(v_stop_3366_);
lean_dec(v_stop_3366_);
v_res_3377_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3(v_as_3364_, v_i_boxed_3375_, v_stop_boxed_3376_, v_b_3367_, v___y_3368_, v___y_3369_, v___y_3370_, v___y_3371_, v___y_3372_, v___y_3373_);
lean_dec(v___y_3373_);
lean_dec_ref(v___y_3372_);
lean_dec(v___y_3371_);
lean_dec_ref(v___y_3370_);
lean_dec(v___y_3369_);
lean_dec_ref(v___y_3368_);
lean_dec_ref(v_as_3364_);
return v_res_3377_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__4(lean_object* v_n_3378_, lean_object* v_as_3379_, lean_object* v_lo_3380_, lean_object* v_hi_3381_, lean_object* v_w_3382_, lean_object* v_hlo_3383_, lean_object* v_hhi_3384_){
_start:
{
lean_object* v___x_3385_; 
v___x_3385_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__4___redArg(v_as_3379_, v_lo_3380_, v_hi_3381_);
return v___x_3385_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__4___boxed(lean_object* v_n_3386_, lean_object* v_as_3387_, lean_object* v_lo_3388_, lean_object* v_hi_3389_, lean_object* v_w_3390_, lean_object* v_hlo_3391_, lean_object* v_hhi_3392_){
_start:
{
lean_object* v_res_3393_; 
v_res_3393_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__4(v_n_3386_, v_as_3387_, v_lo_3388_, v_hi_3389_, v_w_3390_, v_hlo_3391_, v_hhi_3392_);
lean_dec(v_hi_3389_);
lean_dec(v_n_3386_);
return v_res_3393_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__5(lean_object* v_as_3394_, size_t v_i_3395_, size_t v_stop_3396_, lean_object* v_b_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_){
_start:
{
lean_object* v___x_3405_; 
v___x_3405_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__5___redArg(v_as_3394_, v_i_3395_, v_stop_3396_, v_b_3397_, v___y_3398_);
return v___x_3405_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__5___boxed(lean_object* v_as_3406_, lean_object* v_i_3407_, lean_object* v_stop_3408_, lean_object* v_b_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_){
_start:
{
size_t v_i_boxed_3417_; size_t v_stop_boxed_3418_; lean_object* v_res_3419_; 
v_i_boxed_3417_ = lean_unbox_usize(v_i_3407_);
lean_dec(v_i_3407_);
v_stop_boxed_3418_ = lean_unbox_usize(v_stop_3408_);
lean_dec(v_stop_3408_);
v_res_3419_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__5(v_as_3406_, v_i_boxed_3417_, v_stop_boxed_3418_, v_b_3409_, v___y_3410_, v___y_3411_, v___y_3412_, v___y_3413_, v___y_3414_, v___y_3415_);
lean_dec(v___y_3415_);
lean_dec_ref(v___y_3414_);
lean_dec(v___y_3413_);
lean_dec_ref(v___y_3412_);
lean_dec(v___y_3411_);
lean_dec_ref(v___y_3410_);
lean_dec_ref(v_as_3406_);
return v_res_3419_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isFirstOcc_spec__0___redArg(lean_object* v_args_3420_, lean_object* v_x_3421_, lean_object* v_n_3422_, lean_object* v_i_3423_){
_start:
{
lean_object* v_zero_3424_; uint8_t v_isZero_3425_; 
v_zero_3424_ = lean_unsigned_to_nat(0u);
v_isZero_3425_ = lean_nat_dec_eq(v_i_3423_, v_zero_3424_);
if (v_isZero_3425_ == 1)
{
lean_dec(v_i_3423_);
return v_isZero_3425_;
}
else
{
lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; uint8_t v___x_3429_; 
v___x_3426_ = lean_box(0);
v___x_3427_ = lean_nat_sub(v_n_3422_, v_i_3423_);
v___x_3428_ = lean_array_get_borrowed(v___x_3426_, v_args_3420_, v___x_3427_);
lean_dec(v___x_3427_);
v___x_3429_ = l_Lean_Compiler_LCNF_instBEqArg_beq___redArg(v___x_3428_, v_x_3421_);
if (v___x_3429_ == 0)
{
lean_object* v_one_3430_; lean_object* v_n_3431_; 
v_one_3430_ = lean_unsigned_to_nat(1u);
v_n_3431_ = lean_nat_sub(v_i_3423_, v_one_3430_);
lean_dec(v_i_3423_);
v_i_3423_ = v_n_3431_;
goto _start;
}
else
{
lean_dec(v_i_3423_);
return v_isZero_3425_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isFirstOcc_spec__0___redArg___boxed(lean_object* v_args_3433_, lean_object* v_x_3434_, lean_object* v_n_3435_, lean_object* v_i_3436_){
_start:
{
uint8_t v_res_3437_; lean_object* v_r_3438_; 
v_res_3437_ = l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isFirstOcc_spec__0___redArg(v_args_3433_, v_x_3434_, v_n_3435_, v_i_3436_);
lean_dec(v_n_3435_);
lean_dec(v_x_3434_);
lean_dec_ref(v_args_3433_);
v_r_3438_ = lean_box(v_res_3437_);
return v_r_3438_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isFirstOcc(lean_object* v_args_3439_, lean_object* v_i_3440_){
_start:
{
lean_object* v___x_3441_; lean_object* v_x_3442_; uint8_t v___x_3443_; 
v___x_3441_ = lean_box(0);
v_x_3442_ = lean_array_get_borrowed(v___x_3441_, v_args_3439_, v_i_3440_);
lean_inc(v_i_3440_);
v___x_3443_ = l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isFirstOcc_spec__0___redArg(v_args_3439_, v_x_3442_, v_i_3440_, v_i_3440_);
lean_dec(v_i_3440_);
return v___x_3443_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isFirstOcc___boxed(lean_object* v_args_3444_, lean_object* v_i_3445_){
_start:
{
uint8_t v_res_3446_; lean_object* v_r_3447_; 
v_res_3446_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isFirstOcc(v_args_3444_, v_i_3445_);
lean_dec_ref(v_args_3444_);
v_r_3447_ = lean_box(v_res_3446_);
return v_r_3447_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isFirstOcc_spec__0(lean_object* v_args_3448_, lean_object* v_x_3449_, lean_object* v_n_3450_, lean_object* v_i_3451_, lean_object* v_a_3452_){
_start:
{
uint8_t v___x_3453_; 
v___x_3453_ = l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isFirstOcc_spec__0___redArg(v_args_3448_, v_x_3449_, v_n_3450_, v_i_3451_);
return v___x_3453_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isFirstOcc_spec__0___boxed(lean_object* v_args_3454_, lean_object* v_x_3455_, lean_object* v_n_3456_, lean_object* v_i_3457_, lean_object* v_a_3458_){
_start:
{
uint8_t v_res_3459_; lean_object* v_r_3460_; 
v_res_3459_ = l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isFirstOcc_spec__0(v_args_3454_, v_x_3455_, v_n_3456_, v_i_3457_, v_a_3458_);
lean_dec(v_n_3456_);
lean_dec(v_x_3455_);
lean_dec_ref(v_args_3454_);
v_r_3460_ = lean_box(v_res_3459_);
return v_r_3460_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParamAux_spec__0___redArg(lean_object* v_args_3461_, lean_object* v_arg_3462_, lean_object* v_consumeParamPred_3463_, lean_object* v_n_3464_, lean_object* v_i_3465_){
_start:
{
lean_object* v_zero_3466_; uint8_t v_isZero_3467_; 
v_zero_3466_ = lean_unsigned_to_nat(0u);
v_isZero_3467_ = lean_nat_dec_eq(v_i_3465_, v_zero_3466_);
if (v_isZero_3467_ == 1)
{
uint8_t v___x_3468_; 
lean_dec(v_i_3465_);
lean_dec_ref(v_consumeParamPred_3463_);
v___x_3468_ = 0;
return v___x_3468_;
}
else
{
lean_object* v_one_3469_; lean_object* v_n_3470_; uint8_t v___y_3472_; lean_object* v___x_3474_; lean_object* v_arg_x27_3475_; 
v_one_3469_ = lean_unsigned_to_nat(1u);
v_n_3470_ = lean_nat_sub(v_i_3465_, v_one_3469_);
v___x_3474_ = lean_nat_sub(v_n_3464_, v_i_3465_);
lean_dec(v_i_3465_);
v_arg_x27_3475_ = lean_array_fget_borrowed(v_args_3461_, v___x_3474_);
if (lean_obj_tag(v_arg_x27_3475_) == 0)
{
lean_dec(v___x_3474_);
v_i_3465_ = v_n_3470_;
goto _start;
}
else
{
lean_object* v_fvarId_3477_; uint8_t v___x_3478_; 
v_fvarId_3477_ = lean_ctor_get(v_arg_x27_3475_, 0);
v___x_3478_ = l_Lean_instBEqFVarId_beq(v_arg_3462_, v_fvarId_3477_);
if (v___x_3478_ == 0)
{
lean_dec(v___x_3474_);
v___y_3472_ = v___x_3478_;
goto v___jp_3471_;
}
else
{
lean_object* v___x_3479_; uint8_t v___x_3480_; 
lean_inc_ref(v_consumeParamPred_3463_);
v___x_3479_ = lean_apply_1(v_consumeParamPred_3463_, v___x_3474_);
v___x_3480_ = lean_unbox(v___x_3479_);
if (v___x_3480_ == 0)
{
v___y_3472_ = v___x_3478_;
goto v___jp_3471_;
}
else
{
v_i_3465_ = v_n_3470_;
goto _start;
}
}
}
v___jp_3471_:
{
if (v___y_3472_ == 0)
{
v_i_3465_ = v_n_3470_;
goto _start;
}
else
{
lean_dec(v_n_3470_);
lean_dec_ref(v_consumeParamPred_3463_);
return v___y_3472_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParamAux_spec__0___redArg___boxed(lean_object* v_args_3482_, lean_object* v_arg_3483_, lean_object* v_consumeParamPred_3484_, lean_object* v_n_3485_, lean_object* v_i_3486_){
_start:
{
uint8_t v_res_3487_; lean_object* v_r_3488_; 
v_res_3487_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParamAux_spec__0___redArg(v_args_3482_, v_arg_3483_, v_consumeParamPred_3484_, v_n_3485_, v_i_3486_);
lean_dec(v_n_3485_);
lean_dec(v_arg_3483_);
lean_dec_ref(v_args_3482_);
v_r_3488_ = lean_box(v_res_3487_);
return v_r_3488_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParamAux(lean_object* v_arg_3489_, lean_object* v_args_3490_, lean_object* v_consumeParamPred_3491_){
_start:
{
lean_object* v___x_3492_; uint8_t v___x_3493_; 
v___x_3492_ = lean_array_get_size(v_args_3490_);
v___x_3493_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParamAux_spec__0___redArg(v_args_3490_, v_arg_3489_, v_consumeParamPred_3491_, v___x_3492_, v___x_3492_);
return v___x_3493_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParamAux___boxed(lean_object* v_arg_3494_, lean_object* v_args_3495_, lean_object* v_consumeParamPred_3496_){
_start:
{
uint8_t v_res_3497_; lean_object* v_r_3498_; 
v_res_3497_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParamAux(v_arg_3494_, v_args_3495_, v_consumeParamPred_3496_);
lean_dec_ref(v_args_3495_);
lean_dec(v_arg_3494_);
v_r_3498_ = lean_box(v_res_3497_);
return v_r_3498_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParamAux_spec__0(lean_object* v_args_3499_, lean_object* v_arg_3500_, lean_object* v_consumeParamPred_3501_, lean_object* v_n_3502_, lean_object* v_i_3503_, lean_object* v_a_3504_){
_start:
{
uint8_t v___x_3505_; 
v___x_3505_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParamAux_spec__0___redArg(v_args_3499_, v_arg_3500_, v_consumeParamPred_3501_, v_n_3502_, v_i_3503_);
return v___x_3505_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParamAux_spec__0___boxed(lean_object* v_args_3506_, lean_object* v_arg_3507_, lean_object* v_consumeParamPred_3508_, lean_object* v_n_3509_, lean_object* v_i_3510_, lean_object* v_a_3511_){
_start:
{
uint8_t v_res_3512_; lean_object* v_r_3513_; 
v_res_3512_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParamAux_spec__0(v_args_3506_, v_arg_3507_, v_consumeParamPred_3508_, v_n_3509_, v_i_3510_, v_a_3511_);
lean_dec(v_n_3509_);
lean_dec(v_arg_3507_);
lean_dec_ref(v_args_3506_);
v_r_3513_ = lean_box(v_res_3512_);
return v_r_3513_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParam___lam__0___closed__0(void){
_start:
{
uint8_t v___x_3514_; lean_object* v___x_3515_; 
v___x_3514_ = 1;
v___x_3515_ = l_Lean_Compiler_LCNF_instInhabitedParam_default(v___x_3514_);
return v___x_3515_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParam___lam__0(lean_object* v_ps_3516_, lean_object* v_i_3517_){
_start:
{
lean_object* v___x_3518_; lean_object* v___x_3519_; uint8_t v_borrow_3520_; 
v___x_3518_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParam___lam__0___closed__0, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParam___lam__0___closed__0_once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParam___lam__0___closed__0);
v___x_3519_ = lean_array_get_borrowed(v___x_3518_, v_ps_3516_, v_i_3517_);
v_borrow_3520_ = lean_ctor_get_uint8(v___x_3519_, sizeof(void*)*3);
if (v_borrow_3520_ == 0)
{
uint8_t v___x_3521_; 
v___x_3521_ = 1;
return v___x_3521_;
}
else
{
uint8_t v___x_3522_; 
v___x_3522_ = 0;
return v___x_3522_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParam___lam__0___boxed(lean_object* v_ps_3523_, lean_object* v_i_3524_){
_start:
{
uint8_t v_res_3525_; lean_object* v_r_3526_; 
v_res_3525_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParam___lam__0(v_ps_3523_, v_i_3524_);
lean_dec(v_i_3524_);
lean_dec_ref(v_ps_3523_);
v_r_3526_ = lean_box(v_res_3525_);
return v_r_3526_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParam(lean_object* v_arg_3527_, lean_object* v_args_3528_, lean_object* v_ps_3529_){
_start:
{
lean_object* v___f_3530_; uint8_t v___x_3531_; 
v___f_3530_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParam___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3530_, 0, v_ps_3529_);
v___x_3531_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParamAux(v_arg_3527_, v_args_3528_, v___f_3530_);
return v___x_3531_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParam___boxed(lean_object* v_arg_3532_, lean_object* v_args_3533_, lean_object* v_ps_3534_){
_start:
{
uint8_t v_res_3535_; lean_object* v_r_3536_; 
v_res_3535_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParam(v_arg_3532_, v_args_3533_, v_ps_3534_);
lean_dec_ref(v_args_3533_);
lean_dec(v_arg_3532_);
v_r_3536_ = lean_box(v_res_3535_);
return v_r_3536_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getNumConsumptions_spec__0___redArg(lean_object* v_upperBound_3537_, lean_object* v_args_3538_, lean_object* v_arg_3539_, lean_object* v_consumeParamPred_3540_, lean_object* v_a_3541_, lean_object* v_b_3542_){
_start:
{
lean_object* v_a_3544_; uint8_t v___y_3549_; uint8_t v___x_3552_; 
v___x_3552_ = lean_nat_dec_lt(v_a_3541_, v_upperBound_3537_);
if (v___x_3552_ == 0)
{
lean_dec(v_a_3541_);
lean_dec_ref(v_consumeParamPred_3540_);
return v_b_3542_;
}
else
{
lean_object* v___x_3553_; 
v___x_3553_ = lean_array_fget_borrowed(v_args_3538_, v_a_3541_);
if (lean_obj_tag(v___x_3553_) == 1)
{
lean_object* v_fvarId_3554_; uint8_t v___x_3555_; 
v_fvarId_3554_ = lean_ctor_get(v___x_3553_, 0);
v___x_3555_ = l_Lean_instBEqFVarId_beq(v_arg_3539_, v_fvarId_3554_);
if (v___x_3555_ == 0)
{
v___y_3549_ = v___x_3555_;
goto v___jp_3548_;
}
else
{
lean_object* v___x_3556_; uint8_t v___x_3557_; 
lean_inc_ref(v_consumeParamPred_3540_);
lean_inc(v_a_3541_);
v___x_3556_ = lean_apply_1(v_consumeParamPred_3540_, v_a_3541_);
v___x_3557_ = lean_unbox(v___x_3556_);
v___y_3549_ = v___x_3557_;
goto v___jp_3548_;
}
}
else
{
v_a_3544_ = v_b_3542_;
goto v___jp_3543_;
}
}
v___jp_3543_:
{
lean_object* v___x_3545_; lean_object* v___x_3546_; 
v___x_3545_ = lean_unsigned_to_nat(1u);
v___x_3546_ = lean_nat_add(v_a_3541_, v___x_3545_);
lean_dec(v_a_3541_);
v_a_3541_ = v___x_3546_;
v_b_3542_ = v_a_3544_;
goto _start;
}
v___jp_3548_:
{
if (v___y_3549_ == 0)
{
v_a_3544_ = v_b_3542_;
goto v___jp_3543_;
}
else
{
lean_object* v___x_3550_; lean_object* v___x_3551_; 
v___x_3550_ = lean_unsigned_to_nat(1u);
v___x_3551_ = lean_nat_add(v_b_3542_, v___x_3550_);
lean_dec(v_b_3542_);
v_a_3544_ = v___x_3551_;
goto v___jp_3543_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getNumConsumptions_spec__0___redArg___boxed(lean_object* v_upperBound_3558_, lean_object* v_args_3559_, lean_object* v_arg_3560_, lean_object* v_consumeParamPred_3561_, lean_object* v_a_3562_, lean_object* v_b_3563_){
_start:
{
lean_object* v_res_3564_; 
v_res_3564_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getNumConsumptions_spec__0___redArg(v_upperBound_3558_, v_args_3559_, v_arg_3560_, v_consumeParamPred_3561_, v_a_3562_, v_b_3563_);
lean_dec(v_arg_3560_);
lean_dec_ref(v_args_3559_);
lean_dec(v_upperBound_3558_);
return v_res_3564_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getNumConsumptions(lean_object* v_arg_3565_, lean_object* v_args_3566_, lean_object* v_consumeParamPred_3567_){
_start:
{
lean_object* v_num_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; 
v_num_3568_ = lean_unsigned_to_nat(0u);
v___x_3569_ = lean_array_get_size(v_args_3566_);
v___x_3570_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getNumConsumptions_spec__0___redArg(v___x_3569_, v_args_3566_, v_arg_3565_, v_consumeParamPred_3567_, v_num_3568_, v_num_3568_);
return v___x_3570_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getNumConsumptions___boxed(lean_object* v_arg_3571_, lean_object* v_args_3572_, lean_object* v_consumeParamPred_3573_){
_start:
{
lean_object* v_res_3574_; 
v_res_3574_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getNumConsumptions(v_arg_3571_, v_args_3572_, v_consumeParamPred_3573_);
lean_dec_ref(v_args_3572_);
lean_dec(v_arg_3571_);
return v_res_3574_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getNumConsumptions_spec__0(lean_object* v_upperBound_3575_, lean_object* v_args_3576_, lean_object* v_arg_3577_, lean_object* v_consumeParamPred_3578_, lean_object* v_inst_3579_, lean_object* v_R_3580_, lean_object* v_a_3581_, lean_object* v_b_3582_, lean_object* v_c_3583_){
_start:
{
lean_object* v___x_3584_; 
v___x_3584_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getNumConsumptions_spec__0___redArg(v_upperBound_3575_, v_args_3576_, v_arg_3577_, v_consumeParamPred_3578_, v_a_3581_, v_b_3582_);
return v___x_3584_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getNumConsumptions_spec__0___boxed(lean_object* v_upperBound_3585_, lean_object* v_args_3586_, lean_object* v_arg_3587_, lean_object* v_consumeParamPred_3588_, lean_object* v_inst_3589_, lean_object* v_R_3590_, lean_object* v_a_3591_, lean_object* v_b_3592_, lean_object* v_c_3593_){
_start:
{
lean_object* v_res_3594_; 
v_res_3594_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getNumConsumptions_spec__0(v_upperBound_3585_, v_args_3586_, v_arg_3587_, v_consumeParamPred_3588_, v_inst_3589_, v_R_3590_, v_a_3591_, v_b_3592_, v_c_3593_);
lean_dec(v_arg_3587_);
lean_dec_ref(v_args_3586_);
lean_dec(v_upperBound_3585_);
return v_res_3594_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux_spec__0___redArg___lam__0(lean_object* v___x_3595_, lean_object* v_fvarId_3596_, lean_object* v_b_3597_, uint8_t v___x_3598_, lean_object* v_numIncs_3599_, lean_object* v___y_3600_, lean_object* v___y_3601_, lean_object* v___y_3602_, lean_object* v___y_3603_, lean_object* v___y_3604_, lean_object* v___y_3605_){
_start:
{
lean_object* v_a_3608_; lean_object* v___x_3611_; uint8_t v___x_3612_; 
v___x_3611_ = lean_unsigned_to_nat(0u);
v___x_3612_ = lean_nat_dec_eq(v_numIncs_3599_, v___x_3611_);
if (v___x_3612_ == 0)
{
lean_object* v_varMap_3613_; lean_object* v___x_3614_; uint8_t v___y_3616_; uint8_t v_isDefiniteRef_3619_; 
v_varMap_3613_ = lean_ctor_get(v___y_3600_, 2);
v___x_3614_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__0___redArg(v___x_3595_, v_varMap_3613_, v_fvarId_3596_);
v_isDefiniteRef_3619_ = lean_ctor_get_uint8(v___x_3614_, sizeof(void*)*1 + 1);
if (v_isDefiniteRef_3619_ == 0)
{
v___y_3616_ = v___x_3598_;
goto v___jp_3615_;
}
else
{
v___y_3616_ = v___x_3612_;
goto v___jp_3615_;
}
v___jp_3615_:
{
uint8_t v_persistent_3617_; lean_object* v___x_3618_; 
v_persistent_3617_ = lean_ctor_get_uint8(v___x_3614_, sizeof(void*)*1 + 2);
lean_dec(v___x_3614_);
v___x_3618_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v___x_3618_, 0, v_fvarId_3596_);
lean_ctor_set(v___x_3618_, 1, v_numIncs_3599_);
lean_ctor_set(v___x_3618_, 2, v_b_3597_);
lean_ctor_set_uint8(v___x_3618_, sizeof(void*)*3, v___y_3616_);
lean_ctor_set_uint8(v___x_3618_, sizeof(void*)*3 + 1, v_persistent_3617_);
v_a_3608_ = v___x_3618_;
goto v___jp_3607_;
}
}
else
{
lean_dec(v_numIncs_3599_);
lean_dec(v_fvarId_3596_);
lean_dec_ref(v___x_3595_);
v_a_3608_ = v_b_3597_;
goto v___jp_3607_;
}
v___jp_3607_:
{
lean_object* v___x_3609_; lean_object* v___x_3610_; 
v___x_3609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3609_, 0, v_a_3608_);
v___x_3610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3610_, 0, v___x_3609_);
return v___x_3610_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux_spec__0___redArg___lam__0___boxed(lean_object* v___x_3620_, lean_object* v_fvarId_3621_, lean_object* v_b_3622_, lean_object* v___x_3623_, lean_object* v_numIncs_3624_, lean_object* v___y_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_){
_start:
{
uint8_t v___x_6282__boxed_3632_; lean_object* v_res_3633_; 
v___x_6282__boxed_3632_ = lean_unbox(v___x_3623_);
v_res_3633_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux_spec__0___redArg___lam__0(v___x_3620_, v_fvarId_3621_, v_b_3622_, v___x_6282__boxed_3632_, v_numIncs_3624_, v___y_3625_, v___y_3626_, v___y_3627_, v___y_3628_, v___y_3629_, v___y_3630_);
lean_dec(v___y_3630_);
lean_dec_ref(v___y_3629_);
lean_dec(v___y_3628_);
lean_dec_ref(v___y_3627_);
lean_dec(v___y_3626_);
lean_dec_ref(v___y_3625_);
return v_res_3633_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux_spec__0___redArg(lean_object* v_upperBound_3634_, lean_object* v_args_3635_, lean_object* v_consumeParamPred_3636_, lean_object* v_a_3637_, lean_object* v_b_3638_, lean_object* v___y_3639_, lean_object* v___y_3640_, lean_object* v___y_3641_, lean_object* v___y_3642_, lean_object* v___y_3643_, lean_object* v___y_3644_){
_start:
{
lean_object* v_a_3647_; lean_object* v___y_3652_; uint8_t v___x_3671_; 
v___x_3671_ = lean_nat_dec_lt(v_a_3637_, v_upperBound_3634_);
if (v___x_3671_ == 0)
{
lean_object* v___x_3672_; 
lean_dec(v_a_3637_);
lean_dec_ref(v_consumeParamPred_3636_);
v___x_3672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3672_, 0, v_b_3638_);
return v___x_3672_;
}
else
{
lean_object* v___x_3673_; 
v___x_3673_ = lean_array_fget_borrowed(v_args_3635_, v_a_3637_);
if (lean_obj_tag(v___x_3673_) == 1)
{
lean_object* v_fvarId_3674_; lean_object* v_varMap_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; uint8_t v_isPossibleRef_3678_; 
v_fvarId_3674_ = lean_ctor_get(v___x_3673_, 0);
v_varMap_3675_ = lean_ctor_get(v___y_3639_, 2);
v___x_3676_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_instInhabitedVarInfo_default));
v___x_3677_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__0___redArg(v___x_3676_, v_varMap_3675_, v_fvarId_3674_);
v_isPossibleRef_3678_ = lean_ctor_get_uint8(v___x_3677_, sizeof(void*)*1);
lean_dec(v___x_3677_);
if (v_isPossibleRef_3678_ == 0)
{
v_a_3647_ = v_b_3638_;
goto v___jp_3646_;
}
else
{
uint8_t v___x_3679_; 
lean_inc(v_a_3637_);
v___x_3679_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isFirstOcc(v_args_3635_, v_a_3637_);
if (v___x_3679_ == 0)
{
v_a_3647_ = v_b_3638_;
goto v___jp_3646_;
}
else
{
lean_object* v___x_3680_; lean_object* v___x_3681_; uint8_t v___y_3683_; uint8_t v___x_3688_; 
v___x_3680_ = lean_st_ref_get(v___y_3640_);
lean_inc_ref(v_consumeParamPred_3636_);
v___x_3681_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getNumConsumptions(v_fvarId_3674_, v_args_3635_, v_consumeParamPred_3636_);
v___x_3688_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_isAccessible(v___x_3680_, v_fvarId_3674_);
lean_dec(v___x_3680_);
if (v___x_3688_ == 0)
{
uint8_t v___x_3689_; 
lean_inc_ref(v_consumeParamPred_3636_);
v___x_3689_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParamAux(v_fvarId_3674_, v_args_3635_, v_consumeParamPred_3636_);
v___y_3683_ = v___x_3689_;
goto v___jp_3682_;
}
else
{
v___y_3683_ = v___x_3688_;
goto v___jp_3682_;
}
v___jp_3682_:
{
if (v___y_3683_ == 0)
{
lean_object* v___x_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; 
v___x_3684_ = lean_unsigned_to_nat(1u);
v___x_3685_ = lean_nat_sub(v___x_3681_, v___x_3684_);
lean_dec(v___x_3681_);
lean_inc(v_fvarId_3674_);
v___x_3686_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux_spec__0___redArg___lam__0(v___x_3676_, v_fvarId_3674_, v_b_3638_, v___x_3679_, v___x_3685_, v___y_3639_, v___y_3640_, v___y_3641_, v___y_3642_, v___y_3643_, v___y_3644_);
v___y_3652_ = v___x_3686_;
goto v___jp_3651_;
}
else
{
lean_object* v___x_3687_; 
lean_inc(v_fvarId_3674_);
v___x_3687_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux_spec__0___redArg___lam__0(v___x_3676_, v_fvarId_3674_, v_b_3638_, v___x_3679_, v___x_3681_, v___y_3639_, v___y_3640_, v___y_3641_, v___y_3642_, v___y_3643_, v___y_3644_);
v___y_3652_ = v___x_3687_;
goto v___jp_3651_;
}
}
}
}
}
else
{
v_a_3647_ = v_b_3638_;
goto v___jp_3646_;
}
}
v___jp_3646_:
{
lean_object* v___x_3648_; lean_object* v___x_3649_; 
v___x_3648_ = lean_unsigned_to_nat(1u);
v___x_3649_ = lean_nat_add(v_a_3637_, v___x_3648_);
lean_dec(v_a_3637_);
v_a_3637_ = v___x_3649_;
v_b_3638_ = v_a_3647_;
goto _start;
}
v___jp_3651_:
{
if (lean_obj_tag(v___y_3652_) == 0)
{
lean_object* v_a_3653_; lean_object* v___x_3655_; uint8_t v_isShared_3656_; uint8_t v_isSharedCheck_3662_; 
v_a_3653_ = lean_ctor_get(v___y_3652_, 0);
v_isSharedCheck_3662_ = !lean_is_exclusive(v___y_3652_);
if (v_isSharedCheck_3662_ == 0)
{
v___x_3655_ = v___y_3652_;
v_isShared_3656_ = v_isSharedCheck_3662_;
goto v_resetjp_3654_;
}
else
{
lean_inc(v_a_3653_);
lean_dec(v___y_3652_);
v___x_3655_ = lean_box(0);
v_isShared_3656_ = v_isSharedCheck_3662_;
goto v_resetjp_3654_;
}
v_resetjp_3654_:
{
if (lean_obj_tag(v_a_3653_) == 0)
{
lean_object* v_a_3657_; lean_object* v___x_3659_; 
lean_dec(v_a_3637_);
lean_dec_ref(v_consumeParamPred_3636_);
v_a_3657_ = lean_ctor_get(v_a_3653_, 0);
lean_inc(v_a_3657_);
lean_dec_ref(v_a_3653_);
if (v_isShared_3656_ == 0)
{
lean_ctor_set(v___x_3655_, 0, v_a_3657_);
v___x_3659_ = v___x_3655_;
goto v_reusejp_3658_;
}
else
{
lean_object* v_reuseFailAlloc_3660_; 
v_reuseFailAlloc_3660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3660_, 0, v_a_3657_);
v___x_3659_ = v_reuseFailAlloc_3660_;
goto v_reusejp_3658_;
}
v_reusejp_3658_:
{
return v___x_3659_;
}
}
else
{
lean_object* v_a_3661_; 
lean_del_object(v___x_3655_);
v_a_3661_ = lean_ctor_get(v_a_3653_, 0);
lean_inc(v_a_3661_);
lean_dec_ref(v_a_3653_);
v_a_3647_ = v_a_3661_;
goto v___jp_3646_;
}
}
}
else
{
lean_object* v_a_3663_; lean_object* v___x_3665_; uint8_t v_isShared_3666_; uint8_t v_isSharedCheck_3670_; 
lean_dec(v_a_3637_);
lean_dec_ref(v_consumeParamPred_3636_);
v_a_3663_ = lean_ctor_get(v___y_3652_, 0);
v_isSharedCheck_3670_ = !lean_is_exclusive(v___y_3652_);
if (v_isSharedCheck_3670_ == 0)
{
v___x_3665_ = v___y_3652_;
v_isShared_3666_ = v_isSharedCheck_3670_;
goto v_resetjp_3664_;
}
else
{
lean_inc(v_a_3663_);
lean_dec(v___y_3652_);
v___x_3665_ = lean_box(0);
v_isShared_3666_ = v_isSharedCheck_3670_;
goto v_resetjp_3664_;
}
v_resetjp_3664_:
{
lean_object* v___x_3668_; 
if (v_isShared_3666_ == 0)
{
v___x_3668_ = v___x_3665_;
goto v_reusejp_3667_;
}
else
{
lean_object* v_reuseFailAlloc_3669_; 
v_reuseFailAlloc_3669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3669_, 0, v_a_3663_);
v___x_3668_ = v_reuseFailAlloc_3669_;
goto v_reusejp_3667_;
}
v_reusejp_3667_:
{
return v___x_3668_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux_spec__0___redArg___boxed(lean_object* v_upperBound_3690_, lean_object* v_args_3691_, lean_object* v_consumeParamPred_3692_, lean_object* v_a_3693_, lean_object* v_b_3694_, lean_object* v___y_3695_, lean_object* v___y_3696_, lean_object* v___y_3697_, lean_object* v___y_3698_, lean_object* v___y_3699_, lean_object* v___y_3700_, lean_object* v___y_3701_){
_start:
{
lean_object* v_res_3702_; 
v_res_3702_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux_spec__0___redArg(v_upperBound_3690_, v_args_3691_, v_consumeParamPred_3692_, v_a_3693_, v_b_3694_, v___y_3695_, v___y_3696_, v___y_3697_, v___y_3698_, v___y_3699_, v___y_3700_);
lean_dec(v___y_3700_);
lean_dec_ref(v___y_3699_);
lean_dec(v___y_3698_);
lean_dec_ref(v___y_3697_);
lean_dec(v___y_3696_);
lean_dec_ref(v___y_3695_);
lean_dec_ref(v_args_3691_);
lean_dec(v_upperBound_3690_);
return v_res_3702_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux(lean_object* v_args_3703_, lean_object* v_consumeParamPred_3704_, lean_object* v_k_3705_, lean_object* v_a_3706_, lean_object* v_a_3707_, lean_object* v_a_3708_, lean_object* v_a_3709_, lean_object* v_a_3710_, lean_object* v_a_3711_){
_start:
{
lean_object* v___x_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; 
v___x_3713_ = lean_unsigned_to_nat(0u);
v___x_3714_ = lean_array_get_size(v_args_3703_);
v___x_3715_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux_spec__0___redArg(v___x_3714_, v_args_3703_, v_consumeParamPred_3704_, v___x_3713_, v_k_3705_, v_a_3706_, v_a_3707_, v_a_3708_, v_a_3709_, v_a_3710_, v_a_3711_);
return v___x_3715_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux___boxed(lean_object* v_args_3716_, lean_object* v_consumeParamPred_3717_, lean_object* v_k_3718_, lean_object* v_a_3719_, lean_object* v_a_3720_, lean_object* v_a_3721_, lean_object* v_a_3722_, lean_object* v_a_3723_, lean_object* v_a_3724_, lean_object* v_a_3725_){
_start:
{
lean_object* v_res_3726_; 
v_res_3726_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux(v_args_3716_, v_consumeParamPred_3717_, v_k_3718_, v_a_3719_, v_a_3720_, v_a_3721_, v_a_3722_, v_a_3723_, v_a_3724_);
lean_dec(v_a_3724_);
lean_dec_ref(v_a_3723_);
lean_dec(v_a_3722_);
lean_dec_ref(v_a_3721_);
lean_dec(v_a_3720_);
lean_dec_ref(v_a_3719_);
lean_dec_ref(v_args_3716_);
return v_res_3726_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux_spec__0(lean_object* v_upperBound_3727_, lean_object* v_args_3728_, lean_object* v_consumeParamPred_3729_, lean_object* v_inst_3730_, lean_object* v_R_3731_, lean_object* v_a_3732_, lean_object* v_b_3733_, lean_object* v_c_3734_, lean_object* v___y_3735_, lean_object* v___y_3736_, lean_object* v___y_3737_, lean_object* v___y_3738_, lean_object* v___y_3739_, lean_object* v___y_3740_){
_start:
{
lean_object* v___x_3742_; 
v___x_3742_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux_spec__0___redArg(v_upperBound_3727_, v_args_3728_, v_consumeParamPred_3729_, v_a_3732_, v_b_3733_, v___y_3735_, v___y_3736_, v___y_3737_, v___y_3738_, v___y_3739_, v___y_3740_);
return v___x_3742_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux_spec__0___boxed(lean_object* v_upperBound_3743_, lean_object* v_args_3744_, lean_object* v_consumeParamPred_3745_, lean_object* v_inst_3746_, lean_object* v_R_3747_, lean_object* v_a_3748_, lean_object* v_b_3749_, lean_object* v_c_3750_, lean_object* v___y_3751_, lean_object* v___y_3752_, lean_object* v___y_3753_, lean_object* v___y_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_, lean_object* v___y_3757_){
_start:
{
lean_object* v_res_3758_; 
v_res_3758_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux_spec__0(v_upperBound_3743_, v_args_3744_, v_consumeParamPred_3745_, v_inst_3746_, v_R_3747_, v_a_3748_, v_b_3749_, v_c_3750_, v___y_3751_, v___y_3752_, v___y_3753_, v___y_3754_, v___y_3755_, v___y_3756_);
lean_dec(v___y_3756_);
lean_dec_ref(v___y_3755_);
lean_dec(v___y_3754_);
lean_dec_ref(v___y_3753_);
lean_dec(v___y_3752_);
lean_dec_ref(v___y_3751_);
lean_dec_ref(v_args_3744_);
lean_dec(v_upperBound_3743_);
return v_res_3758_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBefore(lean_object* v_args_3759_, lean_object* v_ps_3760_, lean_object* v_k_3761_, lean_object* v_a_3762_, lean_object* v_a_3763_, lean_object* v_a_3764_, lean_object* v_a_3765_, lean_object* v_a_3766_, lean_object* v_a_3767_){
_start:
{
lean_object* v___f_3769_; lean_object* v___x_3770_; 
v___f_3769_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParam___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3769_, 0, v_ps_3760_);
v___x_3770_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux(v_args_3759_, v___f_3769_, v_k_3761_, v_a_3762_, v_a_3763_, v_a_3764_, v_a_3765_, v_a_3766_, v_a_3767_);
return v___x_3770_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBefore___boxed(lean_object* v_args_3771_, lean_object* v_ps_3772_, lean_object* v_k_3773_, lean_object* v_a_3774_, lean_object* v_a_3775_, lean_object* v_a_3776_, lean_object* v_a_3777_, lean_object* v_a_3778_, lean_object* v_a_3779_, lean_object* v_a_3780_){
_start:
{
lean_object* v_res_3781_; 
v_res_3781_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBefore(v_args_3771_, v_ps_3772_, v_k_3773_, v_a_3774_, v_a_3775_, v_a_3776_, v_a_3777_, v_a_3778_, v_a_3779_);
lean_dec(v_a_3779_);
lean_dec_ref(v_a_3778_);
lean_dec(v_a_3777_);
lean_dec_ref(v_a_3776_);
lean_dec(v_a_3775_);
lean_dec_ref(v_a_3774_);
lean_dec_ref(v_args_3771_);
return v_res_3781_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeConsumeAll___lam__0(lean_object* v_x_3782_){
_start:
{
uint8_t v___x_3783_; 
v___x_3783_ = 1;
return v___x_3783_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeConsumeAll___lam__0___boxed(lean_object* v_x_3784_){
_start:
{
uint8_t v_res_3785_; lean_object* v_r_3786_; 
v_res_3785_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeConsumeAll___lam__0(v_x_3784_);
lean_dec(v_x_3784_);
v_r_3786_ = lean_box(v_res_3785_);
return v_r_3786_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeConsumeAll(lean_object* v_args_3788_, lean_object* v_k_3789_, lean_object* v_a_3790_, lean_object* v_a_3791_, lean_object* v_a_3792_, lean_object* v_a_3793_, lean_object* v_a_3794_, lean_object* v_a_3795_){
_start:
{
lean_object* v___f_3797_; lean_object* v___x_3798_; 
v___f_3797_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeConsumeAll___closed__0));
v___x_3798_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux(v_args_3788_, v___f_3797_, v_k_3789_, v_a_3790_, v_a_3791_, v_a_3792_, v_a_3793_, v_a_3794_, v_a_3795_);
return v___x_3798_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeConsumeAll___boxed(lean_object* v_args_3799_, lean_object* v_k_3800_, lean_object* v_a_3801_, lean_object* v_a_3802_, lean_object* v_a_3803_, lean_object* v_a_3804_, lean_object* v_a_3805_, lean_object* v_a_3806_, lean_object* v_a_3807_){
_start:
{
lean_object* v_res_3808_; 
v_res_3808_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeConsumeAll(v_args_3799_, v_k_3800_, v_a_3801_, v_a_3802_, v_a_3803_, v_a_3804_, v_a_3805_, v_a_3806_);
lean_dec(v_a_3806_);
lean_dec_ref(v_a_3805_);
lean_dec(v_a_3804_);
lean_dec_ref(v_a_3803_);
lean_dec(v_a_3802_);
lean_dec_ref(v_a_3801_);
lean_dec_ref(v_args_3799_);
return v_res_3808_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecAfterFullApp_spec__0___redArg(lean_object* v_upperBound_3809_, lean_object* v_args_3810_, lean_object* v_ps_3811_, lean_object* v_a_3812_, lean_object* v_b_3813_, lean_object* v___y_3814_, lean_object* v___y_3815_){
_start:
{
lean_object* v_a_3818_; uint8_t v___x_3822_; 
v___x_3822_ = lean_nat_dec_lt(v_a_3812_, v_upperBound_3809_);
if (v___x_3822_ == 0)
{
lean_object* v___x_3823_; 
lean_dec(v_a_3812_);
lean_dec_ref(v_ps_3811_);
v___x_3823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3823_, 0, v_b_3813_);
return v___x_3823_;
}
else
{
lean_object* v___x_3824_; 
v___x_3824_ = lean_array_fget_borrowed(v_args_3810_, v_a_3812_);
if (lean_obj_tag(v___x_3824_) == 0)
{
v_a_3818_ = v_b_3813_;
goto v___jp_3817_;
}
else
{
lean_object* v_fvarId_3825_; lean_object* v___x_3826_; lean_object* v___x_3827_; lean_object* v_varMap_3828_; lean_object* v___x_3829_; lean_object* v___x_3830_; uint8_t v_isPossibleRef_3831_; 
v_fvarId_3825_ = lean_ctor_get(v___x_3824_, 0);
v___x_3826_ = lean_st_ref_get(v___y_3815_);
v___x_3827_ = lean_st_ref_get(v___y_3815_);
v_varMap_3828_ = lean_ctor_get(v___y_3814_, 2);
v___x_3829_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_instInhabitedVarInfo_default));
v___x_3830_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__0___redArg(v___x_3829_, v_varMap_3828_, v_fvarId_3825_);
v_isPossibleRef_3831_ = lean_ctor_get_uint8(v___x_3830_, sizeof(void*)*1);
if (v_isPossibleRef_3831_ == 0)
{
lean_dec(v___x_3830_);
lean_dec(v___x_3827_);
lean_dec(v___x_3826_);
v_a_3818_ = v_b_3813_;
goto v___jp_3817_;
}
else
{
uint8_t v_isDefiniteRef_3832_; uint8_t v_persistent_3833_; uint8_t v___x_3834_; 
v_isDefiniteRef_3832_ = lean_ctor_get_uint8(v___x_3830_, sizeof(void*)*1 + 1);
v_persistent_3833_ = lean_ctor_get_uint8(v___x_3830_, sizeof(void*)*1 + 2);
lean_dec(v___x_3830_);
lean_inc(v_a_3812_);
v___x_3834_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isFirstOcc(v_args_3810_, v_a_3812_);
if (v___x_3834_ == 0)
{
lean_dec(v___x_3827_);
lean_dec(v___x_3826_);
v_a_3818_ = v_b_3813_;
goto v___jp_3817_;
}
else
{
uint8_t v___x_3835_; 
lean_inc_ref(v_ps_3811_);
v___x_3835_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParam(v_fvarId_3825_, v_args_3810_, v_ps_3811_);
if (v___x_3835_ == 0)
{
lean_dec(v___x_3827_);
lean_dec(v___x_3826_);
v_a_3818_ = v_b_3813_;
goto v___jp_3817_;
}
else
{
lean_object* v_vars_3836_; uint8_t v___x_3837_; 
v_vars_3836_ = lean_ctor_get(v___x_3826_, 0);
lean_inc_ref(v_vars_3836_);
lean_dec(v___x_3826_);
v___x_3837_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_isAccessible_spec__0___redArg(v_vars_3836_, v_fvarId_3825_);
lean_dec_ref(v_vars_3836_);
if (v___x_3837_ == 0)
{
lean_object* v_borrows_3838_; uint8_t v___x_3839_; 
v_borrows_3838_ = lean_ctor_get(v___x_3827_, 1);
lean_inc_ref(v_borrows_3838_);
lean_dec(v___x_3827_);
v___x_3839_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_isAccessible_spec__0___redArg(v_borrows_3838_, v_fvarId_3825_);
lean_dec_ref(v_borrows_3838_);
if (v___x_3839_ == 0)
{
lean_object* v___x_3840_; uint8_t v___y_3842_; 
v___x_3840_ = lean_unsigned_to_nat(1u);
if (v_isDefiniteRef_3832_ == 0)
{
v___y_3842_ = v___x_3835_;
goto v___jp_3841_;
}
else
{
v___y_3842_ = v___x_3839_;
goto v___jp_3841_;
}
v___jp_3841_:
{
lean_object* v___x_3843_; 
lean_inc(v_fvarId_3825_);
v___x_3843_ = lean_alloc_ctor(12, 3, 2);
lean_ctor_set(v___x_3843_, 0, v_fvarId_3825_);
lean_ctor_set(v___x_3843_, 1, v___x_3840_);
lean_ctor_set(v___x_3843_, 2, v_b_3813_);
lean_ctor_set_uint8(v___x_3843_, sizeof(void*)*3, v___y_3842_);
lean_ctor_set_uint8(v___x_3843_, sizeof(void*)*3 + 1, v_persistent_3833_);
v_a_3818_ = v___x_3843_;
goto v___jp_3817_;
}
}
else
{
v_a_3818_ = v_b_3813_;
goto v___jp_3817_;
}
}
else
{
lean_dec(v___x_3827_);
v_a_3818_ = v_b_3813_;
goto v___jp_3817_;
}
}
}
}
}
}
v___jp_3817_:
{
lean_object* v___x_3819_; lean_object* v___x_3820_; 
v___x_3819_ = lean_unsigned_to_nat(1u);
v___x_3820_ = lean_nat_add(v_a_3812_, v___x_3819_);
lean_dec(v_a_3812_);
v_a_3812_ = v___x_3820_;
v_b_3813_ = v_a_3818_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecAfterFullApp_spec__0___redArg___boxed(lean_object* v_upperBound_3844_, lean_object* v_args_3845_, lean_object* v_ps_3846_, lean_object* v_a_3847_, lean_object* v_b_3848_, lean_object* v___y_3849_, lean_object* v___y_3850_, lean_object* v___y_3851_){
_start:
{
lean_object* v_res_3852_; 
v_res_3852_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecAfterFullApp_spec__0___redArg(v_upperBound_3844_, v_args_3845_, v_ps_3846_, v_a_3847_, v_b_3848_, v___y_3849_, v___y_3850_);
lean_dec(v___y_3850_);
lean_dec_ref(v___y_3849_);
lean_dec_ref(v_args_3845_);
lean_dec(v_upperBound_3844_);
return v_res_3852_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecAfterFullApp(lean_object* v_args_3853_, lean_object* v_ps_3854_, lean_object* v_k_3855_, lean_object* v_a_3856_, lean_object* v_a_3857_, lean_object* v_a_3858_, lean_object* v_a_3859_, lean_object* v_a_3860_, lean_object* v_a_3861_){
_start:
{
lean_object* v___x_3863_; lean_object* v___x_3864_; lean_object* v___x_3865_; 
v___x_3863_ = lean_unsigned_to_nat(0u);
v___x_3864_ = lean_array_get_size(v_args_3853_);
v___x_3865_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecAfterFullApp_spec__0___redArg(v___x_3864_, v_args_3853_, v_ps_3854_, v___x_3863_, v_k_3855_, v_a_3856_, v_a_3857_);
return v___x_3865_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecAfterFullApp___boxed(lean_object* v_args_3866_, lean_object* v_ps_3867_, lean_object* v_k_3868_, lean_object* v_a_3869_, lean_object* v_a_3870_, lean_object* v_a_3871_, lean_object* v_a_3872_, lean_object* v_a_3873_, lean_object* v_a_3874_, lean_object* v_a_3875_){
_start:
{
lean_object* v_res_3876_; 
v_res_3876_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecAfterFullApp(v_args_3866_, v_ps_3867_, v_k_3868_, v_a_3869_, v_a_3870_, v_a_3871_, v_a_3872_, v_a_3873_, v_a_3874_);
lean_dec(v_a_3874_);
lean_dec_ref(v_a_3873_);
lean_dec(v_a_3872_);
lean_dec_ref(v_a_3871_);
lean_dec(v_a_3870_);
lean_dec_ref(v_a_3869_);
lean_dec_ref(v_args_3866_);
return v_res_3876_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecAfterFullApp_spec__0(lean_object* v_upperBound_3877_, lean_object* v_args_3878_, lean_object* v_ps_3879_, lean_object* v_inst_3880_, lean_object* v_R_3881_, lean_object* v_a_3882_, lean_object* v_b_3883_, lean_object* v_c_3884_, lean_object* v___y_3885_, lean_object* v___y_3886_, lean_object* v___y_3887_, lean_object* v___y_3888_, lean_object* v___y_3889_, lean_object* v___y_3890_){
_start:
{
lean_object* v___x_3892_; 
v___x_3892_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecAfterFullApp_spec__0___redArg(v_upperBound_3877_, v_args_3878_, v_ps_3879_, v_a_3882_, v_b_3883_, v___y_3885_, v___y_3886_);
return v___x_3892_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecAfterFullApp_spec__0___boxed(lean_object* v_upperBound_3893_, lean_object* v_args_3894_, lean_object* v_ps_3895_, lean_object* v_inst_3896_, lean_object* v_R_3897_, lean_object* v_a_3898_, lean_object* v_b_3899_, lean_object* v_c_3900_, lean_object* v___y_3901_, lean_object* v___y_3902_, lean_object* v___y_3903_, lean_object* v___y_3904_, lean_object* v___y_3905_, lean_object* v___y_3906_, lean_object* v___y_3907_){
_start:
{
lean_object* v_res_3908_; 
v_res_3908_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecAfterFullApp_spec__0(v_upperBound_3893_, v_args_3894_, v_ps_3895_, v_inst_3896_, v_R_3897_, v_a_3898_, v_b_3899_, v_c_3900_, v___y_3901_, v___y_3902_, v___y_3903_, v___y_3904_, v___y_3905_, v___y_3906_);
lean_dec(v___y_3906_);
lean_dec_ref(v___y_3905_);
lean_dec(v___y_3904_);
lean_dec_ref(v___y_3903_);
lean_dec(v___y_3902_);
lean_dec_ref(v___y_3901_);
lean_dec_ref(v_args_3894_);
lean_dec(v_upperBound_3893_);
return v_res_3908_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecIfNeeded___redArg(lean_object* v_fvarId_3909_, lean_object* v_k_3910_, lean_object* v_a_3911_, lean_object* v_a_3912_){
_start:
{
lean_object* v___x_3914_; lean_object* v_varMap_3915_; lean_object* v___x_3916_; lean_object* v___x_3917_; uint8_t v_isPossibleRef_3918_; 
v___x_3914_ = lean_st_ref_get(v_a_3912_);
v_varMap_3915_ = lean_ctor_get(v_a_3911_, 2);
v___x_3916_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_instInhabitedVarInfo_default));
v___x_3917_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__0___redArg(v___x_3916_, v_varMap_3915_, v_fvarId_3909_);
v_isPossibleRef_3918_ = lean_ctor_get_uint8(v___x_3917_, sizeof(void*)*1);
if (v_isPossibleRef_3918_ == 0)
{
lean_object* v___x_3919_; 
lean_dec(v___x_3917_);
lean_dec(v___x_3914_);
lean_dec(v_fvarId_3909_);
v___x_3919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3919_, 0, v_k_3910_);
return v___x_3919_;
}
else
{
uint8_t v_isDefiniteRef_3920_; uint8_t v_persistent_3921_; uint8_t v___x_3922_; 
v_isDefiniteRef_3920_ = lean_ctor_get_uint8(v___x_3917_, sizeof(void*)*1 + 1);
v_persistent_3921_ = lean_ctor_get_uint8(v___x_3917_, sizeof(void*)*1 + 2);
lean_dec(v___x_3917_);
v___x_3922_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_isAccessible(v___x_3914_, v_fvarId_3909_);
lean_dec(v___x_3914_);
if (v___x_3922_ == 0)
{
lean_object* v___x_3923_; uint8_t v___y_3925_; 
v___x_3923_ = lean_unsigned_to_nat(1u);
if (v_isDefiniteRef_3920_ == 0)
{
v___y_3925_ = v_isPossibleRef_3918_;
goto v___jp_3924_;
}
else
{
v___y_3925_ = v___x_3922_;
goto v___jp_3924_;
}
v___jp_3924_:
{
lean_object* v___x_3926_; lean_object* v___x_3927_; 
v___x_3926_ = lean_alloc_ctor(12, 3, 2);
lean_ctor_set(v___x_3926_, 0, v_fvarId_3909_);
lean_ctor_set(v___x_3926_, 1, v___x_3923_);
lean_ctor_set(v___x_3926_, 2, v_k_3910_);
lean_ctor_set_uint8(v___x_3926_, sizeof(void*)*3, v___y_3925_);
lean_ctor_set_uint8(v___x_3926_, sizeof(void*)*3 + 1, v_persistent_3921_);
v___x_3927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3927_, 0, v___x_3926_);
return v___x_3927_;
}
}
else
{
lean_object* v___x_3928_; 
lean_dec(v_fvarId_3909_);
v___x_3928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3928_, 0, v_k_3910_);
return v___x_3928_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecIfNeeded___redArg___boxed(lean_object* v_fvarId_3929_, lean_object* v_k_3930_, lean_object* v_a_3931_, lean_object* v_a_3932_, lean_object* v_a_3933_){
_start:
{
lean_object* v_res_3934_; 
v_res_3934_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecIfNeeded___redArg(v_fvarId_3929_, v_k_3930_, v_a_3931_, v_a_3932_);
lean_dec(v_a_3932_);
lean_dec_ref(v_a_3931_);
return v_res_3934_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecIfNeeded(lean_object* v_fvarId_3935_, lean_object* v_k_3936_, lean_object* v_a_3937_, lean_object* v_a_3938_, lean_object* v_a_3939_, lean_object* v_a_3940_, lean_object* v_a_3941_, lean_object* v_a_3942_){
_start:
{
lean_object* v___x_3944_; 
v___x_3944_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecIfNeeded___redArg(v_fvarId_3935_, v_k_3936_, v_a_3937_, v_a_3938_);
return v___x_3944_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecIfNeeded___boxed(lean_object* v_fvarId_3945_, lean_object* v_k_3946_, lean_object* v_a_3947_, lean_object* v_a_3948_, lean_object* v_a_3949_, lean_object* v_a_3950_, lean_object* v_a_3951_, lean_object* v_a_3952_, lean_object* v_a_3953_){
_start:
{
lean_object* v_res_3954_; 
v_res_3954_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecIfNeeded(v_fvarId_3945_, v_k_3946_, v_a_3947_, v_a_3948_, v_a_3949_, v_a_3950_, v_a_3951_, v_a_3952_);
lean_dec(v_a_3952_);
lean_dec_ref(v_a_3951_);
lean_dec(v_a_3950_);
lean_dec_ref(v_a_3949_);
lean_dec(v_a_3948_);
lean_dec_ref(v_a_3947_);
return v_res_3954_;
}
}
static lean_object* _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_ensureNoBorrow_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_3955_; 
v___x_3955_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3955_;
}
}
static lean_object* _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_ensureNoBorrow_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_3956_; lean_object* v___x_3957_; 
v___x_3956_ = lean_obj_once(&l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_ensureNoBorrow_spec__0___redArg___closed__0, &l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_ensureNoBorrow_spec__0___redArg___closed__0_once, _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_ensureNoBorrow_spec__0___redArg___closed__0);
v___x_3957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3957_, 0, v___x_3956_);
return v___x_3957_;
}
}
static lean_object* _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_ensureNoBorrow_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; 
v___x_3958_ = lean_obj_once(&l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_ensureNoBorrow_spec__0___redArg___closed__1, &l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_ensureNoBorrow_spec__0___redArg___closed__1_once, _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_ensureNoBorrow_spec__0___redArg___closed__1);
v___x_3959_ = lean_unsigned_to_nat(0u);
v___x_3960_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_3960_, 0, v___x_3959_);
lean_ctor_set(v___x_3960_, 1, v___x_3959_);
lean_ctor_set(v___x_3960_, 2, v___x_3959_);
lean_ctor_set(v___x_3960_, 3, v___x_3958_);
lean_ctor_set(v___x_3960_, 4, v___x_3958_);
lean_ctor_set(v___x_3960_, 5, v___x_3958_);
lean_ctor_set(v___x_3960_, 6, v___x_3958_);
lean_ctor_set(v___x_3960_, 7, v___x_3958_);
lean_ctor_set(v___x_3960_, 8, v___x_3958_);
return v___x_3960_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_ensureNoBorrow_spec__0___redArg(lean_object* v_msg_3961_, lean_object* v___y_3962_, lean_object* v___y_3963_, lean_object* v___y_3964_, lean_object* v___y_3965_){
_start:
{
lean_object* v_options_3967_; lean_object* v_ref_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; 
v_options_3967_ = lean_ctor_get(v___y_3964_, 2);
v_ref_3968_ = lean_ctor_get(v___y_3964_, 5);
v___x_3969_ = lean_st_ref_get(v___y_3965_);
v___x_3970_ = lean_st_ref_get(v___y_3963_);
v___x_3971_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_3962_);
if (lean_obj_tag(v___x_3971_) == 0)
{
lean_object* v_a_3972_; lean_object* v___x_3974_; uint8_t v_isShared_3975_; uint8_t v_isSharedCheck_3994_; 
v_a_3972_ = lean_ctor_get(v___x_3971_, 0);
v_isSharedCheck_3994_ = !lean_is_exclusive(v___x_3971_);
if (v_isSharedCheck_3994_ == 0)
{
v___x_3974_ = v___x_3971_;
v_isShared_3975_ = v_isSharedCheck_3994_;
goto v_resetjp_3973_;
}
else
{
lean_inc(v_a_3972_);
lean_dec(v___x_3971_);
v___x_3974_ = lean_box(0);
v_isShared_3975_ = v_isSharedCheck_3994_;
goto v_resetjp_3973_;
}
v_resetjp_3973_:
{
lean_object* v_env_3976_; lean_object* v_lctx_3977_; lean_object* v___x_3979_; uint8_t v_isShared_3980_; uint8_t v_isSharedCheck_3992_; 
v_env_3976_ = lean_ctor_get(v___x_3969_, 0);
lean_inc_ref(v_env_3976_);
lean_dec(v___x_3969_);
v_lctx_3977_ = lean_ctor_get(v___x_3970_, 0);
v_isSharedCheck_3992_ = !lean_is_exclusive(v___x_3970_);
if (v_isSharedCheck_3992_ == 0)
{
lean_object* v_unused_3993_; 
v_unused_3993_ = lean_ctor_get(v___x_3970_, 1);
lean_dec(v_unused_3993_);
v___x_3979_ = v___x_3970_;
v_isShared_3980_ = v_isSharedCheck_3992_;
goto v_resetjp_3978_;
}
else
{
lean_inc(v_lctx_3977_);
lean_dec(v___x_3970_);
v___x_3979_ = lean_box(0);
v_isShared_3980_ = v_isSharedCheck_3992_;
goto v_resetjp_3978_;
}
v_resetjp_3978_:
{
uint8_t v___x_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; lean_object* v___x_3986_; 
v___x_3981_ = lean_unbox(v_a_3972_);
lean_dec(v_a_3972_);
v___x_3982_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_3977_, v___x_3981_);
lean_dec_ref(v_lctx_3977_);
v___x_3983_ = lean_obj_once(&l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_ensureNoBorrow_spec__0___redArg___closed__2, &l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_ensureNoBorrow_spec__0___redArg___closed__2_once, _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_ensureNoBorrow_spec__0___redArg___closed__2);
lean_inc_ref(v_options_3967_);
v___x_3984_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3984_, 0, v_env_3976_);
lean_ctor_set(v___x_3984_, 1, v___x_3983_);
lean_ctor_set(v___x_3984_, 2, v___x_3982_);
lean_ctor_set(v___x_3984_, 3, v_options_3967_);
if (v_isShared_3980_ == 0)
{
lean_ctor_set_tag(v___x_3979_, 3);
lean_ctor_set(v___x_3979_, 1, v_msg_3961_);
lean_ctor_set(v___x_3979_, 0, v___x_3984_);
v___x_3986_ = v___x_3979_;
goto v_reusejp_3985_;
}
else
{
lean_object* v_reuseFailAlloc_3991_; 
v_reuseFailAlloc_3991_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3991_, 0, v___x_3984_);
lean_ctor_set(v_reuseFailAlloc_3991_, 1, v_msg_3961_);
v___x_3986_ = v_reuseFailAlloc_3991_;
goto v_reusejp_3985_;
}
v_reusejp_3985_:
{
lean_object* v___x_3987_; lean_object* v___x_3989_; 
lean_inc(v_ref_3968_);
v___x_3987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3987_, 0, v_ref_3968_);
lean_ctor_set(v___x_3987_, 1, v___x_3986_);
if (v_isShared_3975_ == 0)
{
lean_ctor_set_tag(v___x_3974_, 1);
lean_ctor_set(v___x_3974_, 0, v___x_3987_);
v___x_3989_ = v___x_3974_;
goto v_reusejp_3988_;
}
else
{
lean_object* v_reuseFailAlloc_3990_; 
v_reuseFailAlloc_3990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3990_, 0, v___x_3987_);
v___x_3989_ = v_reuseFailAlloc_3990_;
goto v_reusejp_3988_;
}
v_reusejp_3988_:
{
return v___x_3989_;
}
}
}
}
}
else
{
lean_object* v_a_3995_; lean_object* v___x_3997_; uint8_t v_isShared_3998_; uint8_t v_isSharedCheck_4002_; 
lean_dec(v___x_3970_);
lean_dec(v___x_3969_);
lean_dec_ref(v_msg_3961_);
v_a_3995_ = lean_ctor_get(v___x_3971_, 0);
v_isSharedCheck_4002_ = !lean_is_exclusive(v___x_3971_);
if (v_isSharedCheck_4002_ == 0)
{
v___x_3997_ = v___x_3971_;
v_isShared_3998_ = v_isSharedCheck_4002_;
goto v_resetjp_3996_;
}
else
{
lean_inc(v_a_3995_);
lean_dec(v___x_3971_);
v___x_3997_ = lean_box(0);
v_isShared_3998_ = v_isSharedCheck_4002_;
goto v_resetjp_3996_;
}
v_resetjp_3996_:
{
lean_object* v___x_4000_; 
if (v_isShared_3998_ == 0)
{
v___x_4000_ = v___x_3997_;
goto v_reusejp_3999_;
}
else
{
lean_object* v_reuseFailAlloc_4001_; 
v_reuseFailAlloc_4001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4001_, 0, v_a_3995_);
v___x_4000_ = v_reuseFailAlloc_4001_;
goto v_reusejp_3999_;
}
v_reusejp_3999_:
{
return v___x_4000_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_ensureNoBorrow_spec__0___redArg___boxed(lean_object* v_msg_4003_, lean_object* v___y_4004_, lean_object* v___y_4005_, lean_object* v___y_4006_, lean_object* v___y_4007_, lean_object* v___y_4008_){
_start:
{
lean_object* v_res_4009_; 
v_res_4009_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_ensureNoBorrow_spec__0___redArg(v_msg_4003_, v___y_4004_, v___y_4005_, v___y_4006_, v___y_4007_);
lean_dec(v___y_4007_);
lean_dec_ref(v___y_4006_);
lean_dec(v___y_4005_);
lean_dec_ref(v___y_4004_);
return v_res_4009_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_ensureNoBorrow_spec__0(lean_object* v_00_u03b1_4010_, lean_object* v_msg_4011_, lean_object* v___y_4012_, lean_object* v___y_4013_, lean_object* v___y_4014_, lean_object* v___y_4015_, lean_object* v___y_4016_, lean_object* v___y_4017_){
_start:
{
lean_object* v___x_4019_; 
v___x_4019_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_ensureNoBorrow_spec__0___redArg(v_msg_4011_, v___y_4014_, v___y_4015_, v___y_4016_, v___y_4017_);
return v___x_4019_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_ensureNoBorrow_spec__0___boxed(lean_object* v_00_u03b1_4020_, lean_object* v_msg_4021_, lean_object* v___y_4022_, lean_object* v___y_4023_, lean_object* v___y_4024_, lean_object* v___y_4025_, lean_object* v___y_4026_, lean_object* v___y_4027_, lean_object* v___y_4028_){
_start:
{
lean_object* v_res_4029_; 
v_res_4029_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_ensureNoBorrow_spec__0(v_00_u03b1_4020_, v_msg_4021_, v___y_4022_, v___y_4023_, v___y_4024_, v___y_4025_, v___y_4026_, v___y_4027_);
lean_dec(v___y_4027_);
lean_dec_ref(v___y_4026_);
lean_dec(v___y_4025_);
lean_dec_ref(v___y_4024_);
lean_dec(v___y_4023_);
lean_dec_ref(v___y_4022_);
return v_res_4029_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_ensureNoBorrow___closed__1(void){
_start:
{
lean_object* v___x_4031_; lean_object* v___x_4032_; 
v___x_4031_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_ensureNoBorrow___closed__0));
v___x_4032_ = l_Lean_stringToMessageData(v___x_4031_);
return v___x_4032_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_ensureNoBorrow___closed__3(void){
_start:
{
lean_object* v___x_4034_; lean_object* v___x_4035_; 
v___x_4034_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_ensureNoBorrow___closed__2));
v___x_4035_ = l_Lean_stringToMessageData(v___x_4034_);
return v___x_4035_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_ensureNoBorrow(lean_object* v_decl_4036_, lean_object* v_a_4037_, lean_object* v_a_4038_, lean_object* v_a_4039_, lean_object* v_a_4040_, lean_object* v_a_4041_, lean_object* v_a_4042_){
_start:
{
lean_object* v___x_4044_; lean_object* v_fvarId_4045_; lean_object* v_borrows_4046_; lean_object* v___x_4048_; uint8_t v_isShared_4049_; uint8_t v_isSharedCheck_4075_; 
v___x_4044_ = lean_st_ref_get(v_a_4038_);
v_fvarId_4045_ = lean_ctor_get(v_decl_4036_, 0);
v_borrows_4046_ = lean_ctor_get(v___x_4044_, 1);
v_isSharedCheck_4075_ = !lean_is_exclusive(v___x_4044_);
if (v_isSharedCheck_4075_ == 0)
{
lean_object* v_unused_4076_; 
v_unused_4076_ = lean_ctor_get(v___x_4044_, 0);
lean_dec(v_unused_4076_);
v___x_4048_ = v___x_4044_;
v_isShared_4049_ = v_isSharedCheck_4075_;
goto v_resetjp_4047_;
}
else
{
lean_inc(v_borrows_4046_);
lean_dec(v___x_4044_);
v___x_4048_ = lean_box(0);
v_isShared_4049_ = v_isSharedCheck_4075_;
goto v_resetjp_4047_;
}
v_resetjp_4047_:
{
uint8_t v___x_4050_; 
v___x_4050_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_isAccessible_spec__0___redArg(v_borrows_4046_, v_fvarId_4045_);
lean_dec_ref(v_borrows_4046_);
if (v___x_4050_ == 0)
{
lean_object* v___x_4051_; lean_object* v___x_4052_; 
lean_del_object(v___x_4048_);
lean_dec_ref(v_decl_4036_);
v___x_4051_ = lean_box(0);
v___x_4052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4052_, 0, v___x_4051_);
return v___x_4052_;
}
else
{
uint8_t v___x_4053_; lean_object* v___x_4054_; lean_object* v___x_4055_; lean_object* v___x_4056_; 
v___x_4053_ = 1;
v___x_4054_ = lean_box(v___x_4053_);
v___x_4055_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PP_ppLetDecl___boxed), 8, 2);
lean_closure_set(v___x_4055_, 0, v___x_4054_);
lean_closure_set(v___x_4055_, 1, v_decl_4036_);
lean_inc_ref(v_a_4041_);
v___x_4056_ = l_Lean_Compiler_LCNF_PP_run___redArg(v___x_4055_, v_a_4039_, v_a_4040_, v_a_4041_, v_a_4042_);
if (lean_obj_tag(v___x_4056_) == 0)
{
lean_object* v_a_4057_; lean_object* v___x_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; lean_object* v___x_4062_; 
v_a_4057_ = lean_ctor_get(v___x_4056_, 0);
lean_inc(v_a_4057_);
lean_dec_ref(v___x_4056_);
v___x_4058_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_ensureNoBorrow___closed__1, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_ensureNoBorrow___closed__1_once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_ensureNoBorrow___closed__1);
v___x_4059_ = l_Lean_MessageData_ofFormat(v_a_4057_);
v___x_4060_ = l_Lean_indentD(v___x_4059_);
if (v_isShared_4049_ == 0)
{
lean_ctor_set_tag(v___x_4048_, 7);
lean_ctor_set(v___x_4048_, 1, v___x_4060_);
lean_ctor_set(v___x_4048_, 0, v___x_4058_);
v___x_4062_ = v___x_4048_;
goto v_reusejp_4061_;
}
else
{
lean_object* v_reuseFailAlloc_4066_; 
v_reuseFailAlloc_4066_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4066_, 0, v___x_4058_);
lean_ctor_set(v_reuseFailAlloc_4066_, 1, v___x_4060_);
v___x_4062_ = v_reuseFailAlloc_4066_;
goto v_reusejp_4061_;
}
v_reusejp_4061_:
{
lean_object* v___x_4063_; lean_object* v___x_4064_; lean_object* v___x_4065_; 
v___x_4063_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_ensureNoBorrow___closed__3, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_ensureNoBorrow___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_ensureNoBorrow___closed__3);
v___x_4064_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4064_, 0, v___x_4062_);
lean_ctor_set(v___x_4064_, 1, v___x_4063_);
v___x_4065_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_ensureNoBorrow_spec__0___redArg(v___x_4064_, v_a_4039_, v_a_4040_, v_a_4041_, v_a_4042_);
return v___x_4065_;
}
}
else
{
lean_object* v_a_4067_; lean_object* v___x_4069_; uint8_t v_isShared_4070_; uint8_t v_isSharedCheck_4074_; 
lean_del_object(v___x_4048_);
v_a_4067_ = lean_ctor_get(v___x_4056_, 0);
v_isSharedCheck_4074_ = !lean_is_exclusive(v___x_4056_);
if (v_isSharedCheck_4074_ == 0)
{
v___x_4069_ = v___x_4056_;
v_isShared_4070_ = v_isSharedCheck_4074_;
goto v_resetjp_4068_;
}
else
{
lean_inc(v_a_4067_);
lean_dec(v___x_4056_);
v___x_4069_ = lean_box(0);
v_isShared_4070_ = v_isSharedCheck_4074_;
goto v_resetjp_4068_;
}
v_resetjp_4068_:
{
lean_object* v___x_4072_; 
if (v_isShared_4070_ == 0)
{
v___x_4072_ = v___x_4069_;
goto v_reusejp_4071_;
}
else
{
lean_object* v_reuseFailAlloc_4073_; 
v_reuseFailAlloc_4073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4073_, 0, v_a_4067_);
v___x_4072_ = v_reuseFailAlloc_4073_;
goto v_reusejp_4071_;
}
v_reusejp_4071_:
{
return v___x_4072_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_ensureNoBorrow___boxed(lean_object* v_decl_4077_, lean_object* v_a_4078_, lean_object* v_a_4079_, lean_object* v_a_4080_, lean_object* v_a_4081_, lean_object* v_a_4082_, lean_object* v_a_4083_, lean_object* v_a_4084_){
_start:
{
lean_object* v_res_4085_; 
v_res_4085_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_ensureNoBorrow(v_decl_4077_, v_a_4078_, v_a_4079_, v_a_4080_, v_a_4081_, v_a_4082_, v_a_4083_);
lean_dec(v_a_4083_);
lean_dec_ref(v_a_4082_);
lean_dec(v_a_4081_);
lean_dec_ref(v_a_4080_);
lean_dec(v_a_4079_);
lean_dec_ref(v_a_4078_);
return v_res_4085_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0___closed__1(void){
_start:
{
lean_object* v___x_4087_; lean_object* v___x_4088_; 
v___x_4087_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0___closed__0));
v___x_4088_ = l_Lean_stringToMessageData(v___x_4087_);
return v___x_4088_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0___closed__3(void){
_start:
{
lean_object* v___x_4090_; lean_object* v___x_4091_; 
v___x_4090_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0___closed__2));
v___x_4091_ = l_Lean_stringToMessageData(v___x_4090_);
return v___x_4091_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0(lean_object* v_as_4094_, size_t v_i_4095_, size_t v_stop_4096_, lean_object* v_b_4097_, lean_object* v___y_4098_, lean_object* v___y_4099_, lean_object* v___y_4100_, lean_object* v___y_4101_, lean_object* v___y_4102_, lean_object* v___y_4103_){
_start:
{
lean_object* v_a_4106_; uint8_t v___x_4110_; 
v___x_4110_ = lean_usize_dec_eq(v_i_4095_, v_stop_4096_);
if (v___x_4110_ == 0)
{
lean_object* v___x_4111_; lean_object* v_fvarId_4112_; lean_object* v_binderName_4113_; lean_object* v_type_4114_; uint8_t v_borrow_4115_; lean_object* v___x_4116_; 
v___x_4111_ = lean_array_uget_borrowed(v_as_4094_, v_i_4095_);
v_fvarId_4112_ = lean_ctor_get(v___x_4111_, 0);
v_binderName_4113_ = lean_ctor_get(v___x_4111_, 1);
v_type_4114_ = lean_ctor_get(v___x_4111_, 2);
v_borrow_4115_ = lean_ctor_get_uint8(v___x_4111_, sizeof(void*)*3);
lean_inc(v_fvarId_4112_);
v___x_4116_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecIfNeeded___redArg(v_fvarId_4112_, v_b_4097_, v___y_4098_, v___y_4099_);
if (lean_obj_tag(v___x_4116_) == 0)
{
lean_object* v_a_4117_; lean_object* v___x_4119_; uint8_t v_isShared_4120_; uint8_t v_isSharedCheck_4177_; 
v_a_4117_ = lean_ctor_get(v___x_4116_, 0);
v_isSharedCheck_4177_ = !lean_is_exclusive(v___x_4116_);
if (v_isSharedCheck_4177_ == 0)
{
v___x_4119_ = v___x_4116_;
v_isShared_4120_ = v_isSharedCheck_4177_;
goto v_resetjp_4118_;
}
else
{
lean_inc(v_a_4117_);
lean_dec(v___x_4116_);
v___x_4119_ = lean_box(0);
v_isShared_4120_ = v_isSharedCheck_4177_;
goto v_resetjp_4118_;
}
v_resetjp_4118_:
{
lean_object* v___y_4122_; lean_object* v___y_4137_; lean_object* v___y_4138_; lean_object* v___x_4153_; uint8_t v___y_4155_; lean_object* v_borrows_4173_; uint8_t v___x_4174_; 
v___x_4153_ = lean_st_ref_get(v___y_4099_);
v_borrows_4173_ = lean_ctor_get(v___x_4153_, 1);
lean_inc_ref(v_borrows_4173_);
lean_dec(v___x_4153_);
v___x_4174_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_isAccessible_spec__0___redArg(v_borrows_4173_, v_fvarId_4112_);
lean_dec_ref(v_borrows_4173_);
if (v_borrow_4115_ == 0)
{
goto v___jp_4175_;
}
else
{
uint8_t v___x_4176_; 
v___x_4176_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isPossibleRef(v_type_4114_);
if (v___x_4176_ == 0)
{
goto v___jp_4175_;
}
else
{
v___y_4155_ = v___x_4174_;
goto v___jp_4154_;
}
}
v___jp_4121_:
{
lean_object* v___x_4123_; lean_object* v_vars_4124_; lean_object* v_borrows_4125_; lean_object* v___x_4127_; uint8_t v_isShared_4128_; uint8_t v_isSharedCheck_4135_; 
v___x_4123_ = lean_st_ref_take(v___y_4122_);
v_vars_4124_ = lean_ctor_get(v___x_4123_, 0);
v_borrows_4125_ = lean_ctor_get(v___x_4123_, 1);
v_isSharedCheck_4135_ = !lean_is_exclusive(v___x_4123_);
if (v_isSharedCheck_4135_ == 0)
{
v___x_4127_ = v___x_4123_;
v_isShared_4128_ = v_isSharedCheck_4135_;
goto v_resetjp_4126_;
}
else
{
lean_inc(v_borrows_4125_);
lean_inc(v_vars_4124_);
lean_dec(v___x_4123_);
v___x_4127_ = lean_box(0);
v_isShared_4128_ = v_isSharedCheck_4135_;
goto v_resetjp_4126_;
}
v_resetjp_4126_:
{
lean_object* v_vars_4129_; lean_object* v_borrows_4130_; lean_object* v___x_4132_; 
v_vars_4129_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_removeFromParent_spec__0___redArg(v_vars_4124_, v_fvarId_4112_);
v_borrows_4130_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_removeFromParent_spec__0___redArg(v_borrows_4125_, v_fvarId_4112_);
if (v_isShared_4128_ == 0)
{
lean_ctor_set(v___x_4127_, 1, v_borrows_4130_);
lean_ctor_set(v___x_4127_, 0, v_vars_4129_);
v___x_4132_ = v___x_4127_;
goto v_reusejp_4131_;
}
else
{
lean_object* v_reuseFailAlloc_4134_; 
v_reuseFailAlloc_4134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4134_, 0, v_vars_4129_);
lean_ctor_set(v_reuseFailAlloc_4134_, 1, v_borrows_4130_);
v___x_4132_ = v_reuseFailAlloc_4134_;
goto v_reusejp_4131_;
}
v_reusejp_4131_:
{
lean_object* v___x_4133_; 
v___x_4133_ = lean_st_ref_set(v___y_4122_, v___x_4132_);
v_a_4106_ = v_a_4117_;
goto v___jp_4105_;
}
}
}
v___jp_4136_:
{
lean_object* v___x_4140_; 
if (v_isShared_4120_ == 0)
{
lean_ctor_set_tag(v___x_4119_, 3);
lean_ctor_set(v___x_4119_, 0, v___y_4138_);
v___x_4140_ = v___x_4119_;
goto v_reusejp_4139_;
}
else
{
lean_object* v_reuseFailAlloc_4152_; 
v_reuseFailAlloc_4152_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4152_, 0, v___y_4138_);
v___x_4140_ = v_reuseFailAlloc_4152_;
goto v_reusejp_4139_;
}
v_reusejp_4139_:
{
lean_object* v___x_4141_; lean_object* v___x_4142_; lean_object* v___x_4143_; 
v___x_4141_ = l_Lean_MessageData_ofFormat(v___x_4140_);
v___x_4142_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4142_, 0, v___y_4137_);
lean_ctor_set(v___x_4142_, 1, v___x_4141_);
v___x_4143_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_ensureNoBorrow_spec__0___redArg(v___x_4142_, v___y_4100_, v___y_4101_, v___y_4102_, v___y_4103_);
if (lean_obj_tag(v___x_4143_) == 0)
{
lean_dec_ref(v___x_4143_);
v___y_4122_ = v___y_4099_;
goto v___jp_4121_;
}
else
{
lean_object* v_a_4144_; lean_object* v___x_4146_; uint8_t v_isShared_4147_; uint8_t v_isSharedCheck_4151_; 
lean_dec(v_a_4117_);
v_a_4144_ = lean_ctor_get(v___x_4143_, 0);
v_isSharedCheck_4151_ = !lean_is_exclusive(v___x_4143_);
if (v_isSharedCheck_4151_ == 0)
{
v___x_4146_ = v___x_4143_;
v_isShared_4147_ = v_isSharedCheck_4151_;
goto v_resetjp_4145_;
}
else
{
lean_inc(v_a_4144_);
lean_dec(v___x_4143_);
v___x_4146_ = lean_box(0);
v_isShared_4147_ = v_isSharedCheck_4151_;
goto v_resetjp_4145_;
}
v_resetjp_4145_:
{
lean_object* v___x_4149_; 
if (v_isShared_4147_ == 0)
{
v___x_4149_ = v___x_4146_;
goto v_reusejp_4148_;
}
else
{
lean_object* v_reuseFailAlloc_4150_; 
v_reuseFailAlloc_4150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4150_, 0, v_a_4144_);
v___x_4149_ = v_reuseFailAlloc_4150_;
goto v_reusejp_4148_;
}
v_reusejp_4148_:
{
return v___x_4149_;
}
}
}
}
}
v___jp_4154_:
{
if (v___y_4155_ == 0)
{
lean_object* v___x_4156_; lean_object* v_borrows_4157_; lean_object* v___x_4159_; uint8_t v_isShared_4160_; uint8_t v_isSharedCheck_4171_; 
v___x_4156_ = lean_st_ref_get(v___y_4099_);
v_borrows_4157_ = lean_ctor_get(v___x_4156_, 1);
v_isSharedCheck_4171_ = !lean_is_exclusive(v___x_4156_);
if (v_isSharedCheck_4171_ == 0)
{
lean_object* v_unused_4172_; 
v_unused_4172_ = lean_ctor_get(v___x_4156_, 0);
lean_dec(v_unused_4172_);
v___x_4159_ = v___x_4156_;
v_isShared_4160_ = v_isSharedCheck_4171_;
goto v_resetjp_4158_;
}
else
{
lean_inc(v_borrows_4157_);
lean_dec(v___x_4156_);
v___x_4159_ = lean_box(0);
v_isShared_4160_ = v_isSharedCheck_4171_;
goto v_resetjp_4158_;
}
v_resetjp_4158_:
{
uint8_t v___x_4161_; lean_object* v___x_4162_; lean_object* v___x_4163_; lean_object* v___x_4165_; 
v___x_4161_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_isAccessible_spec__0___redArg(v_borrows_4157_, v_fvarId_4112_);
lean_dec_ref(v_borrows_4157_);
v___x_4162_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0___closed__1);
lean_inc(v_binderName_4113_);
v___x_4163_ = l_Lean_MessageData_ofName(v_binderName_4113_);
if (v_isShared_4160_ == 0)
{
lean_ctor_set_tag(v___x_4159_, 7);
lean_ctor_set(v___x_4159_, 1, v___x_4163_);
lean_ctor_set(v___x_4159_, 0, v___x_4162_);
v___x_4165_ = v___x_4159_;
goto v_reusejp_4164_;
}
else
{
lean_object* v_reuseFailAlloc_4170_; 
v_reuseFailAlloc_4170_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4170_, 0, v___x_4162_);
lean_ctor_set(v_reuseFailAlloc_4170_, 1, v___x_4163_);
v___x_4165_ = v_reuseFailAlloc_4170_;
goto v_reusejp_4164_;
}
v_reusejp_4164_:
{
lean_object* v___x_4166_; lean_object* v___x_4167_; 
v___x_4166_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0___closed__3);
v___x_4167_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4167_, 0, v___x_4165_);
lean_ctor_set(v___x_4167_, 1, v___x_4166_);
if (v___x_4161_ == 0)
{
lean_object* v___x_4168_; 
v___x_4168_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0___closed__4));
v___y_4137_ = v___x_4167_;
v___y_4138_ = v___x_4168_;
goto v___jp_4136_;
}
else
{
lean_object* v___x_4169_; 
v___x_4169_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0___closed__5));
v___y_4137_ = v___x_4167_;
v___y_4138_ = v___x_4169_;
goto v___jp_4136_;
}
}
}
}
else
{
lean_del_object(v___x_4119_);
v___y_4122_ = v___y_4099_;
goto v___jp_4121_;
}
}
v___jp_4175_:
{
if (v___x_4174_ == 0)
{
lean_del_object(v___x_4119_);
v___y_4122_ = v___y_4099_;
goto v___jp_4121_;
}
else
{
v___y_4155_ = v___x_4110_;
goto v___jp_4154_;
}
}
}
}
else
{
if (lean_obj_tag(v___x_4116_) == 0)
{
lean_object* v_a_4178_; 
v_a_4178_ = lean_ctor_get(v___x_4116_, 0);
lean_inc(v_a_4178_);
lean_dec_ref(v___x_4116_);
v_a_4106_ = v_a_4178_;
goto v___jp_4105_;
}
else
{
return v___x_4116_;
}
}
}
else
{
lean_object* v___x_4179_; 
v___x_4179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4179_, 0, v_b_4097_);
return v___x_4179_;
}
v___jp_4105_:
{
size_t v___x_4107_; size_t v___x_4108_; 
v___x_4107_ = ((size_t)1ULL);
v___x_4108_ = lean_usize_add(v_i_4095_, v___x_4107_);
v_i_4095_ = v___x_4108_;
v_b_4097_ = v_a_4106_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0___boxed(lean_object* v_as_4180_, lean_object* v_i_4181_, lean_object* v_stop_4182_, lean_object* v_b_4183_, lean_object* v___y_4184_, lean_object* v___y_4185_, lean_object* v___y_4186_, lean_object* v___y_4187_, lean_object* v___y_4188_, lean_object* v___y_4189_, lean_object* v___y_4190_){
_start:
{
size_t v_i_boxed_4191_; size_t v_stop_boxed_4192_; lean_object* v_res_4193_; 
v_i_boxed_4191_ = lean_unbox_usize(v_i_4181_);
lean_dec(v_i_4181_);
v_stop_boxed_4192_ = lean_unbox_usize(v_stop_4182_);
lean_dec(v_stop_4182_);
v_res_4193_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0(v_as_4180_, v_i_boxed_4191_, v_stop_boxed_4192_, v_b_4183_, v___y_4184_, v___y_4185_, v___y_4186_, v___y_4187_, v___y_4188_, v___y_4189_);
lean_dec(v___y_4189_);
lean_dec_ref(v___y_4188_);
lean_dec(v___y_4187_);
lean_dec_ref(v___y_4186_);
lean_dec(v___y_4185_);
lean_dec_ref(v___y_4184_);
lean_dec_ref(v_as_4180_);
return v_res_4193_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams(lean_object* v_ps_4194_, lean_object* v_k_4195_, lean_object* v_a_4196_, lean_object* v_a_4197_, lean_object* v_a_4198_, lean_object* v_a_4199_, lean_object* v_a_4200_, lean_object* v_a_4201_){
_start:
{
lean_object* v___x_4203_; lean_object* v___x_4204_; uint8_t v___x_4205_; 
v___x_4203_ = lean_unsigned_to_nat(0u);
v___x_4204_ = lean_array_get_size(v_ps_4194_);
v___x_4205_ = lean_nat_dec_lt(v___x_4203_, v___x_4204_);
if (v___x_4205_ == 0)
{
lean_object* v___x_4206_; 
v___x_4206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4206_, 0, v_k_4195_);
return v___x_4206_;
}
else
{
uint8_t v___x_4207_; 
v___x_4207_ = lean_nat_dec_le(v___x_4204_, v___x_4204_);
if (v___x_4207_ == 0)
{
if (v___x_4205_ == 0)
{
lean_object* v___x_4208_; 
v___x_4208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4208_, 0, v_k_4195_);
return v___x_4208_;
}
else
{
size_t v___x_4209_; size_t v___x_4210_; lean_object* v___x_4211_; 
v___x_4209_ = ((size_t)0ULL);
v___x_4210_ = lean_usize_of_nat(v___x_4204_);
v___x_4211_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0(v_ps_4194_, v___x_4209_, v___x_4210_, v_k_4195_, v_a_4196_, v_a_4197_, v_a_4198_, v_a_4199_, v_a_4200_, v_a_4201_);
return v___x_4211_;
}
}
else
{
size_t v___x_4212_; size_t v___x_4213_; lean_object* v___x_4214_; 
v___x_4212_ = ((size_t)0ULL);
v___x_4213_ = lean_usize_of_nat(v___x_4204_);
v___x_4214_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0(v_ps_4194_, v___x_4212_, v___x_4213_, v_k_4195_, v_a_4196_, v_a_4197_, v_a_4198_, v_a_4199_, v_a_4200_, v_a_4201_);
return v___x_4214_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams___boxed(lean_object* v_ps_4215_, lean_object* v_k_4216_, lean_object* v_a_4217_, lean_object* v_a_4218_, lean_object* v_a_4219_, lean_object* v_a_4220_, lean_object* v_a_4221_, lean_object* v_a_4222_, lean_object* v_a_4223_){
_start:
{
lean_object* v_res_4224_; 
v_res_4224_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams(v_ps_4215_, v_k_4216_, v_a_4217_, v_a_4218_, v_a_4219_, v_a_4220_, v_a_4221_, v_a_4222_);
lean_dec(v_a_4222_);
lean_dec_ref(v_a_4221_);
lean_dec(v_a_4220_);
lean_dec_ref(v_a_4219_);
lean_dec(v_a_4218_);
lean_dec_ref(v_a_4217_);
lean_dec_ref(v_ps_4215_);
return v_res_4224_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__0___closed__0(void){
_start:
{
uint8_t v___x_4225_; lean_object* v___x_4226_; 
v___x_4225_ = 1;
v___x_4226_ = l_Lean_Compiler_LCNF_instInhabitedCode_default__1(v___x_4225_);
return v___x_4226_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__0(lean_object* v_msg_4227_){
_start:
{
lean_object* v___x_4228_; lean_object* v___x_4229_; 
v___x_4228_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__0___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__0___closed__0);
v___x_4229_ = lean_panic_fn(v___x_4228_, v_msg_4227_);
return v___x_4229_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__1___closed__0(void){
_start:
{
uint8_t v___x_4230_; lean_object* v___x_4231_; 
v___x_4230_ = 1;
v___x_4231_ = l_Lean_Compiler_LCNF_instInhabitedSignature_default(v___x_4230_);
return v___x_4231_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__1(lean_object* v_msg_4232_){
_start:
{
lean_object* v___x_4233_; lean_object* v___x_4234_; 
v___x_4233_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__1___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__1___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__1___closed__0);
v___x_4234_ = lean_panic_fn(v___x_4233_, v_msg_4232_);
return v___x_4234_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__2(lean_object* v_msg_4235_, lean_object* v___y_4236_, lean_object* v___y_4237_, lean_object* v___y_4238_, lean_object* v___y_4239_, lean_object* v___y_4240_, lean_object* v___y_4241_){
_start:
{
lean_object* v___x_4243_; lean_object* v___x_4244_; lean_object* v_toApplicative_4245_; lean_object* v___x_4247_; uint8_t v_isShared_4248_; uint8_t v_isSharedCheck_4308_; 
v___x_4243_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__7___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__7___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__7___closed__0);
v___x_4244_ = l_StateRefT_x27_instMonad___redArg(v___x_4243_);
v_toApplicative_4245_ = lean_ctor_get(v___x_4244_, 0);
v_isSharedCheck_4308_ = !lean_is_exclusive(v___x_4244_);
if (v_isSharedCheck_4308_ == 0)
{
lean_object* v_unused_4309_; 
v_unused_4309_ = lean_ctor_get(v___x_4244_, 1);
lean_dec(v_unused_4309_);
v___x_4247_ = v___x_4244_;
v_isShared_4248_ = v_isSharedCheck_4308_;
goto v_resetjp_4246_;
}
else
{
lean_inc(v_toApplicative_4245_);
lean_dec(v___x_4244_);
v___x_4247_ = lean_box(0);
v_isShared_4248_ = v_isSharedCheck_4308_;
goto v_resetjp_4246_;
}
v_resetjp_4246_:
{
lean_object* v_toFunctor_4249_; lean_object* v_toSeq_4250_; lean_object* v_toSeqLeft_4251_; lean_object* v_toSeqRight_4252_; lean_object* v___x_4254_; uint8_t v_isShared_4255_; uint8_t v_isSharedCheck_4306_; 
v_toFunctor_4249_ = lean_ctor_get(v_toApplicative_4245_, 0);
v_toSeq_4250_ = lean_ctor_get(v_toApplicative_4245_, 2);
v_toSeqLeft_4251_ = lean_ctor_get(v_toApplicative_4245_, 3);
v_toSeqRight_4252_ = lean_ctor_get(v_toApplicative_4245_, 4);
v_isSharedCheck_4306_ = !lean_is_exclusive(v_toApplicative_4245_);
if (v_isSharedCheck_4306_ == 0)
{
lean_object* v_unused_4307_; 
v_unused_4307_ = lean_ctor_get(v_toApplicative_4245_, 1);
lean_dec(v_unused_4307_);
v___x_4254_ = v_toApplicative_4245_;
v_isShared_4255_ = v_isSharedCheck_4306_;
goto v_resetjp_4253_;
}
else
{
lean_inc(v_toSeqRight_4252_);
lean_inc(v_toSeqLeft_4251_);
lean_inc(v_toSeq_4250_);
lean_inc(v_toFunctor_4249_);
lean_dec(v_toApplicative_4245_);
v___x_4254_ = lean_box(0);
v_isShared_4255_ = v_isSharedCheck_4306_;
goto v_resetjp_4253_;
}
v_resetjp_4253_:
{
lean_object* v___f_4256_; lean_object* v___f_4257_; lean_object* v___f_4258_; lean_object* v___f_4259_; lean_object* v___x_4260_; lean_object* v___f_4261_; lean_object* v___f_4262_; lean_object* v___f_4263_; lean_object* v___x_4265_; 
v___f_4256_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__7___closed__1));
v___f_4257_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__7___closed__2));
lean_inc_ref(v_toFunctor_4249_);
v___f_4258_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4258_, 0, v_toFunctor_4249_);
v___f_4259_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4259_, 0, v_toFunctor_4249_);
v___x_4260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4260_, 0, v___f_4258_);
lean_ctor_set(v___x_4260_, 1, v___f_4259_);
v___f_4261_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4261_, 0, v_toSeqRight_4252_);
v___f_4262_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4262_, 0, v_toSeqLeft_4251_);
v___f_4263_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4263_, 0, v_toSeq_4250_);
if (v_isShared_4255_ == 0)
{
lean_ctor_set(v___x_4254_, 4, v___f_4261_);
lean_ctor_set(v___x_4254_, 3, v___f_4262_);
lean_ctor_set(v___x_4254_, 2, v___f_4263_);
lean_ctor_set(v___x_4254_, 1, v___f_4256_);
lean_ctor_set(v___x_4254_, 0, v___x_4260_);
v___x_4265_ = v___x_4254_;
goto v_reusejp_4264_;
}
else
{
lean_object* v_reuseFailAlloc_4305_; 
v_reuseFailAlloc_4305_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4305_, 0, v___x_4260_);
lean_ctor_set(v_reuseFailAlloc_4305_, 1, v___f_4256_);
lean_ctor_set(v_reuseFailAlloc_4305_, 2, v___f_4263_);
lean_ctor_set(v_reuseFailAlloc_4305_, 3, v___f_4262_);
lean_ctor_set(v_reuseFailAlloc_4305_, 4, v___f_4261_);
v___x_4265_ = v_reuseFailAlloc_4305_;
goto v_reusejp_4264_;
}
v_reusejp_4264_:
{
lean_object* v___x_4267_; 
if (v_isShared_4248_ == 0)
{
lean_ctor_set(v___x_4247_, 1, v___f_4257_);
lean_ctor_set(v___x_4247_, 0, v___x_4265_);
v___x_4267_ = v___x_4247_;
goto v_reusejp_4266_;
}
else
{
lean_object* v_reuseFailAlloc_4304_; 
v_reuseFailAlloc_4304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4304_, 0, v___x_4265_);
lean_ctor_set(v_reuseFailAlloc_4304_, 1, v___f_4257_);
v___x_4267_ = v_reuseFailAlloc_4304_;
goto v_reusejp_4266_;
}
v_reusejp_4266_:
{
lean_object* v___x_4268_; lean_object* v_toApplicative_4269_; lean_object* v___x_4271_; uint8_t v_isShared_4272_; uint8_t v_isSharedCheck_4302_; 
v___x_4268_ = l_StateRefT_x27_instMonad___redArg(v___x_4267_);
v_toApplicative_4269_ = lean_ctor_get(v___x_4268_, 0);
v_isSharedCheck_4302_ = !lean_is_exclusive(v___x_4268_);
if (v_isSharedCheck_4302_ == 0)
{
lean_object* v_unused_4303_; 
v_unused_4303_ = lean_ctor_get(v___x_4268_, 1);
lean_dec(v_unused_4303_);
v___x_4271_ = v___x_4268_;
v_isShared_4272_ = v_isSharedCheck_4302_;
goto v_resetjp_4270_;
}
else
{
lean_inc(v_toApplicative_4269_);
lean_dec(v___x_4268_);
v___x_4271_ = lean_box(0);
v_isShared_4272_ = v_isSharedCheck_4302_;
goto v_resetjp_4270_;
}
v_resetjp_4270_:
{
lean_object* v_toFunctor_4273_; lean_object* v_toSeq_4274_; lean_object* v_toSeqLeft_4275_; lean_object* v_toSeqRight_4276_; lean_object* v___x_4278_; uint8_t v_isShared_4279_; uint8_t v_isSharedCheck_4300_; 
v_toFunctor_4273_ = lean_ctor_get(v_toApplicative_4269_, 0);
v_toSeq_4274_ = lean_ctor_get(v_toApplicative_4269_, 2);
v_toSeqLeft_4275_ = lean_ctor_get(v_toApplicative_4269_, 3);
v_toSeqRight_4276_ = lean_ctor_get(v_toApplicative_4269_, 4);
v_isSharedCheck_4300_ = !lean_is_exclusive(v_toApplicative_4269_);
if (v_isSharedCheck_4300_ == 0)
{
lean_object* v_unused_4301_; 
v_unused_4301_ = lean_ctor_get(v_toApplicative_4269_, 1);
lean_dec(v_unused_4301_);
v___x_4278_ = v_toApplicative_4269_;
v_isShared_4279_ = v_isSharedCheck_4300_;
goto v_resetjp_4277_;
}
else
{
lean_inc(v_toSeqRight_4276_);
lean_inc(v_toSeqLeft_4275_);
lean_inc(v_toSeq_4274_);
lean_inc(v_toFunctor_4273_);
lean_dec(v_toApplicative_4269_);
v___x_4278_ = lean_box(0);
v_isShared_4279_ = v_isSharedCheck_4300_;
goto v_resetjp_4277_;
}
v_resetjp_4277_:
{
lean_object* v___f_4280_; lean_object* v___f_4281_; lean_object* v___f_4282_; lean_object* v___f_4283_; lean_object* v___x_4284_; lean_object* v___f_4285_; lean_object* v___f_4286_; lean_object* v___f_4287_; lean_object* v___x_4289_; 
v___f_4280_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__7___closed__3));
v___f_4281_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__7___closed__4));
lean_inc_ref(v_toFunctor_4273_);
v___f_4282_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4282_, 0, v_toFunctor_4273_);
v___f_4283_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4283_, 0, v_toFunctor_4273_);
v___x_4284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4284_, 0, v___f_4282_);
lean_ctor_set(v___x_4284_, 1, v___f_4283_);
v___f_4285_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4285_, 0, v_toSeqRight_4276_);
v___f_4286_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4286_, 0, v_toSeqLeft_4275_);
v___f_4287_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4287_, 0, v_toSeq_4274_);
if (v_isShared_4279_ == 0)
{
lean_ctor_set(v___x_4278_, 4, v___f_4285_);
lean_ctor_set(v___x_4278_, 3, v___f_4286_);
lean_ctor_set(v___x_4278_, 2, v___f_4287_);
lean_ctor_set(v___x_4278_, 1, v___f_4280_);
lean_ctor_set(v___x_4278_, 0, v___x_4284_);
v___x_4289_ = v___x_4278_;
goto v_reusejp_4288_;
}
else
{
lean_object* v_reuseFailAlloc_4299_; 
v_reuseFailAlloc_4299_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4299_, 0, v___x_4284_);
lean_ctor_set(v_reuseFailAlloc_4299_, 1, v___f_4280_);
lean_ctor_set(v_reuseFailAlloc_4299_, 2, v___f_4287_);
lean_ctor_set(v_reuseFailAlloc_4299_, 3, v___f_4286_);
lean_ctor_set(v_reuseFailAlloc_4299_, 4, v___f_4285_);
v___x_4289_ = v_reuseFailAlloc_4299_;
goto v_reusejp_4288_;
}
v_reusejp_4288_:
{
lean_object* v___x_4291_; 
if (v_isShared_4272_ == 0)
{
lean_ctor_set(v___x_4271_, 1, v___f_4281_);
lean_ctor_set(v___x_4271_, 0, v___x_4289_);
v___x_4291_ = v___x_4271_;
goto v_reusejp_4290_;
}
else
{
lean_object* v_reuseFailAlloc_4298_; 
v_reuseFailAlloc_4298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4298_, 0, v___x_4289_);
lean_ctor_set(v_reuseFailAlloc_4298_, 1, v___f_4281_);
v___x_4291_ = v_reuseFailAlloc_4298_;
goto v_reusejp_4290_;
}
v_reusejp_4290_:
{
lean_object* v___x_4292_; lean_object* v___x_4293_; lean_object* v___x_4294_; lean_object* v___f_4295_; lean_object* v___x_20083__overap_4296_; lean_object* v___x_4297_; 
v___x_4292_ = l_StateRefT_x27_instMonad___redArg(v___x_4291_);
v___x_4293_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__0___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__0___closed__0);
v___x_4294_ = l_instInhabitedOfMonad___redArg(v___x_4292_, v___x_4293_);
v___f_4295_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4295_, 0, v___x_4294_);
v___x_20083__overap_4296_ = lean_panic_fn(v___f_4295_, v_msg_4235_);
lean_inc(v___y_4241_);
lean_inc_ref(v___y_4240_);
lean_inc(v___y_4239_);
lean_inc_ref(v___y_4238_);
lean_inc(v___y_4237_);
lean_inc_ref(v___y_4236_);
v___x_4297_ = lean_apply_7(v___x_20083__overap_4296_, v___y_4236_, v___y_4237_, v___y_4238_, v___y_4239_, v___y_4240_, v___y_4241_, lean_box(0));
return v___x_4297_;
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__2___boxed(lean_object* v_msg_4310_, lean_object* v___y_4311_, lean_object* v___y_4312_, lean_object* v___y_4313_, lean_object* v___y_4314_, lean_object* v___y_4315_, lean_object* v___y_4316_, lean_object* v___y_4317_){
_start:
{
lean_object* v_res_4318_; 
v_res_4318_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__2(v_msg_4310_, v___y_4311_, v___y_4312_, v___y_4313_, v___y_4314_, v___y_4315_, v___y_4316_);
lean_dec(v___y_4316_);
lean_dec_ref(v___y_4315_);
lean_dec(v___y_4314_);
lean_dec_ref(v___y_4313_);
lean_dec(v___y_4312_);
lean_dec_ref(v___y_4311_);
return v_res_4318_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2(void){
_start:
{
lean_object* v___x_4321_; lean_object* v___x_4322_; lean_object* v___x_4323_; lean_object* v___x_4324_; lean_object* v___x_4325_; lean_object* v___x_4326_; 
v___x_4321_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode___closed__6));
v___x_4322_ = lean_unsigned_to_nat(9u);
v___x_4323_ = lean_unsigned_to_nat(611u);
v___x_4324_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__1));
v___x_4325_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__0));
v___x_4326_ = l_mkPanicMessageWithDecl(v___x_4325_, v___x_4324_, v___x_4323_, v___x_4322_, v___x_4321_);
return v___x_4326_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__10(void){
_start:
{
lean_object* v___x_4336_; lean_object* v___x_4337_; lean_object* v___x_4338_; lean_object* v___x_4339_; lean_object* v___x_4340_; lean_object* v___x_4341_; 
v___x_4336_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__9));
v___x_4337_ = lean_unsigned_to_nat(14u);
v___x_4338_ = lean_unsigned_to_nat(22u);
v___x_4339_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__8));
v___x_4340_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__7));
v___x_4341_ = l_mkPanicMessageWithDecl(v___x_4340_, v___x_4339_, v___x_4338_, v___x_4337_, v___x_4336_);
return v___x_4341_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__12(void){
_start:
{
lean_object* v___x_4343_; lean_object* v___x_4344_; lean_object* v___x_4345_; lean_object* v___x_4346_; lean_object* v___x_4347_; lean_object* v___x_4348_; 
v___x_4343_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode___closed__6));
v___x_4344_ = lean_unsigned_to_nat(22u);
v___x_4345_ = lean_unsigned_to_nat(586u);
v___x_4346_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__11));
v___x_4347_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode___closed__4));
v___x_4348_ = l_mkPanicMessageWithDecl(v___x_4347_, v___x_4346_, v___x_4345_, v___x_4344_, v___x_4343_);
return v___x_4348_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc(lean_object* v_code_4349_, lean_object* v_decl_4350_, lean_object* v_k_4351_, lean_object* v_a_4352_, lean_object* v_a_4353_, lean_object* v_a_4354_, lean_object* v_a_4355_, lean_object* v_a_4356_, lean_object* v_a_4357_){
_start:
{
lean_object* v_fvarId_4359_; lean_object* v_value_4360_; lean_object* v_k_4362_; lean_object* v___y_4363_; lean_object* v___y_4364_; lean_object* v___y_4365_; lean_object* v___y_4366_; lean_object* v___y_4367_; lean_object* v___y_4368_; lean_object* v___y_4400_; lean_object* v___y_4401_; lean_object* v___y_4402_; lean_object* v___y_4403_; lean_object* v___y_4404_; lean_object* v___y_4405_; lean_object* v___y_4406_; uint8_t v___y_4407_; lean_object* v_k_4410_; lean_object* v___y_4411_; lean_object* v___y_4412_; lean_object* v___y_4413_; lean_object* v___y_4414_; lean_object* v___y_4415_; lean_object* v___y_4416_; lean_object* v___x_4427_; 
v_fvarId_4359_ = lean_ctor_get(v_decl_4350_, 0);
lean_inc(v_fvarId_4359_);
v_value_4360_ = lean_ctor_get(v_decl_4350_, 3);
lean_inc(v_value_4360_);
lean_inc(v_fvarId_4359_);
v___x_4427_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecIfNeeded___redArg(v_fvarId_4359_, v_k_4351_, v_a_4352_, v_a_4353_);
switch(lean_obj_tag(v_value_4360_))
{
case 4:
{
lean_object* v_a_4428_; lean_object* v___x_4430_; uint8_t v_isShared_4431_; uint8_t v_isSharedCheck_4455_; 
v_a_4428_ = lean_ctor_get(v___x_4427_, 0);
v_isSharedCheck_4455_ = !lean_is_exclusive(v___x_4427_);
if (v_isSharedCheck_4455_ == 0)
{
v___x_4430_ = v___x_4427_;
v_isShared_4431_ = v_isSharedCheck_4455_;
goto v_resetjp_4429_;
}
else
{
lean_inc(v_a_4428_);
lean_dec(v___x_4427_);
v___x_4430_ = lean_box(0);
v_isShared_4431_ = v_isSharedCheck_4455_;
goto v_resetjp_4429_;
}
v_resetjp_4429_:
{
lean_object* v_fvarId_4432_; lean_object* v_args_4433_; lean_object* v___x_4435_; 
v_fvarId_4432_ = lean_ctor_get(v_value_4360_, 0);
v_args_4433_ = lean_ctor_get(v_value_4360_, 1);
lean_inc(v_fvarId_4432_);
if (v_isShared_4431_ == 0)
{
lean_ctor_set_tag(v___x_4430_, 1);
lean_ctor_set(v___x_4430_, 0, v_fvarId_4432_);
v___x_4435_ = v___x_4430_;
goto v_reusejp_4434_;
}
else
{
lean_object* v_reuseFailAlloc_4454_; 
v_reuseFailAlloc_4454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4454_, 0, v_fvarId_4432_);
v___x_4435_ = v_reuseFailAlloc_4454_;
goto v_reusejp_4434_;
}
v_reusejp_4434_:
{
lean_object* v___x_4436_; lean_object* v___y_4438_; uint8_t v___y_4442_; 
lean_inc_ref(v_args_4433_);
v___x_4436_ = lean_array_push(v_args_4433_, v___x_4435_);
if (lean_obj_tag(v_code_4349_) == 0)
{
lean_object* v_decl_4444_; lean_object* v_k_4445_; size_t v___x_4446_; size_t v___x_4447_; uint8_t v___x_4448_; 
v_decl_4444_ = lean_ctor_get(v_code_4349_, 0);
v_k_4445_ = lean_ctor_get(v_code_4349_, 1);
v___x_4446_ = lean_ptr_addr(v_k_4445_);
v___x_4447_ = lean_ptr_addr(v_a_4428_);
v___x_4448_ = lean_usize_dec_eq(v___x_4446_, v___x_4447_);
if (v___x_4448_ == 0)
{
v___y_4442_ = v___x_4448_;
goto v___jp_4441_;
}
else
{
size_t v___x_4449_; size_t v___x_4450_; uint8_t v___x_4451_; 
v___x_4449_ = lean_ptr_addr(v_decl_4444_);
v___x_4450_ = lean_ptr_addr(v_decl_4350_);
v___x_4451_ = lean_usize_dec_eq(v___x_4449_, v___x_4450_);
v___y_4442_ = v___x_4451_;
goto v___jp_4441_;
}
}
else
{
lean_object* v___x_4452_; lean_object* v___x_4453_; 
lean_dec(v_a_4428_);
lean_dec_ref(v_decl_4350_);
lean_dec_ref(v_code_4349_);
v___x_4452_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2);
v___x_4453_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__0(v___x_4452_);
v___y_4438_ = v___x_4453_;
goto v___jp_4437_;
}
v___jp_4437_:
{
lean_object* v___x_4439_; 
v___x_4439_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeConsumeAll(v___x_4436_, v___y_4438_, v_a_4352_, v_a_4353_, v_a_4354_, v_a_4355_, v_a_4356_, v_a_4357_);
lean_dec_ref(v___x_4436_);
if (lean_obj_tag(v___x_4439_) == 0)
{
lean_object* v_a_4440_; 
v_a_4440_ = lean_ctor_get(v___x_4439_, 0);
lean_inc(v_a_4440_);
lean_dec_ref(v___x_4439_);
v_k_4362_ = v_a_4440_;
v___y_4363_ = v_a_4352_;
v___y_4364_ = v_a_4353_;
v___y_4365_ = v_a_4354_;
v___y_4366_ = v_a_4355_;
v___y_4367_ = v_a_4356_;
v___y_4368_ = v_a_4357_;
goto v___jp_4361_;
}
else
{
lean_dec_ref(v_value_4360_);
lean_dec(v_fvarId_4359_);
return v___x_4439_;
}
}
v___jp_4441_:
{
if (v___y_4442_ == 0)
{
lean_object* v___x_4443_; 
lean_dec_ref(v_code_4349_);
v___x_4443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4443_, 0, v_decl_4350_);
lean_ctor_set(v___x_4443_, 1, v_a_4428_);
v___y_4438_ = v___x_4443_;
goto v___jp_4437_;
}
else
{
lean_dec(v_a_4428_);
lean_dec_ref(v_decl_4350_);
v___y_4438_ = v_code_4349_;
goto v___jp_4437_;
}
}
}
}
}
case 5:
{
lean_object* v_a_4456_; lean_object* v_args_4457_; lean_object* v___x_4458_; 
v_a_4456_ = lean_ctor_get(v___x_4427_, 0);
lean_inc(v_a_4456_);
lean_dec_ref(v___x_4427_);
v_args_4457_ = lean_ctor_get(v_value_4360_, 1);
lean_inc_ref(v_decl_4350_);
v___x_4458_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_ensureNoBorrow(v_decl_4350_, v_a_4352_, v_a_4353_, v_a_4354_, v_a_4355_, v_a_4356_, v_a_4357_);
if (lean_obj_tag(v___x_4458_) == 0)
{
lean_object* v___y_4460_; uint8_t v___y_4464_; 
lean_dec_ref(v___x_4458_);
if (lean_obj_tag(v_code_4349_) == 0)
{
lean_object* v_decl_4466_; lean_object* v_k_4467_; size_t v___x_4468_; size_t v___x_4469_; uint8_t v___x_4470_; 
v_decl_4466_ = lean_ctor_get(v_code_4349_, 0);
v_k_4467_ = lean_ctor_get(v_code_4349_, 1);
v___x_4468_ = lean_ptr_addr(v_k_4467_);
v___x_4469_ = lean_ptr_addr(v_a_4456_);
v___x_4470_ = lean_usize_dec_eq(v___x_4468_, v___x_4469_);
if (v___x_4470_ == 0)
{
v___y_4464_ = v___x_4470_;
goto v___jp_4463_;
}
else
{
size_t v___x_4471_; size_t v___x_4472_; uint8_t v___x_4473_; 
v___x_4471_ = lean_ptr_addr(v_decl_4466_);
v___x_4472_ = lean_ptr_addr(v_decl_4350_);
v___x_4473_ = lean_usize_dec_eq(v___x_4471_, v___x_4472_);
v___y_4464_ = v___x_4473_;
goto v___jp_4463_;
}
}
else
{
lean_object* v___x_4474_; lean_object* v___x_4475_; 
lean_dec(v_a_4456_);
lean_dec_ref(v_decl_4350_);
lean_dec_ref(v_code_4349_);
v___x_4474_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2);
v___x_4475_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__0(v___x_4474_);
v___y_4460_ = v___x_4475_;
goto v___jp_4459_;
}
v___jp_4459_:
{
lean_object* v___x_4461_; 
v___x_4461_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeConsumeAll(v_args_4457_, v___y_4460_, v_a_4352_, v_a_4353_, v_a_4354_, v_a_4355_, v_a_4356_, v_a_4357_);
if (lean_obj_tag(v___x_4461_) == 0)
{
lean_object* v_a_4462_; 
v_a_4462_ = lean_ctor_get(v___x_4461_, 0);
lean_inc(v_a_4462_);
lean_dec_ref(v___x_4461_);
v_k_4362_ = v_a_4462_;
v___y_4363_ = v_a_4352_;
v___y_4364_ = v_a_4353_;
v___y_4365_ = v_a_4354_;
v___y_4366_ = v_a_4355_;
v___y_4367_ = v_a_4356_;
v___y_4368_ = v_a_4357_;
goto v___jp_4361_;
}
else
{
lean_dec_ref(v_value_4360_);
lean_dec(v_fvarId_4359_);
return v___x_4461_;
}
}
v___jp_4463_:
{
if (v___y_4464_ == 0)
{
lean_object* v___x_4465_; 
lean_dec_ref(v_code_4349_);
v___x_4465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4465_, 0, v_decl_4350_);
lean_ctor_set(v___x_4465_, 1, v_a_4456_);
v___y_4460_ = v___x_4465_;
goto v___jp_4459_;
}
else
{
lean_dec(v_a_4456_);
lean_dec_ref(v_decl_4350_);
v___y_4460_ = v_code_4349_;
goto v___jp_4459_;
}
}
}
else
{
lean_object* v_a_4476_; lean_object* v___x_4478_; uint8_t v_isShared_4479_; uint8_t v_isSharedCheck_4483_; 
lean_dec_ref(v_value_4360_);
lean_dec(v_a_4456_);
lean_dec(v_fvarId_4359_);
lean_dec_ref(v_decl_4350_);
lean_dec_ref(v_code_4349_);
v_a_4476_ = lean_ctor_get(v___x_4458_, 0);
v_isSharedCheck_4483_ = !lean_is_exclusive(v___x_4458_);
if (v_isSharedCheck_4483_ == 0)
{
v___x_4478_ = v___x_4458_;
v_isShared_4479_ = v_isSharedCheck_4483_;
goto v_resetjp_4477_;
}
else
{
lean_inc(v_a_4476_);
lean_dec(v___x_4458_);
v___x_4478_ = lean_box(0);
v_isShared_4479_ = v_isSharedCheck_4483_;
goto v_resetjp_4477_;
}
v_resetjp_4477_:
{
lean_object* v___x_4481_; 
if (v_isShared_4479_ == 0)
{
v___x_4481_ = v___x_4478_;
goto v_reusejp_4480_;
}
else
{
lean_object* v_reuseFailAlloc_4482_; 
v_reuseFailAlloc_4482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4482_, 0, v_a_4476_);
v___x_4481_ = v_reuseFailAlloc_4482_;
goto v_reusejp_4480_;
}
v_reusejp_4480_:
{
return v___x_4481_;
}
}
}
}
case 6:
{
lean_object* v_a_4484_; lean_object* v_var_4485_; lean_object* v___x_4486_; lean_object* v_a_4487_; lean_object* v___x_4488_; lean_object* v_borrows_4489_; uint8_t v___x_4490_; 
v_a_4484_ = lean_ctor_get(v___x_4427_, 0);
lean_inc(v_a_4484_);
lean_dec_ref(v___x_4427_);
v_var_4485_ = lean_ctor_get(v_value_4360_, 1);
lean_inc(v_var_4485_);
v___x_4486_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecIfNeeded___redArg(v_var_4485_, v_a_4484_, v_a_4352_, v_a_4353_);
v_a_4487_ = lean_ctor_get(v___x_4486_, 0);
lean_inc(v_a_4487_);
lean_dec_ref(v___x_4486_);
v___x_4488_ = lean_st_ref_get(v_a_4353_);
v_borrows_4489_ = lean_ctor_get(v___x_4488_, 1);
lean_inc_ref(v_borrows_4489_);
lean_dec(v___x_4488_);
v___x_4490_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_isAccessible_spec__0___redArg(v_borrows_4489_, v_fvarId_4359_);
lean_dec_ref(v_borrows_4489_);
if (v___x_4490_ == 0)
{
lean_object* v_varMap_4491_; lean_object* v___x_4492_; lean_object* v___x_4493_; uint8_t v_isDefiniteRef_4494_; lean_object* v___x_4495_; uint8_t v___y_4497_; 
v_varMap_4491_ = lean_ctor_get(v_a_4352_, 2);
v___x_4492_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_instInhabitedVarInfo_default));
v___x_4493_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__0___redArg(v___x_4492_, v_varMap_4491_, v_fvarId_4359_);
v_isDefiniteRef_4494_ = lean_ctor_get_uint8(v___x_4493_, sizeof(void*)*1 + 1);
v___x_4495_ = lean_unsigned_to_nat(1u);
if (v_isDefiniteRef_4494_ == 0)
{
uint8_t v___x_4500_; 
v___x_4500_ = 1;
v___y_4497_ = v___x_4500_;
goto v___jp_4496_;
}
else
{
v___y_4497_ = v___x_4490_;
goto v___jp_4496_;
}
v___jp_4496_:
{
uint8_t v_persistent_4498_; lean_object* v___x_4499_; 
v_persistent_4498_ = lean_ctor_get_uint8(v___x_4493_, sizeof(void*)*1 + 2);
lean_dec(v___x_4493_);
lean_inc(v_fvarId_4359_);
v___x_4499_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v___x_4499_, 0, v_fvarId_4359_);
lean_ctor_set(v___x_4499_, 1, v___x_4495_);
lean_ctor_set(v___x_4499_, 2, v_a_4487_);
lean_ctor_set_uint8(v___x_4499_, sizeof(void*)*3, v___y_4497_);
lean_ctor_set_uint8(v___x_4499_, sizeof(void*)*3 + 1, v_persistent_4498_);
v_k_4410_ = v___x_4499_;
v___y_4411_ = v_a_4352_;
v___y_4412_ = v_a_4353_;
v___y_4413_ = v_a_4354_;
v___y_4414_ = v_a_4355_;
v___y_4415_ = v_a_4356_;
v___y_4416_ = v_a_4357_;
goto v___jp_4409_;
}
}
else
{
v_k_4410_ = v_a_4487_;
v___y_4411_ = v_a_4352_;
v___y_4412_ = v_a_4353_;
v___y_4413_ = v_a_4354_;
v___y_4414_ = v_a_4355_;
v___y_4415_ = v_a_4356_;
v___y_4416_ = v_a_4357_;
goto v___jp_4409_;
}
}
case 7:
{
lean_object* v_a_4501_; lean_object* v_var_4502_; lean_object* v___x_4503_; lean_object* v_a_4504_; lean_object* v___x_4505_; 
v_a_4501_ = lean_ctor_get(v___x_4427_, 0);
lean_inc(v_a_4501_);
lean_dec_ref(v___x_4427_);
v_var_4502_ = lean_ctor_get(v_value_4360_, 1);
lean_inc(v_var_4502_);
v___x_4503_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecIfNeeded___redArg(v_var_4502_, v_a_4501_, v_a_4352_, v_a_4353_);
v_a_4504_ = lean_ctor_get(v___x_4503_, 0);
lean_inc(v_a_4504_);
lean_dec_ref(v___x_4503_);
lean_inc_ref(v_decl_4350_);
v___x_4505_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_ensureNoBorrow(v_decl_4350_, v_a_4352_, v_a_4353_, v_a_4354_, v_a_4355_, v_a_4356_, v_a_4357_);
if (lean_obj_tag(v___x_4505_) == 0)
{
uint8_t v___y_4507_; 
lean_dec_ref(v___x_4505_);
if (lean_obj_tag(v_code_4349_) == 0)
{
lean_object* v_decl_4509_; lean_object* v_k_4510_; size_t v___x_4511_; size_t v___x_4512_; uint8_t v___x_4513_; 
v_decl_4509_ = lean_ctor_get(v_code_4349_, 0);
v_k_4510_ = lean_ctor_get(v_code_4349_, 1);
v___x_4511_ = lean_ptr_addr(v_k_4510_);
v___x_4512_ = lean_ptr_addr(v_a_4504_);
v___x_4513_ = lean_usize_dec_eq(v___x_4511_, v___x_4512_);
if (v___x_4513_ == 0)
{
v___y_4507_ = v___x_4513_;
goto v___jp_4506_;
}
else
{
size_t v___x_4514_; size_t v___x_4515_; uint8_t v___x_4516_; 
v___x_4514_ = lean_ptr_addr(v_decl_4509_);
v___x_4515_ = lean_ptr_addr(v_decl_4350_);
v___x_4516_ = lean_usize_dec_eq(v___x_4514_, v___x_4515_);
v___y_4507_ = v___x_4516_;
goto v___jp_4506_;
}
}
else
{
lean_object* v___x_4517_; lean_object* v___x_4518_; 
lean_dec(v_a_4504_);
lean_dec_ref(v_decl_4350_);
lean_dec_ref(v_code_4349_);
v___x_4517_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2);
v___x_4518_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__0(v___x_4517_);
v_k_4362_ = v___x_4518_;
v___y_4363_ = v_a_4352_;
v___y_4364_ = v_a_4353_;
v___y_4365_ = v_a_4354_;
v___y_4366_ = v_a_4355_;
v___y_4367_ = v_a_4356_;
v___y_4368_ = v_a_4357_;
goto v___jp_4361_;
}
v___jp_4506_:
{
if (v___y_4507_ == 0)
{
lean_object* v___x_4508_; 
lean_dec_ref(v_code_4349_);
v___x_4508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4508_, 0, v_decl_4350_);
lean_ctor_set(v___x_4508_, 1, v_a_4504_);
v_k_4362_ = v___x_4508_;
v___y_4363_ = v_a_4352_;
v___y_4364_ = v_a_4353_;
v___y_4365_ = v_a_4354_;
v___y_4366_ = v_a_4355_;
v___y_4367_ = v_a_4356_;
v___y_4368_ = v_a_4357_;
goto v___jp_4361_;
}
else
{
lean_dec(v_a_4504_);
lean_dec_ref(v_decl_4350_);
v_k_4362_ = v_code_4349_;
v___y_4363_ = v_a_4352_;
v___y_4364_ = v_a_4353_;
v___y_4365_ = v_a_4354_;
v___y_4366_ = v_a_4355_;
v___y_4367_ = v_a_4356_;
v___y_4368_ = v_a_4357_;
goto v___jp_4361_;
}
}
}
else
{
lean_object* v_a_4519_; lean_object* v___x_4521_; uint8_t v_isShared_4522_; uint8_t v_isSharedCheck_4526_; 
lean_dec(v_a_4504_);
lean_dec_ref(v_value_4360_);
lean_dec(v_fvarId_4359_);
lean_dec_ref(v_decl_4350_);
lean_dec_ref(v_code_4349_);
v_a_4519_ = lean_ctor_get(v___x_4505_, 0);
v_isSharedCheck_4526_ = !lean_is_exclusive(v___x_4505_);
if (v_isSharedCheck_4526_ == 0)
{
v___x_4521_ = v___x_4505_;
v_isShared_4522_ = v_isSharedCheck_4526_;
goto v_resetjp_4520_;
}
else
{
lean_inc(v_a_4519_);
lean_dec(v___x_4505_);
v___x_4521_ = lean_box(0);
v_isShared_4522_ = v_isSharedCheck_4526_;
goto v_resetjp_4520_;
}
v_resetjp_4520_:
{
lean_object* v___x_4524_; 
if (v_isShared_4522_ == 0)
{
v___x_4524_ = v___x_4521_;
goto v_reusejp_4523_;
}
else
{
lean_object* v_reuseFailAlloc_4525_; 
v_reuseFailAlloc_4525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4525_, 0, v_a_4519_);
v___x_4524_ = v_reuseFailAlloc_4525_;
goto v_reusejp_4523_;
}
v_reusejp_4523_:
{
return v___x_4524_;
}
}
}
}
case 8:
{
lean_object* v_a_4527_; lean_object* v_var_4528_; lean_object* v___x_4529_; lean_object* v_a_4530_; lean_object* v___x_4531_; 
v_a_4527_ = lean_ctor_get(v___x_4427_, 0);
lean_inc(v_a_4527_);
lean_dec_ref(v___x_4427_);
v_var_4528_ = lean_ctor_get(v_value_4360_, 2);
lean_inc(v_var_4528_);
v___x_4529_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecIfNeeded___redArg(v_var_4528_, v_a_4527_, v_a_4352_, v_a_4353_);
v_a_4530_ = lean_ctor_get(v___x_4529_, 0);
lean_inc(v_a_4530_);
lean_dec_ref(v___x_4529_);
lean_inc_ref(v_decl_4350_);
v___x_4531_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_ensureNoBorrow(v_decl_4350_, v_a_4352_, v_a_4353_, v_a_4354_, v_a_4355_, v_a_4356_, v_a_4357_);
if (lean_obj_tag(v___x_4531_) == 0)
{
uint8_t v___y_4533_; 
lean_dec_ref(v___x_4531_);
if (lean_obj_tag(v_code_4349_) == 0)
{
lean_object* v_decl_4535_; lean_object* v_k_4536_; size_t v___x_4537_; size_t v___x_4538_; uint8_t v___x_4539_; 
v_decl_4535_ = lean_ctor_get(v_code_4349_, 0);
v_k_4536_ = lean_ctor_get(v_code_4349_, 1);
v___x_4537_ = lean_ptr_addr(v_k_4536_);
v___x_4538_ = lean_ptr_addr(v_a_4530_);
v___x_4539_ = lean_usize_dec_eq(v___x_4537_, v___x_4538_);
if (v___x_4539_ == 0)
{
v___y_4533_ = v___x_4539_;
goto v___jp_4532_;
}
else
{
size_t v___x_4540_; size_t v___x_4541_; uint8_t v___x_4542_; 
v___x_4540_ = lean_ptr_addr(v_decl_4535_);
v___x_4541_ = lean_ptr_addr(v_decl_4350_);
v___x_4542_ = lean_usize_dec_eq(v___x_4540_, v___x_4541_);
v___y_4533_ = v___x_4542_;
goto v___jp_4532_;
}
}
else
{
lean_object* v___x_4543_; lean_object* v___x_4544_; 
lean_dec(v_a_4530_);
lean_dec_ref(v_decl_4350_);
lean_dec_ref(v_code_4349_);
v___x_4543_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2);
v___x_4544_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__0(v___x_4543_);
v_k_4362_ = v___x_4544_;
v___y_4363_ = v_a_4352_;
v___y_4364_ = v_a_4353_;
v___y_4365_ = v_a_4354_;
v___y_4366_ = v_a_4355_;
v___y_4367_ = v_a_4356_;
v___y_4368_ = v_a_4357_;
goto v___jp_4361_;
}
v___jp_4532_:
{
if (v___y_4533_ == 0)
{
lean_object* v___x_4534_; 
lean_dec_ref(v_code_4349_);
v___x_4534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4534_, 0, v_decl_4350_);
lean_ctor_set(v___x_4534_, 1, v_a_4530_);
v_k_4362_ = v___x_4534_;
v___y_4363_ = v_a_4352_;
v___y_4364_ = v_a_4353_;
v___y_4365_ = v_a_4354_;
v___y_4366_ = v_a_4355_;
v___y_4367_ = v_a_4356_;
v___y_4368_ = v_a_4357_;
goto v___jp_4361_;
}
else
{
lean_dec(v_a_4530_);
lean_dec_ref(v_decl_4350_);
v_k_4362_ = v_code_4349_;
v___y_4363_ = v_a_4352_;
v___y_4364_ = v_a_4353_;
v___y_4365_ = v_a_4354_;
v___y_4366_ = v_a_4355_;
v___y_4367_ = v_a_4356_;
v___y_4368_ = v_a_4357_;
goto v___jp_4361_;
}
}
}
else
{
lean_object* v_a_4545_; lean_object* v___x_4547_; uint8_t v_isShared_4548_; uint8_t v_isSharedCheck_4552_; 
lean_dec(v_a_4530_);
lean_dec_ref(v_value_4360_);
lean_dec(v_fvarId_4359_);
lean_dec_ref(v_decl_4350_);
lean_dec_ref(v_code_4349_);
v_a_4545_ = lean_ctor_get(v___x_4531_, 0);
v_isSharedCheck_4552_ = !lean_is_exclusive(v___x_4531_);
if (v_isSharedCheck_4552_ == 0)
{
v___x_4547_ = v___x_4531_;
v_isShared_4548_ = v_isSharedCheck_4552_;
goto v_resetjp_4546_;
}
else
{
lean_inc(v_a_4545_);
lean_dec(v___x_4531_);
v___x_4547_ = lean_box(0);
v_isShared_4548_ = v_isSharedCheck_4552_;
goto v_resetjp_4546_;
}
v_resetjp_4546_:
{
lean_object* v___x_4550_; 
if (v_isShared_4548_ == 0)
{
v___x_4550_ = v___x_4547_;
goto v_reusejp_4549_;
}
else
{
lean_object* v_reuseFailAlloc_4551_; 
v_reuseFailAlloc_4551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4551_, 0, v_a_4545_);
v___x_4550_ = v_reuseFailAlloc_4551_;
goto v_reusejp_4549_;
}
v_reusejp_4549_:
{
return v___x_4550_;
}
}
}
}
case 9:
{
lean_object* v_a_4553_; lean_object* v_fn_4554_; lean_object* v_args_4555_; lean_object* v___y_4557_; lean_object* v___y_4558_; lean_object* v___y_4559_; lean_object* v___y_4560_; lean_object* v___y_4561_; lean_object* v___y_4562_; lean_object* v___y_4563_; lean_object* v___y_4564_; lean_object* v___y_4568_; lean_object* v___y_4569_; lean_object* v___y_4570_; lean_object* v___y_4571_; lean_object* v___y_4572_; lean_object* v___y_4573_; lean_object* v___y_4574_; lean_object* v___y_4575_; lean_object* v___y_4576_; uint8_t v___y_4577_; lean_object* v___x_4579_; 
v_a_4553_ = lean_ctor_get(v___x_4427_, 0);
lean_inc(v_a_4553_);
lean_dec_ref(v___x_4427_);
v_fn_4554_ = lean_ctor_get(v_value_4360_, 0);
v_args_4555_ = lean_ctor_get(v_value_4360_, 1);
lean_inc(v_fn_4554_);
v___x_4579_ = l_Lean_Compiler_LCNF_getImpureSignature_x3f___redArg(v_fn_4554_, v_a_4357_);
if (lean_obj_tag(v___x_4579_) == 0)
{
lean_object* v_a_4580_; uint8_t v___x_4581_; lean_object* v___y_4583_; lean_object* v___y_4584_; lean_object* v_value_4585_; lean_object* v___y_4586_; lean_object* v___y_4587_; lean_object* v___y_4588_; lean_object* v___y_4589_; lean_object* v___y_4590_; lean_object* v___y_4591_; lean_object* v___y_4613_; lean_object* v___y_4614_; lean_object* v___y_4615_; uint8_t v___y_4616_; lean_object* v___y_4630_; uint8_t v___y_4631_; lean_object* v___y_4632_; lean_object* v___y_4633_; uint8_t v___y_4634_; uint8_t v___y_4642_; lean_object* v___y_4643_; uint8_t v___y_4644_; lean_object* v___y_4645_; lean_object* v___y_4646_; uint8_t v___y_4647_; lean_object* v___y_4655_; 
v_a_4580_ = lean_ctor_get(v___x_4579_, 0);
lean_inc(v_a_4580_);
lean_dec_ref(v___x_4579_);
v___x_4581_ = 1;
if (lean_obj_tag(v_a_4580_) == 0)
{
lean_object* v___x_4671_; lean_object* v___x_4672_; 
v___x_4671_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__10, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__10_once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__10);
v___x_4672_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__1(v___x_4671_);
v___y_4655_ = v___x_4672_;
goto v___jp_4654_;
}
else
{
lean_object* v_val_4673_; 
v_val_4673_ = lean_ctor_get(v_a_4580_, 0);
lean_inc(v_val_4673_);
lean_dec_ref(v_a_4580_);
v___y_4655_ = v_val_4673_;
goto v___jp_4654_;
}
v___jp_4582_:
{
lean_object* v___x_4592_; 
v___x_4592_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v___x_4581_, v_decl_4350_, v_value_4585_, v___y_4589_);
if (lean_obj_tag(v___x_4592_) == 0)
{
if (lean_obj_tag(v_code_4349_) == 0)
{
lean_object* v_a_4593_; lean_object* v_decl_4594_; lean_object* v_k_4595_; size_t v___x_4596_; size_t v___x_4597_; uint8_t v___x_4598_; 
v_a_4593_ = lean_ctor_get(v___x_4592_, 0);
lean_inc(v_a_4593_);
lean_dec_ref(v___x_4592_);
v_decl_4594_ = lean_ctor_get(v_code_4349_, 0);
v_k_4595_ = lean_ctor_get(v_code_4349_, 1);
v___x_4596_ = lean_ptr_addr(v_k_4595_);
v___x_4597_ = lean_ptr_addr(v___y_4583_);
v___x_4598_ = lean_usize_dec_eq(v___x_4596_, v___x_4597_);
if (v___x_4598_ == 0)
{
v___y_4568_ = v___y_4586_;
v___y_4569_ = v___y_4587_;
v___y_4570_ = v___y_4583_;
v___y_4571_ = v_a_4593_;
v___y_4572_ = v___y_4588_;
v___y_4573_ = v___y_4591_;
v___y_4574_ = v___y_4589_;
v___y_4575_ = v___y_4590_;
v___y_4576_ = v___y_4584_;
v___y_4577_ = v___x_4598_;
goto v___jp_4567_;
}
else
{
size_t v___x_4599_; size_t v___x_4600_; uint8_t v___x_4601_; 
v___x_4599_ = lean_ptr_addr(v_decl_4594_);
v___x_4600_ = lean_ptr_addr(v_a_4593_);
v___x_4601_ = lean_usize_dec_eq(v___x_4599_, v___x_4600_);
v___y_4568_ = v___y_4586_;
v___y_4569_ = v___y_4587_;
v___y_4570_ = v___y_4583_;
v___y_4571_ = v_a_4593_;
v___y_4572_ = v___y_4588_;
v___y_4573_ = v___y_4591_;
v___y_4574_ = v___y_4589_;
v___y_4575_ = v___y_4590_;
v___y_4576_ = v___y_4584_;
v___y_4577_ = v___x_4601_;
goto v___jp_4567_;
}
}
else
{
lean_object* v___x_4602_; lean_object* v___x_4603_; 
lean_dec_ref(v___x_4592_);
lean_dec_ref(v___y_4583_);
lean_dec_ref(v_code_4349_);
v___x_4602_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2);
v___x_4603_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__0(v___x_4602_);
v___y_4557_ = v___y_4587_;
v___y_4558_ = v___y_4586_;
v___y_4559_ = v___y_4591_;
v___y_4560_ = v___y_4588_;
v___y_4561_ = v___y_4589_;
v___y_4562_ = v___y_4590_;
v___y_4563_ = v___y_4584_;
v___y_4564_ = v___x_4603_;
goto v___jp_4556_;
}
}
else
{
lean_object* v_a_4604_; lean_object* v___x_4606_; uint8_t v_isShared_4607_; uint8_t v_isSharedCheck_4611_; 
lean_dec_ref(v___y_4584_);
lean_dec_ref(v___y_4583_);
lean_dec_ref(v_value_4360_);
lean_dec(v_fvarId_4359_);
lean_dec_ref(v_code_4349_);
v_a_4604_ = lean_ctor_get(v___x_4592_, 0);
v_isSharedCheck_4611_ = !lean_is_exclusive(v___x_4592_);
if (v_isSharedCheck_4611_ == 0)
{
v___x_4606_ = v___x_4592_;
v_isShared_4607_ = v_isSharedCheck_4611_;
goto v_resetjp_4605_;
}
else
{
lean_inc(v_a_4604_);
lean_dec(v___x_4592_);
v___x_4606_ = lean_box(0);
v_isShared_4607_ = v_isSharedCheck_4611_;
goto v_resetjp_4605_;
}
v_resetjp_4605_:
{
lean_object* v___x_4609_; 
if (v_isShared_4607_ == 0)
{
v___x_4609_ = v___x_4606_;
goto v_reusejp_4608_;
}
else
{
lean_object* v_reuseFailAlloc_4610_; 
v_reuseFailAlloc_4610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4610_, 0, v_a_4604_);
v___x_4609_ = v_reuseFailAlloc_4610_;
goto v_reusejp_4608_;
}
v_reusejp_4608_:
{
return v___x_4609_;
}
}
}
}
v___jp_4612_:
{
if (v___y_4616_ == 0)
{
lean_object* v___x_4617_; 
lean_dec_ref(v___y_4614_);
lean_inc_ref(v_decl_4350_);
v___x_4617_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_ensureNoBorrow(v_decl_4350_, v_a_4352_, v_a_4353_, v_a_4354_, v_a_4355_, v_a_4356_, v_a_4357_);
if (lean_obj_tag(v___x_4617_) == 0)
{
lean_dec_ref(v___x_4617_);
lean_inc_ref(v_value_4360_);
v___y_4583_ = v___y_4613_;
v___y_4584_ = v___y_4615_;
v_value_4585_ = v_value_4360_;
v___y_4586_ = v_a_4352_;
v___y_4587_ = v_a_4353_;
v___y_4588_ = v_a_4354_;
v___y_4589_ = v_a_4355_;
v___y_4590_ = v_a_4356_;
v___y_4591_ = v_a_4357_;
goto v___jp_4582_;
}
else
{
lean_object* v_a_4618_; lean_object* v___x_4620_; uint8_t v_isShared_4621_; uint8_t v_isSharedCheck_4625_; 
lean_dec_ref(v___y_4615_);
lean_dec_ref(v___y_4613_);
lean_dec_ref(v_value_4360_);
lean_dec(v_fvarId_4359_);
lean_dec_ref(v_decl_4350_);
lean_dec_ref(v_code_4349_);
v_a_4618_ = lean_ctor_get(v___x_4617_, 0);
v_isSharedCheck_4625_ = !lean_is_exclusive(v___x_4617_);
if (v_isSharedCheck_4625_ == 0)
{
v___x_4620_ = v___x_4617_;
v_isShared_4621_ = v_isSharedCheck_4625_;
goto v_resetjp_4619_;
}
else
{
lean_inc(v_a_4618_);
lean_dec(v___x_4617_);
v___x_4620_ = lean_box(0);
v_isShared_4621_ = v_isSharedCheck_4625_;
goto v_resetjp_4619_;
}
v_resetjp_4619_:
{
lean_object* v___x_4623_; 
if (v_isShared_4621_ == 0)
{
v___x_4623_ = v___x_4620_;
goto v_reusejp_4622_;
}
else
{
lean_object* v_reuseFailAlloc_4624_; 
v_reuseFailAlloc_4624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4624_, 0, v_a_4618_);
v___x_4623_ = v_reuseFailAlloc_4624_;
goto v_reusejp_4622_;
}
v_reusejp_4622_:
{
return v___x_4623_;
}
}
}
}
else
{
lean_object* v___x_4626_; lean_object* v___x_4627_; lean_object* v___x_4628_; 
v___x_4626_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__3));
v___x_4627_ = l_Lean_Name_mkStr2(v___y_4614_, v___x_4626_);
lean_inc_ref(v_args_4555_);
v___x_4628_ = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(v___x_4628_, 0, v___x_4627_);
lean_ctor_set(v___x_4628_, 1, v_args_4555_);
v___y_4583_ = v___y_4613_;
v___y_4584_ = v___y_4615_;
v_value_4585_ = v___x_4628_;
v___y_4586_ = v_a_4352_;
v___y_4587_ = v_a_4353_;
v___y_4588_ = v_a_4354_;
v___y_4589_ = v_a_4355_;
v___y_4590_ = v_a_4356_;
v___y_4591_ = v_a_4357_;
goto v___jp_4582_;
}
}
v___jp_4629_:
{
if (v___y_4634_ == 0)
{
lean_object* v___x_4635_; lean_object* v___x_4636_; uint8_t v___x_4637_; 
v___x_4635_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode___closed__3));
lean_inc_ref(v___y_4633_);
v___x_4636_ = l_Lean_Name_mkStr2(v___y_4633_, v___x_4635_);
v___x_4637_ = lean_name_eq(v_fn_4554_, v___x_4636_);
lean_dec(v___x_4636_);
if (v___x_4637_ == 0)
{
v___y_4613_ = v___y_4630_;
v___y_4614_ = v___y_4633_;
v___y_4615_ = v___y_4632_;
v___y_4616_ = v___x_4637_;
goto v___jp_4612_;
}
else
{
v___y_4613_ = v___y_4630_;
v___y_4614_ = v___y_4633_;
v___y_4615_ = v___y_4632_;
v___y_4616_ = v___y_4631_;
goto v___jp_4612_;
}
}
else
{
lean_object* v___x_4638_; lean_object* v___x_4639_; lean_object* v___x_4640_; 
v___x_4638_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__4));
v___x_4639_ = l_Lean_Name_mkStr2(v___y_4633_, v___x_4638_);
lean_inc_ref(v_args_4555_);
v___x_4640_ = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(v___x_4640_, 0, v___x_4639_);
lean_ctor_set(v___x_4640_, 1, v_args_4555_);
v___y_4583_ = v___y_4630_;
v___y_4584_ = v___y_4632_;
v_value_4585_ = v___x_4640_;
v___y_4586_ = v_a_4352_;
v___y_4587_ = v_a_4353_;
v___y_4588_ = v_a_4354_;
v___y_4589_ = v_a_4355_;
v___y_4590_ = v_a_4356_;
v___y_4591_ = v_a_4357_;
goto v___jp_4582_;
}
}
v___jp_4641_:
{
if (v___y_4647_ == 0)
{
lean_object* v___x_4648_; lean_object* v___x_4649_; uint8_t v___x_4650_; 
v___x_4648_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode___closed__2));
lean_inc_ref(v___y_4646_);
v___x_4649_ = l_Lean_Name_mkStr2(v___y_4646_, v___x_4648_);
v___x_4650_ = lean_name_eq(v_fn_4554_, v___x_4649_);
lean_dec(v___x_4649_);
if (v___x_4650_ == 0)
{
v___y_4630_ = v___y_4643_;
v___y_4631_ = v___y_4644_;
v___y_4632_ = v___y_4645_;
v___y_4633_ = v___y_4646_;
v___y_4634_ = v___x_4650_;
goto v___jp_4629_;
}
else
{
v___y_4630_ = v___y_4643_;
v___y_4631_ = v___y_4644_;
v___y_4632_ = v___y_4645_;
v___y_4633_ = v___y_4646_;
v___y_4634_ = v___y_4642_;
goto v___jp_4629_;
}
}
else
{
lean_object* v___x_4651_; lean_object* v___x_4652_; lean_object* v___x_4653_; 
v___x_4651_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__5));
v___x_4652_ = l_Lean_Name_mkStr2(v___y_4646_, v___x_4651_);
lean_inc_ref(v_args_4555_);
v___x_4653_ = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(v___x_4653_, 0, v___x_4652_);
lean_ctor_set(v___x_4653_, 1, v_args_4555_);
v___y_4583_ = v___y_4643_;
v___y_4584_ = v___y_4645_;
v_value_4585_ = v___x_4653_;
v___y_4586_ = v_a_4352_;
v___y_4587_ = v_a_4353_;
v___y_4588_ = v_a_4354_;
v___y_4589_ = v_a_4355_;
v___y_4590_ = v_a_4356_;
v___y_4591_ = v_a_4357_;
goto v___jp_4582_;
}
}
v___jp_4654_:
{
lean_object* v_params_4656_; lean_object* v___x_4657_; 
v_params_4656_ = lean_ctor_get(v___y_4655_, 3);
lean_inc_ref(v_params_4656_);
lean_dec_ref(v___y_4655_);
lean_inc_ref(v_params_4656_);
v___x_4657_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecAfterFullApp(v_args_4555_, v_params_4656_, v_a_4553_, v_a_4352_, v_a_4353_, v_a_4354_, v_a_4355_, v_a_4356_, v_a_4357_);
if (lean_obj_tag(v___x_4657_) == 0)
{
lean_object* v_a_4658_; lean_object* v___x_4659_; lean_object* v___x_4660_; lean_object* v_borrows_4661_; lean_object* v___x_4662_; lean_object* v_borrows_4663_; lean_object* v_borrows_4664_; uint8_t v___x_4665_; uint8_t v___x_4666_; lean_object* v___x_4667_; lean_object* v___x_4668_; uint8_t v___x_4669_; 
v_a_4658_ = lean_ctor_get(v___x_4657_, 0);
lean_inc(v_a_4658_);
lean_dec_ref(v___x_4657_);
v___x_4659_ = lean_st_ref_get(v_a_4353_);
v___x_4660_ = lean_st_ref_get(v_a_4353_);
v_borrows_4661_ = lean_ctor_get(v___x_4659_, 1);
lean_inc_ref(v_borrows_4661_);
lean_dec(v___x_4659_);
v___x_4662_ = lean_st_ref_get(v_a_4353_);
v_borrows_4663_ = lean_ctor_get(v___x_4660_, 1);
lean_inc_ref(v_borrows_4663_);
lean_dec(v___x_4660_);
v_borrows_4664_ = lean_ctor_get(v___x_4662_, 1);
lean_inc_ref(v_borrows_4664_);
lean_dec(v___x_4662_);
v___x_4665_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_isAccessible_spec__0___redArg(v_borrows_4663_, v_fvarId_4359_);
lean_dec_ref(v_borrows_4663_);
v___x_4666_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_isAccessible_spec__0___redArg(v_borrows_4664_, v_fvarId_4359_);
lean_dec_ref(v_borrows_4664_);
v___x_4667_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode___closed__0));
v___x_4668_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__6));
v___x_4669_ = lean_name_eq(v_fn_4554_, v___x_4668_);
if (v___x_4669_ == 0)
{
lean_dec_ref(v_borrows_4661_);
v___y_4642_ = v___x_4665_;
v___y_4643_ = v_a_4658_;
v___y_4644_ = v___x_4666_;
v___y_4645_ = v_params_4656_;
v___y_4646_ = v___x_4667_;
v___y_4647_ = v___x_4669_;
goto v___jp_4641_;
}
else
{
uint8_t v___x_4670_; 
v___x_4670_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_isAccessible_spec__0___redArg(v_borrows_4661_, v_fvarId_4359_);
lean_dec_ref(v_borrows_4661_);
v___y_4642_ = v___x_4665_;
v___y_4643_ = v_a_4658_;
v___y_4644_ = v___x_4666_;
v___y_4645_ = v_params_4656_;
v___y_4646_ = v___x_4667_;
v___y_4647_ = v___x_4670_;
goto v___jp_4641_;
}
}
else
{
lean_dec_ref(v_params_4656_);
lean_dec_ref(v_value_4360_);
lean_dec(v_fvarId_4359_);
lean_dec_ref(v_decl_4350_);
lean_dec_ref(v_code_4349_);
return v___x_4657_;
}
}
}
else
{
lean_object* v_a_4674_; lean_object* v___x_4676_; uint8_t v_isShared_4677_; uint8_t v_isSharedCheck_4681_; 
lean_dec(v_a_4553_);
lean_dec_ref(v_value_4360_);
lean_dec(v_fvarId_4359_);
lean_dec_ref(v_decl_4350_);
lean_dec_ref(v_code_4349_);
v_a_4674_ = lean_ctor_get(v___x_4579_, 0);
v_isSharedCheck_4681_ = !lean_is_exclusive(v___x_4579_);
if (v_isSharedCheck_4681_ == 0)
{
v___x_4676_ = v___x_4579_;
v_isShared_4677_ = v_isSharedCheck_4681_;
goto v_resetjp_4675_;
}
else
{
lean_inc(v_a_4674_);
lean_dec(v___x_4579_);
v___x_4676_ = lean_box(0);
v_isShared_4677_ = v_isSharedCheck_4681_;
goto v_resetjp_4675_;
}
v_resetjp_4675_:
{
lean_object* v___x_4679_; 
if (v_isShared_4677_ == 0)
{
v___x_4679_ = v___x_4676_;
goto v_reusejp_4678_;
}
else
{
lean_object* v_reuseFailAlloc_4680_; 
v_reuseFailAlloc_4680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4680_, 0, v_a_4674_);
v___x_4679_ = v_reuseFailAlloc_4680_;
goto v_reusejp_4678_;
}
v_reusejp_4678_:
{
return v___x_4679_;
}
}
}
v___jp_4556_:
{
lean_object* v___x_4565_; 
v___x_4565_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBefore(v_args_4555_, v___y_4563_, v___y_4564_, v___y_4558_, v___y_4557_, v___y_4560_, v___y_4561_, v___y_4562_, v___y_4559_);
if (lean_obj_tag(v___x_4565_) == 0)
{
lean_object* v_a_4566_; 
v_a_4566_ = lean_ctor_get(v___x_4565_, 0);
lean_inc(v_a_4566_);
lean_dec_ref(v___x_4565_);
v_k_4362_ = v_a_4566_;
v___y_4363_ = v___y_4558_;
v___y_4364_ = v___y_4557_;
v___y_4365_ = v___y_4560_;
v___y_4366_ = v___y_4561_;
v___y_4367_ = v___y_4562_;
v___y_4368_ = v___y_4559_;
goto v___jp_4361_;
}
else
{
lean_dec_ref(v_value_4360_);
lean_dec(v_fvarId_4359_);
return v___x_4565_;
}
}
v___jp_4567_:
{
if (v___y_4577_ == 0)
{
lean_object* v___x_4578_; 
lean_dec_ref(v_code_4349_);
v___x_4578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4578_, 0, v___y_4571_);
lean_ctor_set(v___x_4578_, 1, v___y_4570_);
v___y_4557_ = v___y_4569_;
v___y_4558_ = v___y_4568_;
v___y_4559_ = v___y_4573_;
v___y_4560_ = v___y_4572_;
v___y_4561_ = v___y_4574_;
v___y_4562_ = v___y_4575_;
v___y_4563_ = v___y_4576_;
v___y_4564_ = v___x_4578_;
goto v___jp_4556_;
}
else
{
lean_dec_ref(v___y_4571_);
lean_dec_ref(v___y_4570_);
v___y_4557_ = v___y_4569_;
v___y_4558_ = v___y_4568_;
v___y_4559_ = v___y_4573_;
v___y_4560_ = v___y_4572_;
v___y_4561_ = v___y_4574_;
v___y_4562_ = v___y_4575_;
v___y_4563_ = v___y_4576_;
v___y_4564_ = v_code_4349_;
goto v___jp_4556_;
}
}
}
case 10:
{
lean_object* v_a_4682_; lean_object* v_args_4683_; lean_object* v___x_4684_; 
v_a_4682_ = lean_ctor_get(v___x_4427_, 0);
lean_inc(v_a_4682_);
lean_dec_ref(v___x_4427_);
v_args_4683_ = lean_ctor_get(v_value_4360_, 1);
lean_inc_ref(v_decl_4350_);
v___x_4684_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_ensureNoBorrow(v_decl_4350_, v_a_4352_, v_a_4353_, v_a_4354_, v_a_4355_, v_a_4356_, v_a_4357_);
if (lean_obj_tag(v___x_4684_) == 0)
{
lean_object* v___y_4686_; uint8_t v___y_4690_; 
lean_dec_ref(v___x_4684_);
if (lean_obj_tag(v_code_4349_) == 0)
{
lean_object* v_decl_4692_; lean_object* v_k_4693_; size_t v___x_4694_; size_t v___x_4695_; uint8_t v___x_4696_; 
v_decl_4692_ = lean_ctor_get(v_code_4349_, 0);
v_k_4693_ = lean_ctor_get(v_code_4349_, 1);
v___x_4694_ = lean_ptr_addr(v_k_4693_);
v___x_4695_ = lean_ptr_addr(v_a_4682_);
v___x_4696_ = lean_usize_dec_eq(v___x_4694_, v___x_4695_);
if (v___x_4696_ == 0)
{
v___y_4690_ = v___x_4696_;
goto v___jp_4689_;
}
else
{
size_t v___x_4697_; size_t v___x_4698_; uint8_t v___x_4699_; 
v___x_4697_ = lean_ptr_addr(v_decl_4692_);
v___x_4698_ = lean_ptr_addr(v_decl_4350_);
v___x_4699_ = lean_usize_dec_eq(v___x_4697_, v___x_4698_);
v___y_4690_ = v___x_4699_;
goto v___jp_4689_;
}
}
else
{
lean_object* v___x_4700_; lean_object* v___x_4701_; 
lean_dec(v_a_4682_);
lean_dec_ref(v_decl_4350_);
lean_dec_ref(v_code_4349_);
v___x_4700_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2);
v___x_4701_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__0(v___x_4700_);
v___y_4686_ = v___x_4701_;
goto v___jp_4685_;
}
v___jp_4685_:
{
lean_object* v___x_4687_; 
v___x_4687_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeConsumeAll(v_args_4683_, v___y_4686_, v_a_4352_, v_a_4353_, v_a_4354_, v_a_4355_, v_a_4356_, v_a_4357_);
if (lean_obj_tag(v___x_4687_) == 0)
{
lean_object* v_a_4688_; 
v_a_4688_ = lean_ctor_get(v___x_4687_, 0);
lean_inc(v_a_4688_);
lean_dec_ref(v___x_4687_);
v_k_4362_ = v_a_4688_;
v___y_4363_ = v_a_4352_;
v___y_4364_ = v_a_4353_;
v___y_4365_ = v_a_4354_;
v___y_4366_ = v_a_4355_;
v___y_4367_ = v_a_4356_;
v___y_4368_ = v_a_4357_;
goto v___jp_4361_;
}
else
{
lean_dec_ref(v_value_4360_);
lean_dec(v_fvarId_4359_);
return v___x_4687_;
}
}
v___jp_4689_:
{
if (v___y_4690_ == 0)
{
lean_object* v___x_4691_; 
lean_dec_ref(v_code_4349_);
v___x_4691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4691_, 0, v_decl_4350_);
lean_ctor_set(v___x_4691_, 1, v_a_4682_);
v___y_4686_ = v___x_4691_;
goto v___jp_4685_;
}
else
{
lean_dec(v_a_4682_);
lean_dec_ref(v_decl_4350_);
v___y_4686_ = v_code_4349_;
goto v___jp_4685_;
}
}
}
else
{
lean_object* v_a_4702_; lean_object* v___x_4704_; uint8_t v_isShared_4705_; uint8_t v_isSharedCheck_4709_; 
lean_dec(v_a_4682_);
lean_dec_ref(v_value_4360_);
lean_dec(v_fvarId_4359_);
lean_dec_ref(v_decl_4350_);
lean_dec_ref(v_code_4349_);
v_a_4702_ = lean_ctor_get(v___x_4684_, 0);
v_isSharedCheck_4709_ = !lean_is_exclusive(v___x_4684_);
if (v_isSharedCheck_4709_ == 0)
{
v___x_4704_ = v___x_4684_;
v_isShared_4705_ = v_isSharedCheck_4709_;
goto v_resetjp_4703_;
}
else
{
lean_inc(v_a_4702_);
lean_dec(v___x_4684_);
v___x_4704_ = lean_box(0);
v_isShared_4705_ = v_isSharedCheck_4709_;
goto v_resetjp_4703_;
}
v_resetjp_4703_:
{
lean_object* v___x_4707_; 
if (v_isShared_4705_ == 0)
{
v___x_4707_ = v___x_4704_;
goto v_reusejp_4706_;
}
else
{
lean_object* v_reuseFailAlloc_4708_; 
v_reuseFailAlloc_4708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4708_, 0, v_a_4702_);
v___x_4707_ = v_reuseFailAlloc_4708_;
goto v_reusejp_4706_;
}
v_reusejp_4706_:
{
return v___x_4707_;
}
}
}
}
case 12:
{
lean_object* v_a_4710_; lean_object* v_args_4711_; lean_object* v___x_4712_; 
v_a_4710_ = lean_ctor_get(v___x_4427_, 0);
lean_inc(v_a_4710_);
lean_dec_ref(v___x_4427_);
v_args_4711_ = lean_ctor_get(v_value_4360_, 2);
lean_inc_ref(v_decl_4350_);
v___x_4712_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_ensureNoBorrow(v_decl_4350_, v_a_4352_, v_a_4353_, v_a_4354_, v_a_4355_, v_a_4356_, v_a_4357_);
if (lean_obj_tag(v___x_4712_) == 0)
{
lean_object* v___y_4714_; uint8_t v___y_4718_; 
lean_dec_ref(v___x_4712_);
if (lean_obj_tag(v_code_4349_) == 0)
{
lean_object* v_decl_4720_; lean_object* v_k_4721_; size_t v___x_4722_; size_t v___x_4723_; uint8_t v___x_4724_; 
v_decl_4720_ = lean_ctor_get(v_code_4349_, 0);
v_k_4721_ = lean_ctor_get(v_code_4349_, 1);
v___x_4722_ = lean_ptr_addr(v_k_4721_);
v___x_4723_ = lean_ptr_addr(v_a_4710_);
v___x_4724_ = lean_usize_dec_eq(v___x_4722_, v___x_4723_);
if (v___x_4724_ == 0)
{
v___y_4718_ = v___x_4724_;
goto v___jp_4717_;
}
else
{
size_t v___x_4725_; size_t v___x_4726_; uint8_t v___x_4727_; 
v___x_4725_ = lean_ptr_addr(v_decl_4720_);
v___x_4726_ = lean_ptr_addr(v_decl_4350_);
v___x_4727_ = lean_usize_dec_eq(v___x_4725_, v___x_4726_);
v___y_4718_ = v___x_4727_;
goto v___jp_4717_;
}
}
else
{
lean_object* v___x_4728_; lean_object* v___x_4729_; 
lean_dec(v_a_4710_);
lean_dec_ref(v_decl_4350_);
lean_dec_ref(v_code_4349_);
v___x_4728_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2);
v___x_4729_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__0(v___x_4728_);
v___y_4714_ = v___x_4729_;
goto v___jp_4713_;
}
v___jp_4713_:
{
lean_object* v___x_4715_; 
v___x_4715_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeConsumeAll(v_args_4711_, v___y_4714_, v_a_4352_, v_a_4353_, v_a_4354_, v_a_4355_, v_a_4356_, v_a_4357_);
if (lean_obj_tag(v___x_4715_) == 0)
{
lean_object* v_a_4716_; 
v_a_4716_ = lean_ctor_get(v___x_4715_, 0);
lean_inc(v_a_4716_);
lean_dec_ref(v___x_4715_);
v_k_4362_ = v_a_4716_;
v___y_4363_ = v_a_4352_;
v___y_4364_ = v_a_4353_;
v___y_4365_ = v_a_4354_;
v___y_4366_ = v_a_4355_;
v___y_4367_ = v_a_4356_;
v___y_4368_ = v_a_4357_;
goto v___jp_4361_;
}
else
{
lean_dec_ref(v_value_4360_);
lean_dec(v_fvarId_4359_);
return v___x_4715_;
}
}
v___jp_4717_:
{
if (v___y_4718_ == 0)
{
lean_object* v___x_4719_; 
lean_dec_ref(v_code_4349_);
v___x_4719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4719_, 0, v_decl_4350_);
lean_ctor_set(v___x_4719_, 1, v_a_4710_);
v___y_4714_ = v___x_4719_;
goto v___jp_4713_;
}
else
{
lean_dec(v_a_4710_);
lean_dec_ref(v_decl_4350_);
v___y_4714_ = v_code_4349_;
goto v___jp_4713_;
}
}
}
else
{
lean_object* v_a_4730_; lean_object* v___x_4732_; uint8_t v_isShared_4733_; uint8_t v_isSharedCheck_4737_; 
lean_dec_ref(v_value_4360_);
lean_dec(v_a_4710_);
lean_dec(v_fvarId_4359_);
lean_dec_ref(v_decl_4350_);
lean_dec_ref(v_code_4349_);
v_a_4730_ = lean_ctor_get(v___x_4712_, 0);
v_isSharedCheck_4737_ = !lean_is_exclusive(v___x_4712_);
if (v_isSharedCheck_4737_ == 0)
{
v___x_4732_ = v___x_4712_;
v_isShared_4733_ = v_isSharedCheck_4737_;
goto v_resetjp_4731_;
}
else
{
lean_inc(v_a_4730_);
lean_dec(v___x_4712_);
v___x_4732_ = lean_box(0);
v_isShared_4733_ = v_isSharedCheck_4737_;
goto v_resetjp_4731_;
}
v_resetjp_4731_:
{
lean_object* v___x_4735_; 
if (v_isShared_4733_ == 0)
{
v___x_4735_ = v___x_4732_;
goto v_reusejp_4734_;
}
else
{
lean_object* v_reuseFailAlloc_4736_; 
v_reuseFailAlloc_4736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4736_, 0, v_a_4730_);
v___x_4735_ = v_reuseFailAlloc_4736_;
goto v_reusejp_4734_;
}
v_reusejp_4734_:
{
return v___x_4735_;
}
}
}
}
case 14:
{
lean_object* v_a_4738_; lean_object* v_fvarId_4739_; lean_object* v___x_4740_; lean_object* v_a_4741_; lean_object* v___x_4742_; 
v_a_4738_ = lean_ctor_get(v___x_4427_, 0);
lean_inc(v_a_4738_);
lean_dec_ref(v___x_4427_);
v_fvarId_4739_ = lean_ctor_get(v_value_4360_, 0);
lean_inc(v_fvarId_4739_);
v___x_4740_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecIfNeeded___redArg(v_fvarId_4739_, v_a_4738_, v_a_4352_, v_a_4353_);
v_a_4741_ = lean_ctor_get(v___x_4740_, 0);
lean_inc(v_a_4741_);
lean_dec_ref(v___x_4740_);
lean_inc_ref(v_decl_4350_);
v___x_4742_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_ensureNoBorrow(v_decl_4350_, v_a_4352_, v_a_4353_, v_a_4354_, v_a_4355_, v_a_4356_, v_a_4357_);
if (lean_obj_tag(v___x_4742_) == 0)
{
uint8_t v___y_4744_; 
lean_dec_ref(v___x_4742_);
if (lean_obj_tag(v_code_4349_) == 0)
{
lean_object* v_decl_4746_; lean_object* v_k_4747_; size_t v___x_4748_; size_t v___x_4749_; uint8_t v___x_4750_; 
v_decl_4746_ = lean_ctor_get(v_code_4349_, 0);
v_k_4747_ = lean_ctor_get(v_code_4349_, 1);
v___x_4748_ = lean_ptr_addr(v_k_4747_);
v___x_4749_ = lean_ptr_addr(v_a_4741_);
v___x_4750_ = lean_usize_dec_eq(v___x_4748_, v___x_4749_);
if (v___x_4750_ == 0)
{
v___y_4744_ = v___x_4750_;
goto v___jp_4743_;
}
else
{
size_t v___x_4751_; size_t v___x_4752_; uint8_t v___x_4753_; 
v___x_4751_ = lean_ptr_addr(v_decl_4746_);
v___x_4752_ = lean_ptr_addr(v_decl_4350_);
v___x_4753_ = lean_usize_dec_eq(v___x_4751_, v___x_4752_);
v___y_4744_ = v___x_4753_;
goto v___jp_4743_;
}
}
else
{
lean_object* v___x_4754_; lean_object* v___x_4755_; 
lean_dec(v_a_4741_);
lean_dec_ref(v_decl_4350_);
lean_dec_ref(v_code_4349_);
v___x_4754_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2);
v___x_4755_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__0(v___x_4754_);
v_k_4362_ = v___x_4755_;
v___y_4363_ = v_a_4352_;
v___y_4364_ = v_a_4353_;
v___y_4365_ = v_a_4354_;
v___y_4366_ = v_a_4355_;
v___y_4367_ = v_a_4356_;
v___y_4368_ = v_a_4357_;
goto v___jp_4361_;
}
v___jp_4743_:
{
if (v___y_4744_ == 0)
{
lean_object* v___x_4745_; 
lean_dec_ref(v_code_4349_);
v___x_4745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4745_, 0, v_decl_4350_);
lean_ctor_set(v___x_4745_, 1, v_a_4741_);
v_k_4362_ = v___x_4745_;
v___y_4363_ = v_a_4352_;
v___y_4364_ = v_a_4353_;
v___y_4365_ = v_a_4354_;
v___y_4366_ = v_a_4355_;
v___y_4367_ = v_a_4356_;
v___y_4368_ = v_a_4357_;
goto v___jp_4361_;
}
else
{
lean_dec(v_a_4741_);
lean_dec_ref(v_decl_4350_);
v_k_4362_ = v_code_4349_;
v___y_4363_ = v_a_4352_;
v___y_4364_ = v_a_4353_;
v___y_4365_ = v_a_4354_;
v___y_4366_ = v_a_4355_;
v___y_4367_ = v_a_4356_;
v___y_4368_ = v_a_4357_;
goto v___jp_4361_;
}
}
}
else
{
lean_object* v_a_4756_; lean_object* v___x_4758_; uint8_t v_isShared_4759_; uint8_t v_isSharedCheck_4763_; 
lean_dec(v_a_4741_);
lean_dec_ref(v_value_4360_);
lean_dec(v_fvarId_4359_);
lean_dec_ref(v_decl_4350_);
lean_dec_ref(v_code_4349_);
v_a_4756_ = lean_ctor_get(v___x_4742_, 0);
v_isSharedCheck_4763_ = !lean_is_exclusive(v___x_4742_);
if (v_isSharedCheck_4763_ == 0)
{
v___x_4758_ = v___x_4742_;
v_isShared_4759_ = v_isSharedCheck_4763_;
goto v_resetjp_4757_;
}
else
{
lean_inc(v_a_4756_);
lean_dec(v___x_4742_);
v___x_4758_ = lean_box(0);
v_isShared_4759_ = v_isSharedCheck_4763_;
goto v_resetjp_4757_;
}
v_resetjp_4757_:
{
lean_object* v___x_4761_; 
if (v_isShared_4759_ == 0)
{
v___x_4761_ = v___x_4758_;
goto v_reusejp_4760_;
}
else
{
lean_object* v_reuseFailAlloc_4762_; 
v_reuseFailAlloc_4762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4762_, 0, v_a_4756_);
v___x_4761_ = v_reuseFailAlloc_4762_;
goto v_reusejp_4760_;
}
v_reusejp_4760_:
{
return v___x_4761_;
}
}
}
}
case 15:
{
lean_object* v___x_4764_; lean_object* v___x_4765_; 
lean_dec_ref(v___x_4427_);
lean_dec_ref(v_decl_4350_);
lean_dec_ref(v_code_4349_);
v___x_4764_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__12, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__12_once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__12);
v___x_4765_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__2(v___x_4764_, v_a_4352_, v_a_4353_, v_a_4354_, v_a_4355_, v_a_4356_, v_a_4357_);
if (lean_obj_tag(v___x_4765_) == 0)
{
lean_object* v_a_4766_; 
v_a_4766_ = lean_ctor_get(v___x_4765_, 0);
lean_inc(v_a_4766_);
lean_dec_ref(v___x_4765_);
v_k_4362_ = v_a_4766_;
v___y_4363_ = v_a_4352_;
v___y_4364_ = v_a_4353_;
v___y_4365_ = v_a_4354_;
v___y_4366_ = v_a_4355_;
v___y_4367_ = v_a_4356_;
v___y_4368_ = v_a_4357_;
goto v___jp_4361_;
}
else
{
lean_dec_ref(v_value_4360_);
lean_dec(v_fvarId_4359_);
return v___x_4765_;
}
}
default: 
{
lean_object* v_a_4767_; lean_object* v___x_4768_; 
v_a_4767_ = lean_ctor_get(v___x_4427_, 0);
lean_inc(v_a_4767_);
lean_dec_ref(v___x_4427_);
lean_inc_ref(v_decl_4350_);
v___x_4768_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_ensureNoBorrow(v_decl_4350_, v_a_4352_, v_a_4353_, v_a_4354_, v_a_4355_, v_a_4356_, v_a_4357_);
if (lean_obj_tag(v___x_4768_) == 0)
{
uint8_t v___y_4770_; 
lean_dec_ref(v___x_4768_);
if (lean_obj_tag(v_code_4349_) == 0)
{
lean_object* v_decl_4772_; lean_object* v_k_4773_; size_t v___x_4774_; size_t v___x_4775_; uint8_t v___x_4776_; 
v_decl_4772_ = lean_ctor_get(v_code_4349_, 0);
v_k_4773_ = lean_ctor_get(v_code_4349_, 1);
v___x_4774_ = lean_ptr_addr(v_k_4773_);
v___x_4775_ = lean_ptr_addr(v_a_4767_);
v___x_4776_ = lean_usize_dec_eq(v___x_4774_, v___x_4775_);
if (v___x_4776_ == 0)
{
v___y_4770_ = v___x_4776_;
goto v___jp_4769_;
}
else
{
size_t v___x_4777_; size_t v___x_4778_; uint8_t v___x_4779_; 
v___x_4777_ = lean_ptr_addr(v_decl_4772_);
v___x_4778_ = lean_ptr_addr(v_decl_4350_);
v___x_4779_ = lean_usize_dec_eq(v___x_4777_, v___x_4778_);
v___y_4770_ = v___x_4779_;
goto v___jp_4769_;
}
}
else
{
lean_object* v___x_4780_; lean_object* v___x_4781_; 
lean_dec(v_a_4767_);
lean_dec_ref(v_decl_4350_);
lean_dec_ref(v_code_4349_);
v___x_4780_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2);
v___x_4781_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__0(v___x_4780_);
v_k_4362_ = v___x_4781_;
v___y_4363_ = v_a_4352_;
v___y_4364_ = v_a_4353_;
v___y_4365_ = v_a_4354_;
v___y_4366_ = v_a_4355_;
v___y_4367_ = v_a_4356_;
v___y_4368_ = v_a_4357_;
goto v___jp_4361_;
}
v___jp_4769_:
{
if (v___y_4770_ == 0)
{
lean_object* v___x_4771_; 
lean_dec_ref(v_code_4349_);
v___x_4771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4771_, 0, v_decl_4350_);
lean_ctor_set(v___x_4771_, 1, v_a_4767_);
v_k_4362_ = v___x_4771_;
v___y_4363_ = v_a_4352_;
v___y_4364_ = v_a_4353_;
v___y_4365_ = v_a_4354_;
v___y_4366_ = v_a_4355_;
v___y_4367_ = v_a_4356_;
v___y_4368_ = v_a_4357_;
goto v___jp_4361_;
}
else
{
lean_dec(v_a_4767_);
lean_dec_ref(v_decl_4350_);
v_k_4362_ = v_code_4349_;
v___y_4363_ = v_a_4352_;
v___y_4364_ = v_a_4353_;
v___y_4365_ = v_a_4354_;
v___y_4366_ = v_a_4355_;
v___y_4367_ = v_a_4356_;
v___y_4368_ = v_a_4357_;
goto v___jp_4361_;
}
}
}
else
{
lean_object* v_a_4782_; lean_object* v___x_4784_; uint8_t v_isShared_4785_; uint8_t v_isSharedCheck_4789_; 
lean_dec(v_a_4767_);
lean_dec(v_value_4360_);
lean_dec(v_fvarId_4359_);
lean_dec_ref(v_decl_4350_);
lean_dec_ref(v_code_4349_);
v_a_4782_ = lean_ctor_get(v___x_4768_, 0);
v_isSharedCheck_4789_ = !lean_is_exclusive(v___x_4768_);
if (v_isSharedCheck_4789_ == 0)
{
v___x_4784_ = v___x_4768_;
v_isShared_4785_ = v_isSharedCheck_4789_;
goto v_resetjp_4783_;
}
else
{
lean_inc(v_a_4782_);
lean_dec(v___x_4768_);
v___x_4784_ = lean_box(0);
v_isShared_4785_ = v_isSharedCheck_4789_;
goto v_resetjp_4783_;
}
v_resetjp_4783_:
{
lean_object* v___x_4787_; 
if (v_isShared_4785_ == 0)
{
v___x_4787_ = v___x_4784_;
goto v_reusejp_4786_;
}
else
{
lean_object* v_reuseFailAlloc_4788_; 
v_reuseFailAlloc_4788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4788_, 0, v_a_4782_);
v___x_4787_ = v_reuseFailAlloc_4788_;
goto v_reusejp_4786_;
}
v_reusejp_4786_:
{
return v___x_4787_;
}
}
}
}
}
v___jp_4361_:
{
lean_object* v___x_4369_; 
v___x_4369_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue(v_value_4360_, v___y_4363_, v___y_4364_, v___y_4365_, v___y_4366_, v___y_4367_, v___y_4368_);
if (lean_obj_tag(v___x_4369_) == 0)
{
lean_object* v___x_4371_; uint8_t v_isShared_4372_; uint8_t v_isSharedCheck_4389_; 
v_isSharedCheck_4389_ = !lean_is_exclusive(v___x_4369_);
if (v_isSharedCheck_4389_ == 0)
{
lean_object* v_unused_4390_; 
v_unused_4390_ = lean_ctor_get(v___x_4369_, 0);
lean_dec(v_unused_4390_);
v___x_4371_ = v___x_4369_;
v_isShared_4372_ = v_isSharedCheck_4389_;
goto v_resetjp_4370_;
}
else
{
lean_dec(v___x_4369_);
v___x_4371_ = lean_box(0);
v_isShared_4372_ = v_isSharedCheck_4389_;
goto v_resetjp_4370_;
}
v_resetjp_4370_:
{
lean_object* v___x_4373_; lean_object* v_vars_4374_; lean_object* v_borrows_4375_; lean_object* v___x_4377_; uint8_t v_isShared_4378_; uint8_t v_isSharedCheck_4388_; 
v___x_4373_ = lean_st_ref_take(v___y_4364_);
v_vars_4374_ = lean_ctor_get(v___x_4373_, 0);
v_borrows_4375_ = lean_ctor_get(v___x_4373_, 1);
v_isSharedCheck_4388_ = !lean_is_exclusive(v___x_4373_);
if (v_isSharedCheck_4388_ == 0)
{
v___x_4377_ = v___x_4373_;
v_isShared_4378_ = v_isSharedCheck_4388_;
goto v_resetjp_4376_;
}
else
{
lean_inc(v_borrows_4375_);
lean_inc(v_vars_4374_);
lean_dec(v___x_4373_);
v___x_4377_ = lean_box(0);
v_isShared_4378_ = v_isSharedCheck_4388_;
goto v_resetjp_4376_;
}
v_resetjp_4376_:
{
lean_object* v_vars_4379_; lean_object* v_borrows_4380_; lean_object* v___x_4382_; 
v_vars_4379_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_removeFromParent_spec__0___redArg(v_vars_4374_, v_fvarId_4359_);
v_borrows_4380_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_removeFromParent_spec__0___redArg(v_borrows_4375_, v_fvarId_4359_);
lean_dec(v_fvarId_4359_);
if (v_isShared_4378_ == 0)
{
lean_ctor_set(v___x_4377_, 1, v_borrows_4380_);
lean_ctor_set(v___x_4377_, 0, v_vars_4379_);
v___x_4382_ = v___x_4377_;
goto v_reusejp_4381_;
}
else
{
lean_object* v_reuseFailAlloc_4387_; 
v_reuseFailAlloc_4387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4387_, 0, v_vars_4379_);
lean_ctor_set(v_reuseFailAlloc_4387_, 1, v_borrows_4380_);
v___x_4382_ = v_reuseFailAlloc_4387_;
goto v_reusejp_4381_;
}
v_reusejp_4381_:
{
lean_object* v___x_4383_; lean_object* v___x_4385_; 
v___x_4383_ = lean_st_ref_set(v___y_4364_, v___x_4382_);
if (v_isShared_4372_ == 0)
{
lean_ctor_set(v___x_4371_, 0, v_k_4362_);
v___x_4385_ = v___x_4371_;
goto v_reusejp_4384_;
}
else
{
lean_object* v_reuseFailAlloc_4386_; 
v_reuseFailAlloc_4386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4386_, 0, v_k_4362_);
v___x_4385_ = v_reuseFailAlloc_4386_;
goto v_reusejp_4384_;
}
v_reusejp_4384_:
{
return v___x_4385_;
}
}
}
}
}
else
{
lean_object* v_a_4391_; lean_object* v___x_4393_; uint8_t v_isShared_4394_; uint8_t v_isSharedCheck_4398_; 
lean_dec_ref(v_k_4362_);
lean_dec(v_fvarId_4359_);
v_a_4391_ = lean_ctor_get(v___x_4369_, 0);
v_isSharedCheck_4398_ = !lean_is_exclusive(v___x_4369_);
if (v_isSharedCheck_4398_ == 0)
{
v___x_4393_ = v___x_4369_;
v_isShared_4394_ = v_isSharedCheck_4398_;
goto v_resetjp_4392_;
}
else
{
lean_inc(v_a_4391_);
lean_dec(v___x_4369_);
v___x_4393_ = lean_box(0);
v_isShared_4394_ = v_isSharedCheck_4398_;
goto v_resetjp_4392_;
}
v_resetjp_4392_:
{
lean_object* v___x_4396_; 
if (v_isShared_4394_ == 0)
{
v___x_4396_ = v___x_4393_;
goto v_reusejp_4395_;
}
else
{
lean_object* v_reuseFailAlloc_4397_; 
v_reuseFailAlloc_4397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4397_, 0, v_a_4391_);
v___x_4396_ = v_reuseFailAlloc_4397_;
goto v_reusejp_4395_;
}
v_reusejp_4395_:
{
return v___x_4396_;
}
}
}
}
v___jp_4399_:
{
if (v___y_4407_ == 0)
{
lean_object* v___x_4408_; 
lean_dec_ref(v_code_4349_);
v___x_4408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4408_, 0, v_decl_4350_);
lean_ctor_set(v___x_4408_, 1, v___y_4402_);
v_k_4362_ = v___x_4408_;
v___y_4363_ = v___y_4405_;
v___y_4364_ = v___y_4404_;
v___y_4365_ = v___y_4403_;
v___y_4366_ = v___y_4406_;
v___y_4367_ = v___y_4401_;
v___y_4368_ = v___y_4400_;
goto v___jp_4361_;
}
else
{
lean_dec_ref(v___y_4402_);
lean_dec_ref(v_decl_4350_);
v_k_4362_ = v_code_4349_;
v___y_4363_ = v___y_4405_;
v___y_4364_ = v___y_4404_;
v___y_4365_ = v___y_4403_;
v___y_4366_ = v___y_4406_;
v___y_4367_ = v___y_4401_;
v___y_4368_ = v___y_4400_;
goto v___jp_4361_;
}
}
v___jp_4409_:
{
if (lean_obj_tag(v_code_4349_) == 0)
{
lean_object* v_decl_4417_; lean_object* v_k_4418_; size_t v___x_4419_; size_t v___x_4420_; uint8_t v___x_4421_; 
v_decl_4417_ = lean_ctor_get(v_code_4349_, 0);
v_k_4418_ = lean_ctor_get(v_code_4349_, 1);
v___x_4419_ = lean_ptr_addr(v_k_4418_);
v___x_4420_ = lean_ptr_addr(v_k_4410_);
v___x_4421_ = lean_usize_dec_eq(v___x_4419_, v___x_4420_);
if (v___x_4421_ == 0)
{
v___y_4400_ = v___y_4416_;
v___y_4401_ = v___y_4415_;
v___y_4402_ = v_k_4410_;
v___y_4403_ = v___y_4413_;
v___y_4404_ = v___y_4412_;
v___y_4405_ = v___y_4411_;
v___y_4406_ = v___y_4414_;
v___y_4407_ = v___x_4421_;
goto v___jp_4399_;
}
else
{
size_t v___x_4422_; size_t v___x_4423_; uint8_t v___x_4424_; 
v___x_4422_ = lean_ptr_addr(v_decl_4417_);
v___x_4423_ = lean_ptr_addr(v_decl_4350_);
v___x_4424_ = lean_usize_dec_eq(v___x_4422_, v___x_4423_);
v___y_4400_ = v___y_4416_;
v___y_4401_ = v___y_4415_;
v___y_4402_ = v_k_4410_;
v___y_4403_ = v___y_4413_;
v___y_4404_ = v___y_4412_;
v___y_4405_ = v___y_4411_;
v___y_4406_ = v___y_4414_;
v___y_4407_ = v___x_4424_;
goto v___jp_4399_;
}
}
else
{
lean_object* v___x_4425_; lean_object* v___x_4426_; 
lean_dec_ref(v_k_4410_);
lean_dec_ref(v_decl_4350_);
lean_dec_ref(v_code_4349_);
v___x_4425_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2);
v___x_4426_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__0(v___x_4425_);
v_k_4362_ = v___x_4426_;
v___y_4363_ = v___y_4411_;
v___y_4364_ = v___y_4412_;
v___y_4365_ = v___y_4413_;
v___y_4366_ = v___y_4414_;
v___y_4367_ = v___y_4415_;
v___y_4368_ = v___y_4416_;
goto v___jp_4361_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___boxed(lean_object* v_code_4790_, lean_object* v_decl_4791_, lean_object* v_k_4792_, lean_object* v_a_4793_, lean_object* v_a_4794_, lean_object* v_a_4795_, lean_object* v_a_4796_, lean_object* v_a_4797_, lean_object* v_a_4798_, lean_object* v_a_4799_){
_start:
{
lean_object* v_res_4800_; 
v_res_4800_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc(v_code_4790_, v_decl_4791_, v_k_4792_, v_a_4793_, v_a_4794_, v_a_4795_, v_a_4796_, v_a_4797_, v_a_4798_);
lean_dec(v_a_4798_);
lean_dec_ref(v_a_4797_);
lean_dec(v_a_4796_);
lean_dec_ref(v_a_4795_);
lean_dec(v_a_4794_);
lean_dec_ref(v_a_4793_);
return v_res_4800_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__4___closed__0(void){
_start:
{
uint8_t v___x_4801_; lean_object* v___x_4802_; 
v___x_4801_ = 1;
v___x_4802_ = l_Lean_Compiler_LCNF_instInhabitedFunDecl_default__1(v___x_4801_);
return v___x_4802_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__4(lean_object* v_msg_4803_){
_start:
{
lean_object* v___x_4804_; lean_object* v___x_4805_; 
v___x_4804_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__4___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__4___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__4___closed__0);
v___x_4805_ = lean_panic_fn(v___x_4804_, v_msg_4803_);
return v___x_4805_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc___lam__0(lean_object* v_params_4806_, uint8_t v___x_4807_, lean_object* v_decl_4808_, lean_object* v_type_4809_, lean_object* v_value_4810_, lean_object* v___y_4811_, lean_object* v___y_4812_, lean_object* v___y_4813_, lean_object* v___y_4814_, lean_object* v___y_4815_, lean_object* v___y_4816_){
_start:
{
lean_object* v___x_4818_; 
v___x_4818_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams(v_params_4806_, v_value_4810_, v___y_4811_, v___y_4812_, v___y_4813_, v___y_4814_, v___y_4815_, v___y_4816_);
if (lean_obj_tag(v___x_4818_) == 0)
{
lean_object* v_a_4819_; lean_object* v___x_4820_; 
v_a_4819_ = lean_ctor_get(v___x_4818_, 0);
lean_inc(v_a_4819_);
lean_dec_ref(v___x_4818_);
v___x_4820_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_4807_, v_decl_4808_, v_type_4809_, v_params_4806_, v_a_4819_, v___y_4814_);
return v___x_4820_;
}
else
{
lean_object* v_a_4821_; lean_object* v___x_4823_; uint8_t v_isShared_4824_; uint8_t v_isSharedCheck_4828_; 
lean_dec_ref(v_type_4809_);
lean_dec_ref(v_decl_4808_);
lean_dec_ref(v_params_4806_);
v_a_4821_ = lean_ctor_get(v___x_4818_, 0);
v_isSharedCheck_4828_ = !lean_is_exclusive(v___x_4818_);
if (v_isSharedCheck_4828_ == 0)
{
v___x_4823_ = v___x_4818_;
v_isShared_4824_ = v_isSharedCheck_4828_;
goto v_resetjp_4822_;
}
else
{
lean_inc(v_a_4821_);
lean_dec(v___x_4818_);
v___x_4823_ = lean_box(0);
v_isShared_4824_ = v_isSharedCheck_4828_;
goto v_resetjp_4822_;
}
v_resetjp_4822_:
{
lean_object* v___x_4826_; 
if (v_isShared_4824_ == 0)
{
v___x_4826_ = v___x_4823_;
goto v_reusejp_4825_;
}
else
{
lean_object* v_reuseFailAlloc_4827_; 
v_reuseFailAlloc_4827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4827_, 0, v_a_4821_);
v___x_4826_ = v_reuseFailAlloc_4827_;
goto v_reusejp_4825_;
}
v_reusejp_4825_:
{
return v___x_4826_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc___lam__0___boxed(lean_object* v_params_4829_, lean_object* v___x_4830_, lean_object* v_decl_4831_, lean_object* v_type_4832_, lean_object* v_value_4833_, lean_object* v___y_4834_, lean_object* v___y_4835_, lean_object* v___y_4836_, lean_object* v___y_4837_, lean_object* v___y_4838_, lean_object* v___y_4839_, lean_object* v___y_4840_){
_start:
{
uint8_t v___x_18840__boxed_4841_; lean_object* v_res_4842_; 
v___x_18840__boxed_4841_ = lean_unbox(v___x_4830_);
v_res_4842_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc___lam__0(v_params_4829_, v___x_18840__boxed_4841_, v_decl_4831_, v_type_4832_, v_value_4833_, v___y_4834_, v___y_4835_, v___y_4836_, v___y_4837_, v___y_4838_, v___y_4839_);
lean_dec(v___y_4839_);
lean_dec_ref(v___y_4838_);
lean_dec(v___y_4837_);
lean_dec_ref(v___y_4836_);
lean_dec(v___y_4835_);
lean_dec_ref(v___y_4834_);
return v_res_4842_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__0_spec__0(lean_object* v_a_4843_, lean_object* v_a_4844_){
_start:
{
if (lean_obj_tag(v_a_4843_) == 0)
{
lean_object* v___x_4845_; 
v___x_4845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4845_, 0, v_a_4844_);
return v___x_4845_;
}
else
{
lean_object* v_key_4846_; lean_object* v_value_4847_; lean_object* v_tail_4848_; lean_object* v_r_4849_; 
v_key_4846_ = lean_ctor_get(v_a_4843_, 0);
lean_inc(v_key_4846_);
v_value_4847_ = lean_ctor_get(v_a_4843_, 1);
lean_inc(v_value_4847_);
v_tail_4848_ = lean_ctor_get(v_a_4843_, 2);
lean_inc(v_tail_4848_);
lean_dec_ref(v_a_4843_);
v_r_4849_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__0___redArg(v_a_4844_, v_key_4846_, v_value_4847_);
v_a_4843_ = v_tail_4848_;
v_a_4844_ = v_r_4849_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__0_spec__1(lean_object* v_as_4851_, size_t v_sz_4852_, size_t v_i_4853_, lean_object* v_b_4854_){
_start:
{
uint8_t v___x_4855_; 
v___x_4855_ = lean_usize_dec_lt(v_i_4853_, v_sz_4852_);
if (v___x_4855_ == 0)
{
return v_b_4854_;
}
else
{
lean_object* v_a_4856_; lean_object* v___x_4857_; 
v_a_4856_ = lean_array_uget_borrowed(v_as_4851_, v_i_4853_);
lean_inc(v_a_4856_);
v___x_4857_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__0_spec__0(v_a_4856_, v_b_4854_);
if (lean_obj_tag(v___x_4857_) == 0)
{
lean_object* v_a_4858_; 
v_a_4858_ = lean_ctor_get(v___x_4857_, 0);
lean_inc(v_a_4858_);
lean_dec_ref(v___x_4857_);
return v_a_4858_;
}
else
{
lean_object* v_a_4859_; size_t v___x_4860_; size_t v___x_4861_; 
v_a_4859_ = lean_ctor_get(v___x_4857_, 0);
lean_inc(v_a_4859_);
lean_dec_ref(v___x_4857_);
v___x_4860_ = ((size_t)1ULL);
v___x_4861_ = lean_usize_add(v_i_4853_, v___x_4860_);
v_i_4853_ = v___x_4861_;
v_b_4854_ = v_a_4859_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__0_spec__1___boxed(lean_object* v_as_4863_, lean_object* v_sz_4864_, lean_object* v_i_4865_, lean_object* v_b_4866_){
_start:
{
size_t v_sz_boxed_4867_; size_t v_i_boxed_4868_; lean_object* v_res_4869_; 
v_sz_boxed_4867_ = lean_unbox_usize(v_sz_4864_);
lean_dec(v_sz_4864_);
v_i_boxed_4868_ = lean_unbox_usize(v_i_4865_);
lean_dec(v_i_4865_);
v_res_4869_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__0_spec__1(v_as_4863_, v_sz_boxed_4867_, v_i_boxed_4868_, v_b_4866_);
lean_dec_ref(v_as_4863_);
return v_res_4869_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__0(lean_object* v_m_4870_, lean_object* v_l_4871_){
_start:
{
lean_object* v_buckets_4872_; size_t v_sz_4873_; size_t v___x_4874_; lean_object* v___x_4875_; 
v_buckets_4872_ = lean_ctor_get(v_l_4871_, 1);
v_sz_4873_ = lean_array_size(v_buckets_4872_);
v___x_4874_ = ((size_t)0ULL);
v___x_4875_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__0_spec__1(v_buckets_4872_, v_sz_4873_, v___x_4874_, v_m_4870_);
return v___x_4875_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__0___boxed(lean_object* v_m_4876_, lean_object* v_l_4877_){
_start:
{
lean_object* v_res_4878_; 
v_res_4878_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__0(v_m_4876_, v_l_4877_);
lean_dec_ref(v_l_4877_);
return v_res_4878_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__1(lean_object* v_a_4879_, lean_object* v_a_4880_){
_start:
{
if (lean_obj_tag(v_a_4879_) == 0)
{
lean_object* v___x_4881_; 
v___x_4881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4881_, 0, v_a_4880_);
return v___x_4881_;
}
else
{
lean_object* v_key_4882_; lean_object* v_value_4883_; lean_object* v_tail_4884_; lean_object* v_r_4885_; 
v_key_4882_ = lean_ctor_get(v_a_4879_, 0);
lean_inc(v_key_4882_);
v_value_4883_ = lean_ctor_get(v_a_4879_, 1);
lean_inc(v_value_4883_);
v_tail_4884_ = lean_ctor_get(v_a_4879_, 2);
lean_inc(v_tail_4884_);
lean_dec_ref(v_a_4879_);
v_r_4885_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode_spec__1___redArg(v_a_4880_, v_key_4882_, v_value_4883_);
v_a_4879_ = v_tail_4884_;
v_a_4880_ = v_r_4885_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__2(lean_object* v_as_4887_, size_t v_sz_4888_, size_t v_i_4889_, lean_object* v_b_4890_){
_start:
{
uint8_t v___x_4891_; 
v___x_4891_ = lean_usize_dec_lt(v_i_4889_, v_sz_4888_);
if (v___x_4891_ == 0)
{
return v_b_4890_;
}
else
{
lean_object* v_a_4892_; lean_object* v___x_4893_; 
v_a_4892_ = lean_array_uget_borrowed(v_as_4887_, v_i_4889_);
lean_inc(v_a_4892_);
v___x_4893_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__1(v_a_4892_, v_b_4890_);
if (lean_obj_tag(v___x_4893_) == 0)
{
lean_object* v_a_4894_; 
v_a_4894_ = lean_ctor_get(v___x_4893_, 0);
lean_inc(v_a_4894_);
lean_dec_ref(v___x_4893_);
return v_a_4894_;
}
else
{
lean_object* v_a_4895_; size_t v___x_4896_; size_t v___x_4897_; 
v_a_4895_ = lean_ctor_get(v___x_4893_, 0);
lean_inc(v_a_4895_);
lean_dec_ref(v___x_4893_);
v___x_4896_ = ((size_t)1ULL);
v___x_4897_ = lean_usize_add(v_i_4889_, v___x_4896_);
v_i_4889_ = v___x_4897_;
v_b_4890_ = v_a_4895_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__2___boxed(lean_object* v_as_4899_, lean_object* v_sz_4900_, lean_object* v_i_4901_, lean_object* v_b_4902_){
_start:
{
size_t v_sz_boxed_4903_; size_t v_i_boxed_4904_; lean_object* v_res_4905_; 
v_sz_boxed_4903_ = lean_unbox_usize(v_sz_4900_);
lean_dec(v_sz_4900_);
v_i_boxed_4904_ = lean_unbox_usize(v_i_4901_);
lean_dec(v_i_4901_);
v_res_4905_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__2(v_as_4899_, v_sz_boxed_4903_, v_i_boxed_4904_, v_b_4902_);
lean_dec_ref(v_as_4899_);
return v_res_4905_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__8(lean_object* v_as_4906_, size_t v_i_4907_, size_t v_stop_4908_, lean_object* v_b_4909_){
_start:
{
lean_object* v___y_4911_; lean_object* v___y_4912_; uint8_t v___x_4917_; 
v___x_4917_ = lean_usize_dec_eq(v_i_4907_, v_stop_4908_);
if (v___x_4917_ == 0)
{
lean_object* v___x_4918_; lean_object* v_snd_4919_; lean_object* v_vars_4920_; lean_object* v_borrows_4921_; lean_object* v_vars_4922_; lean_object* v_borrows_4923_; lean_object* v___y_4925_; lean_object* v_size_4934_; lean_object* v_buckets_4935_; lean_object* v_size_4936_; uint8_t v___x_4937_; 
v___x_4918_ = lean_array_uget_borrowed(v_as_4906_, v_i_4907_);
v_snd_4919_ = lean_ctor_get(v___x_4918_, 1);
v_vars_4920_ = lean_ctor_get(v_b_4909_, 0);
lean_inc_ref(v_vars_4920_);
v_borrows_4921_ = lean_ctor_get(v_b_4909_, 1);
lean_inc_ref(v_borrows_4921_);
lean_dec_ref(v_b_4909_);
v_vars_4922_ = lean_ctor_get(v_snd_4919_, 0);
v_borrows_4923_ = lean_ctor_get(v_snd_4919_, 1);
v_size_4934_ = lean_ctor_get(v_vars_4920_, 0);
v_buckets_4935_ = lean_ctor_get(v_vars_4920_, 1);
v_size_4936_ = lean_ctor_get(v_vars_4922_, 0);
v___x_4937_ = lean_nat_dec_le(v_size_4934_, v_size_4936_);
if (v___x_4937_ == 0)
{
lean_object* v___x_4938_; 
v___x_4938_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__0(v_vars_4920_, v_vars_4922_);
v___y_4925_ = v___x_4938_;
goto v___jp_4924_;
}
else
{
size_t v_sz_4939_; size_t v___x_4940_; lean_object* v___x_4941_; 
lean_inc_ref(v_buckets_4935_);
lean_dec_ref(v_vars_4920_);
v_sz_4939_ = lean_array_size(v_buckets_4935_);
v___x_4940_ = ((size_t)0ULL);
lean_inc_ref(v_vars_4922_);
v___x_4941_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__2(v_buckets_4935_, v_sz_4939_, v___x_4940_, v_vars_4922_);
lean_dec_ref(v_buckets_4935_);
v___y_4925_ = v___x_4941_;
goto v___jp_4924_;
}
v___jp_4924_:
{
lean_object* v_size_4926_; lean_object* v_buckets_4927_; lean_object* v_size_4928_; uint8_t v___x_4929_; 
v_size_4926_ = lean_ctor_get(v_borrows_4921_, 0);
v_buckets_4927_ = lean_ctor_get(v_borrows_4921_, 1);
v_size_4928_ = lean_ctor_get(v_borrows_4923_, 0);
v___x_4929_ = lean_nat_dec_le(v_size_4926_, v_size_4928_);
if (v___x_4929_ == 0)
{
lean_object* v___x_4930_; 
v___x_4930_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__0(v_borrows_4921_, v_borrows_4923_);
v___y_4911_ = v___y_4925_;
v___y_4912_ = v___x_4930_;
goto v___jp_4910_;
}
else
{
size_t v_sz_4931_; size_t v___x_4932_; lean_object* v___x_4933_; 
lean_inc_ref(v_buckets_4927_);
lean_dec_ref(v_borrows_4921_);
v_sz_4931_ = lean_array_size(v_buckets_4927_);
v___x_4932_ = ((size_t)0ULL);
lean_inc_ref(v_borrows_4923_);
v___x_4933_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__2(v_buckets_4927_, v_sz_4931_, v___x_4932_, v_borrows_4923_);
lean_dec_ref(v_buckets_4927_);
v___y_4911_ = v___y_4925_;
v___y_4912_ = v___x_4933_;
goto v___jp_4910_;
}
}
}
else
{
return v_b_4909_;
}
v___jp_4910_:
{
lean_object* v___x_4913_; size_t v___x_4914_; size_t v___x_4915_; 
v___x_4913_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4913_, 0, v___y_4911_);
lean_ctor_set(v___x_4913_, 1, v___y_4912_);
v___x_4914_ = ((size_t)1ULL);
v___x_4915_ = lean_usize_add(v_i_4907_, v___x_4914_);
v_i_4907_ = v___x_4915_;
v_b_4909_ = v___x_4913_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__8___boxed(lean_object* v_as_4942_, lean_object* v_i_4943_, lean_object* v_stop_4944_, lean_object* v_b_4945_){
_start:
{
size_t v_i_boxed_4946_; size_t v_stop_boxed_4947_; lean_object* v_res_4948_; 
v_i_boxed_4946_ = lean_unbox_usize(v_i_4943_);
lean_dec(v_i_4943_);
v_stop_boxed_4947_ = lean_unbox_usize(v_stop_4944_);
lean_dec(v_stop_4944_);
v_res_4948_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__8(v_as_4942_, v_i_boxed_4946_, v_stop_boxed_4947_, v_b_4945_);
lean_dec_ref(v_as_4942_);
return v_res_4948_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__3(lean_object* v_as_4949_, size_t v_i_4950_, size_t v_stop_4951_, lean_object* v_b_4952_){
_start:
{
uint8_t v___x_4953_; 
v___x_4953_ = lean_usize_dec_eq(v_i_4950_, v_stop_4951_);
if (v___x_4953_ == 0)
{
lean_object* v_borrowedParams_4954_; lean_object* v_derivedValMap_4955_; lean_object* v_varMap_4956_; lean_object* v_jpLiveVarMap_4957_; lean_object* v_idx_4958_; lean_object* v___x_4960_; uint8_t v_isShared_4961_; uint8_t v_isSharedCheck_4977_; 
v_borrowedParams_4954_ = lean_ctor_get(v_b_4952_, 0);
v_derivedValMap_4955_ = lean_ctor_get(v_b_4952_, 1);
v_varMap_4956_ = lean_ctor_get(v_b_4952_, 2);
v_jpLiveVarMap_4957_ = lean_ctor_get(v_b_4952_, 3);
v_idx_4958_ = lean_ctor_get(v_b_4952_, 4);
v_isSharedCheck_4977_ = !lean_is_exclusive(v_b_4952_);
if (v_isSharedCheck_4977_ == 0)
{
v___x_4960_ = v_b_4952_;
v_isShared_4961_ = v_isSharedCheck_4977_;
goto v_resetjp_4959_;
}
else
{
lean_inc(v_idx_4958_);
lean_inc(v_jpLiveVarMap_4957_);
lean_inc(v_varMap_4956_);
lean_inc(v_derivedValMap_4955_);
lean_inc(v_borrowedParams_4954_);
lean_dec(v_b_4952_);
v___x_4960_ = lean_box(0);
v_isShared_4961_ = v_isSharedCheck_4977_;
goto v_resetjp_4959_;
}
v_resetjp_4959_:
{
lean_object* v___x_4962_; lean_object* v_fvarId_4963_; lean_object* v_type_4964_; uint8_t v___x_4965_; uint8_t v___x_4966_; lean_object* v___x_4967_; lean_object* v_varMap_4968_; lean_object* v___x_4969_; lean_object* v___x_4970_; lean_object* v___x_4972_; 
v___x_4962_ = lean_array_uget_borrowed(v_as_4949_, v_i_4950_);
v_fvarId_4963_ = lean_ctor_get(v___x_4962_, 0);
v_type_4964_ = lean_ctor_get(v___x_4962_, 2);
v___x_4965_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isPossibleRef(v_type_4964_);
v___x_4966_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isDefiniteRef(v_type_4964_);
lean_inc(v_idx_4958_);
v___x_4967_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_4967_, 0, v_idx_4958_);
lean_ctor_set_uint8(v___x_4967_, sizeof(void*)*1, v___x_4965_);
lean_ctor_set_uint8(v___x_4967_, sizeof(void*)*1 + 1, v___x_4966_);
lean_ctor_set_uint8(v___x_4967_, sizeof(void*)*1 + 2, v___x_4953_);
lean_inc(v_fvarId_4963_);
v_varMap_4968_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_4963_, v___x_4967_, v_varMap_4956_);
v___x_4969_ = lean_unsigned_to_nat(1u);
v___x_4970_ = lean_nat_add(v_idx_4958_, v___x_4969_);
lean_dec(v_idx_4958_);
if (v_isShared_4961_ == 0)
{
lean_ctor_set(v___x_4960_, 4, v___x_4970_);
lean_ctor_set(v___x_4960_, 2, v_varMap_4968_);
v___x_4972_ = v___x_4960_;
goto v_reusejp_4971_;
}
else
{
lean_object* v_reuseFailAlloc_4976_; 
v_reuseFailAlloc_4976_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4976_, 0, v_borrowedParams_4954_);
lean_ctor_set(v_reuseFailAlloc_4976_, 1, v_derivedValMap_4955_);
lean_ctor_set(v_reuseFailAlloc_4976_, 2, v_varMap_4968_);
lean_ctor_set(v_reuseFailAlloc_4976_, 3, v_jpLiveVarMap_4957_);
lean_ctor_set(v_reuseFailAlloc_4976_, 4, v___x_4970_);
v___x_4972_ = v_reuseFailAlloc_4976_;
goto v_reusejp_4971_;
}
v_reusejp_4971_:
{
size_t v___x_4973_; size_t v___x_4974_; 
v___x_4973_ = ((size_t)1ULL);
v___x_4974_ = lean_usize_add(v_i_4950_, v___x_4973_);
v_i_4950_ = v___x_4974_;
v_b_4952_ = v___x_4972_;
goto _start;
}
}
}
else
{
return v_b_4952_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__3___boxed(lean_object* v_as_4978_, lean_object* v_i_4979_, lean_object* v_stop_4980_, lean_object* v_b_4981_){
_start:
{
size_t v_i_boxed_4982_; size_t v_stop_boxed_4983_; lean_object* v_res_4984_; 
v_i_boxed_4982_ = lean_unbox_usize(v_i_4979_);
lean_dec(v_i_4979_);
v_stop_boxed_4983_ = lean_unbox_usize(v_stop_4980_);
lean_dec(v_stop_4980_);
v_res_4984_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__3(v_as_4978_, v_i_boxed_4982_, v_stop_boxed_4983_, v_b_4981_);
lean_dec_ref(v_as_4978_);
return v_res_4984_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__5___redArg(lean_object* v_t_4985_, lean_object* v_k_4986_){
_start:
{
if (lean_obj_tag(v_t_4985_) == 0)
{
lean_object* v_k_4987_; lean_object* v_v_4988_; lean_object* v_l_4989_; lean_object* v_r_4990_; uint8_t v___x_4991_; 
v_k_4987_ = lean_ctor_get(v_t_4985_, 1);
v_v_4988_ = lean_ctor_get(v_t_4985_, 2);
v_l_4989_ = lean_ctor_get(v_t_4985_, 3);
v_r_4990_ = lean_ctor_get(v_t_4985_, 4);
v___x_4991_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_4986_, v_k_4987_);
switch(v___x_4991_)
{
case 0:
{
v_t_4985_ = v_l_4989_;
goto _start;
}
case 1:
{
lean_object* v___x_4993_; 
lean_inc(v_v_4988_);
v___x_4993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4993_, 0, v_v_4988_);
return v___x_4993_;
}
default: 
{
v_t_4985_ = v_r_4990_;
goto _start;
}
}
}
else
{
lean_object* v___x_4995_; 
v___x_4995_ = lean_box(0);
return v___x_4995_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__5___redArg___boxed(lean_object* v_t_4996_, lean_object* v_k_4997_){
_start:
{
lean_object* v_res_4998_; 
v_res_4998_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__5___redArg(v_t_4996_, v_k_4997_);
lean_dec(v_k_4997_);
lean_dec(v_t_4996_);
return v_res_4998_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__7(lean_object* v_discr_4999_, size_t v_sz_5000_, size_t v_i_5001_, lean_object* v_bs_5002_, lean_object* v___y_5003_, lean_object* v___y_5004_, lean_object* v___y_5005_, lean_object* v___y_5006_, lean_object* v___y_5007_, lean_object* v___y_5008_){
_start:
{
uint8_t v___x_5010_; 
v___x_5010_ = lean_usize_dec_lt(v_i_5001_, v_sz_5000_);
if (v___x_5010_ == 0)
{
lean_object* v___x_5011_; 
lean_dec_ref(v___y_5003_);
lean_dec(v_discr_4999_);
v___x_5011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5011_, 0, v_bs_5002_);
return v___x_5011_;
}
else
{
lean_object* v_v_5012_; lean_object* v_fst_5013_; lean_object* v_snd_5014_; lean_object* v___x_5015_; lean_object* v_bs_x27_5016_; lean_object* v_a_5018_; 
v_v_5012_ = lean_array_uget_borrowed(v_bs_5002_, v_i_5001_);
v_fst_5013_ = lean_ctor_get(v_v_5012_, 0);
lean_inc(v_fst_5013_);
v_snd_5014_ = lean_ctor_get(v_v_5012_, 1);
lean_inc(v_snd_5014_);
v___x_5015_ = lean_unsigned_to_nat(0u);
v_bs_x27_5016_ = lean_array_uset(v_bs_5002_, v_i_5001_, v___x_5015_);
if (lean_obj_tag(v_fst_5013_) == 1)
{
lean_object* v_info_5023_; lean_object* v_code_5024_; lean_object* v_borrowedParams_5025_; lean_object* v_derivedValMap_5026_; lean_object* v_varMap_5027_; lean_object* v_jpLiveVarMap_5028_; lean_object* v_idx_5029_; lean_object* v___y_5031_; lean_object* v___x_5046_; 
v_info_5023_ = lean_ctor_get(v_fst_5013_, 0);
v_code_5024_ = lean_ctor_get(v_fst_5013_, 1);
v_borrowedParams_5025_ = lean_ctor_get(v___y_5003_, 0);
v_derivedValMap_5026_ = lean_ctor_get(v___y_5003_, 1);
v_varMap_5027_ = lean_ctor_get(v___y_5003_, 2);
v_jpLiveVarMap_5028_ = lean_ctor_get(v___y_5003_, 3);
v_idx_5029_ = lean_ctor_get(v___y_5003_, 4);
v___x_5046_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__5___redArg(v_varMap_5027_, v_discr_4999_);
if (lean_obj_tag(v___x_5046_) == 0)
{
lean_inc(v_varMap_5027_);
v___y_5031_ = v_varMap_5027_;
goto v___jp_5030_;
}
else
{
lean_object* v_val_5047_; uint8_t v_persistent_5048_; lean_object* v___x_5050_; uint8_t v_isShared_5051_; uint8_t v_isSharedCheck_5061_; 
v_val_5047_ = lean_ctor_get(v___x_5046_, 0);
lean_inc(v_val_5047_);
lean_dec_ref(v___x_5046_);
v_persistent_5048_ = lean_ctor_get_uint8(v_val_5047_, sizeof(void*)*1 + 2);
v_isSharedCheck_5061_ = !lean_is_exclusive(v_val_5047_);
if (v_isSharedCheck_5061_ == 0)
{
lean_object* v_unused_5062_; 
v_unused_5062_ = lean_ctor_get(v_val_5047_, 0);
lean_dec(v_unused_5062_);
v___x_5050_ = v_val_5047_;
v_isShared_5051_ = v_isSharedCheck_5061_;
goto v_resetjp_5049_;
}
else
{
lean_dec(v_val_5047_);
v___x_5050_ = lean_box(0);
v_isShared_5051_ = v_isSharedCheck_5061_;
goto v_resetjp_5049_;
}
v_resetjp_5049_:
{
lean_object* v___x_5052_; uint8_t v___x_5053_; uint8_t v___x_5054_; lean_object* v___x_5055_; lean_object* v___x_5056_; lean_object* v___x_5058_; 
v___x_5052_ = l_Lean_Compiler_LCNF_CtorInfo_type(v_info_5023_);
v___x_5053_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isPossibleRef(v___x_5052_);
v___x_5054_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isDefiniteRef(v___x_5052_);
lean_dec_ref(v___x_5052_);
v___x_5055_ = lean_unsigned_to_nat(1u);
v___x_5056_ = lean_nat_add(v_idx_5029_, v___x_5055_);
if (v_isShared_5051_ == 0)
{
lean_ctor_set(v___x_5050_, 0, v___x_5056_);
v___x_5058_ = v___x_5050_;
goto v_reusejp_5057_;
}
else
{
lean_object* v_reuseFailAlloc_5060_; 
v_reuseFailAlloc_5060_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v_reuseFailAlloc_5060_, 0, v___x_5056_);
lean_ctor_set_uint8(v_reuseFailAlloc_5060_, sizeof(void*)*1 + 2, v_persistent_5048_);
v___x_5058_ = v_reuseFailAlloc_5060_;
goto v_reusejp_5057_;
}
v_reusejp_5057_:
{
lean_object* v___x_5059_; 
lean_ctor_set_uint8(v___x_5058_, sizeof(void*)*1, v___x_5053_);
lean_ctor_set_uint8(v___x_5058_, sizeof(void*)*1 + 1, v___x_5054_);
lean_inc(v_varMap_5027_);
lean_inc(v_discr_4999_);
v___x_5059_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_discr_4999_, v___x_5058_, v_varMap_5027_);
v___y_5031_ = v___x_5059_;
goto v___jp_5030_;
}
}
}
v___jp_5030_:
{
lean_object* v___x_5032_; lean_object* v___x_5033_; lean_object* v___x_5034_; lean_object* v___x_5035_; 
v___x_5032_ = lean_unsigned_to_nat(1u);
v___x_5033_ = lean_nat_add(v_idx_5029_, v___x_5032_);
lean_inc(v_jpLiveVarMap_5028_);
lean_inc_ref(v_derivedValMap_5026_);
lean_inc_ref(v_borrowedParams_5025_);
v___x_5034_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5034_, 0, v_borrowedParams_5025_);
lean_ctor_set(v___x_5034_, 1, v_derivedValMap_5026_);
lean_ctor_set(v___x_5034_, 2, v___y_5031_);
lean_ctor_set(v___x_5034_, 3, v_jpLiveVarMap_5028_);
lean_ctor_set(v___x_5034_, 4, v___x_5033_);
lean_inc_ref(v_code_5024_);
v___x_5035_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt(v_snd_5014_, v_code_5024_, v___x_5034_, v___y_5004_, v___y_5005_, v___y_5006_, v___y_5007_, v___y_5008_);
lean_dec_ref(v___x_5034_);
lean_dec(v_snd_5014_);
if (lean_obj_tag(v___x_5035_) == 0)
{
lean_object* v_a_5036_; lean_object* v___x_5037_; 
v_a_5036_ = lean_ctor_get(v___x_5035_, 0);
lean_inc(v_a_5036_);
lean_dec_ref(v___x_5035_);
v___x_5037_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_fst_5013_, v_a_5036_);
v_a_5018_ = v___x_5037_;
goto v___jp_5017_;
}
else
{
lean_object* v_a_5038_; lean_object* v___x_5040_; uint8_t v_isShared_5041_; uint8_t v_isSharedCheck_5045_; 
lean_dec_ref(v_fst_5013_);
lean_dec_ref(v_bs_x27_5016_);
lean_dec_ref(v___y_5003_);
lean_dec(v_discr_4999_);
v_a_5038_ = lean_ctor_get(v___x_5035_, 0);
v_isSharedCheck_5045_ = !lean_is_exclusive(v___x_5035_);
if (v_isSharedCheck_5045_ == 0)
{
v___x_5040_ = v___x_5035_;
v_isShared_5041_ = v_isSharedCheck_5045_;
goto v_resetjp_5039_;
}
else
{
lean_inc(v_a_5038_);
lean_dec(v___x_5035_);
v___x_5040_ = lean_box(0);
v_isShared_5041_ = v_isSharedCheck_5045_;
goto v_resetjp_5039_;
}
v_resetjp_5039_:
{
lean_object* v___x_5043_; 
if (v_isShared_5041_ == 0)
{
v___x_5043_ = v___x_5040_;
goto v_reusejp_5042_;
}
else
{
lean_object* v_reuseFailAlloc_5044_; 
v_reuseFailAlloc_5044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5044_, 0, v_a_5038_);
v___x_5043_ = v_reuseFailAlloc_5044_;
goto v_reusejp_5042_;
}
v_reusejp_5042_:
{
return v___x_5043_;
}
}
}
}
}
else
{
lean_object* v_code_5063_; lean_object* v___x_5064_; 
v_code_5063_ = lean_ctor_get(v_fst_5013_, 0);
lean_inc_ref(v_code_5063_);
v___x_5064_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt(v_snd_5014_, v_code_5063_, v___y_5003_, v___y_5004_, v___y_5005_, v___y_5006_, v___y_5007_, v___y_5008_);
lean_dec(v_snd_5014_);
if (lean_obj_tag(v___x_5064_) == 0)
{
lean_object* v_a_5065_; lean_object* v___x_5066_; 
v_a_5065_ = lean_ctor_get(v___x_5064_, 0);
lean_inc(v_a_5065_);
lean_dec_ref(v___x_5064_);
v___x_5066_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_fst_5013_, v_a_5065_);
v_a_5018_ = v___x_5066_;
goto v___jp_5017_;
}
else
{
lean_object* v_a_5067_; lean_object* v___x_5069_; uint8_t v_isShared_5070_; uint8_t v_isSharedCheck_5074_; 
lean_dec_ref(v_fst_5013_);
lean_dec_ref(v_bs_x27_5016_);
lean_dec_ref(v___y_5003_);
lean_dec(v_discr_4999_);
v_a_5067_ = lean_ctor_get(v___x_5064_, 0);
v_isSharedCheck_5074_ = !lean_is_exclusive(v___x_5064_);
if (v_isSharedCheck_5074_ == 0)
{
v___x_5069_ = v___x_5064_;
v_isShared_5070_ = v_isSharedCheck_5074_;
goto v_resetjp_5068_;
}
else
{
lean_inc(v_a_5067_);
lean_dec(v___x_5064_);
v___x_5069_ = lean_box(0);
v_isShared_5070_ = v_isSharedCheck_5074_;
goto v_resetjp_5068_;
}
v_resetjp_5068_:
{
lean_object* v___x_5072_; 
if (v_isShared_5070_ == 0)
{
v___x_5072_ = v___x_5069_;
goto v_reusejp_5071_;
}
else
{
lean_object* v_reuseFailAlloc_5073_; 
v_reuseFailAlloc_5073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5073_, 0, v_a_5067_);
v___x_5072_ = v_reuseFailAlloc_5073_;
goto v_reusejp_5071_;
}
v_reusejp_5071_:
{
return v___x_5072_;
}
}
}
}
v___jp_5017_:
{
size_t v___x_5019_; size_t v___x_5020_; lean_object* v___x_5021_; 
v___x_5019_ = ((size_t)1ULL);
v___x_5020_ = lean_usize_add(v_i_5001_, v___x_5019_);
v___x_5021_ = lean_array_uset(v_bs_x27_5016_, v_i_5001_, v_a_5018_);
v_i_5001_ = v___x_5020_;
v_bs_5002_ = v___x_5021_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__7___boxed(lean_object* v_discr_5075_, lean_object* v_sz_5076_, lean_object* v_i_5077_, lean_object* v_bs_5078_, lean_object* v___y_5079_, lean_object* v___y_5080_, lean_object* v___y_5081_, lean_object* v___y_5082_, lean_object* v___y_5083_, lean_object* v___y_5084_, lean_object* v___y_5085_){
_start:
{
size_t v_sz_boxed_5086_; size_t v_i_boxed_5087_; lean_object* v_res_5088_; 
v_sz_boxed_5086_ = lean_unbox_usize(v_sz_5076_);
lean_dec(v_sz_5076_);
v_i_boxed_5087_ = lean_unbox_usize(v_i_5077_);
lean_dec(v_i_5077_);
v_res_5088_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__7(v_discr_5075_, v_sz_boxed_5086_, v_i_boxed_5087_, v_bs_5078_, v___y_5079_, v___y_5080_, v___y_5081_, v___y_5082_, v___y_5083_, v___y_5084_);
lean_dec(v___y_5084_);
lean_dec_ref(v___y_5083_);
lean_dec(v___y_5082_);
lean_dec_ref(v___y_5081_);
lean_dec(v___y_5080_);
return v_res_5088_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc___closed__1(void){
_start:
{
lean_object* v___x_5090_; lean_object* v___x_5091_; lean_object* v___x_5092_; lean_object* v___x_5093_; lean_object* v___x_5094_; lean_object* v___x_5095_; 
v___x_5090_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode___closed__6));
v___x_5091_ = lean_unsigned_to_nat(59u);
v___x_5092_ = lean_unsigned_to_nat(662u);
v___x_5093_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc___closed__0));
v___x_5094_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collectCode___closed__4));
v___x_5095_ = l_mkPanicMessageWithDecl(v___x_5094_, v___x_5093_, v___x_5092_, v___x_5091_, v___x_5090_);
return v___x_5095_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc(lean_object* v_code_5096_, lean_object* v_a_5097_, lean_object* v_a_5098_, lean_object* v_a_5099_, lean_object* v_a_5100_, lean_object* v_a_5101_, lean_object* v_a_5102_){
_start:
{
lean_object* v___y_5105_; lean_object* v___y_5106_; uint8_t v___y_5107_; 
switch(lean_obj_tag(v_code_5096_))
{
case 0:
{
lean_object* v_decl_5111_; lean_object* v_k_5112_; lean_object* v_fvarId_5113_; lean_object* v_type_5114_; lean_object* v_value_5115_; lean_object* v_borrowedParams_5116_; lean_object* v_derivedValMap_5117_; lean_object* v_varMap_5118_; lean_object* v_jpLiveVarMap_5119_; lean_object* v_idx_5120_; uint8_t v___x_5121_; uint8_t v___x_5122_; uint8_t v___x_5123_; lean_object* v_varInfo_5124_; lean_object* v___x_5125_; lean_object* v___x_5126_; lean_object* v___x_5127_; lean_object* v___x_5128_; lean_object* v___x_5129_; 
v_decl_5111_ = lean_ctor_get(v_code_5096_, 0);
lean_inc_ref(v_decl_5111_);
v_k_5112_ = lean_ctor_get(v_code_5096_, 1);
v_fvarId_5113_ = lean_ctor_get(v_decl_5111_, 0);
v_type_5114_ = lean_ctor_get(v_decl_5111_, 2);
v_value_5115_ = lean_ctor_get(v_decl_5111_, 3);
v_borrowedParams_5116_ = lean_ctor_get(v_a_5097_, 0);
lean_inc_ref(v_borrowedParams_5116_);
v_derivedValMap_5117_ = lean_ctor_get(v_a_5097_, 1);
lean_inc_ref(v_derivedValMap_5117_);
v_varMap_5118_ = lean_ctor_get(v_a_5097_, 2);
lean_inc(v_varMap_5118_);
v_jpLiveVarMap_5119_ = lean_ctor_get(v_a_5097_, 3);
lean_inc(v_jpLiveVarMap_5119_);
v_idx_5120_ = lean_ctor_get(v_a_5097_, 4);
lean_inc(v_idx_5120_);
lean_dec_ref(v_a_5097_);
v___x_5121_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isPossibleRef(v_type_5114_);
v___x_5122_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isDefiniteRef(v_type_5114_);
v___x_5123_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetValue_isPersistent(v_value_5115_);
lean_inc(v_idx_5120_);
v_varInfo_5124_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v_varInfo_5124_, 0, v_idx_5120_);
lean_ctor_set_uint8(v_varInfo_5124_, sizeof(void*)*1, v___x_5121_);
lean_ctor_set_uint8(v_varInfo_5124_, sizeof(void*)*1 + 1, v___x_5122_);
lean_ctor_set_uint8(v_varInfo_5124_, sizeof(void*)*1 + 2, v___x_5123_);
lean_inc(v_fvarId_5113_);
v___x_5125_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_5113_, v_varInfo_5124_, v_varMap_5118_);
v___x_5126_ = lean_unsigned_to_nat(1u);
v___x_5127_ = lean_nat_add(v_idx_5120_, v___x_5126_);
lean_dec(v_idx_5120_);
v___x_5128_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5128_, 0, v_borrowedParams_5116_);
lean_ctor_set(v___x_5128_, 1, v_derivedValMap_5117_);
lean_ctor_set(v___x_5128_, 2, v___x_5125_);
lean_ctor_set(v___x_5128_, 3, v_jpLiveVarMap_5119_);
lean_ctor_set(v___x_5128_, 4, v___x_5127_);
lean_inc_ref(v___x_5128_);
lean_inc_ref(v_k_5112_);
v___x_5129_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc(v_k_5112_, v___x_5128_, v_a_5098_, v_a_5099_, v_a_5100_, v_a_5101_, v_a_5102_);
if (lean_obj_tag(v___x_5129_) == 0)
{
lean_object* v_a_5130_; lean_object* v___x_5131_; 
v_a_5130_ = lean_ctor_get(v___x_5129_, 0);
lean_inc(v_a_5130_);
lean_dec_ref(v___x_5129_);
v___x_5131_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc(v_code_5096_, v_decl_5111_, v_a_5130_, v___x_5128_, v_a_5098_, v_a_5099_, v_a_5100_, v_a_5101_, v_a_5102_);
lean_dec_ref(v___x_5128_);
return v___x_5131_;
}
else
{
lean_dec_ref(v___x_5128_);
lean_dec_ref(v_code_5096_);
lean_dec_ref(v_decl_5111_);
return v___x_5129_;
}
}
case 2:
{
lean_object* v_decl_5132_; lean_object* v_k_5133_; lean_object* v_fst_5135_; lean_object* v_snd_5136_; lean_object* v_params_5153_; lean_object* v_type_5154_; lean_object* v_value_5155_; uint8_t v___x_5156_; lean_object* v___x_5157_; lean_object* v___x_5158_; uint8_t v___x_5159_; 
v_decl_5132_ = lean_ctor_get(v_code_5096_, 0);
v_k_5133_ = lean_ctor_get(v_code_5096_, 1);
v_params_5153_ = lean_ctor_get(v_decl_5132_, 2);
v_type_5154_ = lean_ctor_get(v_decl_5132_, 3);
v_value_5155_ = lean_ctor_get(v_decl_5132_, 4);
v___x_5156_ = 1;
v___x_5157_ = lean_unsigned_to_nat(0u);
v___x_5158_ = lean_array_get_size(v_params_5153_);
v___x_5159_ = lean_nat_dec_lt(v___x_5157_, v___x_5158_);
if (v___x_5159_ == 0)
{
lean_object* v___x_5160_; lean_object* v___x_5161_; lean_object* v___x_5162_; lean_object* v___x_5163_; lean_object* v___x_5164_; 
v___x_5160_ = lean_st_ref_get(v_a_5098_);
v___x_5161_ = lean_st_ref_take(v_a_5098_);
lean_dec(v___x_5161_);
v___x_5162_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__0, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__0_once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__0);
v___x_5163_ = lean_st_ref_set(v_a_5098_, v___x_5162_);
lean_inc_ref(v_a_5097_);
lean_inc_ref(v_value_5155_);
v___x_5164_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc(v_value_5155_, v_a_5097_, v_a_5098_, v_a_5099_, v_a_5100_, v_a_5101_, v_a_5102_);
if (lean_obj_tag(v___x_5164_) == 0)
{
lean_object* v_a_5165_; lean_object* v___x_5166_; 
v_a_5165_ = lean_ctor_get(v___x_5164_, 0);
lean_inc(v_a_5165_);
lean_dec_ref(v___x_5164_);
v___x_5166_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams(v_params_5153_, v_a_5165_, v_a_5097_, v_a_5098_, v_a_5099_, v_a_5100_, v_a_5101_, v_a_5102_);
if (lean_obj_tag(v___x_5166_) == 0)
{
lean_object* v_a_5167_; lean_object* v___x_5168_; 
v_a_5167_ = lean_ctor_get(v___x_5166_, 0);
lean_inc(v_a_5167_);
lean_dec_ref(v___x_5166_);
lean_inc_ref(v_params_5153_);
lean_inc_ref(v_type_5154_);
lean_inc_ref(v_decl_5132_);
v___x_5168_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_5156_, v_decl_5132_, v_type_5154_, v_params_5153_, v_a_5167_, v_a_5100_);
if (lean_obj_tag(v___x_5168_) == 0)
{
lean_object* v_a_5169_; lean_object* v___x_5170_; lean_object* v___x_5171_; lean_object* v___x_5172_; 
v_a_5169_ = lean_ctor_get(v___x_5168_, 0);
lean_inc(v_a_5169_);
lean_dec_ref(v___x_5168_);
v___x_5170_ = lean_st_ref_get(v_a_5098_);
v___x_5171_ = lean_st_ref_take(v_a_5098_);
lean_dec(v___x_5171_);
v___x_5172_ = lean_st_ref_set(v_a_5098_, v___x_5160_);
v_fst_5135_ = v_a_5169_;
v_snd_5136_ = v___x_5170_;
goto v___jp_5134_;
}
else
{
lean_object* v_a_5173_; lean_object* v___x_5175_; uint8_t v_isShared_5176_; uint8_t v_isSharedCheck_5180_; 
lean_dec(v___x_5160_);
lean_dec_ref(v_code_5096_);
lean_dec_ref(v_a_5097_);
v_a_5173_ = lean_ctor_get(v___x_5168_, 0);
v_isSharedCheck_5180_ = !lean_is_exclusive(v___x_5168_);
if (v_isSharedCheck_5180_ == 0)
{
v___x_5175_ = v___x_5168_;
v_isShared_5176_ = v_isSharedCheck_5180_;
goto v_resetjp_5174_;
}
else
{
lean_inc(v_a_5173_);
lean_dec(v___x_5168_);
v___x_5175_ = lean_box(0);
v_isShared_5176_ = v_isSharedCheck_5180_;
goto v_resetjp_5174_;
}
v_resetjp_5174_:
{
lean_object* v___x_5178_; 
if (v_isShared_5176_ == 0)
{
v___x_5178_ = v___x_5175_;
goto v_reusejp_5177_;
}
else
{
lean_object* v_reuseFailAlloc_5179_; 
v_reuseFailAlloc_5179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5179_, 0, v_a_5173_);
v___x_5178_ = v_reuseFailAlloc_5179_;
goto v_reusejp_5177_;
}
v_reusejp_5177_:
{
return v___x_5178_;
}
}
}
}
else
{
lean_dec(v___x_5160_);
lean_dec_ref(v_code_5096_);
lean_dec_ref(v_a_5097_);
return v___x_5166_;
}
}
else
{
lean_dec(v___x_5160_);
lean_dec_ref(v_code_5096_);
lean_dec_ref(v_a_5097_);
return v___x_5164_;
}
}
else
{
uint8_t v___x_5181_; 
v___x_5181_ = lean_nat_dec_le(v___x_5158_, v___x_5158_);
if (v___x_5181_ == 0)
{
if (v___x_5159_ == 0)
{
lean_object* v___x_5182_; lean_object* v___x_5183_; lean_object* v___x_5184_; lean_object* v___x_5185_; lean_object* v___x_5186_; 
v___x_5182_ = lean_st_ref_get(v_a_5098_);
v___x_5183_ = lean_st_ref_take(v_a_5098_);
lean_dec(v___x_5183_);
v___x_5184_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__0, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__0_once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__0);
v___x_5185_ = lean_st_ref_set(v_a_5098_, v___x_5184_);
lean_inc_ref(v_a_5097_);
lean_inc_ref(v_value_5155_);
v___x_5186_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc(v_value_5155_, v_a_5097_, v_a_5098_, v_a_5099_, v_a_5100_, v_a_5101_, v_a_5102_);
if (lean_obj_tag(v___x_5186_) == 0)
{
lean_object* v_a_5187_; lean_object* v___x_5188_; 
v_a_5187_ = lean_ctor_get(v___x_5186_, 0);
lean_inc(v_a_5187_);
lean_dec_ref(v___x_5186_);
lean_inc_ref(v_type_5154_);
lean_inc_ref(v_decl_5132_);
lean_inc_ref(v_params_5153_);
v___x_5188_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc___lam__0(v_params_5153_, v___x_5156_, v_decl_5132_, v_type_5154_, v_a_5187_, v_a_5097_, v_a_5098_, v_a_5099_, v_a_5100_, v_a_5101_, v_a_5102_);
if (lean_obj_tag(v___x_5188_) == 0)
{
lean_object* v_a_5189_; lean_object* v___x_5190_; lean_object* v___x_5191_; lean_object* v___x_5192_; 
v_a_5189_ = lean_ctor_get(v___x_5188_, 0);
lean_inc(v_a_5189_);
lean_dec_ref(v___x_5188_);
v___x_5190_ = lean_st_ref_get(v_a_5098_);
v___x_5191_ = lean_st_ref_take(v_a_5098_);
lean_dec(v___x_5191_);
v___x_5192_ = lean_st_ref_set(v_a_5098_, v___x_5182_);
v_fst_5135_ = v_a_5189_;
v_snd_5136_ = v___x_5190_;
goto v___jp_5134_;
}
else
{
lean_object* v_a_5193_; lean_object* v___x_5195_; uint8_t v_isShared_5196_; uint8_t v_isSharedCheck_5200_; 
lean_dec(v___x_5182_);
lean_dec_ref(v_code_5096_);
lean_dec_ref(v_a_5097_);
v_a_5193_ = lean_ctor_get(v___x_5188_, 0);
v_isSharedCheck_5200_ = !lean_is_exclusive(v___x_5188_);
if (v_isSharedCheck_5200_ == 0)
{
v___x_5195_ = v___x_5188_;
v_isShared_5196_ = v_isSharedCheck_5200_;
goto v_resetjp_5194_;
}
else
{
lean_inc(v_a_5193_);
lean_dec(v___x_5188_);
v___x_5195_ = lean_box(0);
v_isShared_5196_ = v_isSharedCheck_5200_;
goto v_resetjp_5194_;
}
v_resetjp_5194_:
{
lean_object* v___x_5198_; 
if (v_isShared_5196_ == 0)
{
v___x_5198_ = v___x_5195_;
goto v_reusejp_5197_;
}
else
{
lean_object* v_reuseFailAlloc_5199_; 
v_reuseFailAlloc_5199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5199_, 0, v_a_5193_);
v___x_5198_ = v_reuseFailAlloc_5199_;
goto v_reusejp_5197_;
}
v_reusejp_5197_:
{
return v___x_5198_;
}
}
}
}
else
{
lean_dec(v___x_5182_);
lean_dec_ref(v_code_5096_);
lean_dec_ref(v_a_5097_);
return v___x_5186_;
}
}
else
{
lean_object* v___x_5201_; lean_object* v___x_5202_; lean_object* v___x_5203_; lean_object* v___x_5204_; size_t v___x_5205_; size_t v___x_5206_; lean_object* v___x_5207_; lean_object* v___x_5208_; 
v___x_5201_ = lean_st_ref_get(v_a_5098_);
v___x_5202_ = lean_st_ref_take(v_a_5098_);
lean_dec(v___x_5202_);
v___x_5203_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__0, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__0_once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__0);
v___x_5204_ = lean_st_ref_set(v_a_5098_, v___x_5203_);
v___x_5205_ = ((size_t)0ULL);
v___x_5206_ = lean_usize_of_nat(v___x_5158_);
lean_inc_ref(v_a_5097_);
v___x_5207_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__3(v_params_5153_, v___x_5205_, v___x_5206_, v_a_5097_);
lean_inc_ref(v___x_5207_);
lean_inc_ref(v_value_5155_);
v___x_5208_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc(v_value_5155_, v___x_5207_, v_a_5098_, v_a_5099_, v_a_5100_, v_a_5101_, v_a_5102_);
if (lean_obj_tag(v___x_5208_) == 0)
{
lean_object* v_a_5209_; lean_object* v___x_5210_; 
v_a_5209_ = lean_ctor_get(v___x_5208_, 0);
lean_inc(v_a_5209_);
lean_dec_ref(v___x_5208_);
lean_inc_ref(v_type_5154_);
lean_inc_ref(v_decl_5132_);
lean_inc_ref(v_params_5153_);
v___x_5210_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc___lam__0(v_params_5153_, v___x_5156_, v_decl_5132_, v_type_5154_, v_a_5209_, v___x_5207_, v_a_5098_, v_a_5099_, v_a_5100_, v_a_5101_, v_a_5102_);
lean_dec_ref(v___x_5207_);
if (lean_obj_tag(v___x_5210_) == 0)
{
lean_object* v_a_5211_; lean_object* v___x_5212_; lean_object* v___x_5213_; lean_object* v___x_5214_; 
v_a_5211_ = lean_ctor_get(v___x_5210_, 0);
lean_inc(v_a_5211_);
lean_dec_ref(v___x_5210_);
v___x_5212_ = lean_st_ref_get(v_a_5098_);
v___x_5213_ = lean_st_ref_take(v_a_5098_);
lean_dec(v___x_5213_);
v___x_5214_ = lean_st_ref_set(v_a_5098_, v___x_5201_);
v_fst_5135_ = v_a_5211_;
v_snd_5136_ = v___x_5212_;
goto v___jp_5134_;
}
else
{
lean_object* v_a_5215_; lean_object* v___x_5217_; uint8_t v_isShared_5218_; uint8_t v_isSharedCheck_5222_; 
lean_dec(v___x_5201_);
lean_dec_ref(v_code_5096_);
lean_dec_ref(v_a_5097_);
v_a_5215_ = lean_ctor_get(v___x_5210_, 0);
v_isSharedCheck_5222_ = !lean_is_exclusive(v___x_5210_);
if (v_isSharedCheck_5222_ == 0)
{
v___x_5217_ = v___x_5210_;
v_isShared_5218_ = v_isSharedCheck_5222_;
goto v_resetjp_5216_;
}
else
{
lean_inc(v_a_5215_);
lean_dec(v___x_5210_);
v___x_5217_ = lean_box(0);
v_isShared_5218_ = v_isSharedCheck_5222_;
goto v_resetjp_5216_;
}
v_resetjp_5216_:
{
lean_object* v___x_5220_; 
if (v_isShared_5218_ == 0)
{
v___x_5220_ = v___x_5217_;
goto v_reusejp_5219_;
}
else
{
lean_object* v_reuseFailAlloc_5221_; 
v_reuseFailAlloc_5221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5221_, 0, v_a_5215_);
v___x_5220_ = v_reuseFailAlloc_5221_;
goto v_reusejp_5219_;
}
v_reusejp_5219_:
{
return v___x_5220_;
}
}
}
}
else
{
lean_dec_ref(v___x_5207_);
lean_dec(v___x_5201_);
lean_dec_ref(v_code_5096_);
lean_dec_ref(v_a_5097_);
return v___x_5208_;
}
}
}
else
{
lean_object* v___x_5223_; lean_object* v___x_5224_; lean_object* v___x_5225_; lean_object* v___x_5226_; size_t v___x_5227_; size_t v___x_5228_; lean_object* v___x_5229_; lean_object* v___x_5230_; 
v___x_5223_ = lean_st_ref_get(v_a_5098_);
v___x_5224_ = lean_st_ref_take(v_a_5098_);
lean_dec(v___x_5224_);
v___x_5225_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__0, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__0_once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__0);
v___x_5226_ = lean_st_ref_set(v_a_5098_, v___x_5225_);
v___x_5227_ = ((size_t)0ULL);
v___x_5228_ = lean_usize_of_nat(v___x_5158_);
lean_inc_ref(v_a_5097_);
v___x_5229_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__3(v_params_5153_, v___x_5227_, v___x_5228_, v_a_5097_);
lean_inc_ref(v___x_5229_);
lean_inc_ref(v_value_5155_);
v___x_5230_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc(v_value_5155_, v___x_5229_, v_a_5098_, v_a_5099_, v_a_5100_, v_a_5101_, v_a_5102_);
if (lean_obj_tag(v___x_5230_) == 0)
{
lean_object* v_a_5231_; lean_object* v___x_5232_; 
v_a_5231_ = lean_ctor_get(v___x_5230_, 0);
lean_inc(v_a_5231_);
lean_dec_ref(v___x_5230_);
lean_inc_ref(v_type_5154_);
lean_inc_ref(v_decl_5132_);
lean_inc_ref(v_params_5153_);
v___x_5232_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc___lam__0(v_params_5153_, v___x_5156_, v_decl_5132_, v_type_5154_, v_a_5231_, v___x_5229_, v_a_5098_, v_a_5099_, v_a_5100_, v_a_5101_, v_a_5102_);
lean_dec_ref(v___x_5229_);
if (lean_obj_tag(v___x_5232_) == 0)
{
lean_object* v_a_5233_; lean_object* v___x_5234_; lean_object* v___x_5235_; lean_object* v___x_5236_; 
v_a_5233_ = lean_ctor_get(v___x_5232_, 0);
lean_inc(v_a_5233_);
lean_dec_ref(v___x_5232_);
v___x_5234_ = lean_st_ref_get(v_a_5098_);
v___x_5235_ = lean_st_ref_take(v_a_5098_);
lean_dec(v___x_5235_);
v___x_5236_ = lean_st_ref_set(v_a_5098_, v___x_5223_);
v_fst_5135_ = v_a_5233_;
v_snd_5136_ = v___x_5234_;
goto v___jp_5134_;
}
else
{
lean_object* v_a_5237_; lean_object* v___x_5239_; uint8_t v_isShared_5240_; uint8_t v_isSharedCheck_5244_; 
lean_dec(v___x_5223_);
lean_dec_ref(v_code_5096_);
lean_dec_ref(v_a_5097_);
v_a_5237_ = lean_ctor_get(v___x_5232_, 0);
v_isSharedCheck_5244_ = !lean_is_exclusive(v___x_5232_);
if (v_isSharedCheck_5244_ == 0)
{
v___x_5239_ = v___x_5232_;
v_isShared_5240_ = v_isSharedCheck_5244_;
goto v_resetjp_5238_;
}
else
{
lean_inc(v_a_5237_);
lean_dec(v___x_5232_);
v___x_5239_ = lean_box(0);
v_isShared_5240_ = v_isSharedCheck_5244_;
goto v_resetjp_5238_;
}
v_resetjp_5238_:
{
lean_object* v___x_5242_; 
if (v_isShared_5240_ == 0)
{
v___x_5242_ = v___x_5239_;
goto v_reusejp_5241_;
}
else
{
lean_object* v_reuseFailAlloc_5243_; 
v_reuseFailAlloc_5243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5243_, 0, v_a_5237_);
v___x_5242_ = v_reuseFailAlloc_5243_;
goto v_reusejp_5241_;
}
v_reusejp_5241_:
{
return v___x_5242_;
}
}
}
}
else
{
lean_dec_ref(v___x_5229_);
lean_dec(v___x_5223_);
lean_dec_ref(v_code_5096_);
lean_dec_ref(v_a_5097_);
return v___x_5230_;
}
}
}
v___jp_5134_:
{
lean_object* v_fvarId_5137_; lean_object* v_borrowedParams_5138_; lean_object* v_derivedValMap_5139_; lean_object* v_varMap_5140_; lean_object* v_jpLiveVarMap_5141_; lean_object* v_idx_5142_; lean_object* v___x_5143_; lean_object* v___x_5144_; lean_object* v___x_5145_; 
v_fvarId_5137_ = lean_ctor_get(v_fst_5135_, 0);
v_borrowedParams_5138_ = lean_ctor_get(v_a_5097_, 0);
lean_inc_ref(v_borrowedParams_5138_);
v_derivedValMap_5139_ = lean_ctor_get(v_a_5097_, 1);
lean_inc_ref(v_derivedValMap_5139_);
v_varMap_5140_ = lean_ctor_get(v_a_5097_, 2);
lean_inc(v_varMap_5140_);
v_jpLiveVarMap_5141_ = lean_ctor_get(v_a_5097_, 3);
lean_inc(v_jpLiveVarMap_5141_);
v_idx_5142_ = lean_ctor_get(v_a_5097_, 4);
lean_inc(v_idx_5142_);
lean_dec_ref(v_a_5097_);
lean_inc(v_fvarId_5137_);
v___x_5143_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_5137_, v_snd_5136_, v_jpLiveVarMap_5141_);
v___x_5144_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5144_, 0, v_borrowedParams_5138_);
lean_ctor_set(v___x_5144_, 1, v_derivedValMap_5139_);
lean_ctor_set(v___x_5144_, 2, v_varMap_5140_);
lean_ctor_set(v___x_5144_, 3, v___x_5143_);
lean_ctor_set(v___x_5144_, 4, v_idx_5142_);
lean_inc_ref(v_k_5133_);
v___x_5145_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc(v_k_5133_, v___x_5144_, v_a_5098_, v_a_5099_, v_a_5100_, v_a_5101_, v_a_5102_);
if (lean_obj_tag(v___x_5145_) == 0)
{
lean_object* v_a_5146_; size_t v___x_5147_; size_t v___x_5148_; uint8_t v___x_5149_; 
v_a_5146_ = lean_ctor_get(v___x_5145_, 0);
lean_inc(v_a_5146_);
lean_dec_ref(v___x_5145_);
v___x_5147_ = lean_ptr_addr(v_k_5133_);
v___x_5148_ = lean_ptr_addr(v_a_5146_);
v___x_5149_ = lean_usize_dec_eq(v___x_5147_, v___x_5148_);
if (v___x_5149_ == 0)
{
v___y_5105_ = v_fst_5135_;
v___y_5106_ = v_a_5146_;
v___y_5107_ = v___x_5149_;
goto v___jp_5104_;
}
else
{
size_t v___x_5150_; size_t v___x_5151_; uint8_t v___x_5152_; 
v___x_5150_ = lean_ptr_addr(v_decl_5132_);
v___x_5151_ = lean_ptr_addr(v_fst_5135_);
v___x_5152_ = lean_usize_dec_eq(v___x_5150_, v___x_5151_);
v___y_5105_ = v_fst_5135_;
v___y_5106_ = v_a_5146_;
v___y_5107_ = v___x_5152_;
goto v___jp_5104_;
}
}
else
{
lean_dec_ref(v_fst_5135_);
lean_dec_ref(v_code_5096_);
return v___x_5145_;
}
}
}
case 3:
{
lean_object* v_fvarId_5245_; lean_object* v_args_5246_; lean_object* v___x_5247_; lean_object* v_jpLiveVarMap_5248_; lean_object* v___x_5249_; lean_object* v___x_5250_; lean_object* v___x_5251_; uint8_t v___x_5252_; lean_object* v___x_5253_; 
v_fvarId_5245_ = lean_ctor_get(v_code_5096_, 0);
v_args_5246_ = lean_ctor_get(v_code_5096_, 1);
lean_inc_ref(v_args_5246_);
v___x_5247_ = lean_st_ref_take(v_a_5098_);
lean_dec(v___x_5247_);
v_jpLiveVarMap_5248_ = lean_ctor_get(v_a_5097_, 3);
v___x_5249_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_instInhabitedLiveVars_default;
v___x_5250_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__0___redArg(v___x_5249_, v_jpLiveVarMap_5248_, v_fvarId_5245_);
v___x_5251_ = lean_st_ref_set(v_a_5098_, v___x_5250_);
v___x_5252_ = 1;
v___x_5253_ = l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(v___x_5252_, v_fvarId_5245_, v_a_5100_);
if (lean_obj_tag(v___x_5253_) == 0)
{
lean_object* v_a_5254_; lean_object* v___y_5256_; 
v_a_5254_ = lean_ctor_get(v___x_5253_, 0);
lean_inc(v_a_5254_);
lean_dec_ref(v___x_5253_);
if (lean_obj_tag(v_a_5254_) == 0)
{
lean_object* v___x_5277_; lean_object* v___x_5278_; 
v___x_5277_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__10, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__10_once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__10);
v___x_5278_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__4(v___x_5277_);
v___y_5256_ = v___x_5278_;
goto v___jp_5255_;
}
else
{
lean_object* v_val_5279_; 
v_val_5279_ = lean_ctor_get(v_a_5254_, 0);
lean_inc(v_val_5279_);
lean_dec_ref(v_a_5254_);
v___y_5256_ = v_val_5279_;
goto v___jp_5255_;
}
v___jp_5255_:
{
lean_object* v_params_5257_; lean_object* v___x_5258_; 
v_params_5257_ = lean_ctor_get(v___y_5256_, 2);
lean_inc_ref(v_params_5257_);
lean_dec_ref(v___y_5256_);
v___x_5258_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBefore(v_args_5246_, v_params_5257_, v_code_5096_, v_a_5097_, v_a_5098_, v_a_5099_, v_a_5100_, v_a_5101_, v_a_5102_);
if (lean_obj_tag(v___x_5258_) == 0)
{
lean_object* v_a_5259_; lean_object* v___x_5260_; 
v_a_5259_ = lean_ctor_get(v___x_5258_, 0);
lean_inc(v_a_5259_);
lean_dec_ref(v___x_5258_);
v___x_5260_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs(v_args_5246_, v_a_5097_, v_a_5098_, v_a_5099_, v_a_5100_, v_a_5101_, v_a_5102_);
lean_dec_ref(v_a_5097_);
lean_dec_ref(v_args_5246_);
if (lean_obj_tag(v___x_5260_) == 0)
{
lean_object* v___x_5262_; uint8_t v_isShared_5263_; uint8_t v_isSharedCheck_5267_; 
v_isSharedCheck_5267_ = !lean_is_exclusive(v___x_5260_);
if (v_isSharedCheck_5267_ == 0)
{
lean_object* v_unused_5268_; 
v_unused_5268_ = lean_ctor_get(v___x_5260_, 0);
lean_dec(v_unused_5268_);
v___x_5262_ = v___x_5260_;
v_isShared_5263_ = v_isSharedCheck_5267_;
goto v_resetjp_5261_;
}
else
{
lean_dec(v___x_5260_);
v___x_5262_ = lean_box(0);
v_isShared_5263_ = v_isSharedCheck_5267_;
goto v_resetjp_5261_;
}
v_resetjp_5261_:
{
lean_object* v___x_5265_; 
if (v_isShared_5263_ == 0)
{
lean_ctor_set(v___x_5262_, 0, v_a_5259_);
v___x_5265_ = v___x_5262_;
goto v_reusejp_5264_;
}
else
{
lean_object* v_reuseFailAlloc_5266_; 
v_reuseFailAlloc_5266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5266_, 0, v_a_5259_);
v___x_5265_ = v_reuseFailAlloc_5266_;
goto v_reusejp_5264_;
}
v_reusejp_5264_:
{
return v___x_5265_;
}
}
}
else
{
lean_object* v_a_5269_; lean_object* v___x_5271_; uint8_t v_isShared_5272_; uint8_t v_isSharedCheck_5276_; 
lean_dec(v_a_5259_);
v_a_5269_ = lean_ctor_get(v___x_5260_, 0);
v_isSharedCheck_5276_ = !lean_is_exclusive(v___x_5260_);
if (v_isSharedCheck_5276_ == 0)
{
v___x_5271_ = v___x_5260_;
v_isShared_5272_ = v_isSharedCheck_5276_;
goto v_resetjp_5270_;
}
else
{
lean_inc(v_a_5269_);
lean_dec(v___x_5260_);
v___x_5271_ = lean_box(0);
v_isShared_5272_ = v_isSharedCheck_5276_;
goto v_resetjp_5270_;
}
v_resetjp_5270_:
{
lean_object* v___x_5274_; 
if (v_isShared_5272_ == 0)
{
v___x_5274_ = v___x_5271_;
goto v_reusejp_5273_;
}
else
{
lean_object* v_reuseFailAlloc_5275_; 
v_reuseFailAlloc_5275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5275_, 0, v_a_5269_);
v___x_5274_ = v_reuseFailAlloc_5275_;
goto v_reusejp_5273_;
}
v_reusejp_5273_:
{
return v___x_5274_;
}
}
}
}
else
{
lean_dec_ref(v_args_5246_);
lean_dec_ref(v_a_5097_);
return v___x_5258_;
}
}
}
else
{
lean_object* v_a_5280_; lean_object* v___x_5282_; uint8_t v_isShared_5283_; uint8_t v_isSharedCheck_5287_; 
lean_dec_ref(v_args_5246_);
lean_dec_ref(v_code_5096_);
lean_dec_ref(v_a_5097_);
v_a_5280_ = lean_ctor_get(v___x_5253_, 0);
v_isSharedCheck_5287_ = !lean_is_exclusive(v___x_5253_);
if (v_isSharedCheck_5287_ == 0)
{
v___x_5282_ = v___x_5253_;
v_isShared_5283_ = v_isSharedCheck_5287_;
goto v_resetjp_5281_;
}
else
{
lean_inc(v_a_5280_);
lean_dec(v___x_5253_);
v___x_5282_ = lean_box(0);
v_isShared_5283_ = v_isSharedCheck_5287_;
goto v_resetjp_5281_;
}
v_resetjp_5281_:
{
lean_object* v___x_5285_; 
if (v_isShared_5283_ == 0)
{
v___x_5285_ = v___x_5282_;
goto v_reusejp_5284_;
}
else
{
lean_object* v_reuseFailAlloc_5286_; 
v_reuseFailAlloc_5286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5286_, 0, v_a_5280_);
v___x_5285_ = v_reuseFailAlloc_5286_;
goto v_reusejp_5284_;
}
v_reusejp_5284_:
{
return v___x_5285_;
}
}
}
}
case 4:
{
lean_object* v_cases_5288_; lean_object* v_typeName_5289_; lean_object* v_resultType_5290_; lean_object* v_discr_5291_; lean_object* v_alts_5292_; size_t v_sz_5293_; size_t v___x_5294_; lean_object* v___x_5295_; 
v_cases_5288_ = lean_ctor_get(v_code_5096_, 0);
v_typeName_5289_ = lean_ctor_get(v_cases_5288_, 0);
v_resultType_5290_ = lean_ctor_get(v_cases_5288_, 1);
v_discr_5291_ = lean_ctor_get(v_cases_5288_, 2);
v_alts_5292_ = lean_ctor_get(v_cases_5288_, 3);
v_sz_5293_ = lean_array_size(v_alts_5292_);
v___x_5294_ = ((size_t)0ULL);
lean_inc_ref(v_a_5097_);
lean_inc_ref(v_alts_5292_);
lean_inc_ref(v_cases_5288_);
v___x_5295_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__6(v_cases_5288_, v_sz_5293_, v___x_5294_, v_alts_5292_, v_a_5097_, v_a_5098_, v_a_5099_, v_a_5100_, v_a_5101_, v_a_5102_);
if (lean_obj_tag(v___x_5295_) == 0)
{
lean_object* v_a_5296_; lean_object* v___y_5298_; lean_object* v___x_5343_; lean_object* v___x_5344_; lean_object* v___x_5345_; uint8_t v___x_5346_; 
v_a_5296_ = lean_ctor_get(v___x_5295_, 0);
lean_inc(v_a_5296_);
lean_dec_ref(v___x_5295_);
v___x_5343_ = lean_unsigned_to_nat(0u);
v___x_5344_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__0, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__0_once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__0);
v___x_5345_ = lean_array_get_size(v_a_5296_);
v___x_5346_ = lean_nat_dec_lt(v___x_5343_, v___x_5345_);
if (v___x_5346_ == 0)
{
v___y_5298_ = v___x_5344_;
goto v___jp_5297_;
}
else
{
uint8_t v___x_5347_; 
v___x_5347_ = lean_nat_dec_le(v___x_5345_, v___x_5345_);
if (v___x_5347_ == 0)
{
if (v___x_5346_ == 0)
{
v___y_5298_ = v___x_5344_;
goto v___jp_5297_;
}
else
{
size_t v___x_5348_; lean_object* v___x_5349_; 
v___x_5348_ = lean_usize_of_nat(v___x_5345_);
v___x_5349_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__8(v_a_5296_, v___x_5294_, v___x_5348_, v___x_5344_);
v___y_5298_ = v___x_5349_;
goto v___jp_5297_;
}
}
else
{
size_t v___x_5350_; lean_object* v___x_5351_; 
v___x_5350_ = lean_usize_of_nat(v___x_5345_);
v___x_5351_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__8(v_a_5296_, v___x_5294_, v___x_5350_, v___x_5344_);
v___y_5298_ = v___x_5351_;
goto v___jp_5297_;
}
}
v___jp_5297_:
{
lean_object* v___x_5299_; lean_object* v___x_5300_; lean_object* v___x_5301_; 
v___x_5299_ = lean_st_ref_take(v_a_5098_);
lean_dec(v___x_5299_);
v___x_5300_ = lean_st_ref_set(v_a_5098_, v___y_5298_);
lean_inc(v_discr_5291_);
v___x_5301_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___redArg(v_discr_5291_, v_a_5097_, v_a_5098_);
if (lean_obj_tag(v___x_5301_) == 0)
{
size_t v_sz_5302_; lean_object* v___x_5303_; 
lean_dec_ref(v___x_5301_);
v_sz_5302_ = lean_array_size(v_a_5296_);
lean_inc(v_discr_5291_);
v___x_5303_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__7(v_discr_5291_, v_sz_5302_, v___x_5294_, v_a_5296_, v_a_5097_, v_a_5098_, v_a_5099_, v_a_5100_, v_a_5101_, v_a_5102_);
if (lean_obj_tag(v___x_5303_) == 0)
{
lean_object* v_a_5304_; lean_object* v___x_5306_; uint8_t v_isShared_5307_; uint8_t v_isSharedCheck_5326_; 
v_a_5304_ = lean_ctor_get(v___x_5303_, 0);
v_isSharedCheck_5326_ = !lean_is_exclusive(v___x_5303_);
if (v_isSharedCheck_5326_ == 0)
{
v___x_5306_ = v___x_5303_;
v_isShared_5307_ = v_isSharedCheck_5326_;
goto v_resetjp_5305_;
}
else
{
lean_inc(v_a_5304_);
lean_dec(v___x_5303_);
v___x_5306_ = lean_box(0);
v_isShared_5307_ = v_isSharedCheck_5326_;
goto v_resetjp_5305_;
}
v_resetjp_5305_:
{
size_t v___x_5308_; size_t v___x_5309_; uint8_t v___x_5310_; 
v___x_5308_ = lean_ptr_addr(v_alts_5292_);
v___x_5309_ = lean_ptr_addr(v_a_5304_);
v___x_5310_ = lean_usize_dec_eq(v___x_5308_, v___x_5309_);
if (v___x_5310_ == 0)
{
lean_object* v___x_5312_; uint8_t v_isShared_5313_; uint8_t v_isSharedCheck_5321_; 
lean_inc(v_discr_5291_);
lean_inc_ref(v_resultType_5290_);
lean_inc(v_typeName_5289_);
v_isSharedCheck_5321_ = !lean_is_exclusive(v_code_5096_);
if (v_isSharedCheck_5321_ == 0)
{
lean_object* v_unused_5322_; 
v_unused_5322_ = lean_ctor_get(v_code_5096_, 0);
lean_dec(v_unused_5322_);
v___x_5312_ = v_code_5096_;
v_isShared_5313_ = v_isSharedCheck_5321_;
goto v_resetjp_5311_;
}
else
{
lean_dec(v_code_5096_);
v___x_5312_ = lean_box(0);
v_isShared_5313_ = v_isSharedCheck_5321_;
goto v_resetjp_5311_;
}
v_resetjp_5311_:
{
lean_object* v___x_5314_; lean_object* v___x_5316_; 
v___x_5314_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5314_, 0, v_typeName_5289_);
lean_ctor_set(v___x_5314_, 1, v_resultType_5290_);
lean_ctor_set(v___x_5314_, 2, v_discr_5291_);
lean_ctor_set(v___x_5314_, 3, v_a_5304_);
if (v_isShared_5313_ == 0)
{
lean_ctor_set(v___x_5312_, 0, v___x_5314_);
v___x_5316_ = v___x_5312_;
goto v_reusejp_5315_;
}
else
{
lean_object* v_reuseFailAlloc_5320_; 
v_reuseFailAlloc_5320_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5320_, 0, v___x_5314_);
v___x_5316_ = v_reuseFailAlloc_5320_;
goto v_reusejp_5315_;
}
v_reusejp_5315_:
{
lean_object* v___x_5318_; 
if (v_isShared_5307_ == 0)
{
lean_ctor_set(v___x_5306_, 0, v___x_5316_);
v___x_5318_ = v___x_5306_;
goto v_reusejp_5317_;
}
else
{
lean_object* v_reuseFailAlloc_5319_; 
v_reuseFailAlloc_5319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5319_, 0, v___x_5316_);
v___x_5318_ = v_reuseFailAlloc_5319_;
goto v_reusejp_5317_;
}
v_reusejp_5317_:
{
return v___x_5318_;
}
}
}
}
else
{
lean_object* v___x_5324_; 
lean_dec(v_a_5304_);
if (v_isShared_5307_ == 0)
{
lean_ctor_set(v___x_5306_, 0, v_code_5096_);
v___x_5324_ = v___x_5306_;
goto v_reusejp_5323_;
}
else
{
lean_object* v_reuseFailAlloc_5325_; 
v_reuseFailAlloc_5325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5325_, 0, v_code_5096_);
v___x_5324_ = v_reuseFailAlloc_5325_;
goto v_reusejp_5323_;
}
v_reusejp_5323_:
{
return v___x_5324_;
}
}
}
}
else
{
lean_object* v_a_5327_; lean_object* v___x_5329_; uint8_t v_isShared_5330_; uint8_t v_isSharedCheck_5334_; 
lean_dec_ref(v_code_5096_);
v_a_5327_ = lean_ctor_get(v___x_5303_, 0);
v_isSharedCheck_5334_ = !lean_is_exclusive(v___x_5303_);
if (v_isSharedCheck_5334_ == 0)
{
v___x_5329_ = v___x_5303_;
v_isShared_5330_ = v_isSharedCheck_5334_;
goto v_resetjp_5328_;
}
else
{
lean_inc(v_a_5327_);
lean_dec(v___x_5303_);
v___x_5329_ = lean_box(0);
v_isShared_5330_ = v_isSharedCheck_5334_;
goto v_resetjp_5328_;
}
v_resetjp_5328_:
{
lean_object* v___x_5332_; 
if (v_isShared_5330_ == 0)
{
v___x_5332_ = v___x_5329_;
goto v_reusejp_5331_;
}
else
{
lean_object* v_reuseFailAlloc_5333_; 
v_reuseFailAlloc_5333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5333_, 0, v_a_5327_);
v___x_5332_ = v_reuseFailAlloc_5333_;
goto v_reusejp_5331_;
}
v_reusejp_5331_:
{
return v___x_5332_;
}
}
}
}
else
{
lean_object* v_a_5335_; lean_object* v___x_5337_; uint8_t v_isShared_5338_; uint8_t v_isSharedCheck_5342_; 
lean_dec(v_a_5296_);
lean_dec_ref(v_code_5096_);
lean_dec_ref(v_a_5097_);
v_a_5335_ = lean_ctor_get(v___x_5301_, 0);
v_isSharedCheck_5342_ = !lean_is_exclusive(v___x_5301_);
if (v_isSharedCheck_5342_ == 0)
{
v___x_5337_ = v___x_5301_;
v_isShared_5338_ = v_isSharedCheck_5342_;
goto v_resetjp_5336_;
}
else
{
lean_inc(v_a_5335_);
lean_dec(v___x_5301_);
v___x_5337_ = lean_box(0);
v_isShared_5338_ = v_isSharedCheck_5342_;
goto v_resetjp_5336_;
}
v_resetjp_5336_:
{
lean_object* v___x_5340_; 
if (v_isShared_5338_ == 0)
{
v___x_5340_ = v___x_5337_;
goto v_reusejp_5339_;
}
else
{
lean_object* v_reuseFailAlloc_5341_; 
v_reuseFailAlloc_5341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5341_, 0, v_a_5335_);
v___x_5340_ = v_reuseFailAlloc_5341_;
goto v_reusejp_5339_;
}
v_reusejp_5339_:
{
return v___x_5340_;
}
}
}
}
}
else
{
lean_object* v_a_5352_; lean_object* v___x_5354_; uint8_t v_isShared_5355_; uint8_t v_isSharedCheck_5359_; 
lean_dec_ref(v_code_5096_);
lean_dec_ref(v_a_5097_);
v_a_5352_ = lean_ctor_get(v___x_5295_, 0);
v_isSharedCheck_5359_ = !lean_is_exclusive(v___x_5295_);
if (v_isSharedCheck_5359_ == 0)
{
v___x_5354_ = v___x_5295_;
v_isShared_5355_ = v_isSharedCheck_5359_;
goto v_resetjp_5353_;
}
else
{
lean_inc(v_a_5352_);
lean_dec(v___x_5295_);
v___x_5354_ = lean_box(0);
v_isShared_5355_ = v_isSharedCheck_5359_;
goto v_resetjp_5353_;
}
v_resetjp_5353_:
{
lean_object* v___x_5357_; 
if (v_isShared_5355_ == 0)
{
v___x_5357_ = v___x_5354_;
goto v_reusejp_5356_;
}
else
{
lean_object* v_reuseFailAlloc_5358_; 
v_reuseFailAlloc_5358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5358_, 0, v_a_5352_);
v___x_5357_ = v_reuseFailAlloc_5358_;
goto v_reusejp_5356_;
}
v_reusejp_5356_:
{
return v___x_5357_;
}
}
}
}
case 5:
{
lean_object* v_fvarId_5360_; lean_object* v___x_5361_; 
v_fvarId_5360_ = lean_ctor_get(v_code_5096_, 0);
v___x_5361_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_setRetLiveVars___redArg(v_a_5097_, v_a_5098_);
if (lean_obj_tag(v___x_5361_) == 0)
{
lean_object* v_varMap_5362_; lean_object* v___x_5363_; lean_object* v___x_5364_; lean_object* v___x_5365_; 
lean_dec_ref(v___x_5361_);
v_varMap_5362_ = lean_ctor_get(v_a_5097_, 2);
v___x_5363_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_instInhabitedVarInfo_default));
v___x_5364_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__0___redArg(v___x_5363_, v_varMap_5362_, v_fvarId_5360_);
lean_inc(v_fvarId_5360_);
v___x_5365_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___redArg(v_fvarId_5360_, v_a_5097_, v_a_5098_);
lean_dec_ref(v_a_5097_);
if (lean_obj_tag(v___x_5365_) == 0)
{
lean_object* v___x_5367_; uint8_t v_isShared_5368_; uint8_t v_isSharedCheck_5389_; 
v_isSharedCheck_5389_ = !lean_is_exclusive(v___x_5365_);
if (v_isSharedCheck_5389_ == 0)
{
lean_object* v_unused_5390_; 
v_unused_5390_ = lean_ctor_get(v___x_5365_, 0);
lean_dec(v_unused_5390_);
v___x_5367_ = v___x_5365_;
v_isShared_5368_ = v_isSharedCheck_5389_;
goto v_resetjp_5366_;
}
else
{
lean_dec(v___x_5365_);
v___x_5367_ = lean_box(0);
v_isShared_5368_ = v_isSharedCheck_5389_;
goto v_resetjp_5366_;
}
v_resetjp_5366_:
{
lean_object* v___x_5369_; uint8_t v_isPossibleRef_5370_; 
v___x_5369_ = lean_st_ref_get(v_a_5098_);
v_isPossibleRef_5370_ = lean_ctor_get_uint8(v___x_5364_, sizeof(void*)*1);
if (v_isPossibleRef_5370_ == 0)
{
lean_object* v___x_5372_; 
lean_dec(v___x_5369_);
lean_dec(v___x_5364_);
if (v_isShared_5368_ == 0)
{
lean_ctor_set(v___x_5367_, 0, v_code_5096_);
v___x_5372_ = v___x_5367_;
goto v_reusejp_5371_;
}
else
{
lean_object* v_reuseFailAlloc_5373_; 
v_reuseFailAlloc_5373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5373_, 0, v_code_5096_);
v___x_5372_ = v_reuseFailAlloc_5373_;
goto v_reusejp_5371_;
}
v_reusejp_5371_:
{
return v___x_5372_;
}
}
else
{
uint8_t v_isDefiniteRef_5374_; uint8_t v_persistent_5375_; lean_object* v_borrows_5376_; uint8_t v___x_5377_; 
v_isDefiniteRef_5374_ = lean_ctor_get_uint8(v___x_5364_, sizeof(void*)*1 + 1);
v_persistent_5375_ = lean_ctor_get_uint8(v___x_5364_, sizeof(void*)*1 + 2);
lean_dec(v___x_5364_);
v_borrows_5376_ = lean_ctor_get(v___x_5369_, 1);
lean_inc_ref(v_borrows_5376_);
lean_dec(v___x_5369_);
v___x_5377_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_isAccessible_spec__0___redArg(v_borrows_5376_, v_fvarId_5360_);
lean_dec_ref(v_borrows_5376_);
if (v___x_5377_ == 0)
{
lean_object* v___x_5379_; 
if (v_isShared_5368_ == 0)
{
lean_ctor_set(v___x_5367_, 0, v_code_5096_);
v___x_5379_ = v___x_5367_;
goto v_reusejp_5378_;
}
else
{
lean_object* v_reuseFailAlloc_5380_; 
v_reuseFailAlloc_5380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5380_, 0, v_code_5096_);
v___x_5379_ = v_reuseFailAlloc_5380_;
goto v_reusejp_5378_;
}
v_reusejp_5378_:
{
return v___x_5379_;
}
}
else
{
lean_object* v___x_5381_; uint8_t v___y_5383_; 
lean_inc(v_fvarId_5360_);
v___x_5381_ = lean_unsigned_to_nat(1u);
if (v_isDefiniteRef_5374_ == 0)
{
v___y_5383_ = v___x_5377_;
goto v___jp_5382_;
}
else
{
uint8_t v___x_5388_; 
v___x_5388_ = 0;
v___y_5383_ = v___x_5388_;
goto v___jp_5382_;
}
v___jp_5382_:
{
lean_object* v___x_5384_; lean_object* v___x_5386_; 
v___x_5384_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v___x_5384_, 0, v_fvarId_5360_);
lean_ctor_set(v___x_5384_, 1, v___x_5381_);
lean_ctor_set(v___x_5384_, 2, v_code_5096_);
lean_ctor_set_uint8(v___x_5384_, sizeof(void*)*3, v___y_5383_);
lean_ctor_set_uint8(v___x_5384_, sizeof(void*)*3 + 1, v_persistent_5375_);
if (v_isShared_5368_ == 0)
{
lean_ctor_set(v___x_5367_, 0, v___x_5384_);
v___x_5386_ = v___x_5367_;
goto v_reusejp_5385_;
}
else
{
lean_object* v_reuseFailAlloc_5387_; 
v_reuseFailAlloc_5387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5387_, 0, v___x_5384_);
v___x_5386_ = v_reuseFailAlloc_5387_;
goto v_reusejp_5385_;
}
v_reusejp_5385_:
{
return v___x_5386_;
}
}
}
}
}
}
else
{
lean_object* v_a_5391_; lean_object* v___x_5393_; uint8_t v_isShared_5394_; uint8_t v_isSharedCheck_5398_; 
lean_dec(v___x_5364_);
lean_dec_ref(v_code_5096_);
v_a_5391_ = lean_ctor_get(v___x_5365_, 0);
v_isSharedCheck_5398_ = !lean_is_exclusive(v___x_5365_);
if (v_isSharedCheck_5398_ == 0)
{
v___x_5393_ = v___x_5365_;
v_isShared_5394_ = v_isSharedCheck_5398_;
goto v_resetjp_5392_;
}
else
{
lean_inc(v_a_5391_);
lean_dec(v___x_5365_);
v___x_5393_ = lean_box(0);
v_isShared_5394_ = v_isSharedCheck_5398_;
goto v_resetjp_5392_;
}
v_resetjp_5392_:
{
lean_object* v___x_5396_; 
if (v_isShared_5394_ == 0)
{
v___x_5396_ = v___x_5393_;
goto v_reusejp_5395_;
}
else
{
lean_object* v_reuseFailAlloc_5397_; 
v_reuseFailAlloc_5397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5397_, 0, v_a_5391_);
v___x_5396_ = v_reuseFailAlloc_5397_;
goto v_reusejp_5395_;
}
v_reusejp_5395_:
{
return v___x_5396_;
}
}
}
}
else
{
lean_object* v_a_5399_; lean_object* v___x_5401_; uint8_t v_isShared_5402_; uint8_t v_isSharedCheck_5406_; 
lean_dec_ref(v_code_5096_);
lean_dec_ref(v_a_5097_);
v_a_5399_ = lean_ctor_get(v___x_5361_, 0);
v_isSharedCheck_5406_ = !lean_is_exclusive(v___x_5361_);
if (v_isSharedCheck_5406_ == 0)
{
v___x_5401_ = v___x_5361_;
v_isShared_5402_ = v_isSharedCheck_5406_;
goto v_resetjp_5400_;
}
else
{
lean_inc(v_a_5399_);
lean_dec(v___x_5361_);
v___x_5401_ = lean_box(0);
v_isShared_5402_ = v_isSharedCheck_5406_;
goto v_resetjp_5400_;
}
v_resetjp_5400_:
{
lean_object* v___x_5404_; 
if (v_isShared_5402_ == 0)
{
v___x_5404_ = v___x_5401_;
goto v_reusejp_5403_;
}
else
{
lean_object* v_reuseFailAlloc_5405_; 
v_reuseFailAlloc_5405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5405_, 0, v_a_5399_);
v___x_5404_ = v_reuseFailAlloc_5405_;
goto v_reusejp_5403_;
}
v_reusejp_5403_:
{
return v___x_5404_;
}
}
}
}
case 6:
{
lean_object* v___x_5407_; 
v___x_5407_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_setRetLiveVars___redArg(v_a_5097_, v_a_5098_);
lean_dec_ref(v_a_5097_);
if (lean_obj_tag(v___x_5407_) == 0)
{
lean_object* v___x_5409_; uint8_t v_isShared_5410_; uint8_t v_isSharedCheck_5414_; 
v_isSharedCheck_5414_ = !lean_is_exclusive(v___x_5407_);
if (v_isSharedCheck_5414_ == 0)
{
lean_object* v_unused_5415_; 
v_unused_5415_ = lean_ctor_get(v___x_5407_, 0);
lean_dec(v_unused_5415_);
v___x_5409_ = v___x_5407_;
v_isShared_5410_ = v_isSharedCheck_5414_;
goto v_resetjp_5408_;
}
else
{
lean_dec(v___x_5407_);
v___x_5409_ = lean_box(0);
v_isShared_5410_ = v_isSharedCheck_5414_;
goto v_resetjp_5408_;
}
v_resetjp_5408_:
{
lean_object* v___x_5412_; 
if (v_isShared_5410_ == 0)
{
lean_ctor_set(v___x_5409_, 0, v_code_5096_);
v___x_5412_ = v___x_5409_;
goto v_reusejp_5411_;
}
else
{
lean_object* v_reuseFailAlloc_5413_; 
v_reuseFailAlloc_5413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5413_, 0, v_code_5096_);
v___x_5412_ = v_reuseFailAlloc_5413_;
goto v_reusejp_5411_;
}
v_reusejp_5411_:
{
return v___x_5412_;
}
}
}
else
{
lean_object* v_a_5416_; lean_object* v___x_5418_; uint8_t v_isShared_5419_; uint8_t v_isSharedCheck_5423_; 
lean_dec_ref(v_code_5096_);
v_a_5416_ = lean_ctor_get(v___x_5407_, 0);
v_isSharedCheck_5423_ = !lean_is_exclusive(v___x_5407_);
if (v_isSharedCheck_5423_ == 0)
{
v___x_5418_ = v___x_5407_;
v_isShared_5419_ = v_isSharedCheck_5423_;
goto v_resetjp_5417_;
}
else
{
lean_inc(v_a_5416_);
lean_dec(v___x_5407_);
v___x_5418_ = lean_box(0);
v_isShared_5419_ = v_isSharedCheck_5423_;
goto v_resetjp_5417_;
}
v_resetjp_5417_:
{
lean_object* v___x_5421_; 
if (v_isShared_5419_ == 0)
{
v___x_5421_ = v___x_5418_;
goto v_reusejp_5420_;
}
else
{
lean_object* v_reuseFailAlloc_5422_; 
v_reuseFailAlloc_5422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5422_, 0, v_a_5416_);
v___x_5421_ = v_reuseFailAlloc_5422_;
goto v_reusejp_5420_;
}
v_reusejp_5420_:
{
return v___x_5421_;
}
}
}
}
case 8:
{
lean_object* v_fvarId_5424_; lean_object* v_i_5425_; lean_object* v_y_5426_; lean_object* v_k_5427_; lean_object* v___x_5428_; 
v_fvarId_5424_ = lean_ctor_get(v_code_5096_, 0);
v_i_5425_ = lean_ctor_get(v_code_5096_, 1);
v_y_5426_ = lean_ctor_get(v_code_5096_, 2);
v_k_5427_ = lean_ctor_get(v_code_5096_, 3);
lean_inc_ref(v_a_5097_);
lean_inc_ref(v_k_5427_);
v___x_5428_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc(v_k_5427_, v_a_5097_, v_a_5098_, v_a_5099_, v_a_5100_, v_a_5101_, v_a_5102_);
if (lean_obj_tag(v___x_5428_) == 0)
{
lean_object* v_a_5429_; lean_object* v___x_5430_; 
v_a_5429_ = lean_ctor_get(v___x_5428_, 0);
lean_inc(v_a_5429_);
lean_dec_ref(v___x_5428_);
lean_inc(v_fvarId_5424_);
v___x_5430_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___redArg(v_fvarId_5424_, v_a_5097_, v_a_5098_);
lean_dec_ref(v_a_5097_);
if (lean_obj_tag(v___x_5430_) == 0)
{
lean_object* v___x_5432_; uint8_t v_isShared_5433_; uint8_t v_isSharedCheck_5454_; 
v_isSharedCheck_5454_ = !lean_is_exclusive(v___x_5430_);
if (v_isSharedCheck_5454_ == 0)
{
lean_object* v_unused_5455_; 
v_unused_5455_ = lean_ctor_get(v___x_5430_, 0);
lean_dec(v_unused_5455_);
v___x_5432_ = v___x_5430_;
v_isShared_5433_ = v_isSharedCheck_5454_;
goto v_resetjp_5431_;
}
else
{
lean_dec(v___x_5430_);
v___x_5432_ = lean_box(0);
v_isShared_5433_ = v_isSharedCheck_5454_;
goto v_resetjp_5431_;
}
v_resetjp_5431_:
{
size_t v___x_5434_; size_t v___x_5435_; uint8_t v___x_5436_; 
v___x_5434_ = lean_ptr_addr(v_k_5427_);
v___x_5435_ = lean_ptr_addr(v_a_5429_);
v___x_5436_ = lean_usize_dec_eq(v___x_5434_, v___x_5435_);
if (v___x_5436_ == 0)
{
lean_object* v___x_5438_; uint8_t v_isShared_5439_; uint8_t v_isSharedCheck_5446_; 
lean_inc(v_y_5426_);
lean_inc(v_i_5425_);
lean_inc(v_fvarId_5424_);
v_isSharedCheck_5446_ = !lean_is_exclusive(v_code_5096_);
if (v_isSharedCheck_5446_ == 0)
{
lean_object* v_unused_5447_; lean_object* v_unused_5448_; lean_object* v_unused_5449_; lean_object* v_unused_5450_; 
v_unused_5447_ = lean_ctor_get(v_code_5096_, 3);
lean_dec(v_unused_5447_);
v_unused_5448_ = lean_ctor_get(v_code_5096_, 2);
lean_dec(v_unused_5448_);
v_unused_5449_ = lean_ctor_get(v_code_5096_, 1);
lean_dec(v_unused_5449_);
v_unused_5450_ = lean_ctor_get(v_code_5096_, 0);
lean_dec(v_unused_5450_);
v___x_5438_ = v_code_5096_;
v_isShared_5439_ = v_isSharedCheck_5446_;
goto v_resetjp_5437_;
}
else
{
lean_dec(v_code_5096_);
v___x_5438_ = lean_box(0);
v_isShared_5439_ = v_isSharedCheck_5446_;
goto v_resetjp_5437_;
}
v_resetjp_5437_:
{
lean_object* v___x_5441_; 
if (v_isShared_5439_ == 0)
{
lean_ctor_set(v___x_5438_, 3, v_a_5429_);
v___x_5441_ = v___x_5438_;
goto v_reusejp_5440_;
}
else
{
lean_object* v_reuseFailAlloc_5445_; 
v_reuseFailAlloc_5445_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_5445_, 0, v_fvarId_5424_);
lean_ctor_set(v_reuseFailAlloc_5445_, 1, v_i_5425_);
lean_ctor_set(v_reuseFailAlloc_5445_, 2, v_y_5426_);
lean_ctor_set(v_reuseFailAlloc_5445_, 3, v_a_5429_);
v___x_5441_ = v_reuseFailAlloc_5445_;
goto v_reusejp_5440_;
}
v_reusejp_5440_:
{
lean_object* v___x_5443_; 
if (v_isShared_5433_ == 0)
{
lean_ctor_set(v___x_5432_, 0, v___x_5441_);
v___x_5443_ = v___x_5432_;
goto v_reusejp_5442_;
}
else
{
lean_object* v_reuseFailAlloc_5444_; 
v_reuseFailAlloc_5444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5444_, 0, v___x_5441_);
v___x_5443_ = v_reuseFailAlloc_5444_;
goto v_reusejp_5442_;
}
v_reusejp_5442_:
{
return v___x_5443_;
}
}
}
}
else
{
lean_object* v___x_5452_; 
lean_dec(v_a_5429_);
if (v_isShared_5433_ == 0)
{
lean_ctor_set(v___x_5432_, 0, v_code_5096_);
v___x_5452_ = v___x_5432_;
goto v_reusejp_5451_;
}
else
{
lean_object* v_reuseFailAlloc_5453_; 
v_reuseFailAlloc_5453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5453_, 0, v_code_5096_);
v___x_5452_ = v_reuseFailAlloc_5453_;
goto v_reusejp_5451_;
}
v_reusejp_5451_:
{
return v___x_5452_;
}
}
}
}
else
{
lean_object* v_a_5456_; lean_object* v___x_5458_; uint8_t v_isShared_5459_; uint8_t v_isSharedCheck_5463_; 
lean_dec(v_a_5429_);
lean_dec_ref(v_code_5096_);
v_a_5456_ = lean_ctor_get(v___x_5430_, 0);
v_isSharedCheck_5463_ = !lean_is_exclusive(v___x_5430_);
if (v_isSharedCheck_5463_ == 0)
{
v___x_5458_ = v___x_5430_;
v_isShared_5459_ = v_isSharedCheck_5463_;
goto v_resetjp_5457_;
}
else
{
lean_inc(v_a_5456_);
lean_dec(v___x_5430_);
v___x_5458_ = lean_box(0);
v_isShared_5459_ = v_isSharedCheck_5463_;
goto v_resetjp_5457_;
}
v_resetjp_5457_:
{
lean_object* v___x_5461_; 
if (v_isShared_5459_ == 0)
{
v___x_5461_ = v___x_5458_;
goto v_reusejp_5460_;
}
else
{
lean_object* v_reuseFailAlloc_5462_; 
v_reuseFailAlloc_5462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5462_, 0, v_a_5456_);
v___x_5461_ = v_reuseFailAlloc_5462_;
goto v_reusejp_5460_;
}
v_reusejp_5460_:
{
return v___x_5461_;
}
}
}
}
else
{
lean_dec_ref(v_code_5096_);
lean_dec_ref(v_a_5097_);
return v___x_5428_;
}
}
case 9:
{
lean_object* v_fvarId_5464_; lean_object* v_i_5465_; lean_object* v_offset_5466_; lean_object* v_y_5467_; lean_object* v_ty_5468_; lean_object* v_k_5469_; lean_object* v___x_5470_; 
v_fvarId_5464_ = lean_ctor_get(v_code_5096_, 0);
v_i_5465_ = lean_ctor_get(v_code_5096_, 1);
v_offset_5466_ = lean_ctor_get(v_code_5096_, 2);
v_y_5467_ = lean_ctor_get(v_code_5096_, 3);
v_ty_5468_ = lean_ctor_get(v_code_5096_, 4);
v_k_5469_ = lean_ctor_get(v_code_5096_, 5);
lean_inc_ref(v_a_5097_);
lean_inc_ref(v_k_5469_);
v___x_5470_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc(v_k_5469_, v_a_5097_, v_a_5098_, v_a_5099_, v_a_5100_, v_a_5101_, v_a_5102_);
if (lean_obj_tag(v___x_5470_) == 0)
{
lean_object* v_a_5471_; lean_object* v___x_5472_; 
v_a_5471_ = lean_ctor_get(v___x_5470_, 0);
lean_inc(v_a_5471_);
lean_dec_ref(v___x_5470_);
lean_inc(v_fvarId_5464_);
v___x_5472_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___redArg(v_fvarId_5464_, v_a_5097_, v_a_5098_);
lean_dec_ref(v_a_5097_);
if (lean_obj_tag(v___x_5472_) == 0)
{
lean_object* v___x_5474_; uint8_t v_isShared_5475_; uint8_t v_isSharedCheck_5498_; 
v_isSharedCheck_5498_ = !lean_is_exclusive(v___x_5472_);
if (v_isSharedCheck_5498_ == 0)
{
lean_object* v_unused_5499_; 
v_unused_5499_ = lean_ctor_get(v___x_5472_, 0);
lean_dec(v_unused_5499_);
v___x_5474_ = v___x_5472_;
v_isShared_5475_ = v_isSharedCheck_5498_;
goto v_resetjp_5473_;
}
else
{
lean_dec(v___x_5472_);
v___x_5474_ = lean_box(0);
v_isShared_5475_ = v_isSharedCheck_5498_;
goto v_resetjp_5473_;
}
v_resetjp_5473_:
{
size_t v___x_5476_; size_t v___x_5477_; uint8_t v___x_5478_; 
v___x_5476_ = lean_ptr_addr(v_k_5469_);
v___x_5477_ = lean_ptr_addr(v_a_5471_);
v___x_5478_ = lean_usize_dec_eq(v___x_5476_, v___x_5477_);
if (v___x_5478_ == 0)
{
lean_object* v___x_5480_; uint8_t v_isShared_5481_; uint8_t v_isSharedCheck_5488_; 
lean_inc_ref(v_ty_5468_);
lean_inc(v_y_5467_);
lean_inc(v_offset_5466_);
lean_inc(v_i_5465_);
lean_inc(v_fvarId_5464_);
v_isSharedCheck_5488_ = !lean_is_exclusive(v_code_5096_);
if (v_isSharedCheck_5488_ == 0)
{
lean_object* v_unused_5489_; lean_object* v_unused_5490_; lean_object* v_unused_5491_; lean_object* v_unused_5492_; lean_object* v_unused_5493_; lean_object* v_unused_5494_; 
v_unused_5489_ = lean_ctor_get(v_code_5096_, 5);
lean_dec(v_unused_5489_);
v_unused_5490_ = lean_ctor_get(v_code_5096_, 4);
lean_dec(v_unused_5490_);
v_unused_5491_ = lean_ctor_get(v_code_5096_, 3);
lean_dec(v_unused_5491_);
v_unused_5492_ = lean_ctor_get(v_code_5096_, 2);
lean_dec(v_unused_5492_);
v_unused_5493_ = lean_ctor_get(v_code_5096_, 1);
lean_dec(v_unused_5493_);
v_unused_5494_ = lean_ctor_get(v_code_5096_, 0);
lean_dec(v_unused_5494_);
v___x_5480_ = v_code_5096_;
v_isShared_5481_ = v_isSharedCheck_5488_;
goto v_resetjp_5479_;
}
else
{
lean_dec(v_code_5096_);
v___x_5480_ = lean_box(0);
v_isShared_5481_ = v_isSharedCheck_5488_;
goto v_resetjp_5479_;
}
v_resetjp_5479_:
{
lean_object* v___x_5483_; 
if (v_isShared_5481_ == 0)
{
lean_ctor_set(v___x_5480_, 5, v_a_5471_);
v___x_5483_ = v___x_5480_;
goto v_reusejp_5482_;
}
else
{
lean_object* v_reuseFailAlloc_5487_; 
v_reuseFailAlloc_5487_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_5487_, 0, v_fvarId_5464_);
lean_ctor_set(v_reuseFailAlloc_5487_, 1, v_i_5465_);
lean_ctor_set(v_reuseFailAlloc_5487_, 2, v_offset_5466_);
lean_ctor_set(v_reuseFailAlloc_5487_, 3, v_y_5467_);
lean_ctor_set(v_reuseFailAlloc_5487_, 4, v_ty_5468_);
lean_ctor_set(v_reuseFailAlloc_5487_, 5, v_a_5471_);
v___x_5483_ = v_reuseFailAlloc_5487_;
goto v_reusejp_5482_;
}
v_reusejp_5482_:
{
lean_object* v___x_5485_; 
if (v_isShared_5475_ == 0)
{
lean_ctor_set(v___x_5474_, 0, v___x_5483_);
v___x_5485_ = v___x_5474_;
goto v_reusejp_5484_;
}
else
{
lean_object* v_reuseFailAlloc_5486_; 
v_reuseFailAlloc_5486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5486_, 0, v___x_5483_);
v___x_5485_ = v_reuseFailAlloc_5486_;
goto v_reusejp_5484_;
}
v_reusejp_5484_:
{
return v___x_5485_;
}
}
}
}
else
{
lean_object* v___x_5496_; 
lean_dec(v_a_5471_);
if (v_isShared_5475_ == 0)
{
lean_ctor_set(v___x_5474_, 0, v_code_5096_);
v___x_5496_ = v___x_5474_;
goto v_reusejp_5495_;
}
else
{
lean_object* v_reuseFailAlloc_5497_; 
v_reuseFailAlloc_5497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5497_, 0, v_code_5096_);
v___x_5496_ = v_reuseFailAlloc_5497_;
goto v_reusejp_5495_;
}
v_reusejp_5495_:
{
return v___x_5496_;
}
}
}
}
else
{
lean_object* v_a_5500_; lean_object* v___x_5502_; uint8_t v_isShared_5503_; uint8_t v_isSharedCheck_5507_; 
lean_dec(v_a_5471_);
lean_dec_ref(v_code_5096_);
v_a_5500_ = lean_ctor_get(v___x_5472_, 0);
v_isSharedCheck_5507_ = !lean_is_exclusive(v___x_5472_);
if (v_isSharedCheck_5507_ == 0)
{
v___x_5502_ = v___x_5472_;
v_isShared_5503_ = v_isSharedCheck_5507_;
goto v_resetjp_5501_;
}
else
{
lean_inc(v_a_5500_);
lean_dec(v___x_5472_);
v___x_5502_ = lean_box(0);
v_isShared_5503_ = v_isSharedCheck_5507_;
goto v_resetjp_5501_;
}
v_resetjp_5501_:
{
lean_object* v___x_5505_; 
if (v_isShared_5503_ == 0)
{
v___x_5505_ = v___x_5502_;
goto v_reusejp_5504_;
}
else
{
lean_object* v_reuseFailAlloc_5506_; 
v_reuseFailAlloc_5506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5506_, 0, v_a_5500_);
v___x_5505_ = v_reuseFailAlloc_5506_;
goto v_reusejp_5504_;
}
v_reusejp_5504_:
{
return v___x_5505_;
}
}
}
}
else
{
lean_dec_ref(v_code_5096_);
lean_dec_ref(v_a_5097_);
return v___x_5470_;
}
}
default: 
{
lean_object* v___x_5508_; lean_object* v___x_5509_; 
lean_dec_ref(v_code_5096_);
v___x_5508_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc___closed__1, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc___closed__1_once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc___closed__1);
v___x_5509_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__2(v___x_5508_, v_a_5097_, v_a_5098_, v_a_5099_, v_a_5100_, v_a_5101_, v_a_5102_);
lean_dec_ref(v_a_5097_);
return v___x_5509_;
}
}
v___jp_5104_:
{
if (v___y_5107_ == 0)
{
lean_object* v___x_5108_; lean_object* v___x_5109_; 
lean_dec_ref(v_code_5096_);
v___x_5108_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5108_, 0, v___y_5105_);
lean_ctor_set(v___x_5108_, 1, v___y_5106_);
v___x_5109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5109_, 0, v___x_5108_);
return v___x_5109_;
}
else
{
lean_object* v___x_5110_; 
lean_dec_ref(v___y_5106_);
lean_dec_ref(v___y_5105_);
v___x_5110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5110_, 0, v_code_5096_);
return v___x_5110_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__6(lean_object* v_cases_5510_, size_t v_sz_5511_, size_t v_i_5512_, lean_object* v_bs_5513_, lean_object* v___y_5514_, lean_object* v___y_5515_, lean_object* v___y_5516_, lean_object* v___y_5517_, lean_object* v___y_5518_, lean_object* v___y_5519_){
_start:
{
uint8_t v___x_5521_; 
v___x_5521_ = lean_usize_dec_lt(v_i_5512_, v_sz_5511_);
if (v___x_5521_ == 0)
{
lean_object* v___x_5522_; 
lean_dec_ref(v___y_5514_);
lean_dec_ref(v_cases_5510_);
v___x_5522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5522_, 0, v_bs_5513_);
return v___x_5522_;
}
else
{
lean_object* v___x_5523_; lean_object* v___x_5524_; lean_object* v___x_5525_; lean_object* v___x_5526_; lean_object* v___x_5527_; lean_object* v_v_5528_; lean_object* v_bs_x27_5529_; lean_object* v_a_5531_; 
v___x_5523_ = lean_st_ref_get(v___y_5515_);
v___x_5524_ = lean_st_ref_take(v___y_5515_);
lean_dec(v___x_5524_);
v___x_5525_ = lean_unsigned_to_nat(0u);
v___x_5526_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__0, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__0_once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__0);
v___x_5527_ = lean_st_ref_set(v___y_5515_, v___x_5526_);
v_v_5528_ = lean_array_uget(v_bs_5513_, v_i_5512_);
v_bs_x27_5529_ = lean_array_uset(v_bs_5513_, v_i_5512_, v___x_5525_);
if (lean_obj_tag(v_v_5528_) == 1)
{
lean_object* v_info_5540_; lean_object* v_code_5541_; lean_object* v_discr_5542_; lean_object* v_borrowedParams_5543_; lean_object* v_derivedValMap_5544_; lean_object* v_varMap_5545_; lean_object* v_jpLiveVarMap_5546_; lean_object* v_idx_5547_; lean_object* v___y_5549_; lean_object* v___x_5564_; 
v_info_5540_ = lean_ctor_get(v_v_5528_, 0);
v_code_5541_ = lean_ctor_get(v_v_5528_, 1);
v_discr_5542_ = lean_ctor_get(v_cases_5510_, 2);
v_borrowedParams_5543_ = lean_ctor_get(v___y_5514_, 0);
v_derivedValMap_5544_ = lean_ctor_get(v___y_5514_, 1);
v_varMap_5545_ = lean_ctor_get(v___y_5514_, 2);
v_jpLiveVarMap_5546_ = lean_ctor_get(v___y_5514_, 3);
v_idx_5547_ = lean_ctor_get(v___y_5514_, 4);
v___x_5564_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__5___redArg(v_varMap_5545_, v_discr_5542_);
if (lean_obj_tag(v___x_5564_) == 0)
{
lean_inc(v_varMap_5545_);
v___y_5549_ = v_varMap_5545_;
goto v___jp_5548_;
}
else
{
lean_object* v_val_5565_; uint8_t v_persistent_5566_; lean_object* v___x_5568_; uint8_t v_isShared_5569_; uint8_t v_isSharedCheck_5579_; 
v_val_5565_ = lean_ctor_get(v___x_5564_, 0);
lean_inc(v_val_5565_);
lean_dec_ref(v___x_5564_);
v_persistent_5566_ = lean_ctor_get_uint8(v_val_5565_, sizeof(void*)*1 + 2);
v_isSharedCheck_5579_ = !lean_is_exclusive(v_val_5565_);
if (v_isSharedCheck_5579_ == 0)
{
lean_object* v_unused_5580_; 
v_unused_5580_ = lean_ctor_get(v_val_5565_, 0);
lean_dec(v_unused_5580_);
v___x_5568_ = v_val_5565_;
v_isShared_5569_ = v_isSharedCheck_5579_;
goto v_resetjp_5567_;
}
else
{
lean_dec(v_val_5565_);
v___x_5568_ = lean_box(0);
v_isShared_5569_ = v_isSharedCheck_5579_;
goto v_resetjp_5567_;
}
v_resetjp_5567_:
{
lean_object* v___x_5570_; uint8_t v___x_5571_; uint8_t v___x_5572_; lean_object* v___x_5573_; lean_object* v___x_5574_; lean_object* v___x_5576_; 
v___x_5570_ = l_Lean_Compiler_LCNF_CtorInfo_type(v_info_5540_);
v___x_5571_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isPossibleRef(v___x_5570_);
v___x_5572_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isDefiniteRef(v___x_5570_);
lean_dec_ref(v___x_5570_);
v___x_5573_ = lean_unsigned_to_nat(1u);
v___x_5574_ = lean_nat_add(v_idx_5547_, v___x_5573_);
if (v_isShared_5569_ == 0)
{
lean_ctor_set(v___x_5568_, 0, v___x_5574_);
v___x_5576_ = v___x_5568_;
goto v_reusejp_5575_;
}
else
{
lean_object* v_reuseFailAlloc_5578_; 
v_reuseFailAlloc_5578_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v_reuseFailAlloc_5578_, 0, v___x_5574_);
lean_ctor_set_uint8(v_reuseFailAlloc_5578_, sizeof(void*)*1 + 2, v_persistent_5566_);
v___x_5576_ = v_reuseFailAlloc_5578_;
goto v_reusejp_5575_;
}
v_reusejp_5575_:
{
lean_object* v___x_5577_; 
lean_ctor_set_uint8(v___x_5576_, sizeof(void*)*1, v___x_5571_);
lean_ctor_set_uint8(v___x_5576_, sizeof(void*)*1 + 1, v___x_5572_);
lean_inc(v_varMap_5545_);
lean_inc(v_discr_5542_);
v___x_5577_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_discr_5542_, v___x_5576_, v_varMap_5545_);
v___y_5549_ = v___x_5577_;
goto v___jp_5548_;
}
}
}
v___jp_5548_:
{
lean_object* v___x_5550_; lean_object* v___x_5551_; lean_object* v___x_5552_; lean_object* v___x_5553_; 
v___x_5550_ = lean_unsigned_to_nat(1u);
v___x_5551_ = lean_nat_add(v_idx_5547_, v___x_5550_);
lean_inc(v_jpLiveVarMap_5546_);
lean_inc_ref(v_derivedValMap_5544_);
lean_inc_ref(v_borrowedParams_5543_);
v___x_5552_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5552_, 0, v_borrowedParams_5543_);
lean_ctor_set(v___x_5552_, 1, v_derivedValMap_5544_);
lean_ctor_set(v___x_5552_, 2, v___y_5549_);
lean_ctor_set(v___x_5552_, 3, v_jpLiveVarMap_5546_);
lean_ctor_set(v___x_5552_, 4, v___x_5551_);
lean_inc_ref(v_code_5541_);
v___x_5553_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc(v_code_5541_, v___x_5552_, v___y_5515_, v___y_5516_, v___y_5517_, v___y_5518_, v___y_5519_);
if (lean_obj_tag(v___x_5553_) == 0)
{
lean_object* v_a_5554_; lean_object* v___x_5555_; 
v_a_5554_ = lean_ctor_get(v___x_5553_, 0);
lean_inc(v_a_5554_);
lean_dec_ref(v___x_5553_);
v___x_5555_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_v_5528_, v_a_5554_);
v_a_5531_ = v___x_5555_;
goto v___jp_5530_;
}
else
{
lean_object* v_a_5556_; lean_object* v___x_5558_; uint8_t v_isShared_5559_; uint8_t v_isSharedCheck_5563_; 
lean_dec_ref(v_v_5528_);
lean_dec_ref(v_bs_x27_5529_);
lean_dec(v___x_5523_);
lean_dec_ref(v___y_5514_);
lean_dec_ref(v_cases_5510_);
v_a_5556_ = lean_ctor_get(v___x_5553_, 0);
v_isSharedCheck_5563_ = !lean_is_exclusive(v___x_5553_);
if (v_isSharedCheck_5563_ == 0)
{
v___x_5558_ = v___x_5553_;
v_isShared_5559_ = v_isSharedCheck_5563_;
goto v_resetjp_5557_;
}
else
{
lean_inc(v_a_5556_);
lean_dec(v___x_5553_);
v___x_5558_ = lean_box(0);
v_isShared_5559_ = v_isSharedCheck_5563_;
goto v_resetjp_5557_;
}
v_resetjp_5557_:
{
lean_object* v___x_5561_; 
if (v_isShared_5559_ == 0)
{
v___x_5561_ = v___x_5558_;
goto v_reusejp_5560_;
}
else
{
lean_object* v_reuseFailAlloc_5562_; 
v_reuseFailAlloc_5562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5562_, 0, v_a_5556_);
v___x_5561_ = v_reuseFailAlloc_5562_;
goto v_reusejp_5560_;
}
v_reusejp_5560_:
{
return v___x_5561_;
}
}
}
}
}
else
{
lean_object* v_code_5581_; lean_object* v___x_5582_; 
v_code_5581_ = lean_ctor_get(v_v_5528_, 0);
lean_inc_ref(v___y_5514_);
lean_inc_ref(v_code_5581_);
v___x_5582_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc(v_code_5581_, v___y_5514_, v___y_5515_, v___y_5516_, v___y_5517_, v___y_5518_, v___y_5519_);
if (lean_obj_tag(v___x_5582_) == 0)
{
lean_object* v_a_5583_; lean_object* v___x_5584_; 
v_a_5583_ = lean_ctor_get(v___x_5582_, 0);
lean_inc(v_a_5583_);
lean_dec_ref(v___x_5582_);
v___x_5584_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_v_5528_, v_a_5583_);
v_a_5531_ = v___x_5584_;
goto v___jp_5530_;
}
else
{
lean_object* v_a_5585_; lean_object* v___x_5587_; uint8_t v_isShared_5588_; uint8_t v_isSharedCheck_5592_; 
lean_dec_ref(v_v_5528_);
lean_dec_ref(v_bs_x27_5529_);
lean_dec(v___x_5523_);
lean_dec_ref(v___y_5514_);
lean_dec_ref(v_cases_5510_);
v_a_5585_ = lean_ctor_get(v___x_5582_, 0);
v_isSharedCheck_5592_ = !lean_is_exclusive(v___x_5582_);
if (v_isSharedCheck_5592_ == 0)
{
v___x_5587_ = v___x_5582_;
v_isShared_5588_ = v_isSharedCheck_5592_;
goto v_resetjp_5586_;
}
else
{
lean_inc(v_a_5585_);
lean_dec(v___x_5582_);
v___x_5587_ = lean_box(0);
v_isShared_5588_ = v_isSharedCheck_5592_;
goto v_resetjp_5586_;
}
v_resetjp_5586_:
{
lean_object* v___x_5590_; 
if (v_isShared_5588_ == 0)
{
v___x_5590_ = v___x_5587_;
goto v_reusejp_5589_;
}
else
{
lean_object* v_reuseFailAlloc_5591_; 
v_reuseFailAlloc_5591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5591_, 0, v_a_5585_);
v___x_5590_ = v_reuseFailAlloc_5591_;
goto v_reusejp_5589_;
}
v_reusejp_5589_:
{
return v___x_5590_;
}
}
}
}
v___jp_5530_:
{
lean_object* v___x_5532_; lean_object* v___x_5533_; lean_object* v___x_5534_; lean_object* v___x_5535_; size_t v___x_5536_; size_t v___x_5537_; lean_object* v___x_5538_; 
v___x_5532_ = lean_st_ref_get(v___y_5515_);
v___x_5533_ = lean_st_ref_take(v___y_5515_);
lean_dec(v___x_5533_);
v___x_5534_ = lean_st_ref_set(v___y_5515_, v___x_5523_);
v___x_5535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5535_, 0, v_a_5531_);
lean_ctor_set(v___x_5535_, 1, v___x_5532_);
v___x_5536_ = ((size_t)1ULL);
v___x_5537_ = lean_usize_add(v_i_5512_, v___x_5536_);
v___x_5538_ = lean_array_uset(v_bs_x27_5529_, v_i_5512_, v___x_5535_);
v_i_5512_ = v___x_5537_;
v_bs_5513_ = v___x_5538_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__6___boxed(lean_object* v_cases_5593_, lean_object* v_sz_5594_, lean_object* v_i_5595_, lean_object* v_bs_5596_, lean_object* v___y_5597_, lean_object* v___y_5598_, lean_object* v___y_5599_, lean_object* v___y_5600_, lean_object* v___y_5601_, lean_object* v___y_5602_, lean_object* v___y_5603_){
_start:
{
size_t v_sz_boxed_5604_; size_t v_i_boxed_5605_; lean_object* v_res_5606_; 
v_sz_boxed_5604_ = lean_unbox_usize(v_sz_5594_);
lean_dec(v_sz_5594_);
v_i_boxed_5605_ = lean_unbox_usize(v_i_5595_);
lean_dec(v_i_5595_);
v_res_5606_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__6(v_cases_5593_, v_sz_boxed_5604_, v_i_boxed_5605_, v_bs_5596_, v___y_5597_, v___y_5598_, v___y_5599_, v___y_5600_, v___y_5601_, v___y_5602_);
lean_dec(v___y_5602_);
lean_dec_ref(v___y_5601_);
lean_dec(v___y_5600_);
lean_dec_ref(v___y_5599_);
lean_dec(v___y_5598_);
return v_res_5606_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc___boxed(lean_object* v_code_5607_, lean_object* v_a_5608_, lean_object* v_a_5609_, lean_object* v_a_5610_, lean_object* v_a_5611_, lean_object* v_a_5612_, lean_object* v_a_5613_, lean_object* v_a_5614_){
_start:
{
lean_object* v_res_5615_; 
v_res_5615_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc(v_code_5607_, v_a_5608_, v_a_5609_, v_a_5610_, v_a_5611_, v_a_5612_, v_a_5613_);
lean_dec(v_a_5613_);
lean_dec_ref(v_a_5612_);
lean_dec(v_a_5611_);
lean_dec_ref(v_a_5610_);
lean_dec(v_a_5609_);
return v_res_5615_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__5(lean_object* v_00_u03b4_5616_, lean_object* v_t_5617_, lean_object* v_k_5618_){
_start:
{
lean_object* v___x_5619_; 
v___x_5619_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__5___redArg(v_t_5617_, v_k_5618_);
return v___x_5619_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__5___boxed(lean_object* v_00_u03b4_5620_, lean_object* v_t_5621_, lean_object* v_k_5622_){
_start:
{
lean_object* v_res_5623_; 
v_res_5623_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__5(v_00_u03b4_5620_, v_t_5621_, v_k_5622_);
lean_dec(v_k_5622_);
lean_dec(v_t_5621_);
return v_res_5623_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc_go(lean_object* v_decl_5624_, lean_object* v_code_5625_, lean_object* v_a_5626_, lean_object* v_a_5627_, lean_object* v_a_5628_, lean_object* v_a_5629_, lean_object* v_a_5630_, lean_object* v_a_5631_){
_start:
{
lean_object* v_toSignature_5633_; lean_object* v_params_5634_; lean_object* v___x_5635_; lean_object* v___x_5636_; uint8_t v___x_5637_; 
v_toSignature_5633_ = lean_ctor_get(v_decl_5624_, 0);
v_params_5634_ = lean_ctor_get(v_toSignature_5633_, 3);
v___x_5635_ = lean_unsigned_to_nat(0u);
v___x_5636_ = lean_array_get_size(v_params_5634_);
v___x_5637_ = lean_nat_dec_lt(v___x_5635_, v___x_5636_);
if (v___x_5637_ == 0)
{
lean_object* v___x_5638_; 
lean_inc_ref(v_a_5626_);
v___x_5638_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc(v_code_5625_, v_a_5626_, v_a_5627_, v_a_5628_, v_a_5629_, v_a_5630_, v_a_5631_);
if (lean_obj_tag(v___x_5638_) == 0)
{
lean_object* v_a_5639_; lean_object* v___x_5640_; 
v_a_5639_ = lean_ctor_get(v___x_5638_, 0);
lean_inc(v_a_5639_);
lean_dec_ref(v___x_5638_);
v___x_5640_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams(v_params_5634_, v_a_5639_, v_a_5626_, v_a_5627_, v_a_5628_, v_a_5629_, v_a_5630_, v_a_5631_);
return v___x_5640_;
}
else
{
return v___x_5638_;
}
}
else
{
uint8_t v___x_5641_; 
v___x_5641_ = lean_nat_dec_le(v___x_5636_, v___x_5636_);
if (v___x_5641_ == 0)
{
if (v___x_5637_ == 0)
{
lean_object* v___x_5642_; 
lean_inc_ref(v_a_5626_);
v___x_5642_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc(v_code_5625_, v_a_5626_, v_a_5627_, v_a_5628_, v_a_5629_, v_a_5630_, v_a_5631_);
if (lean_obj_tag(v___x_5642_) == 0)
{
lean_object* v_a_5643_; lean_object* v___x_5644_; 
v_a_5643_ = lean_ctor_get(v___x_5642_, 0);
lean_inc(v_a_5643_);
lean_dec_ref(v___x_5642_);
v___x_5644_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams(v_params_5634_, v_a_5643_, v_a_5626_, v_a_5627_, v_a_5628_, v_a_5629_, v_a_5630_, v_a_5631_);
return v___x_5644_;
}
else
{
return v___x_5642_;
}
}
else
{
size_t v___x_5645_; size_t v___x_5646_; lean_object* v___x_5647_; lean_object* v___x_5648_; 
v___x_5645_ = ((size_t)0ULL);
v___x_5646_ = lean_usize_of_nat(v___x_5636_);
lean_inc_ref(v_a_5626_);
v___x_5647_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__3(v_params_5634_, v___x_5645_, v___x_5646_, v_a_5626_);
lean_inc_ref(v___x_5647_);
v___x_5648_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc(v_code_5625_, v___x_5647_, v_a_5627_, v_a_5628_, v_a_5629_, v_a_5630_, v_a_5631_);
if (lean_obj_tag(v___x_5648_) == 0)
{
lean_object* v_a_5649_; lean_object* v___x_5650_; 
v_a_5649_ = lean_ctor_get(v___x_5648_, 0);
lean_inc(v_a_5649_);
lean_dec_ref(v___x_5648_);
v___x_5650_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams(v_params_5634_, v_a_5649_, v___x_5647_, v_a_5627_, v_a_5628_, v_a_5629_, v_a_5630_, v_a_5631_);
lean_dec_ref(v___x_5647_);
return v___x_5650_;
}
else
{
lean_dec_ref(v___x_5647_);
return v___x_5648_;
}
}
}
else
{
size_t v___x_5651_; size_t v___x_5652_; lean_object* v___x_5653_; lean_object* v___x_5654_; 
v___x_5651_ = ((size_t)0ULL);
v___x_5652_ = lean_usize_of_nat(v___x_5636_);
lean_inc_ref(v_a_5626_);
v___x_5653_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__3(v_params_5634_, v___x_5651_, v___x_5652_, v_a_5626_);
lean_inc_ref(v___x_5653_);
v___x_5654_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc(v_code_5625_, v___x_5653_, v_a_5627_, v_a_5628_, v_a_5629_, v_a_5630_, v_a_5631_);
if (lean_obj_tag(v___x_5654_) == 0)
{
lean_object* v_a_5655_; lean_object* v___x_5656_; 
v_a_5655_ = lean_ctor_get(v___x_5654_, 0);
lean_inc(v_a_5655_);
lean_dec_ref(v___x_5654_);
v___x_5656_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams(v_params_5634_, v_a_5655_, v___x_5653_, v_a_5627_, v_a_5628_, v_a_5629_, v_a_5630_, v_a_5631_);
lean_dec_ref(v___x_5653_);
return v___x_5656_;
}
else
{
lean_dec_ref(v___x_5653_);
return v___x_5654_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc_go___boxed(lean_object* v_decl_5657_, lean_object* v_code_5658_, lean_object* v_a_5659_, lean_object* v_a_5660_, lean_object* v_a_5661_, lean_object* v_a_5662_, lean_object* v_a_5663_, lean_object* v_a_5664_, lean_object* v_a_5665_){
_start:
{
lean_object* v_res_5666_; 
v_res_5666_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc_go(v_decl_5657_, v_code_5658_, v_a_5659_, v_a_5660_, v_a_5661_, v_a_5662_, v_a_5663_, v_a_5664_);
lean_dec(v_a_5664_);
lean_dec_ref(v_a_5663_);
lean_dec(v_a_5662_);
lean_dec_ref(v_a_5661_);
lean_dec(v_a_5660_);
lean_dec_ref(v_a_5659_);
lean_dec_ref(v_decl_5657_);
return v_res_5666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc_spec__0___redArg(lean_object* v_f_5667_, lean_object* v_v_5668_, lean_object* v___y_5669_, lean_object* v___y_5670_, lean_object* v___y_5671_, lean_object* v___y_5672_){
_start:
{
if (lean_obj_tag(v_v_5668_) == 0)
{
lean_object* v_code_5674_; lean_object* v___x_5676_; uint8_t v_isShared_5677_; uint8_t v_isSharedCheck_5698_; 
v_code_5674_ = lean_ctor_get(v_v_5668_, 0);
v_isSharedCheck_5698_ = !lean_is_exclusive(v_v_5668_);
if (v_isSharedCheck_5698_ == 0)
{
v___x_5676_ = v_v_5668_;
v_isShared_5677_ = v_isSharedCheck_5698_;
goto v_resetjp_5675_;
}
else
{
lean_inc(v_code_5674_);
lean_dec(v_v_5668_);
v___x_5676_ = lean_box(0);
v_isShared_5677_ = v_isSharedCheck_5698_;
goto v_resetjp_5675_;
}
v_resetjp_5675_:
{
lean_object* v___x_5678_; 
lean_inc(v___y_5672_);
lean_inc_ref(v___y_5671_);
lean_inc(v___y_5670_);
lean_inc_ref(v___y_5669_);
v___x_5678_ = lean_apply_6(v_f_5667_, v_code_5674_, v___y_5669_, v___y_5670_, v___y_5671_, v___y_5672_, lean_box(0));
if (lean_obj_tag(v___x_5678_) == 0)
{
lean_object* v_a_5679_; lean_object* v___x_5681_; uint8_t v_isShared_5682_; uint8_t v_isSharedCheck_5689_; 
v_a_5679_ = lean_ctor_get(v___x_5678_, 0);
v_isSharedCheck_5689_ = !lean_is_exclusive(v___x_5678_);
if (v_isSharedCheck_5689_ == 0)
{
v___x_5681_ = v___x_5678_;
v_isShared_5682_ = v_isSharedCheck_5689_;
goto v_resetjp_5680_;
}
else
{
lean_inc(v_a_5679_);
lean_dec(v___x_5678_);
v___x_5681_ = lean_box(0);
v_isShared_5682_ = v_isSharedCheck_5689_;
goto v_resetjp_5680_;
}
v_resetjp_5680_:
{
lean_object* v___x_5684_; 
if (v_isShared_5677_ == 0)
{
lean_ctor_set(v___x_5676_, 0, v_a_5679_);
v___x_5684_ = v___x_5676_;
goto v_reusejp_5683_;
}
else
{
lean_object* v_reuseFailAlloc_5688_; 
v_reuseFailAlloc_5688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5688_, 0, v_a_5679_);
v___x_5684_ = v_reuseFailAlloc_5688_;
goto v_reusejp_5683_;
}
v_reusejp_5683_:
{
lean_object* v___x_5686_; 
if (v_isShared_5682_ == 0)
{
lean_ctor_set(v___x_5681_, 0, v___x_5684_);
v___x_5686_ = v___x_5681_;
goto v_reusejp_5685_;
}
else
{
lean_object* v_reuseFailAlloc_5687_; 
v_reuseFailAlloc_5687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5687_, 0, v___x_5684_);
v___x_5686_ = v_reuseFailAlloc_5687_;
goto v_reusejp_5685_;
}
v_reusejp_5685_:
{
return v___x_5686_;
}
}
}
}
else
{
lean_object* v_a_5690_; lean_object* v___x_5692_; uint8_t v_isShared_5693_; uint8_t v_isSharedCheck_5697_; 
lean_del_object(v___x_5676_);
v_a_5690_ = lean_ctor_get(v___x_5678_, 0);
v_isSharedCheck_5697_ = !lean_is_exclusive(v___x_5678_);
if (v_isSharedCheck_5697_ == 0)
{
v___x_5692_ = v___x_5678_;
v_isShared_5693_ = v_isSharedCheck_5697_;
goto v_resetjp_5691_;
}
else
{
lean_inc(v_a_5690_);
lean_dec(v___x_5678_);
v___x_5692_ = lean_box(0);
v_isShared_5693_ = v_isSharedCheck_5697_;
goto v_resetjp_5691_;
}
v_resetjp_5691_:
{
lean_object* v___x_5695_; 
if (v_isShared_5693_ == 0)
{
v___x_5695_ = v___x_5692_;
goto v_reusejp_5694_;
}
else
{
lean_object* v_reuseFailAlloc_5696_; 
v_reuseFailAlloc_5696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5696_, 0, v_a_5690_);
v___x_5695_ = v_reuseFailAlloc_5696_;
goto v_reusejp_5694_;
}
v_reusejp_5694_:
{
return v___x_5695_;
}
}
}
}
}
else
{
lean_object* v___x_5699_; 
lean_dec_ref(v_f_5667_);
v___x_5699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5699_, 0, v_v_5668_);
return v___x_5699_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc_spec__0___redArg___boxed(lean_object* v_f_5700_, lean_object* v_v_5701_, lean_object* v___y_5702_, lean_object* v___y_5703_, lean_object* v___y_5704_, lean_object* v___y_5705_, lean_object* v___y_5706_){
_start:
{
lean_object* v_res_5707_; 
v_res_5707_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc_spec__0___redArg(v_f_5700_, v_v_5701_, v___y_5702_, v___y_5703_, v___y_5704_, v___y_5705_);
lean_dec(v___y_5705_);
lean_dec_ref(v___y_5704_);
lean_dec(v___y_5703_);
lean_dec_ref(v___y_5702_);
return v_res_5707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc_spec__0(uint8_t v_pu_5708_, lean_object* v_f_5709_, lean_object* v_v_5710_, lean_object* v___y_5711_, lean_object* v___y_5712_, lean_object* v___y_5713_, lean_object* v___y_5714_){
_start:
{
lean_object* v___x_5716_; 
v___x_5716_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc_spec__0___redArg(v_f_5709_, v_v_5710_, v___y_5711_, v___y_5712_, v___y_5713_, v___y_5714_);
return v___x_5716_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc_spec__0___boxed(lean_object* v_pu_5717_, lean_object* v_f_5718_, lean_object* v_v_5719_, lean_object* v___y_5720_, lean_object* v___y_5721_, lean_object* v___y_5722_, lean_object* v___y_5723_, lean_object* v___y_5724_){
_start:
{
uint8_t v_pu_boxed_5725_; lean_object* v_res_5726_; 
v_pu_boxed_5725_ = lean_unbox(v_pu_5717_);
v_res_5726_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc_spec__0(v_pu_boxed_5725_, v_f_5718_, v_v_5719_, v___y_5720_, v___y_5721_, v___y_5722_, v___y_5723_);
lean_dec(v___y_5723_);
lean_dec_ref(v___y_5722_);
lean_dec(v___y_5721_);
lean_dec_ref(v___y_5720_);
return v_res_5726_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc___lam__0(lean_object* v_toSignature_5727_, lean_object* v_decl_5728_, lean_object* v_code_5729_, lean_object* v___y_5730_, lean_object* v___y_5731_, lean_object* v___y_5732_, lean_object* v___y_5733_){
_start:
{
lean_object* v_params_5735_; lean_object* v___x_5736_; 
v_params_5735_ = lean_ctor_get(v_toSignature_5727_, 3);
lean_inc_ref(v_code_5729_);
v___x_5736_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_CollectDerivedValInfo_collect(v_params_5735_, v_code_5729_, v___y_5730_, v___y_5731_, v___y_5732_, v___y_5733_);
if (lean_obj_tag(v___x_5736_) == 0)
{
lean_object* v_a_5737_; lean_object* v_fst_5738_; lean_object* v_snd_5739_; lean_object* v___x_5740_; lean_object* v___x_5741_; lean_object* v___x_5742_; lean_object* v___x_5743_; lean_object* v___x_5744_; lean_object* v___x_5745_; 
v_a_5737_ = lean_ctor_get(v___x_5736_, 0);
lean_inc(v_a_5737_);
lean_dec_ref(v___x_5736_);
v_fst_5738_ = lean_ctor_get(v_a_5737_, 0);
lean_inc(v_fst_5738_);
v_snd_5739_ = lean_ctor_get(v_a_5737_, 1);
lean_inc(v_snd_5739_);
lean_dec(v_a_5737_);
v___x_5740_ = lean_unsigned_to_nat(0u);
v___x_5741_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__0, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__0_once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__0);
v___x_5742_ = lean_st_mk_ref(v___x_5741_);
v___x_5743_ = lean_box(1);
v___x_5744_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5744_, 0, v_snd_5739_);
lean_ctor_set(v___x_5744_, 1, v_fst_5738_);
lean_ctor_set(v___x_5744_, 2, v___x_5743_);
lean_ctor_set(v___x_5744_, 3, v___x_5743_);
lean_ctor_set(v___x_5744_, 4, v___x_5740_);
v___x_5745_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc_go(v_decl_5728_, v_code_5729_, v___x_5744_, v___x_5742_, v___y_5730_, v___y_5731_, v___y_5732_, v___y_5733_);
lean_dec_ref(v___x_5744_);
if (lean_obj_tag(v___x_5745_) == 0)
{
lean_object* v_a_5746_; lean_object* v___x_5748_; uint8_t v_isShared_5749_; uint8_t v_isSharedCheck_5754_; 
v_a_5746_ = lean_ctor_get(v___x_5745_, 0);
v_isSharedCheck_5754_ = !lean_is_exclusive(v___x_5745_);
if (v_isSharedCheck_5754_ == 0)
{
v___x_5748_ = v___x_5745_;
v_isShared_5749_ = v_isSharedCheck_5754_;
goto v_resetjp_5747_;
}
else
{
lean_inc(v_a_5746_);
lean_dec(v___x_5745_);
v___x_5748_ = lean_box(0);
v_isShared_5749_ = v_isSharedCheck_5754_;
goto v_resetjp_5747_;
}
v_resetjp_5747_:
{
lean_object* v___x_5750_; lean_object* v___x_5752_; 
v___x_5750_ = lean_st_ref_get(v___x_5742_);
lean_dec(v___x_5742_);
lean_dec(v___x_5750_);
if (v_isShared_5749_ == 0)
{
v___x_5752_ = v___x_5748_;
goto v_reusejp_5751_;
}
else
{
lean_object* v_reuseFailAlloc_5753_; 
v_reuseFailAlloc_5753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5753_, 0, v_a_5746_);
v___x_5752_ = v_reuseFailAlloc_5753_;
goto v_reusejp_5751_;
}
v_reusejp_5751_:
{
return v___x_5752_;
}
}
}
else
{
lean_dec(v___x_5742_);
return v___x_5745_;
}
}
else
{
lean_object* v_a_5755_; lean_object* v___x_5757_; uint8_t v_isShared_5758_; uint8_t v_isSharedCheck_5762_; 
lean_dec_ref(v_code_5729_);
v_a_5755_ = lean_ctor_get(v___x_5736_, 0);
v_isSharedCheck_5762_ = !lean_is_exclusive(v___x_5736_);
if (v_isSharedCheck_5762_ == 0)
{
v___x_5757_ = v___x_5736_;
v_isShared_5758_ = v_isSharedCheck_5762_;
goto v_resetjp_5756_;
}
else
{
lean_inc(v_a_5755_);
lean_dec(v___x_5736_);
v___x_5757_ = lean_box(0);
v_isShared_5758_ = v_isSharedCheck_5762_;
goto v_resetjp_5756_;
}
v_resetjp_5756_:
{
lean_object* v___x_5760_; 
if (v_isShared_5758_ == 0)
{
v___x_5760_ = v___x_5757_;
goto v_reusejp_5759_;
}
else
{
lean_object* v_reuseFailAlloc_5761_; 
v_reuseFailAlloc_5761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5761_, 0, v_a_5755_);
v___x_5760_ = v_reuseFailAlloc_5761_;
goto v_reusejp_5759_;
}
v_reusejp_5759_:
{
return v___x_5760_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc___lam__0___boxed(lean_object* v_toSignature_5763_, lean_object* v_decl_5764_, lean_object* v_code_5765_, lean_object* v___y_5766_, lean_object* v___y_5767_, lean_object* v___y_5768_, lean_object* v___y_5769_, lean_object* v___y_5770_){
_start:
{
lean_object* v_res_5771_; 
v_res_5771_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc___lam__0(v_toSignature_5763_, v_decl_5764_, v_code_5765_, v___y_5766_, v___y_5767_, v___y_5768_, v___y_5769_);
lean_dec(v___y_5769_);
lean_dec_ref(v___y_5768_);
lean_dec(v___y_5767_);
lean_dec_ref(v___y_5766_);
lean_dec_ref(v_decl_5764_);
lean_dec_ref(v_toSignature_5763_);
return v_res_5771_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc(lean_object* v_decl_5772_, lean_object* v_a_5773_, lean_object* v_a_5774_, lean_object* v_a_5775_, lean_object* v_a_5776_){
_start:
{
lean_object* v_toSignature_5778_; lean_object* v_value_5779_; uint8_t v_recursive_5780_; lean_object* v_inlineAttr_x3f_5781_; lean_object* v___f_5782_; lean_object* v___x_5783_; 
v_toSignature_5778_ = lean_ctor_get(v_decl_5772_, 0);
lean_inc_ref(v_toSignature_5778_);
v_value_5779_ = lean_ctor_get(v_decl_5772_, 1);
lean_inc_ref(v_value_5779_);
v_recursive_5780_ = lean_ctor_get_uint8(v_decl_5772_, sizeof(void*)*3);
v_inlineAttr_x3f_5781_ = lean_ctor_get(v_decl_5772_, 2);
lean_inc(v_inlineAttr_x3f_5781_);
lean_inc_ref(v_toSignature_5778_);
v___f_5782_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc___lam__0___boxed), 8, 2);
lean_closure_set(v___f_5782_, 0, v_toSignature_5778_);
lean_closure_set(v___f_5782_, 1, v_decl_5772_);
v___x_5783_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc_spec__0___redArg(v___f_5782_, v_value_5779_, v_a_5773_, v_a_5774_, v_a_5775_, v_a_5776_);
if (lean_obj_tag(v___x_5783_) == 0)
{
lean_object* v_a_5784_; lean_object* v___x_5786_; uint8_t v_isShared_5787_; uint8_t v_isSharedCheck_5792_; 
v_a_5784_ = lean_ctor_get(v___x_5783_, 0);
v_isSharedCheck_5792_ = !lean_is_exclusive(v___x_5783_);
if (v_isSharedCheck_5792_ == 0)
{
v___x_5786_ = v___x_5783_;
v_isShared_5787_ = v_isSharedCheck_5792_;
goto v_resetjp_5785_;
}
else
{
lean_inc(v_a_5784_);
lean_dec(v___x_5783_);
v___x_5786_ = lean_box(0);
v_isShared_5787_ = v_isSharedCheck_5792_;
goto v_resetjp_5785_;
}
v_resetjp_5785_:
{
lean_object* v___x_5788_; lean_object* v___x_5790_; 
v___x_5788_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_5788_, 0, v_toSignature_5778_);
lean_ctor_set(v___x_5788_, 1, v_a_5784_);
lean_ctor_set(v___x_5788_, 2, v_inlineAttr_x3f_5781_);
lean_ctor_set_uint8(v___x_5788_, sizeof(void*)*3, v_recursive_5780_);
if (v_isShared_5787_ == 0)
{
lean_ctor_set(v___x_5786_, 0, v___x_5788_);
v___x_5790_ = v___x_5786_;
goto v_reusejp_5789_;
}
else
{
lean_object* v_reuseFailAlloc_5791_; 
v_reuseFailAlloc_5791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5791_, 0, v___x_5788_);
v___x_5790_ = v_reuseFailAlloc_5791_;
goto v_reusejp_5789_;
}
v_reusejp_5789_:
{
return v___x_5790_;
}
}
}
else
{
lean_object* v_a_5793_; lean_object* v___x_5795_; uint8_t v_isShared_5796_; uint8_t v_isSharedCheck_5800_; 
lean_dec(v_inlineAttr_x3f_5781_);
lean_dec_ref(v_toSignature_5778_);
v_a_5793_ = lean_ctor_get(v___x_5783_, 0);
v_isSharedCheck_5800_ = !lean_is_exclusive(v___x_5783_);
if (v_isSharedCheck_5800_ == 0)
{
v___x_5795_ = v___x_5783_;
v_isShared_5796_ = v_isSharedCheck_5800_;
goto v_resetjp_5794_;
}
else
{
lean_inc(v_a_5793_);
lean_dec(v___x_5783_);
v___x_5795_ = lean_box(0);
v_isShared_5796_ = v_isSharedCheck_5800_;
goto v_resetjp_5794_;
}
v_resetjp_5794_:
{
lean_object* v___x_5798_; 
if (v_isShared_5796_ == 0)
{
v___x_5798_ = v___x_5795_;
goto v_reusejp_5797_;
}
else
{
lean_object* v_reuseFailAlloc_5799_; 
v_reuseFailAlloc_5799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5799_, 0, v_a_5793_);
v___x_5798_ = v_reuseFailAlloc_5799_;
goto v_reusejp_5797_;
}
v_reusejp_5797_:
{
return v___x_5798_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc___boxed(lean_object* v_decl_5801_, lean_object* v_a_5802_, lean_object* v_a_5803_, lean_object* v_a_5804_, lean_object* v_a_5805_, lean_object* v_a_5806_){
_start:
{
lean_object* v_res_5807_; 
v_res_5807_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc(v_decl_5801_, v_a_5802_, v_a_5803_, v_a_5804_, v_a_5805_);
lean_dec(v_a_5805_);
lean_dec_ref(v_a_5804_);
lean_dec(v_a_5803_);
lean_dec_ref(v_a_5802_);
return v_res_5807_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_runExplicitRc_spec__1(lean_object* v_as_5808_, size_t v_i_5809_, size_t v_stop_5810_, lean_object* v_b_5811_, lean_object* v___y_5812_, lean_object* v___y_5813_, lean_object* v___y_5814_, lean_object* v___y_5815_){
_start:
{
uint8_t v___x_5817_; 
v___x_5817_ = lean_usize_dec_eq(v_i_5809_, v_stop_5810_);
if (v___x_5817_ == 0)
{
lean_object* v___x_5818_; lean_object* v___x_5819_; 
v___x_5818_ = lean_array_uget_borrowed(v_as_5808_, v_i_5809_);
lean_inc(v___x_5818_);
v___x_5819_ = l_Lean_Compiler_LCNF_Decl_checkRC(v___x_5818_, v___y_5812_, v___y_5813_, v___y_5814_, v___y_5815_);
if (lean_obj_tag(v___x_5819_) == 0)
{
lean_object* v_a_5820_; size_t v___x_5821_; size_t v___x_5822_; 
v_a_5820_ = lean_ctor_get(v___x_5819_, 0);
lean_inc(v_a_5820_);
lean_dec_ref(v___x_5819_);
v___x_5821_ = ((size_t)1ULL);
v___x_5822_ = lean_usize_add(v_i_5809_, v___x_5821_);
v_i_5809_ = v___x_5822_;
v_b_5811_ = v_a_5820_;
goto _start;
}
else
{
return v___x_5819_;
}
}
else
{
lean_object* v___x_5824_; 
v___x_5824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5824_, 0, v_b_5811_);
return v___x_5824_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_runExplicitRc_spec__1___boxed(lean_object* v_as_5825_, lean_object* v_i_5826_, lean_object* v_stop_5827_, lean_object* v_b_5828_, lean_object* v___y_5829_, lean_object* v___y_5830_, lean_object* v___y_5831_, lean_object* v___y_5832_, lean_object* v___y_5833_){
_start:
{
size_t v_i_boxed_5834_; size_t v_stop_boxed_5835_; lean_object* v_res_5836_; 
v_i_boxed_5834_ = lean_unbox_usize(v_i_5826_);
lean_dec(v_i_5826_);
v_stop_boxed_5835_ = lean_unbox_usize(v_stop_5827_);
lean_dec(v_stop_5827_);
v_res_5836_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_runExplicitRc_spec__1(v_as_5825_, v_i_boxed_5834_, v_stop_boxed_5835_, v_b_5828_, v___y_5829_, v___y_5830_, v___y_5831_, v___y_5832_);
lean_dec(v___y_5832_);
lean_dec_ref(v___y_5831_);
lean_dec(v___y_5830_);
lean_dec_ref(v___y_5829_);
lean_dec_ref(v_as_5825_);
return v_res_5836_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_runExplicitRc_spec__0(size_t v_sz_5837_, size_t v_i_5838_, lean_object* v_bs_5839_, lean_object* v___y_5840_, lean_object* v___y_5841_, lean_object* v___y_5842_, lean_object* v___y_5843_){
_start:
{
uint8_t v___x_5845_; 
v___x_5845_ = lean_usize_dec_lt(v_i_5838_, v_sz_5837_);
if (v___x_5845_ == 0)
{
lean_object* v___x_5846_; 
v___x_5846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5846_, 0, v_bs_5839_);
return v___x_5846_;
}
else
{
lean_object* v_v_5847_; lean_object* v___x_5848_; 
v_v_5847_ = lean_array_uget_borrowed(v_bs_5839_, v_i_5838_);
lean_inc(v_v_5847_);
v___x_5848_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc(v_v_5847_, v___y_5840_, v___y_5841_, v___y_5842_, v___y_5843_);
if (lean_obj_tag(v___x_5848_) == 0)
{
lean_object* v_a_5849_; lean_object* v___x_5850_; lean_object* v_bs_x27_5851_; size_t v___x_5852_; size_t v___x_5853_; lean_object* v___x_5854_; 
v_a_5849_ = lean_ctor_get(v___x_5848_, 0);
lean_inc(v_a_5849_);
lean_dec_ref(v___x_5848_);
v___x_5850_ = lean_unsigned_to_nat(0u);
v_bs_x27_5851_ = lean_array_uset(v_bs_5839_, v_i_5838_, v___x_5850_);
v___x_5852_ = ((size_t)1ULL);
v___x_5853_ = lean_usize_add(v_i_5838_, v___x_5852_);
v___x_5854_ = lean_array_uset(v_bs_x27_5851_, v_i_5838_, v_a_5849_);
v_i_5838_ = v___x_5853_;
v_bs_5839_ = v___x_5854_;
goto _start;
}
else
{
lean_object* v_a_5856_; lean_object* v___x_5858_; uint8_t v_isShared_5859_; uint8_t v_isSharedCheck_5863_; 
lean_dec_ref(v_bs_5839_);
v_a_5856_ = lean_ctor_get(v___x_5848_, 0);
v_isSharedCheck_5863_ = !lean_is_exclusive(v___x_5848_);
if (v_isSharedCheck_5863_ == 0)
{
v___x_5858_ = v___x_5848_;
v_isShared_5859_ = v_isSharedCheck_5863_;
goto v_resetjp_5857_;
}
else
{
lean_inc(v_a_5856_);
lean_dec(v___x_5848_);
v___x_5858_ = lean_box(0);
v_isShared_5859_ = v_isSharedCheck_5863_;
goto v_resetjp_5857_;
}
v_resetjp_5857_:
{
lean_object* v___x_5861_; 
if (v_isShared_5859_ == 0)
{
v___x_5861_ = v___x_5858_;
goto v_reusejp_5860_;
}
else
{
lean_object* v_reuseFailAlloc_5862_; 
v_reuseFailAlloc_5862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5862_, 0, v_a_5856_);
v___x_5861_ = v_reuseFailAlloc_5862_;
goto v_reusejp_5860_;
}
v_reusejp_5860_:
{
return v___x_5861_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_runExplicitRc_spec__0___boxed(lean_object* v_sz_5864_, lean_object* v_i_5865_, lean_object* v_bs_5866_, lean_object* v___y_5867_, lean_object* v___y_5868_, lean_object* v___y_5869_, lean_object* v___y_5870_, lean_object* v___y_5871_){
_start:
{
size_t v_sz_boxed_5872_; size_t v_i_boxed_5873_; lean_object* v_res_5874_; 
v_sz_boxed_5872_ = lean_unbox_usize(v_sz_5864_);
lean_dec(v_sz_5864_);
v_i_boxed_5873_ = lean_unbox_usize(v_i_5865_);
lean_dec(v_i_5865_);
v_res_5874_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_runExplicitRc_spec__0(v_sz_boxed_5872_, v_i_boxed_5873_, v_bs_5866_, v___y_5867_, v___y_5868_, v___y_5869_, v___y_5870_);
lean_dec(v___y_5870_);
lean_dec_ref(v___y_5869_);
lean_dec(v___y_5868_);
lean_dec_ref(v___y_5867_);
return v_res_5874_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_runExplicitRc(lean_object* v_decls_5875_, lean_object* v_a_5876_, lean_object* v_a_5877_, lean_object* v_a_5878_, lean_object* v_a_5879_){
_start:
{
size_t v_sz_5881_; size_t v___x_5882_; lean_object* v___x_5883_; 
v_sz_5881_ = lean_array_size(v_decls_5875_);
v___x_5882_ = ((size_t)0ULL);
v___x_5883_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_runExplicitRc_spec__0(v_sz_5881_, v___x_5882_, v_decls_5875_, v_a_5876_, v_a_5877_, v_a_5878_, v_a_5879_);
if (lean_obj_tag(v___x_5883_) == 0)
{
lean_object* v_a_5884_; lean_object* v___y_5886_; lean_object* v___x_5903_; lean_object* v___x_5904_; uint8_t v___x_5905_; 
v_a_5884_ = lean_ctor_get(v___x_5883_, 0);
lean_inc(v_a_5884_);
v___x_5903_ = lean_unsigned_to_nat(0u);
v___x_5904_ = lean_array_get_size(v_a_5884_);
v___x_5905_ = lean_nat_dec_lt(v___x_5903_, v___x_5904_);
if (v___x_5905_ == 0)
{
lean_dec(v_a_5884_);
return v___x_5883_;
}
else
{
lean_object* v___x_5906_; uint8_t v___x_5907_; 
v___x_5906_ = lean_box(0);
v___x_5907_ = lean_nat_dec_le(v___x_5904_, v___x_5904_);
if (v___x_5907_ == 0)
{
if (v___x_5905_ == 0)
{
lean_dec(v_a_5884_);
return v___x_5883_;
}
else
{
size_t v___x_5908_; lean_object* v___x_5909_; 
lean_dec_ref(v___x_5883_);
v___x_5908_ = lean_usize_of_nat(v___x_5904_);
v___x_5909_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_runExplicitRc_spec__1(v_a_5884_, v___x_5882_, v___x_5908_, v___x_5906_, v_a_5876_, v_a_5877_, v_a_5878_, v_a_5879_);
v___y_5886_ = v___x_5909_;
goto v___jp_5885_;
}
}
else
{
size_t v___x_5910_; lean_object* v___x_5911_; 
lean_dec_ref(v___x_5883_);
v___x_5910_ = lean_usize_of_nat(v___x_5904_);
v___x_5911_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_runExplicitRc_spec__1(v_a_5884_, v___x_5882_, v___x_5910_, v___x_5906_, v_a_5876_, v_a_5877_, v_a_5878_, v_a_5879_);
v___y_5886_ = v___x_5911_;
goto v___jp_5885_;
}
}
v___jp_5885_:
{
if (lean_obj_tag(v___y_5886_) == 0)
{
lean_object* v___x_5888_; uint8_t v_isShared_5889_; uint8_t v_isSharedCheck_5893_; 
v_isSharedCheck_5893_ = !lean_is_exclusive(v___y_5886_);
if (v_isSharedCheck_5893_ == 0)
{
lean_object* v_unused_5894_; 
v_unused_5894_ = lean_ctor_get(v___y_5886_, 0);
lean_dec(v_unused_5894_);
v___x_5888_ = v___y_5886_;
v_isShared_5889_ = v_isSharedCheck_5893_;
goto v_resetjp_5887_;
}
else
{
lean_dec(v___y_5886_);
v___x_5888_ = lean_box(0);
v_isShared_5889_ = v_isSharedCheck_5893_;
goto v_resetjp_5887_;
}
v_resetjp_5887_:
{
lean_object* v___x_5891_; 
if (v_isShared_5889_ == 0)
{
lean_ctor_set(v___x_5888_, 0, v_a_5884_);
v___x_5891_ = v___x_5888_;
goto v_reusejp_5890_;
}
else
{
lean_object* v_reuseFailAlloc_5892_; 
v_reuseFailAlloc_5892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5892_, 0, v_a_5884_);
v___x_5891_ = v_reuseFailAlloc_5892_;
goto v_reusejp_5890_;
}
v_reusejp_5890_:
{
return v___x_5891_;
}
}
}
else
{
lean_object* v_a_5895_; lean_object* v___x_5897_; uint8_t v_isShared_5898_; uint8_t v_isSharedCheck_5902_; 
lean_dec(v_a_5884_);
v_a_5895_ = lean_ctor_get(v___y_5886_, 0);
v_isSharedCheck_5902_ = !lean_is_exclusive(v___y_5886_);
if (v_isSharedCheck_5902_ == 0)
{
v___x_5897_ = v___y_5886_;
v_isShared_5898_ = v_isSharedCheck_5902_;
goto v_resetjp_5896_;
}
else
{
lean_inc(v_a_5895_);
lean_dec(v___y_5886_);
v___x_5897_ = lean_box(0);
v_isShared_5898_ = v_isSharedCheck_5902_;
goto v_resetjp_5896_;
}
v_resetjp_5896_:
{
lean_object* v___x_5900_; 
if (v_isShared_5898_ == 0)
{
v___x_5900_ = v___x_5897_;
goto v_reusejp_5899_;
}
else
{
lean_object* v_reuseFailAlloc_5901_; 
v_reuseFailAlloc_5901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5901_, 0, v_a_5895_);
v___x_5900_ = v_reuseFailAlloc_5901_;
goto v_reusejp_5899_;
}
v_reusejp_5899_:
{
return v___x_5900_;
}
}
}
}
}
else
{
return v___x_5883_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_runExplicitRc___boxed(lean_object* v_decls_5912_, lean_object* v_a_5913_, lean_object* v_a_5914_, lean_object* v_a_5915_, lean_object* v_a_5916_, lean_object* v_a_5917_){
_start:
{
lean_object* v_res_5918_; 
v_res_5918_ = l_Lean_Compiler_LCNF_runExplicitRc(v_decls_5912_, v_a_5913_, v_a_5914_, v_a_5915_, v_a_5916_);
lean_dec(v_a_5916_);
lean_dec_ref(v_a_5915_);
lean_dec(v_a_5914_);
lean_dec_ref(v_a_5913_);
return v_res_5918_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_explicitRc___closed__3(void){
_start:
{
lean_object* v___x_5923_; lean_object* v___x_5924_; uint8_t v___x_5925_; lean_object* v___x_5926_; lean_object* v___x_5927_; 
v___x_5923_ = lean_unsigned_to_nat(0u);
v___x_5924_ = ((lean_object*)(l_Lean_Compiler_LCNF_explicitRc___closed__2));
v___x_5925_ = 2;
v___x_5926_ = ((lean_object*)(l_Lean_Compiler_LCNF_explicitRc___closed__1));
v___x_5927_ = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(v___x_5926_, v___x_5925_, v___x_5924_, v___x_5923_);
return v___x_5927_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_explicitRc(void){
_start:
{
lean_object* v___x_5928_; 
v___x_5928_ = lean_obj_once(&l_Lean_Compiler_LCNF_explicitRc___closed__3, &l_Lean_Compiler_LCNF_explicitRc___closed__3_once, _init_l_Lean_Compiler_LCNF_explicitRc___closed__3);
return v___x_5928_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5984_; lean_object* v___x_5985_; lean_object* v___x_5986_; 
v___x_5984_ = lean_unsigned_to_nat(3791338971u);
v___x_5985_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_));
v___x_5986_ = l_Lean_Name_num___override(v___x_5985_, v___x_5984_);
return v___x_5986_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5988_; lean_object* v___x_5989_; lean_object* v___x_5990_; 
v___x_5988_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_));
v___x_5989_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_);
v___x_5990_ = l_Lean_Name_str___override(v___x_5989_, v___x_5988_);
return v___x_5990_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5992_; lean_object* v___x_5993_; lean_object* v___x_5994_; 
v___x_5992_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_));
v___x_5993_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_);
v___x_5994_ = l_Lean_Name_str___override(v___x_5993_, v___x_5992_);
return v___x_5994_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5995_; lean_object* v___x_5996_; lean_object* v___x_5997_; 
v___x_5995_ = lean_unsigned_to_nat(2u);
v___x_5996_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_);
v___x_5997_ = l_Lean_Name_num___override(v___x_5996_, v___x_5995_);
return v___x_5997_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5999_; uint8_t v___x_6000_; lean_object* v___x_6001_; lean_object* v___x_6002_; 
v___x_5999_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_));
v___x_6000_ = 1;
v___x_6001_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_);
v___x_6002_ = l_Lean_registerTraceClass(v___x_5999_, v___x_6000_, v___x_6001_);
return v___x_6002_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2____boxed(lean_object* v_a_6003_){
_start:
{
lean_object* v_res_6004_; 
v_res_6004_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_();
return v_res_6004_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_CompilerM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_PassManager(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_PhaseExt(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_CheckRC(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_PrettyPrinter(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_ExplicitRC(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Compiler_LCNF_CompilerM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_PassManager(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_PhaseExt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_CheckRC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_PrettyPrinter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_instInhabitedDerivedValInfo_default = _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_instInhabitedDerivedValInfo_default();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_instInhabitedDerivedValInfo_default);
l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_instInhabitedDerivedValInfo = _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_instInhabitedDerivedValInfo();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_instInhabitedDerivedValInfo);
l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_instInhabitedLiveVars_default = _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_instInhabitedLiveVars_default();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_instInhabitedLiveVars_default);
l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_instInhabitedLiveVars = _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_instInhabitedLiveVars();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_instInhabitedLiveVars);
l_Lean_Compiler_LCNF_explicitRc = _init_l_Lean_Compiler_LCNF_explicitRc();
lean_mark_persistent(l_Lean_Compiler_LCNF_explicitRc);
res = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_LCNF_ExplicitRC(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Compiler_LCNF_CompilerM(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_PassManager(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_PhaseExt(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_CheckRC(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_PrettyPrinter(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_ExplicitRC(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_CompilerM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_PassManager(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_PhaseExt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_CheckRC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_PrettyPrinter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_ExplicitRC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_LCNF_ExplicitRC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_LCNF_ExplicitRC(builtin);
}
#ifdef __cplusplus
}
#endif
