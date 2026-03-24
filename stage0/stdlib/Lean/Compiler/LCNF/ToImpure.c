// Lean compiler output
// Module: Lean.Compiler.LCNF.ToImpure
// Imports: import Lean.Compiler.LCNF.ToImpureType public import Lean.Compiler.LCNF.PassManager import Lean.Compiler.LCNF.PhaseExt import Init.Data.Format.Macro
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
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(uint8_t, lean_object*, lean_object*, uint8_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Compiler_LCNF_toImpureType(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_addParam(uint8_t, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isVoid(lean_object*);
uint8_t l_Lean_Expr_isErased(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
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
lean_object* l_ReaderT_instMonadLift___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_liftIOCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadLiftBaseIOEIO___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_instMonadLiftSTRealWorldBaseIO___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadLiftT___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_instMonadLiftTOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_instMonad___aux__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedCode_default__1(uint8_t);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(uint8_t, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_addLetDecl(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_hasTrivialImpureStructure_x3f(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_normFVarImp___redArg(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Compiler_LCNF_getCtorLayout(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Compiler_LCNF_getImpureSignature_x3f___redArg(lean_object*, lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkLetDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_boxed(lean_object*);
lean_object* l_Lean_Compiler_LCNF_getMonoDecl_x3f___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Compiler_LCNF_getPurity___redArg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_toLocalContext(lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_nameToImpureType(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_CtorInfo_type(lean_object*);
lean_object* l_Lean_Compiler_LCNF_LitValue_impureTypeScalarNumLit(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_addFunDecl(uint8_t, lean_object*, lean_object*);
lean_object* l_Array_zip___redArg(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Array_instInhabited(lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedAlt_default__1(uint8_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedParam_default(uint8_t);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_constName_x21(lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkReturnErased(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTagAttribute(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
uint8_t l_Lean_TagAttribute_hasTag(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_saveImpure___redArg(lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2____boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "tagged_return"};
static const lean_object* l_Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(42, 116, 83, 63, 133, 144, 27, 22)}};
static const lean_object* l_Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "mark extern definition to always return tagged values"};
static const lean_object* l_Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Compiler"};
static const lean_object* l_Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "LCNF"};
static const lean_object* l_Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "taggedReturnAttr"};
static const lean_object* l_Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(68, 195, 72, 11, 109, 136, 143, 118)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value_aux_1),((lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(229, 76, 245, 57, 5, 8, 44, 184)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value_aux_2),((lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(217, 168, 64, 69, 229, 21, 118, 230)}};
static const lean_object* l_Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__1_value),((lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__2 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__2_value),((lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(72, 245, 227, 28, 172, 102, 215, 20)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__3 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__3_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__3_value),((lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(225, 25, 15, 1, 146, 18, 87, 58)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__4 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__4_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "ToImpure"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__5 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__5_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__4_value),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(104, 151, 203, 144, 27, 18, 236, 68)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__6 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__6_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__6_value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(65, 46, 141, 239, 133, 91, 141, 199)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__7 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__7_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__7_value),((lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(228, 234, 69, 211, 145, 232, 229, 254)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__8 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__8_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__8_value),((lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(78, 187, 249, 147, 190, 91, 90, 40)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__9 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__9_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__9_value),((lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(183, 4, 28, 224, 230, 52, 114, 252)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__10 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__10_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__10_value),((lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(243, 95, 219, 231, 93, 109, 209, 250)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__11 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__11_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 150, .m_capacity = 150, .m_length = 149, .m_data = "Marks an extern definition to be guaranteed to always return tagged values.\nThis information is used to optimize reference counting in the compiler.\n"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__12 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__12_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__0;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__1;
static const lean_closure_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__2 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__2_value;
static const lean_closure_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__3 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__3_value;
static const lean_closure_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__4 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__4_value;
static const lean_closure_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__5 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__5_value;
static const lean_closure_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__6 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__6_value;
static const lean_closure_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadLift___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__7 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__7_value;
static const lean_closure_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_lift___boxed, .m_arity = 6, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__8 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__8_value;
static const lean_closure_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_liftIOCore___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__9 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__9_value;
static const lean_closure_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftBaseIOEIO___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__10 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__10_value;
static const lean_closure_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_IO_instMonadLiftSTRealWorldBaseIO___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__11 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__11_value;
static const lean_closure_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftT___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__12 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__12_value;
static const lean_closure_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftTOfMonadLift___redArg___lam__0, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__12_value),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__11_value)} };
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__13 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__13_value;
static const lean_closure_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftTOfMonadLift___redArg___lam__0, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__13_value),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__10_value)} };
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__14 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__14_value;
static const lean_closure_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftTOfMonadLift___redArg___lam__0, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__14_value),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__9_value)} };
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__15 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__15_value;
static const lean_closure_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftTOfMonadLift___redArg___lam__0, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__15_value),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__8_value)} };
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__16 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__16_value;
static const lean_closure_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftTOfMonadLift___redArg___lam__0, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__16_value),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__7_value)} };
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__17 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__17_value;
static const lean_closure_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_get___boxed, .m_arity = 5, .m_num_fixed = 4, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__17_value)} };
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__18 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__18_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstStateToImpureMPure___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstStateToImpureMPure___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstStateToImpureMPure___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstStateToImpureMPure___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstStateToImpureMPure___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstStateToImpureMPure___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstStateToImpureMPure = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstStateToImpureMPure___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "lcErased"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__0_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__0_value),LEAN_SCALAR_PTR_LITERAL(171, 218, 234, 194, 194, 57, 75, 5)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__1_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__2;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__3;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "USize"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__4 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__4_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__4_value),LEAN_SCALAR_PTR_LITERAL(109, 217, 26, 131, 232, 198, 207, 245)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__5 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__5_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__6;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "lcVoid"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__7 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__7_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__7_value),LEAN_SCALAR_PTR_LITERAL(68, 180, 59, 167, 252, 217, 37, 174)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__8 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__8_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__9;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__10;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Arg_toImpure___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Arg_toImpure___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Arg_toImpure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Arg_toImpure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity_spec__0(lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Lean.Compiler.LCNF.ToImpure"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__0_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 93, .m_capacity = 93, .m_length = 92, .m_data = "_private.Lean.Compiler.LCNF.ToImpure.0.Lean.Compiler.LCNF.lowerResultType.resultTypeForArity"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__1_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "invalid arity"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__2 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__2_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__3;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_lowerResultType(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_lowerResultType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "tobj"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__0_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__0_value),LEAN_SCALAR_PTR_LITERAL(25, 168, 138, 20, 203, 141, 233, 12)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__1_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__2;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "tagged"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__3 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__3_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__3_value),LEAN_SCALAR_PTR_LITERAL(167, 57, 252, 162, 142, 133, 51, 193)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__4 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__4_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__5;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "obj"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__6 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__6_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__6_value),LEAN_SCALAR_PTR_LITERAL(240, 235, 44, 74, 242, 121, 239, 90)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__7 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__7_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__8;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "UInt8"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__9 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__9_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__9_value),LEAN_SCALAR_PTR_LITERAL(144, 254, 64, 72, 7, 99, 197, 218)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__10 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__10_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__11;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UInt16"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__12 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__12_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__12_value),LEAN_SCALAR_PTR_LITERAL(6, 214, 154, 233, 192, 74, 99, 135)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__13 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__13_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__14;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UInt32"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__15 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__15_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__15_value),LEAN_SCALAR_PTR_LITERAL(98, 192, 58, 241, 186, 14, 255, 186)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__16 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__16_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__17;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UInt64"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__18 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__18_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__18_value),LEAN_SCALAR_PTR_LITERAL(58, 113, 45, 150, 103, 228, 0, 41)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__19 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__19_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__20;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__4(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "Std.Data.DHashMap.Internal.AssocList.Basic"};
static const lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___redArg___closed__0 = (const lean_object*)&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___redArg___closed__0_value;
static const lean_string_object l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.DHashMap.Internal.AssocList.get!"};
static const lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___redArg___closed__1 = (const lean_object*)&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___redArg___closed__1_value;
static const lean_string_object l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "key is not present in hash table"};
static const lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___redArg___closed__2 = (const lean_object*)&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___redArg___closed__2_value;
static lean_once_cell_t l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___redArg___closed__3;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___redArg___closed__0;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__3___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__0;
static lean_once_cell_t l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__1;
static lean_once_cell_t l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__11___redArg(size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__6___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__2___redArg(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "projection of non-structure type"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__1_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 67, .m_capacity = 67, .m_length = 66, .m_data = "_private.Lean.Compiler.LCNF.ToImpure.0.Lean.Compiler.LCNF.lowerLet"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__0_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueLet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueErased(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkOverApplication___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "overap"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkOverApplication___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkOverApplication___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkOverApplication(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkFap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkPap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkApplication(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "reference to unbound name"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__3 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__3_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__4;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "ToImpure: unexpected use of noncomputable declaration `"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__5 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__5_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__5_value)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__6 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__6_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "`; please report this issue"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__7 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__7_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__7_value)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__8 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__8_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__9;
static const lean_array_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__5 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__5_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "code generator does not support recursor `"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__10 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__10_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__10_value)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__11 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__11_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 67, .m_capacity = 67, .m_length = 66, .m_data = "` yet, consider using 'match ... with' and/or structural recursion"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__12 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__12_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__12_value)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__13 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__13_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 38, .m_data = "all local functions should be λ-lifted"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__1_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 72, .m_capacity = 72, .m_length = 71, .m_data = "_private.Lean.Compiler.LCNF.ToImpure.0.Lean.Compiler.LCNF.Code.toImpure"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__0_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__2;
static const lean_array_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__3 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__3_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__4;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "assertion violation: c.alts.size == 1\n      "};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__6 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__6_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__7;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__8;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "assertion violation: ctorName == info.ctorName\n      "};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__9 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__9_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__10;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 52, .m_capacity = 52, .m_length = 51, .m_data = "assertion violation: info.fieldIdx < ps.size\n      "};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__11 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__11_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__12;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__13 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__13_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__14;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "mismatched fields and params"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop___closed__1_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 76, .m_capacity = 76, .m_length = 75, .m_data = "_private.Lean.Compiler.LCNF.ToImpure.0.Lean.Compiler.LCNF.Alt.toImpure.loop"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop___closed__0_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__8(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkPap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkFap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueErased___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkApplication___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueLet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkOverApplication___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__2(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__6(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__11(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13_spec__17___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13_spec__17(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "Error while compiling function '"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__0_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__1;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 58, .m_capacity = 58, .m_length = 57, .m_data = "': @[tagged_return] is only valid for extern declarations"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__2 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__2_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__3;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "@[tagged_return] on function '"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__4 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__4_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__5;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "' with scalar return type "};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__6 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__6_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__0;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__1;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toImpure_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toImpure_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toImpure___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toImpure___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_toImpure___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_toImpure___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_toImpure___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_toImpure___closed__0_value;
static const lean_string_object l_Lean_Compiler_LCNF_toImpure___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "toImpure"};
static const lean_object* l_Lean_Compiler_LCNF_toImpure___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_toImpure___closed__1_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_toImpure___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_toImpure___closed__1_value),LEAN_SCALAR_PTR_LITERAL(136, 181, 13, 187, 73, 36, 105, 247)}};
static const lean_object* l_Lean_Compiler_LCNF_toImpure___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_toImpure___closed__2_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_toImpure___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_toImpure___closed__2_value),((lean_object*)&l_Lean_Compiler_LCNF_toImpure___closed__0_value),LEAN_SCALAR_PTR_LITERAL(1, 2, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Compiler_LCNF_toImpure___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_toImpure___closed__3_value;
LEAN_EXPORT const lean_object* l_Lean_Compiler_LCNF_toImpure = (const lean_object*)&l_Lean_Compiler_LCNF_toImpure___closed__3_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(253, 55, 142, 128, 91, 63, 88, 28)}};
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_toImpure___closed__1_value),LEAN_SCALAR_PTR_LITERAL(198, 36, 7, 136, 133, 159, 176, 55)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__10_value),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(134, 198, 164, 214, 24, 238, 231, 213)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(55, 168, 178, 247, 202, 119, 73, 243)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(202, 77, 105, 21, 218, 121, 239, 197)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(24, 184, 169, 248, 178, 143, 79, 195)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(209, 14, 162, 97, 10, 113, 167, 163)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(88, 160, 236, 105, 16, 144, 54, 23)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value),((lean_object*)(((size_t)(6355896) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(233, 87, 80, 162, 250, 65, 116, 159)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(186, 254, 170, 235, 80, 165, 179, 171)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(134, 19, 111, 73, 147, 106, 206, 64)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(135, 181, 11, 188, 89, 247, 207, 91)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_(lean_object* v_x_1_, lean_object* v___y_2_, lean_object* v___y_3_){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = lean_box(0);
v___x_6_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2____boxed(lean_object* v_x_7_, lean_object* v___y_8_, lean_object* v___y_9_, lean_object* v___y_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = l_Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_(v_x_7_, v___y_8_, v___y_9_);
lean_dec(v___y_9_);
lean_dec_ref(v___y_8_);
lean_dec(v_x_7_);
return v_res_11_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; uint8_t v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; 
v___f_27_ = ((lean_object*)(l_Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_));
v___x_28_ = ((lean_object*)(l_Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_));
v___x_29_ = ((lean_object*)(l_Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_));
v___x_30_ = ((lean_object*)(l_Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_));
v___x_31_ = 0;
v___x_32_ = lean_box(2);
v___x_33_ = l_Lean_registerTagAttribute(v___x_28_, v___x_29_, v___f_27_, v___x_30_, v___x_31_, v___x_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2____boxed(lean_object* v_a_34_){
_start:
{
lean_object* v_res_35_; 
v_res_35_ = l_Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_();
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1(){
_start:
{
lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_70_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__11));
v___x_71_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__12));
v___x_72_ = l_Lean_addBuiltinDocString(v___x_70_, v___x_71_);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___boxed(lean_object* v_a_73_){
_start:
{
lean_object* v_res_74_; 
v_res_74_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1();
return v_res_74_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___lam__0(lean_object* v_____do__lift_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_){
_start:
{
lean_object* v_subst_82_; lean_object* v___x_83_; 
v_subst_82_ = lean_ctor_get(v_____do__lift_75_, 0);
lean_inc_ref(v_subst_82_);
v___x_83_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_83_, 0, v_subst_82_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___lam__0___boxed(lean_object* v_____do__lift_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_){
_start:
{
lean_object* v_res_91_; 
v_res_91_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___lam__0(v_____do__lift_84_, v___y_85_, v___y_86_, v___y_87_, v___y_88_, v___y_89_);
lean_dec(v___y_89_);
lean_dec_ref(v___y_88_);
lean_dec(v___y_87_);
lean_dec_ref(v___y_86_);
lean_dec(v___y_85_);
lean_dec_ref(v_____do__lift_84_);
return v_res_91_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__0(void){
_start:
{
lean_object* v___x_92_; 
v___x_92_ = l_instMonadEIO(lean_box(0));
return v___x_92_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__1(void){
_start:
{
lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_93_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__0, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__0_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__0);
v___x_94_ = l_StateRefT_x27_instMonad___redArg(v___x_93_);
return v___x_94_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue(void){
_start:
{
lean_object* v___x_123_; lean_object* v_toApplicative_124_; lean_object* v___x_126_; uint8_t v_isShared_127_; uint8_t v_isSharedCheck_184_; 
v___x_123_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__1, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__1_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__1);
v_toApplicative_124_ = lean_ctor_get(v___x_123_, 0);
v_isSharedCheck_184_ = !lean_is_exclusive(v___x_123_);
if (v_isSharedCheck_184_ == 0)
{
lean_object* v_unused_185_; 
v_unused_185_ = lean_ctor_get(v___x_123_, 1);
lean_dec(v_unused_185_);
v___x_126_ = v___x_123_;
v_isShared_127_ = v_isSharedCheck_184_;
goto v_resetjp_125_;
}
else
{
lean_inc(v_toApplicative_124_);
lean_dec(v___x_123_);
v___x_126_ = lean_box(0);
v_isShared_127_ = v_isSharedCheck_184_;
goto v_resetjp_125_;
}
v_resetjp_125_:
{
lean_object* v_toFunctor_128_; lean_object* v_toSeq_129_; lean_object* v_toSeqLeft_130_; lean_object* v_toSeqRight_131_; lean_object* v___x_133_; uint8_t v_isShared_134_; uint8_t v_isSharedCheck_182_; 
v_toFunctor_128_ = lean_ctor_get(v_toApplicative_124_, 0);
v_toSeq_129_ = lean_ctor_get(v_toApplicative_124_, 2);
v_toSeqLeft_130_ = lean_ctor_get(v_toApplicative_124_, 3);
v_toSeqRight_131_ = lean_ctor_get(v_toApplicative_124_, 4);
v_isSharedCheck_182_ = !lean_is_exclusive(v_toApplicative_124_);
if (v_isSharedCheck_182_ == 0)
{
lean_object* v_unused_183_; 
v_unused_183_ = lean_ctor_get(v_toApplicative_124_, 1);
lean_dec(v_unused_183_);
v___x_133_ = v_toApplicative_124_;
v_isShared_134_ = v_isSharedCheck_182_;
goto v_resetjp_132_;
}
else
{
lean_inc(v_toSeqRight_131_);
lean_inc(v_toSeqLeft_130_);
lean_inc(v_toSeq_129_);
lean_inc(v_toFunctor_128_);
lean_dec(v_toApplicative_124_);
v___x_133_ = lean_box(0);
v_isShared_134_ = v_isSharedCheck_182_;
goto v_resetjp_132_;
}
v_resetjp_132_:
{
lean_object* v___f_135_; lean_object* v___f_136_; lean_object* v___f_137_; lean_object* v___f_138_; lean_object* v___x_139_; lean_object* v___f_140_; lean_object* v___f_141_; lean_object* v___f_142_; lean_object* v___x_144_; 
v___f_135_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__2));
v___f_136_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__3));
lean_inc_ref(v_toFunctor_128_);
v___f_137_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_137_, 0, v_toFunctor_128_);
v___f_138_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_138_, 0, v_toFunctor_128_);
v___x_139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_139_, 0, v___f_137_);
lean_ctor_set(v___x_139_, 1, v___f_138_);
v___f_140_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_140_, 0, v_toSeqRight_131_);
v___f_141_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_141_, 0, v_toSeqLeft_130_);
v___f_142_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_142_, 0, v_toSeq_129_);
if (v_isShared_134_ == 0)
{
lean_ctor_set(v___x_133_, 4, v___f_140_);
lean_ctor_set(v___x_133_, 3, v___f_141_);
lean_ctor_set(v___x_133_, 2, v___f_142_);
lean_ctor_set(v___x_133_, 1, v___f_135_);
lean_ctor_set(v___x_133_, 0, v___x_139_);
v___x_144_ = v___x_133_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_181_; 
v_reuseFailAlloc_181_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_181_, 0, v___x_139_);
lean_ctor_set(v_reuseFailAlloc_181_, 1, v___f_135_);
lean_ctor_set(v_reuseFailAlloc_181_, 2, v___f_142_);
lean_ctor_set(v_reuseFailAlloc_181_, 3, v___f_141_);
lean_ctor_set(v_reuseFailAlloc_181_, 4, v___f_140_);
v___x_144_ = v_reuseFailAlloc_181_;
goto v_reusejp_143_;
}
v_reusejp_143_:
{
lean_object* v___x_146_; 
if (v_isShared_127_ == 0)
{
lean_ctor_set(v___x_126_, 1, v___f_136_);
lean_ctor_set(v___x_126_, 0, v___x_144_);
v___x_146_ = v___x_126_;
goto v_reusejp_145_;
}
else
{
lean_object* v_reuseFailAlloc_180_; 
v_reuseFailAlloc_180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_180_, 0, v___x_144_);
lean_ctor_set(v_reuseFailAlloc_180_, 1, v___f_136_);
v___x_146_ = v_reuseFailAlloc_180_;
goto v_reusejp_145_;
}
v_reusejp_145_:
{
lean_object* v___x_147_; lean_object* v_toApplicative_148_; lean_object* v___x_150_; uint8_t v_isShared_151_; uint8_t v_isSharedCheck_178_; 
v___x_147_ = l_StateRefT_x27_instMonad___redArg(v___x_146_);
v_toApplicative_148_ = lean_ctor_get(v___x_147_, 0);
v_isSharedCheck_178_ = !lean_is_exclusive(v___x_147_);
if (v_isSharedCheck_178_ == 0)
{
lean_object* v_unused_179_; 
v_unused_179_ = lean_ctor_get(v___x_147_, 1);
lean_dec(v_unused_179_);
v___x_150_ = v___x_147_;
v_isShared_151_ = v_isSharedCheck_178_;
goto v_resetjp_149_;
}
else
{
lean_inc(v_toApplicative_148_);
lean_dec(v___x_147_);
v___x_150_ = lean_box(0);
v_isShared_151_ = v_isSharedCheck_178_;
goto v_resetjp_149_;
}
v_resetjp_149_:
{
lean_object* v_toFunctor_152_; lean_object* v_toSeq_153_; lean_object* v_toSeqLeft_154_; lean_object* v_toSeqRight_155_; lean_object* v___x_157_; uint8_t v_isShared_158_; uint8_t v_isSharedCheck_176_; 
v_toFunctor_152_ = lean_ctor_get(v_toApplicative_148_, 0);
v_toSeq_153_ = lean_ctor_get(v_toApplicative_148_, 2);
v_toSeqLeft_154_ = lean_ctor_get(v_toApplicative_148_, 3);
v_toSeqRight_155_ = lean_ctor_get(v_toApplicative_148_, 4);
v_isSharedCheck_176_ = !lean_is_exclusive(v_toApplicative_148_);
if (v_isSharedCheck_176_ == 0)
{
lean_object* v_unused_177_; 
v_unused_177_ = lean_ctor_get(v_toApplicative_148_, 1);
lean_dec(v_unused_177_);
v___x_157_ = v_toApplicative_148_;
v_isShared_158_ = v_isSharedCheck_176_;
goto v_resetjp_156_;
}
else
{
lean_inc(v_toSeqRight_155_);
lean_inc(v_toSeqLeft_154_);
lean_inc(v_toSeq_153_);
lean_inc(v_toFunctor_152_);
lean_dec(v_toApplicative_148_);
v___x_157_ = lean_box(0);
v_isShared_158_ = v_isSharedCheck_176_;
goto v_resetjp_156_;
}
v_resetjp_156_:
{
lean_object* v___f_159_; lean_object* v___f_160_; lean_object* v___f_161_; lean_object* v___f_162_; lean_object* v___f_163_; lean_object* v___x_164_; lean_object* v___f_165_; lean_object* v___f_166_; lean_object* v___f_167_; lean_object* v___x_169_; 
v___f_159_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__4));
v___f_160_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__5));
v___f_161_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__6));
lean_inc_ref(v_toFunctor_152_);
v___f_162_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_162_, 0, v_toFunctor_152_);
v___f_163_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_163_, 0, v_toFunctor_152_);
v___x_164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_164_, 0, v___f_162_);
lean_ctor_set(v___x_164_, 1, v___f_163_);
v___f_165_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_165_, 0, v_toSeqRight_155_);
v___f_166_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_166_, 0, v_toSeqLeft_154_);
v___f_167_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_167_, 0, v_toSeq_153_);
if (v_isShared_158_ == 0)
{
lean_ctor_set(v___x_157_, 4, v___f_165_);
lean_ctor_set(v___x_157_, 3, v___f_166_);
lean_ctor_set(v___x_157_, 2, v___f_167_);
lean_ctor_set(v___x_157_, 1, v___f_160_);
lean_ctor_set(v___x_157_, 0, v___x_164_);
v___x_169_ = v___x_157_;
goto v_reusejp_168_;
}
else
{
lean_object* v_reuseFailAlloc_175_; 
v_reuseFailAlloc_175_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_175_, 0, v___x_164_);
lean_ctor_set(v_reuseFailAlloc_175_, 1, v___f_160_);
lean_ctor_set(v_reuseFailAlloc_175_, 2, v___f_167_);
lean_ctor_set(v_reuseFailAlloc_175_, 3, v___f_166_);
lean_ctor_set(v_reuseFailAlloc_175_, 4, v___f_165_);
v___x_169_ = v_reuseFailAlloc_175_;
goto v_reusejp_168_;
}
v_reusejp_168_:
{
lean_object* v___x_171_; 
if (v_isShared_151_ == 0)
{
lean_ctor_set(v___x_150_, 1, v___f_161_);
lean_ctor_set(v___x_150_, 0, v___x_169_);
v___x_171_ = v___x_150_;
goto v_reusejp_170_;
}
else
{
lean_object* v_reuseFailAlloc_174_; 
v_reuseFailAlloc_174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_174_, 0, v___x_169_);
lean_ctor_set(v_reuseFailAlloc_174_, 1, v___f_161_);
v___x_171_ = v_reuseFailAlloc_174_;
goto v_reusejp_170_;
}
v_reusejp_170_:
{
lean_object* v___x_172_; lean_object* v___x_173_; 
v___x_172_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__18));
v___x_173_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonad___aux__13___boxed), 9, 8);
lean_closure_set(v___x_173_, 0, lean_box(0));
lean_closure_set(v___x_173_, 1, lean_box(0));
lean_closure_set(v___x_173_, 2, lean_box(0));
lean_closure_set(v___x_173_, 3, v___x_171_);
lean_closure_set(v___x_173_, 4, lean_box(0));
lean_closure_set(v___x_173_, 5, lean_box(0));
lean_closure_set(v___x_173_, 6, v___x_172_);
lean_closure_set(v___x_173_, 7, v___f_159_);
return v___x_173_;
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
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstStateToImpureMPure___lam__0(lean_object* v_f_186_, lean_object* v___y_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_){
_start:
{
lean_object* v___x_193_; lean_object* v_subst_194_; lean_object* v_jpParamMask_195_; lean_object* v___x_197_; uint8_t v_isShared_198_; uint8_t v_isSharedCheck_206_; 
v___x_193_ = lean_st_ref_take(v___y_187_);
v_subst_194_ = lean_ctor_get(v___x_193_, 0);
v_jpParamMask_195_ = lean_ctor_get(v___x_193_, 1);
v_isSharedCheck_206_ = !lean_is_exclusive(v___x_193_);
if (v_isSharedCheck_206_ == 0)
{
v___x_197_ = v___x_193_;
v_isShared_198_ = v_isSharedCheck_206_;
goto v_resetjp_196_;
}
else
{
lean_inc(v_jpParamMask_195_);
lean_inc(v_subst_194_);
lean_dec(v___x_193_);
v___x_197_ = lean_box(0);
v_isShared_198_ = v_isSharedCheck_206_;
goto v_resetjp_196_;
}
v_resetjp_196_:
{
lean_object* v___x_199_; lean_object* v___x_201_; 
v___x_199_ = lean_apply_1(v_f_186_, v_subst_194_);
if (v_isShared_198_ == 0)
{
lean_ctor_set(v___x_197_, 0, v___x_199_);
v___x_201_ = v___x_197_;
goto v_reusejp_200_;
}
else
{
lean_object* v_reuseFailAlloc_205_; 
v_reuseFailAlloc_205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_205_, 0, v___x_199_);
lean_ctor_set(v_reuseFailAlloc_205_, 1, v_jpParamMask_195_);
v___x_201_ = v_reuseFailAlloc_205_;
goto v_reusejp_200_;
}
v_reusejp_200_:
{
lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; 
v___x_202_ = lean_st_ref_set(v___y_187_, v___x_201_);
v___x_203_ = lean_box(0);
v___x_204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_204_, 0, v___x_203_);
return v___x_204_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstStateToImpureMPure___lam__0___boxed(lean_object* v_f_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_){
_start:
{
lean_object* v_res_214_; 
v_res_214_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstStateToImpureMPure___lam__0(v_f_207_, v___y_208_, v___y_209_, v___y_210_, v___y_211_, v___y_212_);
lean_dec(v___y_212_);
lean_dec_ref(v___y_211_);
lean_dec(v___y_210_);
lean_dec_ref(v___y_209_);
lean_dec(v___y_208_);
return v_res_214_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__2___redArg(lean_object* v_a_217_, lean_object* v_b_218_, lean_object* v_x_219_){
_start:
{
if (lean_obj_tag(v_x_219_) == 0)
{
lean_dec(v_b_218_);
lean_dec(v_a_217_);
return v_x_219_;
}
else
{
lean_object* v_key_220_; lean_object* v_value_221_; lean_object* v_tail_222_; lean_object* v___x_224_; uint8_t v_isShared_225_; uint8_t v_isSharedCheck_234_; 
v_key_220_ = lean_ctor_get(v_x_219_, 0);
v_value_221_ = lean_ctor_get(v_x_219_, 1);
v_tail_222_ = lean_ctor_get(v_x_219_, 2);
v_isSharedCheck_234_ = !lean_is_exclusive(v_x_219_);
if (v_isSharedCheck_234_ == 0)
{
v___x_224_ = v_x_219_;
v_isShared_225_ = v_isSharedCheck_234_;
goto v_resetjp_223_;
}
else
{
lean_inc(v_tail_222_);
lean_inc(v_value_221_);
lean_inc(v_key_220_);
lean_dec(v_x_219_);
v___x_224_ = lean_box(0);
v_isShared_225_ = v_isSharedCheck_234_;
goto v_resetjp_223_;
}
v_resetjp_223_:
{
uint8_t v___x_226_; 
v___x_226_ = l_Lean_instBEqFVarId_beq(v_key_220_, v_a_217_);
if (v___x_226_ == 0)
{
lean_object* v___x_227_; lean_object* v___x_229_; 
v___x_227_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__2___redArg(v_a_217_, v_b_218_, v_tail_222_);
if (v_isShared_225_ == 0)
{
lean_ctor_set(v___x_224_, 2, v___x_227_);
v___x_229_ = v___x_224_;
goto v_reusejp_228_;
}
else
{
lean_object* v_reuseFailAlloc_230_; 
v_reuseFailAlloc_230_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_230_, 0, v_key_220_);
lean_ctor_set(v_reuseFailAlloc_230_, 1, v_value_221_);
lean_ctor_set(v_reuseFailAlloc_230_, 2, v___x_227_);
v___x_229_ = v_reuseFailAlloc_230_;
goto v_reusejp_228_;
}
v_reusejp_228_:
{
return v___x_229_;
}
}
else
{
lean_object* v___x_232_; 
lean_dec(v_value_221_);
lean_dec(v_key_220_);
if (v_isShared_225_ == 0)
{
lean_ctor_set(v___x_224_, 1, v_b_218_);
lean_ctor_set(v___x_224_, 0, v_a_217_);
v___x_232_ = v___x_224_;
goto v_reusejp_231_;
}
else
{
lean_object* v_reuseFailAlloc_233_; 
v_reuseFailAlloc_233_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_233_, 0, v_a_217_);
lean_ctor_set(v_reuseFailAlloc_233_, 1, v_b_218_);
lean_ctor_set(v_reuseFailAlloc_233_, 2, v_tail_222_);
v___x_232_ = v_reuseFailAlloc_233_;
goto v_reusejp_231_;
}
v_reusejp_231_:
{
return v___x_232_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_235_, lean_object* v_x_236_){
_start:
{
if (lean_obj_tag(v_x_236_) == 0)
{
return v_x_235_;
}
else
{
lean_object* v_key_237_; lean_object* v_value_238_; lean_object* v_tail_239_; lean_object* v___x_241_; uint8_t v_isShared_242_; uint8_t v_isSharedCheck_262_; 
v_key_237_ = lean_ctor_get(v_x_236_, 0);
v_value_238_ = lean_ctor_get(v_x_236_, 1);
v_tail_239_ = lean_ctor_get(v_x_236_, 2);
v_isSharedCheck_262_ = !lean_is_exclusive(v_x_236_);
if (v_isSharedCheck_262_ == 0)
{
v___x_241_ = v_x_236_;
v_isShared_242_ = v_isSharedCheck_262_;
goto v_resetjp_240_;
}
else
{
lean_inc(v_tail_239_);
lean_inc(v_value_238_);
lean_inc(v_key_237_);
lean_dec(v_x_236_);
v___x_241_ = lean_box(0);
v_isShared_242_ = v_isSharedCheck_262_;
goto v_resetjp_240_;
}
v_resetjp_240_:
{
lean_object* v___x_243_; uint64_t v___x_244_; uint64_t v___x_245_; uint64_t v___x_246_; uint64_t v_fold_247_; uint64_t v___x_248_; uint64_t v___x_249_; uint64_t v___x_250_; size_t v___x_251_; size_t v___x_252_; size_t v___x_253_; size_t v___x_254_; size_t v___x_255_; lean_object* v___x_256_; lean_object* v___x_258_; 
v___x_243_ = lean_array_get_size(v_x_235_);
v___x_244_ = l_Lean_instHashableFVarId_hash(v_key_237_);
v___x_245_ = 32ULL;
v___x_246_ = lean_uint64_shift_right(v___x_244_, v___x_245_);
v_fold_247_ = lean_uint64_xor(v___x_244_, v___x_246_);
v___x_248_ = 16ULL;
v___x_249_ = lean_uint64_shift_right(v_fold_247_, v___x_248_);
v___x_250_ = lean_uint64_xor(v_fold_247_, v___x_249_);
v___x_251_ = lean_uint64_to_usize(v___x_250_);
v___x_252_ = lean_usize_of_nat(v___x_243_);
v___x_253_ = ((size_t)1ULL);
v___x_254_ = lean_usize_sub(v___x_252_, v___x_253_);
v___x_255_ = lean_usize_land(v___x_251_, v___x_254_);
v___x_256_ = lean_array_uget_borrowed(v_x_235_, v___x_255_);
lean_inc(v___x_256_);
if (v_isShared_242_ == 0)
{
lean_ctor_set(v___x_241_, 2, v___x_256_);
v___x_258_ = v___x_241_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v_key_237_);
lean_ctor_set(v_reuseFailAlloc_261_, 1, v_value_238_);
lean_ctor_set(v_reuseFailAlloc_261_, 2, v___x_256_);
v___x_258_ = v_reuseFailAlloc_261_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
lean_object* v___x_259_; 
v___x_259_ = lean_array_uset(v_x_235_, v___x_255_, v___x_258_);
v_x_235_ = v___x_259_;
v_x_236_ = v_tail_239_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__1_spec__2___redArg(lean_object* v_i_263_, lean_object* v_source_264_, lean_object* v_target_265_){
_start:
{
lean_object* v___x_266_; uint8_t v___x_267_; 
v___x_266_ = lean_array_get_size(v_source_264_);
v___x_267_ = lean_nat_dec_lt(v_i_263_, v___x_266_);
if (v___x_267_ == 0)
{
lean_dec_ref(v_source_264_);
lean_dec(v_i_263_);
return v_target_265_;
}
else
{
lean_object* v_es_268_; lean_object* v___x_269_; lean_object* v_source_270_; lean_object* v_target_271_; lean_object* v___x_272_; lean_object* v___x_273_; 
v_es_268_ = lean_array_fget(v_source_264_, v_i_263_);
v___x_269_ = lean_box(0);
v_source_270_ = lean_array_fset(v_source_264_, v_i_263_, v___x_269_);
v_target_271_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__1_spec__2_spec__3___redArg(v_target_265_, v_es_268_);
v___x_272_ = lean_unsigned_to_nat(1u);
v___x_273_ = lean_nat_add(v_i_263_, v___x_272_);
lean_dec(v_i_263_);
v_i_263_ = v___x_273_;
v_source_264_ = v_source_270_;
v_target_265_ = v_target_271_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__1___redArg(lean_object* v_data_275_){
_start:
{
lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v_nbuckets_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_276_ = lean_array_get_size(v_data_275_);
v___x_277_ = lean_unsigned_to_nat(2u);
v_nbuckets_278_ = lean_nat_mul(v___x_276_, v___x_277_);
v___x_279_ = lean_unsigned_to_nat(0u);
v___x_280_ = lean_box(0);
v___x_281_ = lean_mk_array(v_nbuckets_278_, v___x_280_);
v___x_282_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__1_spec__2___redArg(v___x_279_, v_data_275_, v___x_281_);
return v___x_282_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__0___redArg(lean_object* v_a_283_, lean_object* v_x_284_){
_start:
{
if (lean_obj_tag(v_x_284_) == 0)
{
uint8_t v___x_285_; 
v___x_285_ = 0;
return v___x_285_;
}
else
{
lean_object* v_key_286_; lean_object* v_tail_287_; uint8_t v___x_288_; 
v_key_286_ = lean_ctor_get(v_x_284_, 0);
v_tail_287_ = lean_ctor_get(v_x_284_, 2);
v___x_288_ = l_Lean_instBEqFVarId_beq(v_key_286_, v_a_283_);
if (v___x_288_ == 0)
{
v_x_284_ = v_tail_287_;
goto _start;
}
else
{
return v___x_288_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__0___redArg___boxed(lean_object* v_a_290_, lean_object* v_x_291_){
_start:
{
uint8_t v_res_292_; lean_object* v_r_293_; 
v_res_292_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__0___redArg(v_a_290_, v_x_291_);
lean_dec(v_x_291_);
lean_dec(v_a_290_);
v_r_293_ = lean_box(v_res_292_);
return v_r_293_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(lean_object* v_m_294_, lean_object* v_a_295_, lean_object* v_b_296_){
_start:
{
lean_object* v_size_297_; lean_object* v_buckets_298_; lean_object* v___x_300_; uint8_t v_isShared_301_; uint8_t v_isSharedCheck_341_; 
v_size_297_ = lean_ctor_get(v_m_294_, 0);
v_buckets_298_ = lean_ctor_get(v_m_294_, 1);
v_isSharedCheck_341_ = !lean_is_exclusive(v_m_294_);
if (v_isSharedCheck_341_ == 0)
{
v___x_300_ = v_m_294_;
v_isShared_301_ = v_isSharedCheck_341_;
goto v_resetjp_299_;
}
else
{
lean_inc(v_buckets_298_);
lean_inc(v_size_297_);
lean_dec(v_m_294_);
v___x_300_ = lean_box(0);
v_isShared_301_ = v_isSharedCheck_341_;
goto v_resetjp_299_;
}
v_resetjp_299_:
{
lean_object* v___x_302_; uint64_t v___x_303_; uint64_t v___x_304_; uint64_t v___x_305_; uint64_t v_fold_306_; uint64_t v___x_307_; uint64_t v___x_308_; uint64_t v___x_309_; size_t v___x_310_; size_t v___x_311_; size_t v___x_312_; size_t v___x_313_; size_t v___x_314_; lean_object* v_bkt_315_; uint8_t v___x_316_; 
v___x_302_ = lean_array_get_size(v_buckets_298_);
v___x_303_ = l_Lean_instHashableFVarId_hash(v_a_295_);
v___x_304_ = 32ULL;
v___x_305_ = lean_uint64_shift_right(v___x_303_, v___x_304_);
v_fold_306_ = lean_uint64_xor(v___x_303_, v___x_305_);
v___x_307_ = 16ULL;
v___x_308_ = lean_uint64_shift_right(v_fold_306_, v___x_307_);
v___x_309_ = lean_uint64_xor(v_fold_306_, v___x_308_);
v___x_310_ = lean_uint64_to_usize(v___x_309_);
v___x_311_ = lean_usize_of_nat(v___x_302_);
v___x_312_ = ((size_t)1ULL);
v___x_313_ = lean_usize_sub(v___x_311_, v___x_312_);
v___x_314_ = lean_usize_land(v___x_310_, v___x_313_);
v_bkt_315_ = lean_array_uget_borrowed(v_buckets_298_, v___x_314_);
v___x_316_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__0___redArg(v_a_295_, v_bkt_315_);
if (v___x_316_ == 0)
{
lean_object* v___x_317_; lean_object* v_size_x27_318_; lean_object* v___x_319_; lean_object* v_buckets_x27_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; uint8_t v___x_326_; 
v___x_317_ = lean_unsigned_to_nat(1u);
v_size_x27_318_ = lean_nat_add(v_size_297_, v___x_317_);
lean_dec(v_size_297_);
lean_inc(v_bkt_315_);
v___x_319_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_319_, 0, v_a_295_);
lean_ctor_set(v___x_319_, 1, v_b_296_);
lean_ctor_set(v___x_319_, 2, v_bkt_315_);
v_buckets_x27_320_ = lean_array_uset(v_buckets_298_, v___x_314_, v___x_319_);
v___x_321_ = lean_unsigned_to_nat(4u);
v___x_322_ = lean_nat_mul(v_size_x27_318_, v___x_321_);
v___x_323_ = lean_unsigned_to_nat(3u);
v___x_324_ = lean_nat_div(v___x_322_, v___x_323_);
lean_dec(v___x_322_);
v___x_325_ = lean_array_get_size(v_buckets_x27_320_);
v___x_326_ = lean_nat_dec_le(v___x_324_, v___x_325_);
lean_dec(v___x_324_);
if (v___x_326_ == 0)
{
lean_object* v_val_327_; lean_object* v___x_329_; 
v_val_327_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__1___redArg(v_buckets_x27_320_);
if (v_isShared_301_ == 0)
{
lean_ctor_set(v___x_300_, 1, v_val_327_);
lean_ctor_set(v___x_300_, 0, v_size_x27_318_);
v___x_329_ = v___x_300_;
goto v_reusejp_328_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v_size_x27_318_);
lean_ctor_set(v_reuseFailAlloc_330_, 1, v_val_327_);
v___x_329_ = v_reuseFailAlloc_330_;
goto v_reusejp_328_;
}
v_reusejp_328_:
{
return v___x_329_;
}
}
else
{
lean_object* v___x_332_; 
if (v_isShared_301_ == 0)
{
lean_ctor_set(v___x_300_, 1, v_buckets_x27_320_);
lean_ctor_set(v___x_300_, 0, v_size_x27_318_);
v___x_332_ = v___x_300_;
goto v_reusejp_331_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v_size_x27_318_);
lean_ctor_set(v_reuseFailAlloc_333_, 1, v_buckets_x27_320_);
v___x_332_ = v_reuseFailAlloc_333_;
goto v_reusejp_331_;
}
v_reusejp_331_:
{
return v___x_332_;
}
}
}
else
{
lean_object* v___x_334_; lean_object* v_buckets_x27_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_339_; 
lean_inc(v_bkt_315_);
v___x_334_ = lean_box(0);
v_buckets_x27_335_ = lean_array_uset(v_buckets_298_, v___x_314_, v___x_334_);
v___x_336_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__2___redArg(v_a_295_, v_b_296_, v_bkt_315_);
v___x_337_ = lean_array_uset(v_buckets_x27_335_, v___x_314_, v___x_336_);
if (v_isShared_301_ == 0)
{
lean_ctor_set(v___x_300_, 1, v___x_337_);
v___x_339_ = v___x_300_;
goto v_reusejp_338_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v_size_297_);
lean_ctor_set(v_reuseFailAlloc_340_, 1, v___x_337_);
v___x_339_ = v_reuseFailAlloc_340_;
goto v_reusejp_338_;
}
v_reusejp_338_:
{
return v___x_339_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure___redArg(lean_object* v_p_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_){
_start:
{
lean_object* v_fvarId_348_; lean_object* v_binderName_349_; lean_object* v_type_350_; uint8_t v_borrow_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_408_; 
v_fvarId_348_ = lean_ctor_get(v_p_342_, 0);
v_binderName_349_ = lean_ctor_get(v_p_342_, 1);
v_type_350_ = lean_ctor_get(v_p_342_, 2);
v_borrow_351_ = lean_ctor_get_uint8(v_p_342_, sizeof(void*)*3);
v_isSharedCheck_408_ = !lean_is_exclusive(v_p_342_);
if (v_isSharedCheck_408_ == 0)
{
v___x_353_ = v_p_342_;
v_isShared_354_ = v_isSharedCheck_408_;
goto v_resetjp_352_;
}
else
{
lean_inc(v_type_350_);
lean_inc(v_binderName_349_);
lean_inc(v_fvarId_348_);
lean_dec(v_p_342_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_408_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
uint8_t v___x_355_; lean_object* v___x_356_; 
v___x_355_ = 0;
v___x_356_ = l_Lean_Compiler_LCNF_toImpureType(v_type_350_, v___x_355_, v_a_345_, v_a_346_);
if (lean_obj_tag(v___x_356_) == 0)
{
lean_object* v_a_357_; lean_object* v___x_359_; uint8_t v_isShared_360_; uint8_t v_isSharedCheck_399_; 
v_a_357_ = lean_ctor_get(v___x_356_, 0);
v_isSharedCheck_399_ = !lean_is_exclusive(v___x_356_);
if (v_isSharedCheck_399_ == 0)
{
v___x_359_ = v___x_356_;
v_isShared_360_ = v_isSharedCheck_399_;
goto v_resetjp_358_;
}
else
{
lean_inc(v_a_357_);
lean_dec(v___x_356_);
v___x_359_ = lean_box(0);
v_isShared_360_ = v_isSharedCheck_399_;
goto v_resetjp_358_;
}
v_resetjp_358_:
{
lean_object* v___y_362_; uint8_t v___y_383_; uint8_t v___x_397_; 
v___x_397_ = l_Lean_Expr_isVoid(v_a_357_);
if (v___x_397_ == 0)
{
uint8_t v___x_398_; 
v___x_398_ = l_Lean_Expr_isErased(v_a_357_);
v___y_383_ = v___x_398_;
goto v___jp_382_;
}
else
{
v___y_383_ = v___x_397_;
goto v___jp_382_;
}
v___jp_361_:
{
lean_object* v___x_363_; lean_object* v_lctx_364_; lean_object* v_nextIdx_365_; lean_object* v___x_367_; uint8_t v_isShared_368_; uint8_t v_isSharedCheck_381_; 
v___x_363_ = lean_st_ref_take(v___y_362_);
v_lctx_364_ = lean_ctor_get(v___x_363_, 0);
v_nextIdx_365_ = lean_ctor_get(v___x_363_, 1);
v_isSharedCheck_381_ = !lean_is_exclusive(v___x_363_);
if (v_isSharedCheck_381_ == 0)
{
v___x_367_ = v___x_363_;
v_isShared_368_ = v_isSharedCheck_381_;
goto v_resetjp_366_;
}
else
{
lean_inc(v_nextIdx_365_);
lean_inc(v_lctx_364_);
lean_dec(v___x_363_);
v___x_367_ = lean_box(0);
v_isShared_368_ = v_isSharedCheck_381_;
goto v_resetjp_366_;
}
v_resetjp_366_:
{
uint8_t v___x_369_; lean_object* v___x_371_; 
v___x_369_ = 1;
if (v_isShared_354_ == 0)
{
lean_ctor_set(v___x_353_, 2, v_a_357_);
v___x_371_ = v___x_353_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v_fvarId_348_);
lean_ctor_set(v_reuseFailAlloc_380_, 1, v_binderName_349_);
lean_ctor_set(v_reuseFailAlloc_380_, 2, v_a_357_);
lean_ctor_set_uint8(v_reuseFailAlloc_380_, sizeof(void*)*3, v_borrow_351_);
v___x_371_ = v_reuseFailAlloc_380_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
lean_object* v___x_372_; lean_object* v___x_374_; 
lean_inc_ref(v___x_371_);
v___x_372_ = l_Lean_Compiler_LCNF_LCtx_addParam(v___x_369_, v_lctx_364_, v___x_371_);
if (v_isShared_368_ == 0)
{
lean_ctor_set(v___x_367_, 0, v___x_372_);
v___x_374_ = v___x_367_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_379_; 
v_reuseFailAlloc_379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_379_, 0, v___x_372_);
lean_ctor_set(v_reuseFailAlloc_379_, 1, v_nextIdx_365_);
v___x_374_ = v_reuseFailAlloc_379_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
lean_object* v___x_375_; lean_object* v___x_377_; 
v___x_375_ = lean_st_ref_set(v___y_362_, v___x_374_);
if (v_isShared_360_ == 0)
{
lean_ctor_set(v___x_359_, 0, v___x_371_);
v___x_377_ = v___x_359_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v___x_371_);
v___x_377_ = v_reuseFailAlloc_378_;
goto v_reusejp_376_;
}
v_reusejp_376_:
{
return v___x_377_;
}
}
}
}
}
v___jp_382_:
{
if (v___y_383_ == 0)
{
v___y_362_ = v_a_344_;
goto v___jp_361_;
}
else
{
lean_object* v___x_384_; lean_object* v_subst_385_; lean_object* v_jpParamMask_386_; lean_object* v___x_388_; uint8_t v_isShared_389_; uint8_t v_isSharedCheck_396_; 
v___x_384_ = lean_st_ref_take(v_a_343_);
v_subst_385_ = lean_ctor_get(v___x_384_, 0);
v_jpParamMask_386_ = lean_ctor_get(v___x_384_, 1);
v_isSharedCheck_396_ = !lean_is_exclusive(v___x_384_);
if (v_isSharedCheck_396_ == 0)
{
v___x_388_ = v___x_384_;
v_isShared_389_ = v_isSharedCheck_396_;
goto v_resetjp_387_;
}
else
{
lean_inc(v_jpParamMask_386_);
lean_inc(v_subst_385_);
lean_dec(v___x_384_);
v___x_388_ = lean_box(0);
v_isShared_389_ = v_isSharedCheck_396_;
goto v_resetjp_387_;
}
v_resetjp_387_:
{
lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_393_; 
v___x_390_ = lean_box(0);
lean_inc(v_fvarId_348_);
v___x_391_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v_subst_385_, v_fvarId_348_, v___x_390_);
if (v_isShared_389_ == 0)
{
lean_ctor_set(v___x_388_, 0, v___x_391_);
v___x_393_ = v___x_388_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v___x_391_);
lean_ctor_set(v_reuseFailAlloc_395_, 1, v_jpParamMask_386_);
v___x_393_ = v_reuseFailAlloc_395_;
goto v_reusejp_392_;
}
v_reusejp_392_:
{
lean_object* v___x_394_; 
v___x_394_ = lean_st_ref_set(v_a_343_, v___x_393_);
v___y_362_ = v_a_344_;
goto v___jp_361_;
}
}
}
}
}
}
else
{
lean_object* v_a_400_; lean_object* v___x_402_; uint8_t v_isShared_403_; uint8_t v_isSharedCheck_407_; 
lean_del_object(v___x_353_);
lean_dec(v_binderName_349_);
lean_dec(v_fvarId_348_);
v_a_400_ = lean_ctor_get(v___x_356_, 0);
v_isSharedCheck_407_ = !lean_is_exclusive(v___x_356_);
if (v_isSharedCheck_407_ == 0)
{
v___x_402_ = v___x_356_;
v_isShared_403_ = v_isSharedCheck_407_;
goto v_resetjp_401_;
}
else
{
lean_inc(v_a_400_);
lean_dec(v___x_356_);
v___x_402_ = lean_box(0);
v_isShared_403_ = v_isSharedCheck_407_;
goto v_resetjp_401_;
}
v_resetjp_401_:
{
lean_object* v___x_405_; 
if (v_isShared_403_ == 0)
{
v___x_405_ = v___x_402_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v_a_400_);
v___x_405_ = v_reuseFailAlloc_406_;
goto v_reusejp_404_;
}
v_reusejp_404_:
{
return v___x_405_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure___redArg___boxed(lean_object* v_p_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_){
_start:
{
lean_object* v_res_415_; 
v_res_415_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure___redArg(v_p_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_);
lean_dec(v_a_413_);
lean_dec_ref(v_a_412_);
lean_dec(v_a_411_);
lean_dec(v_a_410_);
return v_res_415_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure(lean_object* v_p_416_, lean_object* v_a_417_, lean_object* v_a_418_, lean_object* v_a_419_, lean_object* v_a_420_, lean_object* v_a_421_){
_start:
{
lean_object* v___x_423_; 
v___x_423_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure___redArg(v_p_416_, v_a_417_, v_a_419_, v_a_420_, v_a_421_);
return v___x_423_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure___boxed(lean_object* v_p_424_, lean_object* v_a_425_, lean_object* v_a_426_, lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_){
_start:
{
lean_object* v_res_431_; 
v_res_431_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure(v_p_424_, v_a_425_, v_a_426_, v_a_427_, v_a_428_, v_a_429_);
lean_dec(v_a_429_);
lean_dec_ref(v_a_428_);
lean_dec(v_a_427_);
lean_dec_ref(v_a_426_);
lean_dec(v_a_425_);
return v_res_431_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0(lean_object* v_00_u03b2_432_, lean_object* v_m_433_, lean_object* v_a_434_, lean_object* v_b_435_){
_start:
{
lean_object* v___x_436_; 
v___x_436_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v_m_433_, v_a_434_, v_b_435_);
return v___x_436_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__0(lean_object* v_00_u03b2_437_, lean_object* v_a_438_, lean_object* v_x_439_){
_start:
{
uint8_t v___x_440_; 
v___x_440_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__0___redArg(v_a_438_, v_x_439_);
return v___x_440_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__0___boxed(lean_object* v_00_u03b2_441_, lean_object* v_a_442_, lean_object* v_x_443_){
_start:
{
uint8_t v_res_444_; lean_object* v_r_445_; 
v_res_444_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__0(v_00_u03b2_441_, v_a_442_, v_x_443_);
lean_dec(v_x_443_);
lean_dec(v_a_442_);
v_r_445_ = lean_box(v_res_444_);
return v_r_445_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__1(lean_object* v_00_u03b2_446_, lean_object* v_data_447_){
_start:
{
lean_object* v___x_448_; 
v___x_448_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__1___redArg(v_data_447_);
return v___x_448_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__2(lean_object* v_00_u03b2_449_, lean_object* v_a_450_, lean_object* v_b_451_, lean_object* v_x_452_){
_start:
{
lean_object* v___x_453_; 
v___x_453_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__2___redArg(v_a_450_, v_b_451_, v_x_452_);
return v___x_453_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_454_, lean_object* v_i_455_, lean_object* v_source_456_, lean_object* v_target_457_){
_start:
{
lean_object* v___x_458_; 
v___x_458_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__1_spec__2___redArg(v_i_455_, v_source_456_, v_target_457_);
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_459_, lean_object* v_x_460_, lean_object* v_x_461_){
_start:
{
lean_object* v___x_462_; 
v___x_462_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__1_spec__2_spec__3___redArg(v_x_460_, v_x_461_);
return v___x_462_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__2(void){
_start:
{
lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; 
v___x_466_ = lean_box(0);
v___x_467_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__1));
v___x_468_ = l_Lean_Expr_const___override(v___x_467_, v___x_466_);
return v___x_468_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__3(void){
_start:
{
lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; 
v___x_469_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__2, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__2);
v___x_470_ = lean_box(1);
v___x_471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_471_, 0, v___x_470_);
lean_ctor_set(v___x_471_, 1, v___x_469_);
return v___x_471_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__6(void){
_start:
{
lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; 
v___x_475_ = lean_box(0);
v___x_476_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__5));
v___x_477_ = l_Lean_Expr_const___override(v___x_476_, v___x_475_);
return v___x_477_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__9(void){
_start:
{
lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_481_ = lean_box(0);
v___x_482_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__8));
v___x_483_ = l_Lean_Expr_const___override(v___x_482_, v___x_481_);
return v___x_483_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__10(void){
_start:
{
lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; 
v___x_484_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__9, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__9_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__9);
v___x_485_ = lean_box(1);
v___x_486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_486_, 0, v___x_485_);
lean_ctor_set(v___x_486_, 1, v___x_484_);
return v___x_486_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj(lean_object* v_base_487_, lean_object* v_ctorInfo_488_, lean_object* v_field_489_){
_start:
{
switch(lean_obj_tag(v_field_489_))
{
case 0:
{
lean_object* v___x_490_; 
lean_dec(v_base_487_);
v___x_490_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__3, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__3);
return v___x_490_;
}
case 1:
{
lean_object* v_i_491_; lean_object* v_type_492_; lean_object* v___x_494_; uint8_t v_isShared_495_; uint8_t v_isSharedCheck_500_; 
v_i_491_ = lean_ctor_get(v_field_489_, 0);
v_type_492_ = lean_ctor_get(v_field_489_, 1);
v_isSharedCheck_500_ = !lean_is_exclusive(v_field_489_);
if (v_isSharedCheck_500_ == 0)
{
v___x_494_ = v_field_489_;
v_isShared_495_ = v_isSharedCheck_500_;
goto v_resetjp_493_;
}
else
{
lean_inc(v_type_492_);
lean_inc(v_i_491_);
lean_dec(v_field_489_);
v___x_494_ = lean_box(0);
v_isShared_495_ = v_isSharedCheck_500_;
goto v_resetjp_493_;
}
v_resetjp_493_:
{
lean_object* v___x_497_; 
if (v_isShared_495_ == 0)
{
lean_ctor_set_tag(v___x_494_, 6);
lean_ctor_set(v___x_494_, 1, v_base_487_);
v___x_497_ = v___x_494_;
goto v_reusejp_496_;
}
else
{
lean_object* v_reuseFailAlloc_499_; 
v_reuseFailAlloc_499_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_499_, 0, v_i_491_);
lean_ctor_set(v_reuseFailAlloc_499_, 1, v_base_487_);
v___x_497_ = v_reuseFailAlloc_499_;
goto v_reusejp_496_;
}
v_reusejp_496_:
{
lean_object* v___x_498_; 
v___x_498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_498_, 0, v___x_497_);
lean_ctor_set(v___x_498_, 1, v_type_492_);
return v___x_498_;
}
}
}
case 2:
{
lean_object* v_i_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; 
v_i_501_ = lean_ctor_get(v_field_489_, 0);
lean_inc(v_i_501_);
lean_dec_ref(v_field_489_);
v___x_502_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_502_, 0, v_i_501_);
lean_ctor_set(v___x_502_, 1, v_base_487_);
v___x_503_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__6, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__6_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__6);
v___x_504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_504_, 0, v___x_502_);
lean_ctor_set(v___x_504_, 1, v___x_503_);
return v___x_504_;
}
case 3:
{
lean_object* v_offset_505_; lean_object* v_type_506_; lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_517_; 
v_offset_505_ = lean_ctor_get(v_field_489_, 1);
v_type_506_ = lean_ctor_get(v_field_489_, 2);
v_isSharedCheck_517_ = !lean_is_exclusive(v_field_489_);
if (v_isSharedCheck_517_ == 0)
{
lean_object* v_unused_518_; 
v_unused_518_ = lean_ctor_get(v_field_489_, 0);
lean_dec(v_unused_518_);
v___x_508_ = v_field_489_;
v_isShared_509_ = v_isSharedCheck_517_;
goto v_resetjp_507_;
}
else
{
lean_inc(v_type_506_);
lean_inc(v_offset_505_);
lean_dec(v_field_489_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_517_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
lean_object* v_size_510_; lean_object* v_usize_511_; lean_object* v___x_512_; lean_object* v___x_514_; 
v_size_510_ = lean_ctor_get(v_ctorInfo_488_, 2);
v_usize_511_ = lean_ctor_get(v_ctorInfo_488_, 3);
v___x_512_ = lean_nat_add(v_size_510_, v_usize_511_);
if (v_isShared_509_ == 0)
{
lean_ctor_set_tag(v___x_508_, 8);
lean_ctor_set(v___x_508_, 2, v_base_487_);
lean_ctor_set(v___x_508_, 0, v___x_512_);
v___x_514_ = v___x_508_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(8, 3, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v___x_512_);
lean_ctor_set(v_reuseFailAlloc_516_, 1, v_offset_505_);
lean_ctor_set(v_reuseFailAlloc_516_, 2, v_base_487_);
v___x_514_ = v_reuseFailAlloc_516_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
lean_object* v___x_515_; 
v___x_515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_515_, 0, v___x_514_);
lean_ctor_set(v___x_515_, 1, v_type_506_);
return v___x_515_;
}
}
}
default: 
{
lean_object* v___x_519_; 
lean_dec(v_base_487_);
v___x_519_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__10, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__10_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__10);
return v___x_519_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___boxed(lean_object* v_base_520_, lean_object* v_ctorInfo_521_, lean_object* v_field_522_){
_start:
{
lean_object* v_res_523_; 
v_res_523_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj(v_base_520_, v_ctorInfo_521_, v_field_522_);
lean_dec_ref(v_ctorInfo_521_);
return v_res_523_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Arg_toImpure___redArg(lean_object* v_arg_524_, lean_object* v_a_525_){
_start:
{
lean_object* v___x_527_; lean_object* v_subst_528_; uint8_t v___x_529_; uint8_t v___x_530_; lean_object* v___x_531_; 
v___x_527_ = lean_st_ref_get(v_a_525_);
v_subst_528_ = lean_ctor_get(v___x_527_, 0);
lean_inc_ref(v_subst_528_);
lean_dec(v___x_527_);
v___x_529_ = 0;
v___x_530_ = 1;
v___x_531_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(v___x_529_, v_subst_528_, v_arg_524_, v___x_530_);
lean_dec_ref(v_subst_528_);
if (lean_obj_tag(v___x_531_) == 1)
{
lean_object* v_fvarId_532_; lean_object* v___x_534_; uint8_t v_isShared_535_; uint8_t v_isSharedCheck_540_; 
v_fvarId_532_ = lean_ctor_get(v___x_531_, 0);
v_isSharedCheck_540_ = !lean_is_exclusive(v___x_531_);
if (v_isSharedCheck_540_ == 0)
{
v___x_534_ = v___x_531_;
v_isShared_535_ = v_isSharedCheck_540_;
goto v_resetjp_533_;
}
else
{
lean_inc(v_fvarId_532_);
lean_dec(v___x_531_);
v___x_534_ = lean_box(0);
v_isShared_535_ = v_isSharedCheck_540_;
goto v_resetjp_533_;
}
v_resetjp_533_:
{
lean_object* v___x_537_; 
if (v_isShared_535_ == 0)
{
v___x_537_ = v___x_534_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v_fvarId_532_);
v___x_537_ = v_reuseFailAlloc_539_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
lean_object* v___x_538_; 
v___x_538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_538_, 0, v___x_537_);
return v___x_538_;
}
}
}
else
{
lean_object* v___x_541_; lean_object* v___x_542_; 
lean_dec(v___x_531_);
v___x_541_ = lean_box(0);
v___x_542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_542_, 0, v___x_541_);
return v___x_542_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Arg_toImpure___redArg___boxed(lean_object* v_arg_543_, lean_object* v_a_544_, lean_object* v_a_545_){
_start:
{
lean_object* v_res_546_; 
v_res_546_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Arg_toImpure___redArg(v_arg_543_, v_a_544_);
lean_dec(v_a_544_);
return v_res_546_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Arg_toImpure(lean_object* v_arg_547_, lean_object* v_a_548_, lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_, lean_object* v_a_552_){
_start:
{
lean_object* v___x_554_; 
v___x_554_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Arg_toImpure___redArg(v_arg_547_, v_a_548_);
return v___x_554_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Arg_toImpure___boxed(lean_object* v_arg_555_, lean_object* v_a_556_, lean_object* v_a_557_, lean_object* v_a_558_, lean_object* v_a_559_, lean_object* v_a_560_, lean_object* v_a_561_){
_start:
{
lean_object* v_res_562_; 
v_res_562_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Arg_toImpure(v_arg_555_, v_a_556_, v_a_557_, v_a_558_, v_a_559_, v_a_560_);
lean_dec(v_a_560_);
lean_dec_ref(v_a_559_);
lean_dec(v_a_558_);
lean_dec_ref(v_a_557_);
lean_dec(v_a_556_);
return v_res_562_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity_spec__0(lean_object* v_msg_563_){
_start:
{
lean_object* v___x_564_; lean_object* v___x_565_; 
v___x_564_ = l_Lean_instInhabitedExpr;
v___x_565_ = lean_panic_fn(v___x_564_, v_msg_563_);
return v___x_565_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__3(void){
_start:
{
lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; 
v___x_569_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__2));
v___x_570_ = lean_unsigned_to_nat(11u);
v___x_571_ = lean_unsigned_to_nat(83u);
v___x_572_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__1));
v___x_573_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__0));
v___x_574_ = l_mkPanicMessageWithDecl(v___x_573_, v___x_572_, v___x_571_, v___x_570_, v___x_569_);
return v___x_574_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__4(void){
_start:
{
lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_575_ = lean_box(0);
v___x_576_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__1));
v___x_577_ = l_Lean_mkConst(v___x_576_, v___x_575_);
return v___x_577_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity(lean_object* v_type_578_, lean_object* v_arity_579_){
_start:
{
lean_object* v___x_583_; uint8_t v___x_584_; 
v___x_583_ = lean_unsigned_to_nat(0u);
v___x_584_ = lean_nat_dec_eq(v_arity_579_, v___x_583_);
if (v___x_584_ == 0)
{
switch(lean_obj_tag(v_type_578_))
{
case 7:
{
lean_object* v_body_585_; lean_object* v___x_586_; lean_object* v___x_587_; 
v_body_585_ = lean_ctor_get(v_type_578_, 2);
v___x_586_ = lean_unsigned_to_nat(1u);
v___x_587_ = lean_nat_sub(v_arity_579_, v___x_586_);
lean_dec(v_arity_579_);
v_type_578_ = v_body_585_;
v_arity_579_ = v___x_587_;
goto _start;
}
case 4:
{
lean_object* v_declName_589_; 
lean_dec(v_arity_579_);
v_declName_589_ = lean_ctor_get(v_type_578_, 0);
if (lean_obj_tag(v_declName_589_) == 1)
{
lean_object* v_pre_590_; 
v_pre_590_ = lean_ctor_get(v_declName_589_, 0);
if (lean_obj_tag(v_pre_590_) == 0)
{
lean_object* v_str_591_; lean_object* v___x_592_; uint8_t v___x_593_; 
v_str_591_ = lean_ctor_get(v_declName_589_, 1);
v___x_592_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__0));
v___x_593_ = lean_string_dec_eq(v_str_591_, v___x_592_);
if (v___x_593_ == 0)
{
goto v___jp_580_;
}
else
{
lean_object* v___x_594_; 
v___x_594_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__4, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__4_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__4);
return v___x_594_;
}
}
else
{
goto v___jp_580_;
}
}
else
{
goto v___jp_580_;
}
}
default: 
{
lean_dec(v_arity_579_);
goto v___jp_580_;
}
}
}
else
{
lean_dec(v_arity_579_);
lean_inc_ref(v_type_578_);
return v_type_578_;
}
v___jp_580_:
{
lean_object* v___x_581_; lean_object* v___x_582_; 
v___x_581_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__3, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__3);
v___x_582_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity_spec__0(v___x_581_);
return v___x_582_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___boxed(lean_object* v_type_595_, lean_object* v_arity_596_){
_start:
{
lean_object* v_res_597_; 
v_res_597_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity(v_type_595_, v_arity_596_);
lean_dec_ref(v_type_595_);
return v_res_597_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_lowerResultType(lean_object* v_type_598_, lean_object* v_arity_599_, lean_object* v_a_600_, lean_object* v_a_601_){
_start:
{
lean_object* v___x_603_; uint8_t v___x_604_; lean_object* v___x_605_; 
v___x_603_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity(v_type_598_, v_arity_599_);
v___x_604_ = 0;
v___x_605_ = l_Lean_Compiler_LCNF_toImpureType(v___x_603_, v___x_604_, v_a_600_, v_a_601_);
return v___x_605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_lowerResultType___boxed(lean_object* v_type_606_, lean_object* v_arity_607_, lean_object* v_a_608_, lean_object* v_a_609_, lean_object* v_a_610_){
_start:
{
lean_object* v_res_611_; 
v_res_611_ = l_Lean_Compiler_LCNF_lowerResultType(v_type_606_, v_arity_607_, v_a_608_, v_a_609_);
lean_dec(v_a_609_);
lean_dec_ref(v_a_608_);
lean_dec_ref(v_type_606_);
return v_res_611_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__2(void){
_start:
{
lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_615_ = lean_box(0);
v___x_616_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__1));
v___x_617_ = l_Lean_Expr_const___override(v___x_616_, v___x_615_);
return v___x_617_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__5(void){
_start:
{
lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; 
v___x_621_ = lean_box(0);
v___x_622_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__4));
v___x_623_ = l_Lean_Expr_const___override(v___x_622_, v___x_621_);
return v___x_623_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__8(void){
_start:
{
lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; 
v___x_627_ = lean_box(0);
v___x_628_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__7));
v___x_629_ = l_Lean_Expr_const___override(v___x_628_, v___x_627_);
return v___x_629_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__11(void){
_start:
{
lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_633_ = lean_box(0);
v___x_634_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__10));
v___x_635_ = l_Lean_Expr_const___override(v___x_634_, v___x_633_);
return v___x_635_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__14(void){
_start:
{
lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; 
v___x_639_ = lean_box(0);
v___x_640_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__13));
v___x_641_ = l_Lean_Expr_const___override(v___x_640_, v___x_639_);
return v___x_641_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__17(void){
_start:
{
lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_645_ = lean_box(0);
v___x_646_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__16));
v___x_647_ = l_Lean_Expr_const___override(v___x_646_, v___x_645_);
return v___x_647_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__20(void){
_start:
{
lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; 
v___x_651_ = lean_box(0);
v___x_652_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__19));
v___x_653_ = l_Lean_Expr_const___override(v___x_652_, v___x_651_);
return v___x_653_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType(lean_object* v_v_654_){
_start:
{
switch(lean_obj_tag(v_v_654_))
{
case 0:
{
lean_object* v_val_655_; lean_object* v___x_656_; uint8_t v___x_657_; 
v_val_655_ = lean_ctor_get(v_v_654_, 0);
v___x_656_ = lean_cstr_to_nat("4294967296");
v___x_657_ = lean_nat_dec_lt(v_val_655_, v___x_656_);
if (v___x_657_ == 0)
{
lean_object* v___x_658_; 
v___x_658_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__2, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__2);
return v___x_658_;
}
else
{
lean_object* v___x_659_; 
v___x_659_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__5, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__5_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__5);
return v___x_659_;
}
}
case 1:
{
lean_object* v___x_660_; 
v___x_660_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__8, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__8_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__8);
return v___x_660_;
}
case 2:
{
lean_object* v___x_661_; 
v___x_661_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__11, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__11_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__11);
return v___x_661_;
}
case 3:
{
lean_object* v___x_662_; 
v___x_662_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__14, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__14_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__14);
return v___x_662_;
}
case 4:
{
lean_object* v___x_663_; 
v___x_663_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__17, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__17_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__17);
return v___x_663_;
}
case 5:
{
lean_object* v___x_664_; 
v___x_664_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__20, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__20_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__20);
return v___x_664_;
}
default: 
{
lean_object* v___x_665_; 
v___x_665_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__6, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__6_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__6);
return v___x_665_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___boxed(lean_object* v_v_666_){
_start:
{
lean_object* v_res_667_; 
v_res_667_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType(v_v_666_);
lean_dec_ref(v_v_666_);
return v_res_667_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__4(lean_object* v_as_668_, size_t v_i_669_, size_t v_stop_670_, lean_object* v_b_671_){
_start:
{
lean_object* v___y_673_; uint8_t v___x_677_; 
v___x_677_ = lean_usize_dec_eq(v_i_669_, v_stop_670_);
if (v___x_677_ == 0)
{
lean_object* v___x_678_; lean_object* v_snd_679_; uint8_t v___x_680_; 
v___x_678_ = lean_array_uget_borrowed(v_as_668_, v_i_669_);
v_snd_679_ = lean_ctor_get(v___x_678_, 1);
v___x_680_ = lean_unbox(v_snd_679_);
if (v___x_680_ == 0)
{
v___y_673_ = v_b_671_;
goto v___jp_672_;
}
else
{
lean_object* v_fst_681_; lean_object* v___x_682_; 
v_fst_681_ = lean_ctor_get(v___x_678_, 0);
lean_inc(v_fst_681_);
v___x_682_ = lean_array_push(v_b_671_, v_fst_681_);
v___y_673_ = v___x_682_;
goto v___jp_672_;
}
}
else
{
return v_b_671_;
}
v___jp_672_:
{
size_t v___x_674_; size_t v___x_675_; 
v___x_674_ = ((size_t)1ULL);
v___x_675_ = lean_usize_add(v_i_669_, v___x_674_);
v_i_669_ = v___x_675_;
v_b_671_ = v___y_673_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__4___boxed(lean_object* v_as_683_, lean_object* v_i_684_, lean_object* v_stop_685_, lean_object* v_b_686_){
_start:
{
size_t v_i_boxed_687_; size_t v_stop_boxed_688_; lean_object* v_res_689_; 
v_i_boxed_687_ = lean_unbox_usize(v_i_684_);
lean_dec(v_i_684_);
v_stop_boxed_688_ = lean_unbox_usize(v_stop_685_);
lean_dec(v_stop_685_);
v_res_689_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__4(v_as_683_, v_i_boxed_687_, v_stop_boxed_688_, v_b_686_);
lean_dec_ref(v_as_683_);
return v_res_689_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___redArg___closed__3(void){
_start:
{
lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; 
v___x_693_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___redArg___closed__2));
v___x_694_ = lean_unsigned_to_nat(11u);
v___x_695_ = lean_unsigned_to_nat(163u);
v___x_696_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___redArg___closed__1));
v___x_697_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___redArg___closed__0));
v___x_698_ = l_mkPanicMessageWithDecl(v___x_697_, v___x_696_, v___x_695_, v___x_694_, v___x_693_);
return v___x_698_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___redArg(lean_object* v_inst_699_, lean_object* v_a_700_, lean_object* v_x_701_){
_start:
{
if (lean_obj_tag(v_x_701_) == 0)
{
lean_object* v___x_702_; lean_object* v___x_703_; 
v___x_702_ = lean_obj_once(&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___redArg___closed__3, &l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___redArg___closed__3_once, _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___redArg___closed__3);
v___x_703_ = lean_panic_fn(v_inst_699_, v___x_702_);
return v___x_703_;
}
else
{
lean_object* v_key_704_; lean_object* v_value_705_; lean_object* v_tail_706_; uint8_t v___x_707_; 
v_key_704_ = lean_ctor_get(v_x_701_, 0);
v_value_705_ = lean_ctor_get(v_x_701_, 1);
v_tail_706_ = lean_ctor_get(v_x_701_, 2);
v___x_707_ = l_Lean_instBEqFVarId_beq(v_key_704_, v_a_700_);
if (v___x_707_ == 0)
{
v_x_701_ = v_tail_706_;
goto _start;
}
else
{
lean_dec(v_inst_699_);
lean_inc(v_value_705_);
return v_value_705_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___redArg___boxed(lean_object* v_inst_709_, lean_object* v_a_710_, lean_object* v_x_711_){
_start:
{
lean_object* v_res_712_; 
v_res_712_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___redArg(v_inst_709_, v_a_710_, v_x_711_);
lean_dec(v_x_711_);
lean_dec(v_a_710_);
return v_res_712_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5___redArg(lean_object* v_inst_713_, lean_object* v_m_714_, lean_object* v_a_715_){
_start:
{
lean_object* v_buckets_716_; lean_object* v___x_717_; uint64_t v___x_718_; uint64_t v___x_719_; uint64_t v___x_720_; uint64_t v_fold_721_; uint64_t v___x_722_; uint64_t v___x_723_; uint64_t v___x_724_; size_t v___x_725_; size_t v___x_726_; size_t v___x_727_; size_t v___x_728_; size_t v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; 
v_buckets_716_ = lean_ctor_get(v_m_714_, 1);
v___x_717_ = lean_array_get_size(v_buckets_716_);
v___x_718_ = l_Lean_instHashableFVarId_hash(v_a_715_);
v___x_719_ = 32ULL;
v___x_720_ = lean_uint64_shift_right(v___x_718_, v___x_719_);
v_fold_721_ = lean_uint64_xor(v___x_718_, v___x_720_);
v___x_722_ = 16ULL;
v___x_723_ = lean_uint64_shift_right(v_fold_721_, v___x_722_);
v___x_724_ = lean_uint64_xor(v_fold_721_, v___x_723_);
v___x_725_ = lean_uint64_to_usize(v___x_724_);
v___x_726_ = lean_usize_of_nat(v___x_717_);
v___x_727_ = ((size_t)1ULL);
v___x_728_ = lean_usize_sub(v___x_726_, v___x_727_);
v___x_729_ = lean_usize_land(v___x_725_, v___x_728_);
v___x_730_ = lean_array_uget_borrowed(v_buckets_716_, v___x_729_);
v___x_731_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___redArg(v_inst_713_, v_a_715_, v___x_730_);
return v___x_731_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5___redArg___boxed(lean_object* v_inst_732_, lean_object* v_m_733_, lean_object* v_a_734_){
_start:
{
lean_object* v_res_735_; 
v_res_735_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5___redArg(v_inst_732_, v_m_733_, v_a_734_);
lean_dec(v_a_734_);
lean_dec_ref(v_m_733_);
return v_res_735_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0___closed__0(void){
_start:
{
uint8_t v___x_736_; lean_object* v___x_737_; 
v___x_736_ = 1;
v___x_737_ = l_Lean_Compiler_LCNF_instInhabitedCode_default__1(v___x_736_);
return v___x_737_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0(lean_object* v_msg_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_){
_start:
{
lean_object* v___x_745_; lean_object* v_toApplicative_746_; lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_808_; 
v___x_745_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__1, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__1_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__1);
v_toApplicative_746_ = lean_ctor_get(v___x_745_, 0);
v_isSharedCheck_808_ = !lean_is_exclusive(v___x_745_);
if (v_isSharedCheck_808_ == 0)
{
lean_object* v_unused_809_; 
v_unused_809_ = lean_ctor_get(v___x_745_, 1);
lean_dec(v_unused_809_);
v___x_748_ = v___x_745_;
v_isShared_749_ = v_isSharedCheck_808_;
goto v_resetjp_747_;
}
else
{
lean_inc(v_toApplicative_746_);
lean_dec(v___x_745_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_808_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
lean_object* v_toFunctor_750_; lean_object* v_toSeq_751_; lean_object* v_toSeqLeft_752_; lean_object* v_toSeqRight_753_; lean_object* v___x_755_; uint8_t v_isShared_756_; uint8_t v_isSharedCheck_806_; 
v_toFunctor_750_ = lean_ctor_get(v_toApplicative_746_, 0);
v_toSeq_751_ = lean_ctor_get(v_toApplicative_746_, 2);
v_toSeqLeft_752_ = lean_ctor_get(v_toApplicative_746_, 3);
v_toSeqRight_753_ = lean_ctor_get(v_toApplicative_746_, 4);
v_isSharedCheck_806_ = !lean_is_exclusive(v_toApplicative_746_);
if (v_isSharedCheck_806_ == 0)
{
lean_object* v_unused_807_; 
v_unused_807_ = lean_ctor_get(v_toApplicative_746_, 1);
lean_dec(v_unused_807_);
v___x_755_ = v_toApplicative_746_;
v_isShared_756_ = v_isSharedCheck_806_;
goto v_resetjp_754_;
}
else
{
lean_inc(v_toSeqRight_753_);
lean_inc(v_toSeqLeft_752_);
lean_inc(v_toSeq_751_);
lean_inc(v_toFunctor_750_);
lean_dec(v_toApplicative_746_);
v___x_755_ = lean_box(0);
v_isShared_756_ = v_isSharedCheck_806_;
goto v_resetjp_754_;
}
v_resetjp_754_:
{
lean_object* v___f_757_; lean_object* v___f_758_; lean_object* v___f_759_; lean_object* v___f_760_; lean_object* v___x_761_; lean_object* v___f_762_; lean_object* v___f_763_; lean_object* v___f_764_; lean_object* v___x_766_; 
v___f_757_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__2));
v___f_758_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__3));
lean_inc_ref(v_toFunctor_750_);
v___f_759_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_759_, 0, v_toFunctor_750_);
v___f_760_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_760_, 0, v_toFunctor_750_);
v___x_761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_761_, 0, v___f_759_);
lean_ctor_set(v___x_761_, 1, v___f_760_);
v___f_762_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_762_, 0, v_toSeqRight_753_);
v___f_763_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_763_, 0, v_toSeqLeft_752_);
v___f_764_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_764_, 0, v_toSeq_751_);
if (v_isShared_756_ == 0)
{
lean_ctor_set(v___x_755_, 4, v___f_762_);
lean_ctor_set(v___x_755_, 3, v___f_763_);
lean_ctor_set(v___x_755_, 2, v___f_764_);
lean_ctor_set(v___x_755_, 1, v___f_757_);
lean_ctor_set(v___x_755_, 0, v___x_761_);
v___x_766_ = v___x_755_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v___x_761_);
lean_ctor_set(v_reuseFailAlloc_805_, 1, v___f_757_);
lean_ctor_set(v_reuseFailAlloc_805_, 2, v___f_764_);
lean_ctor_set(v_reuseFailAlloc_805_, 3, v___f_763_);
lean_ctor_set(v_reuseFailAlloc_805_, 4, v___f_762_);
v___x_766_ = v_reuseFailAlloc_805_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
lean_object* v___x_768_; 
if (v_isShared_749_ == 0)
{
lean_ctor_set(v___x_748_, 1, v___f_758_);
lean_ctor_set(v___x_748_, 0, v___x_766_);
v___x_768_ = v___x_748_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v___x_766_);
lean_ctor_set(v_reuseFailAlloc_804_, 1, v___f_758_);
v___x_768_ = v_reuseFailAlloc_804_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
lean_object* v___x_769_; lean_object* v_toApplicative_770_; lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_802_; 
v___x_769_ = l_StateRefT_x27_instMonad___redArg(v___x_768_);
v_toApplicative_770_ = lean_ctor_get(v___x_769_, 0);
v_isSharedCheck_802_ = !lean_is_exclusive(v___x_769_);
if (v_isSharedCheck_802_ == 0)
{
lean_object* v_unused_803_; 
v_unused_803_ = lean_ctor_get(v___x_769_, 1);
lean_dec(v_unused_803_);
v___x_772_ = v___x_769_;
v_isShared_773_ = v_isSharedCheck_802_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_toApplicative_770_);
lean_dec(v___x_769_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_802_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
lean_object* v_toFunctor_774_; lean_object* v_toSeq_775_; lean_object* v_toSeqLeft_776_; lean_object* v_toSeqRight_777_; lean_object* v___x_779_; uint8_t v_isShared_780_; uint8_t v_isSharedCheck_800_; 
v_toFunctor_774_ = lean_ctor_get(v_toApplicative_770_, 0);
v_toSeq_775_ = lean_ctor_get(v_toApplicative_770_, 2);
v_toSeqLeft_776_ = lean_ctor_get(v_toApplicative_770_, 3);
v_toSeqRight_777_ = lean_ctor_get(v_toApplicative_770_, 4);
v_isSharedCheck_800_ = !lean_is_exclusive(v_toApplicative_770_);
if (v_isSharedCheck_800_ == 0)
{
lean_object* v_unused_801_; 
v_unused_801_ = lean_ctor_get(v_toApplicative_770_, 1);
lean_dec(v_unused_801_);
v___x_779_ = v_toApplicative_770_;
v_isShared_780_ = v_isSharedCheck_800_;
goto v_resetjp_778_;
}
else
{
lean_inc(v_toSeqRight_777_);
lean_inc(v_toSeqLeft_776_);
lean_inc(v_toSeq_775_);
lean_inc(v_toFunctor_774_);
lean_dec(v_toApplicative_770_);
v___x_779_ = lean_box(0);
v_isShared_780_ = v_isSharedCheck_800_;
goto v_resetjp_778_;
}
v_resetjp_778_:
{
lean_object* v___f_781_; lean_object* v___f_782_; lean_object* v___f_783_; lean_object* v___f_784_; lean_object* v___x_785_; lean_object* v___f_786_; lean_object* v___f_787_; lean_object* v___f_788_; lean_object* v___x_790_; 
v___f_781_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__5));
v___f_782_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__6));
lean_inc_ref(v_toFunctor_774_);
v___f_783_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_783_, 0, v_toFunctor_774_);
v___f_784_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_784_, 0, v_toFunctor_774_);
v___x_785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_785_, 0, v___f_783_);
lean_ctor_set(v___x_785_, 1, v___f_784_);
v___f_786_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_786_, 0, v_toSeqRight_777_);
v___f_787_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_787_, 0, v_toSeqLeft_776_);
v___f_788_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_788_, 0, v_toSeq_775_);
if (v_isShared_780_ == 0)
{
lean_ctor_set(v___x_779_, 4, v___f_786_);
lean_ctor_set(v___x_779_, 3, v___f_787_);
lean_ctor_set(v___x_779_, 2, v___f_788_);
lean_ctor_set(v___x_779_, 1, v___f_781_);
lean_ctor_set(v___x_779_, 0, v___x_785_);
v___x_790_ = v___x_779_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_799_; 
v_reuseFailAlloc_799_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_799_, 0, v___x_785_);
lean_ctor_set(v_reuseFailAlloc_799_, 1, v___f_781_);
lean_ctor_set(v_reuseFailAlloc_799_, 2, v___f_788_);
lean_ctor_set(v_reuseFailAlloc_799_, 3, v___f_787_);
lean_ctor_set(v_reuseFailAlloc_799_, 4, v___f_786_);
v___x_790_ = v_reuseFailAlloc_799_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
lean_object* v___x_792_; 
if (v_isShared_773_ == 0)
{
lean_ctor_set(v___x_772_, 1, v___f_782_);
lean_ctor_set(v___x_772_, 0, v___x_790_);
v___x_792_ = v___x_772_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_798_; 
v_reuseFailAlloc_798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_798_, 0, v___x_790_);
lean_ctor_set(v_reuseFailAlloc_798_, 1, v___f_782_);
v___x_792_ = v_reuseFailAlloc_798_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_38267__overap_796_; lean_object* v___x_797_; 
v___x_793_ = l_StateRefT_x27_instMonad___redArg(v___x_792_);
v___x_794_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0___closed__0);
v___x_795_ = l_instInhabitedOfMonad___redArg(v___x_793_, v___x_794_);
v___x_38267__overap_796_ = lean_panic_fn(v___x_795_, v_msg_738_);
lean_inc(v___y_743_);
lean_inc_ref(v___y_742_);
lean_inc(v___y_741_);
lean_inc_ref(v___y_740_);
lean_inc(v___y_739_);
v___x_797_ = lean_apply_6(v___x_38267__overap_796_, v___y_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_, lean_box(0));
return v___x_797_;
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0___boxed(lean_object* v_msg_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_){
_start:
{
lean_object* v_res_817_; 
v_res_817_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0(v_msg_810_, v___y_811_, v___y_812_, v___y_813_, v___y_814_, v___y_815_);
lean_dec(v___y_815_);
lean_dec_ref(v___y_814_);
lean_dec(v___y_813_);
lean_dec_ref(v___y_812_);
lean_dec(v___y_811_);
return v_res_817_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___redArg___closed__0(void){
_start:
{
uint8_t v___x_818_; lean_object* v___x_819_; 
v___x_818_ = 0;
v___x_819_ = l_Lean_Compiler_LCNF_instInhabitedParam_default(v___x_818_);
return v___x_819_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___redArg(lean_object* v_upperBound_820_, lean_object* v_params_821_, lean_object* v___x_822_, lean_object* v_discr_823_, lean_object* v_a_824_, lean_object* v_b_825_, lean_object* v___y_826_){
_start:
{
lean_object* v_a_829_; uint8_t v___x_833_; 
v___x_833_ = lean_nat_dec_lt(v_a_824_, v_upperBound_820_);
if (v___x_833_ == 0)
{
lean_object* v___x_834_; 
lean_dec(v_a_824_);
lean_dec(v_discr_823_);
v___x_834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_834_, 0, v_b_825_);
return v___x_834_;
}
else
{
lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; uint8_t v___x_838_; 
v___x_835_ = lean_box(0);
v___x_836_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___redArg___closed__0);
v___x_837_ = lean_array_get_borrowed(v___x_836_, v_params_821_, v_a_824_);
v___x_838_ = lean_nat_dec_eq(v_a_824_, v___x_822_);
if (v___x_838_ == 0)
{
lean_object* v___x_839_; lean_object* v_fvarId_840_; lean_object* v_subst_841_; lean_object* v_jpParamMask_842_; lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_852_; 
v___x_839_ = lean_st_ref_take(v___y_826_);
v_fvarId_840_ = lean_ctor_get(v___x_837_, 0);
v_subst_841_ = lean_ctor_get(v___x_839_, 0);
v_jpParamMask_842_ = lean_ctor_get(v___x_839_, 1);
v_isSharedCheck_852_ = !lean_is_exclusive(v___x_839_);
if (v_isSharedCheck_852_ == 0)
{
v___x_844_ = v___x_839_;
v_isShared_845_ = v_isSharedCheck_852_;
goto v_resetjp_843_;
}
else
{
lean_inc(v_jpParamMask_842_);
lean_inc(v_subst_841_);
lean_dec(v___x_839_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_852_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_849_; 
v___x_846_ = lean_box(0);
lean_inc(v_fvarId_840_);
v___x_847_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v_subst_841_, v_fvarId_840_, v___x_846_);
if (v_isShared_845_ == 0)
{
lean_ctor_set(v___x_844_, 0, v___x_847_);
v___x_849_ = v___x_844_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v___x_847_);
lean_ctor_set(v_reuseFailAlloc_851_, 1, v_jpParamMask_842_);
v___x_849_ = v_reuseFailAlloc_851_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
lean_object* v___x_850_; 
v___x_850_ = lean_st_ref_set(v___y_826_, v___x_849_);
v_a_829_ = v___x_835_;
goto v___jp_828_;
}
}
}
else
{
lean_object* v___x_853_; lean_object* v_fvarId_854_; lean_object* v_subst_855_; lean_object* v_jpParamMask_856_; lean_object* v___x_858_; uint8_t v_isShared_859_; uint8_t v_isSharedCheck_866_; 
v___x_853_ = lean_st_ref_take(v___y_826_);
v_fvarId_854_ = lean_ctor_get(v___x_837_, 0);
v_subst_855_ = lean_ctor_get(v___x_853_, 0);
v_jpParamMask_856_ = lean_ctor_get(v___x_853_, 1);
v_isSharedCheck_866_ = !lean_is_exclusive(v___x_853_);
if (v_isSharedCheck_866_ == 0)
{
v___x_858_ = v___x_853_;
v_isShared_859_ = v_isSharedCheck_866_;
goto v_resetjp_857_;
}
else
{
lean_inc(v_jpParamMask_856_);
lean_inc(v_subst_855_);
lean_dec(v___x_853_);
v___x_858_ = lean_box(0);
v_isShared_859_ = v_isSharedCheck_866_;
goto v_resetjp_857_;
}
v_resetjp_857_:
{
lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_863_; 
lean_inc(v_discr_823_);
v___x_860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_860_, 0, v_discr_823_);
lean_inc(v_fvarId_854_);
v___x_861_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v_subst_855_, v_fvarId_854_, v___x_860_);
if (v_isShared_859_ == 0)
{
lean_ctor_set(v___x_858_, 0, v___x_861_);
v___x_863_ = v___x_858_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v___x_861_);
lean_ctor_set(v_reuseFailAlloc_865_, 1, v_jpParamMask_856_);
v___x_863_ = v_reuseFailAlloc_865_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
lean_object* v___x_864_; 
v___x_864_ = lean_st_ref_set(v___y_826_, v___x_863_);
v_a_829_ = v___x_835_;
goto v___jp_828_;
}
}
}
}
v___jp_828_:
{
lean_object* v___x_830_; lean_object* v___x_831_; 
v___x_830_ = lean_unsigned_to_nat(1u);
v___x_831_ = lean_nat_add(v_a_824_, v___x_830_);
lean_dec(v_a_824_);
v_a_824_ = v___x_831_;
v_b_825_ = v_a_829_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___redArg___boxed(lean_object* v_upperBound_867_, lean_object* v_params_868_, lean_object* v___x_869_, lean_object* v_discr_870_, lean_object* v_a_871_, lean_object* v_b_872_, lean_object* v___y_873_, lean_object* v___y_874_){
_start:
{
lean_object* v_res_875_; 
v_res_875_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___redArg(v_upperBound_867_, v_params_868_, v___x_869_, v_discr_870_, v_a_871_, v_b_872_, v___y_873_);
lean_dec(v___y_873_);
lean_dec(v___x_869_);
lean_dec_ref(v_params_868_);
lean_dec(v_upperBound_867_);
return v_res_875_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__3(size_t v_sz_876_, size_t v_i_877_, lean_object* v_bs_878_){
_start:
{
uint8_t v___x_879_; 
v___x_879_ = lean_usize_dec_lt(v_i_877_, v_sz_876_);
if (v___x_879_ == 0)
{
return v_bs_878_;
}
else
{
lean_object* v_v_880_; lean_object* v_type_881_; lean_object* v___x_882_; lean_object* v_bs_x27_883_; uint8_t v___y_885_; uint8_t v___y_892_; uint8_t v___x_894_; 
v_v_880_ = lean_array_uget_borrowed(v_bs_878_, v_i_877_);
v_type_881_ = lean_ctor_get(v_v_880_, 2);
lean_inc_ref(v_type_881_);
v___x_882_ = lean_unsigned_to_nat(0u);
v_bs_x27_883_ = lean_array_uset(v_bs_878_, v_i_877_, v___x_882_);
v___x_894_ = l_Lean_Expr_isVoid(v_type_881_);
if (v___x_894_ == 0)
{
uint8_t v___x_895_; 
v___x_895_ = l_Lean_Expr_isErased(v_type_881_);
lean_dec_ref(v_type_881_);
v___y_892_ = v___x_895_;
goto v___jp_891_;
}
else
{
lean_dec_ref(v_type_881_);
v___y_892_ = v___x_894_;
goto v___jp_891_;
}
v___jp_884_:
{
size_t v___x_886_; size_t v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; 
v___x_886_ = ((size_t)1ULL);
v___x_887_ = lean_usize_add(v_i_877_, v___x_886_);
v___x_888_ = lean_box(v___y_885_);
v___x_889_ = lean_array_uset(v_bs_x27_883_, v_i_877_, v___x_888_);
v_i_877_ = v___x_887_;
v_bs_878_ = v___x_889_;
goto _start;
}
v___jp_891_:
{
if (v___y_892_ == 0)
{
v___y_885_ = v___x_879_;
goto v___jp_884_;
}
else
{
uint8_t v___x_893_; 
v___x_893_ = 0;
v___y_885_ = v___x_893_;
goto v___jp_884_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__3___boxed(lean_object* v_sz_896_, lean_object* v_i_897_, lean_object* v_bs_898_){
_start:
{
size_t v_sz_boxed_899_; size_t v_i_boxed_900_; lean_object* v_res_901_; 
v_sz_boxed_899_ = lean_unbox_usize(v_sz_896_);
lean_dec(v_sz_896_);
v_i_boxed_900_ = lean_unbox_usize(v_i_897_);
lean_dec(v_i_897_);
v_res_901_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__3(v_sz_boxed_899_, v_i_boxed_900_, v_bs_898_);
return v_res_901_;
}
}
static lean_object* _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__0(void){
_start:
{
lean_object* v___x_902_; 
v___x_902_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_902_;
}
}
static lean_object* _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__1(void){
_start:
{
lean_object* v___x_903_; lean_object* v___x_904_; 
v___x_903_ = lean_obj_once(&l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__0, &l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__0_once, _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__0);
v___x_904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_904_, 0, v___x_903_);
return v___x_904_;
}
}
static lean_object* _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__2(void){
_start:
{
lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; 
v___x_905_ = lean_obj_once(&l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__1, &l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__1_once, _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__1);
v___x_906_ = lean_unsigned_to_nat(0u);
v___x_907_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_907_, 0, v___x_906_);
lean_ctor_set(v___x_907_, 1, v___x_906_);
lean_ctor_set(v___x_907_, 2, v___x_906_);
lean_ctor_set(v___x_907_, 3, v___x_905_);
lean_ctor_set(v___x_907_, 4, v___x_905_);
lean_ctor_set(v___x_907_, 5, v___x_905_);
lean_ctor_set(v___x_907_, 6, v___x_905_);
lean_ctor_set(v___x_907_, 7, v___x_905_);
lean_ctor_set(v___x_907_, 8, v___x_905_);
return v___x_907_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg(lean_object* v_msg_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_){
_start:
{
lean_object* v_options_914_; lean_object* v_ref_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; 
v_options_914_ = lean_ctor_get(v___y_911_, 2);
v_ref_915_ = lean_ctor_get(v___y_911_, 5);
v___x_916_ = lean_st_ref_get(v___y_912_);
v___x_917_ = lean_st_ref_get(v___y_910_);
v___x_918_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_909_);
if (lean_obj_tag(v___x_918_) == 0)
{
lean_object* v_a_919_; lean_object* v___x_921_; uint8_t v_isShared_922_; uint8_t v_isSharedCheck_941_; 
v_a_919_ = lean_ctor_get(v___x_918_, 0);
v_isSharedCheck_941_ = !lean_is_exclusive(v___x_918_);
if (v_isSharedCheck_941_ == 0)
{
v___x_921_ = v___x_918_;
v_isShared_922_ = v_isSharedCheck_941_;
goto v_resetjp_920_;
}
else
{
lean_inc(v_a_919_);
lean_dec(v___x_918_);
v___x_921_ = lean_box(0);
v_isShared_922_ = v_isSharedCheck_941_;
goto v_resetjp_920_;
}
v_resetjp_920_:
{
lean_object* v_env_923_; lean_object* v_lctx_924_; lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_939_; 
v_env_923_ = lean_ctor_get(v___x_916_, 0);
lean_inc_ref(v_env_923_);
lean_dec(v___x_916_);
v_lctx_924_ = lean_ctor_get(v___x_917_, 0);
v_isSharedCheck_939_ = !lean_is_exclusive(v___x_917_);
if (v_isSharedCheck_939_ == 0)
{
lean_object* v_unused_940_; 
v_unused_940_ = lean_ctor_get(v___x_917_, 1);
lean_dec(v_unused_940_);
v___x_926_ = v___x_917_;
v_isShared_927_ = v_isSharedCheck_939_;
goto v_resetjp_925_;
}
else
{
lean_inc(v_lctx_924_);
lean_dec(v___x_917_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_939_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
uint8_t v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_933_; 
v___x_928_ = lean_unbox(v_a_919_);
lean_dec(v_a_919_);
v___x_929_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_924_, v___x_928_);
lean_dec_ref(v_lctx_924_);
v___x_930_ = lean_obj_once(&l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__2, &l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__2_once, _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__2);
lean_inc_ref(v_options_914_);
v___x_931_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_931_, 0, v_env_923_);
lean_ctor_set(v___x_931_, 1, v___x_930_);
lean_ctor_set(v___x_931_, 2, v___x_929_);
lean_ctor_set(v___x_931_, 3, v_options_914_);
if (v_isShared_927_ == 0)
{
lean_ctor_set_tag(v___x_926_, 3);
lean_ctor_set(v___x_926_, 1, v_msg_908_);
lean_ctor_set(v___x_926_, 0, v___x_931_);
v___x_933_ = v___x_926_;
goto v_reusejp_932_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v___x_931_);
lean_ctor_set(v_reuseFailAlloc_938_, 1, v_msg_908_);
v___x_933_ = v_reuseFailAlloc_938_;
goto v_reusejp_932_;
}
v_reusejp_932_:
{
lean_object* v___x_934_; lean_object* v___x_936_; 
lean_inc(v_ref_915_);
v___x_934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_934_, 0, v_ref_915_);
lean_ctor_set(v___x_934_, 1, v___x_933_);
if (v_isShared_922_ == 0)
{
lean_ctor_set_tag(v___x_921_, 1);
lean_ctor_set(v___x_921_, 0, v___x_934_);
v___x_936_ = v___x_921_;
goto v_reusejp_935_;
}
else
{
lean_object* v_reuseFailAlloc_937_; 
v_reuseFailAlloc_937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_937_, 0, v___x_934_);
v___x_936_ = v_reuseFailAlloc_937_;
goto v_reusejp_935_;
}
v_reusejp_935_:
{
return v___x_936_;
}
}
}
}
}
else
{
lean_object* v_a_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_949_; 
lean_dec(v___x_917_);
lean_dec(v___x_916_);
lean_dec_ref(v_msg_908_);
v_a_942_ = lean_ctor_get(v___x_918_, 0);
v_isSharedCheck_949_ = !lean_is_exclusive(v___x_918_);
if (v_isSharedCheck_949_ == 0)
{
v___x_944_ = v___x_918_;
v_isShared_945_ = v_isSharedCheck_949_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_a_942_);
lean_dec(v___x_918_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_949_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
lean_object* v___x_947_; 
if (v_isShared_945_ == 0)
{
v___x_947_ = v___x_944_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v_a_942_);
v___x_947_ = v_reuseFailAlloc_948_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
return v___x_947_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___boxed(lean_object* v_msg_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_){
_start:
{
lean_object* v_res_956_; 
v_res_956_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg(v_msg_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_);
lean_dec(v___y_954_);
lean_dec_ref(v___y_953_);
lean_dec(v___y_952_);
lean_dec_ref(v___y_951_);
return v_res_956_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__11___redArg(size_t v_sz_957_, size_t v_i_958_, lean_object* v_bs_959_, lean_object* v___y_960_){
_start:
{
uint8_t v___x_962_; 
v___x_962_ = lean_usize_dec_lt(v_i_958_, v_sz_957_);
if (v___x_962_ == 0)
{
lean_object* v___x_963_; 
v___x_963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_963_, 0, v_bs_959_);
return v___x_963_;
}
else
{
lean_object* v_v_964_; lean_object* v___x_965_; 
v_v_964_ = lean_array_uget_borrowed(v_bs_959_, v_i_958_);
lean_inc(v_v_964_);
v___x_965_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Arg_toImpure___redArg(v_v_964_, v___y_960_);
if (lean_obj_tag(v___x_965_) == 0)
{
lean_object* v_a_966_; lean_object* v___x_967_; lean_object* v_bs_x27_968_; size_t v___x_969_; size_t v___x_970_; lean_object* v___x_971_; 
v_a_966_ = lean_ctor_get(v___x_965_, 0);
lean_inc(v_a_966_);
lean_dec_ref(v___x_965_);
v___x_967_ = lean_unsigned_to_nat(0u);
v_bs_x27_968_ = lean_array_uset(v_bs_959_, v_i_958_, v___x_967_);
v___x_969_ = ((size_t)1ULL);
v___x_970_ = lean_usize_add(v_i_958_, v___x_969_);
v___x_971_ = lean_array_uset(v_bs_x27_968_, v_i_958_, v_a_966_);
v_i_958_ = v___x_970_;
v_bs_959_ = v___x_971_;
goto _start;
}
else
{
lean_object* v_a_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_980_; 
lean_dec_ref(v_bs_959_);
v_a_973_ = lean_ctor_get(v___x_965_, 0);
v_isSharedCheck_980_ = !lean_is_exclusive(v___x_965_);
if (v_isSharedCheck_980_ == 0)
{
v___x_975_ = v___x_965_;
v_isShared_976_ = v_isSharedCheck_980_;
goto v_resetjp_974_;
}
else
{
lean_inc(v_a_973_);
lean_dec(v___x_965_);
v___x_975_ = lean_box(0);
v_isShared_976_ = v_isSharedCheck_980_;
goto v_resetjp_974_;
}
v_resetjp_974_:
{
lean_object* v___x_978_; 
if (v_isShared_976_ == 0)
{
v___x_978_ = v___x_975_;
goto v_reusejp_977_;
}
else
{
lean_object* v_reuseFailAlloc_979_; 
v_reuseFailAlloc_979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_979_, 0, v_a_973_);
v___x_978_ = v_reuseFailAlloc_979_;
goto v_reusejp_977_;
}
v_reusejp_977_:
{
return v___x_978_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__11___redArg___boxed(lean_object* v_sz_981_, lean_object* v_i_982_, lean_object* v_bs_983_, lean_object* v___y_984_, lean_object* v___y_985_){
_start:
{
size_t v_sz_boxed_986_; size_t v_i_boxed_987_; lean_object* v_res_988_; 
v_sz_boxed_986_ = lean_unbox_usize(v_sz_981_);
lean_dec(v_sz_981_);
v_i_boxed_987_ = lean_unbox_usize(v_i_982_);
lean_dec(v_i_982_);
v_res_988_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__11___redArg(v_sz_boxed_986_, v_i_boxed_987_, v_bs_983_, v___y_984_);
lean_dec(v___y_984_);
return v_res_988_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___redArg(lean_object* v_upperBound_989_, lean_object* v_fieldInfo_990_, lean_object* v___x_991_, lean_object* v_a_992_, lean_object* v_b_993_){
_start:
{
lean_object* v_a_996_; uint8_t v___x_1000_; 
v___x_1000_ = lean_nat_dec_lt(v_a_992_, v_upperBound_989_);
if (v___x_1000_ == 0)
{
lean_object* v___x_1001_; 
lean_dec(v_a_992_);
v___x_1001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1001_, 0, v_b_993_);
return v___x_1001_;
}
else
{
lean_object* v___x_1002_; 
v___x_1002_ = lean_array_fget_borrowed(v_fieldInfo_990_, v_a_992_);
switch(lean_obj_tag(v___x_1002_))
{
case 1:
{
lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; 
v___x_1003_ = lean_box(0);
v___x_1004_ = lean_array_get_borrowed(v___x_1003_, v___x_991_, v_a_992_);
lean_inc(v___x_1004_);
v___x_1005_ = lean_array_push(v_b_993_, v___x_1004_);
v_a_996_ = v___x_1005_;
goto v___jp_995_;
}
case 2:
{
v_a_996_ = v_b_993_;
goto v___jp_995_;
}
case 3:
{
v_a_996_ = v_b_993_;
goto v___jp_995_;
}
default: 
{
v_a_996_ = v_b_993_;
goto v___jp_995_;
}
}
}
v___jp_995_:
{
lean_object* v___x_997_; lean_object* v___x_998_; 
v___x_997_ = lean_unsigned_to_nat(1u);
v___x_998_ = lean_nat_add(v_a_992_, v___x_997_);
lean_dec(v_a_992_);
v_a_992_ = v___x_998_;
v_b_993_ = v_a_996_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___redArg___boxed(lean_object* v_upperBound_1006_, lean_object* v_fieldInfo_1007_, lean_object* v___x_1008_, lean_object* v_a_1009_, lean_object* v_b_1010_, lean_object* v___y_1011_){
_start:
{
lean_object* v_res_1012_; 
v_res_1012_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___redArg(v_upperBound_1006_, v_fieldInfo_1007_, v___x_1008_, v_a_1009_, v_b_1010_);
lean_dec_ref(v___x_1008_);
lean_dec_ref(v_fieldInfo_1007_);
lean_dec(v_upperBound_1006_);
return v_res_1012_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__6___redArg(lean_object* v_as_1013_, size_t v_i_1014_, size_t v_stop_1015_, lean_object* v_b_1016_, lean_object* v___y_1017_){
_start:
{
lean_object* v_a_1020_; uint8_t v___x_1024_; 
v___x_1024_ = lean_usize_dec_eq(v_i_1014_, v_stop_1015_);
if (v___x_1024_ == 0)
{
lean_object* v___x_1025_; lean_object* v_snd_1026_; uint8_t v___x_1027_; 
v___x_1025_ = lean_array_uget_borrowed(v_as_1013_, v_i_1014_);
v_snd_1026_ = lean_ctor_get(v___x_1025_, 1);
v___x_1027_ = lean_unbox(v_snd_1026_);
if (v___x_1027_ == 0)
{
v_a_1020_ = v_b_1016_;
goto v___jp_1019_;
}
else
{
lean_object* v_fst_1028_; lean_object* v___x_1029_; 
v_fst_1028_ = lean_ctor_get(v___x_1025_, 0);
lean_inc(v_fst_1028_);
v___x_1029_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Arg_toImpure___redArg(v_fst_1028_, v___y_1017_);
if (lean_obj_tag(v___x_1029_) == 0)
{
lean_object* v_a_1030_; lean_object* v___x_1031_; 
v_a_1030_ = lean_ctor_get(v___x_1029_, 0);
lean_inc(v_a_1030_);
lean_dec_ref(v___x_1029_);
v___x_1031_ = lean_array_push(v_b_1016_, v_a_1030_);
v_a_1020_ = v___x_1031_;
goto v___jp_1019_;
}
else
{
lean_object* v_a_1032_; lean_object* v___x_1034_; uint8_t v_isShared_1035_; uint8_t v_isSharedCheck_1039_; 
lean_dec_ref(v_b_1016_);
v_a_1032_ = lean_ctor_get(v___x_1029_, 0);
v_isSharedCheck_1039_ = !lean_is_exclusive(v___x_1029_);
if (v_isSharedCheck_1039_ == 0)
{
v___x_1034_ = v___x_1029_;
v_isShared_1035_ = v_isSharedCheck_1039_;
goto v_resetjp_1033_;
}
else
{
lean_inc(v_a_1032_);
lean_dec(v___x_1029_);
v___x_1034_ = lean_box(0);
v_isShared_1035_ = v_isSharedCheck_1039_;
goto v_resetjp_1033_;
}
v_resetjp_1033_:
{
lean_object* v___x_1037_; 
if (v_isShared_1035_ == 0)
{
v___x_1037_ = v___x_1034_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v_a_1032_);
v___x_1037_ = v_reuseFailAlloc_1038_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
return v___x_1037_;
}
}
}
}
}
else
{
lean_object* v___x_1040_; 
v___x_1040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1040_, 0, v_b_1016_);
return v___x_1040_;
}
v___jp_1019_:
{
size_t v___x_1021_; size_t v___x_1022_; 
v___x_1021_ = ((size_t)1ULL);
v___x_1022_ = lean_usize_add(v_i_1014_, v___x_1021_);
v_i_1014_ = v___x_1022_;
v_b_1016_ = v_a_1020_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__6___redArg___boxed(lean_object* v_as_1041_, lean_object* v_i_1042_, lean_object* v_stop_1043_, lean_object* v_b_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_){
_start:
{
size_t v_i_boxed_1047_; size_t v_stop_boxed_1048_; lean_object* v_res_1049_; 
v_i_boxed_1047_ = lean_unbox_usize(v_i_1042_);
lean_dec(v_i_1042_);
v_stop_boxed_1048_ = lean_unbox_usize(v_stop_1043_);
lean_dec(v_stop_1043_);
v_res_1049_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__6___redArg(v_as_1041_, v_i_boxed_1047_, v_stop_boxed_1048_, v_b_1044_, v___y_1045_);
lean_dec(v___y_1045_);
lean_dec_ref(v_as_1041_);
return v_res_1049_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__2___redArg(size_t v_sz_1050_, size_t v_i_1051_, lean_object* v_bs_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_){
_start:
{
uint8_t v___x_1058_; 
v___x_1058_ = lean_usize_dec_lt(v_i_1051_, v_sz_1050_);
if (v___x_1058_ == 0)
{
lean_object* v___x_1059_; 
v___x_1059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1059_, 0, v_bs_1052_);
return v___x_1059_;
}
else
{
lean_object* v_v_1060_; lean_object* v___x_1061_; 
v_v_1060_ = lean_array_uget_borrowed(v_bs_1052_, v_i_1051_);
lean_inc(v_v_1060_);
v___x_1061_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure___redArg(v_v_1060_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_);
if (lean_obj_tag(v___x_1061_) == 0)
{
lean_object* v_a_1062_; lean_object* v___x_1063_; lean_object* v_bs_x27_1064_; size_t v___x_1065_; size_t v___x_1066_; lean_object* v___x_1067_; 
v_a_1062_ = lean_ctor_get(v___x_1061_, 0);
lean_inc(v_a_1062_);
lean_dec_ref(v___x_1061_);
v___x_1063_ = lean_unsigned_to_nat(0u);
v_bs_x27_1064_ = lean_array_uset(v_bs_1052_, v_i_1051_, v___x_1063_);
v___x_1065_ = ((size_t)1ULL);
v___x_1066_ = lean_usize_add(v_i_1051_, v___x_1065_);
v___x_1067_ = lean_array_uset(v_bs_x27_1064_, v_i_1051_, v_a_1062_);
v_i_1051_ = v___x_1066_;
v_bs_1052_ = v___x_1067_;
goto _start;
}
else
{
lean_object* v_a_1069_; lean_object* v___x_1071_; uint8_t v_isShared_1072_; uint8_t v_isSharedCheck_1076_; 
lean_dec_ref(v_bs_1052_);
v_a_1069_ = lean_ctor_get(v___x_1061_, 0);
v_isSharedCheck_1076_ = !lean_is_exclusive(v___x_1061_);
if (v_isSharedCheck_1076_ == 0)
{
v___x_1071_ = v___x_1061_;
v_isShared_1072_ = v_isSharedCheck_1076_;
goto v_resetjp_1070_;
}
else
{
lean_inc(v_a_1069_);
lean_dec(v___x_1061_);
v___x_1071_ = lean_box(0);
v_isShared_1072_ = v_isSharedCheck_1076_;
goto v_resetjp_1070_;
}
v_resetjp_1070_:
{
lean_object* v___x_1074_; 
if (v_isShared_1072_ == 0)
{
v___x_1074_ = v___x_1071_;
goto v_reusejp_1073_;
}
else
{
lean_object* v_reuseFailAlloc_1075_; 
v_reuseFailAlloc_1075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1075_, 0, v_a_1069_);
v___x_1074_ = v_reuseFailAlloc_1075_;
goto v_reusejp_1073_;
}
v_reusejp_1073_:
{
return v___x_1074_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__2___redArg___boxed(lean_object* v_sz_1077_, lean_object* v_i_1078_, lean_object* v_bs_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_){
_start:
{
size_t v_sz_boxed_1085_; size_t v_i_boxed_1086_; lean_object* v_res_1087_; 
v_sz_boxed_1085_ = lean_unbox_usize(v_sz_1077_);
lean_dec(v_sz_1077_);
v_i_boxed_1086_ = lean_unbox_usize(v_i_1078_);
lean_dec(v_i_1078_);
v_res_1087_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__2___redArg(v_sz_boxed_1085_, v_i_boxed_1086_, v_bs_1079_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_);
lean_dec(v___y_1083_);
lean_dec_ref(v___y_1082_);
lean_dec(v___y_1081_);
lean_dec(v___y_1080_);
return v_res_1087_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__2(void){
_start:
{
lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; 
v___x_1090_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__1));
v___x_1091_ = lean_unsigned_to_nat(12u);
v___x_1092_ = lean_unsigned_to_nat(116u);
v___x_1093_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__0));
v___x_1094_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__0));
v___x_1095_ = l_mkPanicMessageWithDecl(v___x_1094_, v___x_1093_, v___x_1092_, v___x_1091_, v___x_1090_);
return v___x_1095_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueLet(lean_object* v_k_1096_, lean_object* v_decl_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_){
_start:
{
lean_object* v___x_1104_; lean_object* v_lctx_1105_; lean_object* v_nextIdx_1106_; lean_object* v___x_1108_; uint8_t v_isShared_1109_; uint8_t v_isSharedCheck_1126_; 
v___x_1104_ = lean_st_ref_take(v_a_1100_);
v_lctx_1105_ = lean_ctor_get(v___x_1104_, 0);
v_nextIdx_1106_ = lean_ctor_get(v___x_1104_, 1);
v_isSharedCheck_1126_ = !lean_is_exclusive(v___x_1104_);
if (v_isSharedCheck_1126_ == 0)
{
v___x_1108_ = v___x_1104_;
v_isShared_1109_ = v_isSharedCheck_1126_;
goto v_resetjp_1107_;
}
else
{
lean_inc(v_nextIdx_1106_);
lean_inc(v_lctx_1105_);
lean_dec(v___x_1104_);
v___x_1108_ = lean_box(0);
v_isShared_1109_ = v_isSharedCheck_1126_;
goto v_resetjp_1107_;
}
v_resetjp_1107_:
{
uint8_t v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1113_; 
v___x_1110_ = 1;
lean_inc_ref(v_decl_1097_);
v___x_1111_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_1110_, v_lctx_1105_, v_decl_1097_);
if (v_isShared_1109_ == 0)
{
lean_ctor_set(v___x_1108_, 0, v___x_1111_);
v___x_1113_ = v___x_1108_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v___x_1111_);
lean_ctor_set(v_reuseFailAlloc_1125_, 1, v_nextIdx_1106_);
v___x_1113_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
lean_object* v___x_1114_; lean_object* v___x_1115_; 
v___x_1114_ = lean_st_ref_set(v_a_1100_, v___x_1113_);
v___x_1115_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_k_1096_, v_a_1098_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_);
if (lean_obj_tag(v___x_1115_) == 0)
{
lean_object* v_a_1116_; lean_object* v___x_1118_; uint8_t v_isShared_1119_; uint8_t v_isSharedCheck_1124_; 
v_a_1116_ = lean_ctor_get(v___x_1115_, 0);
v_isSharedCheck_1124_ = !lean_is_exclusive(v___x_1115_);
if (v_isSharedCheck_1124_ == 0)
{
v___x_1118_ = v___x_1115_;
v_isShared_1119_ = v_isSharedCheck_1124_;
goto v_resetjp_1117_;
}
else
{
lean_inc(v_a_1116_);
lean_dec(v___x_1115_);
v___x_1118_ = lean_box(0);
v_isShared_1119_ = v_isSharedCheck_1124_;
goto v_resetjp_1117_;
}
v_resetjp_1117_:
{
lean_object* v___x_1120_; lean_object* v___x_1122_; 
v___x_1120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1120_, 0, v_decl_1097_);
lean_ctor_set(v___x_1120_, 1, v_a_1116_);
if (v_isShared_1119_ == 0)
{
lean_ctor_set(v___x_1118_, 0, v___x_1120_);
v___x_1122_ = v___x_1118_;
goto v_reusejp_1121_;
}
else
{
lean_object* v_reuseFailAlloc_1123_; 
v_reuseFailAlloc_1123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1123_, 0, v___x_1120_);
v___x_1122_ = v_reuseFailAlloc_1123_;
goto v_reusejp_1121_;
}
v_reusejp_1121_:
{
return v___x_1122_;
}
}
}
else
{
lean_dec_ref(v_decl_1097_);
return v___x_1115_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueErased(lean_object* v_k_1127_, lean_object* v_fvarId_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_){
_start:
{
lean_object* v___x_1135_; lean_object* v_subst_1136_; lean_object* v_jpParamMask_1137_; lean_object* v___x_1139_; uint8_t v_isShared_1140_; uint8_t v_isSharedCheck_1148_; 
v___x_1135_ = lean_st_ref_take(v_a_1129_);
v_subst_1136_ = lean_ctor_get(v___x_1135_, 0);
v_jpParamMask_1137_ = lean_ctor_get(v___x_1135_, 1);
v_isSharedCheck_1148_ = !lean_is_exclusive(v___x_1135_);
if (v_isSharedCheck_1148_ == 0)
{
v___x_1139_ = v___x_1135_;
v_isShared_1140_ = v_isSharedCheck_1148_;
goto v_resetjp_1138_;
}
else
{
lean_inc(v_jpParamMask_1137_);
lean_inc(v_subst_1136_);
lean_dec(v___x_1135_);
v___x_1139_ = lean_box(0);
v_isShared_1140_ = v_isSharedCheck_1148_;
goto v_resetjp_1138_;
}
v_resetjp_1138_:
{
lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1144_; 
v___x_1141_ = lean_box(0);
v___x_1142_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v_subst_1136_, v_fvarId_1128_, v___x_1141_);
if (v_isShared_1140_ == 0)
{
lean_ctor_set(v___x_1139_, 0, v___x_1142_);
v___x_1144_ = v___x_1139_;
goto v_reusejp_1143_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v___x_1142_);
lean_ctor_set(v_reuseFailAlloc_1147_, 1, v_jpParamMask_1137_);
v___x_1144_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1143_;
}
v_reusejp_1143_:
{
lean_object* v___x_1145_; lean_object* v___x_1146_; 
v___x_1145_ = lean_st_ref_set(v_a_1129_, v___x_1144_);
v___x_1146_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_k_1127_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_, v_a_1133_);
return v___x_1146_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkOverApplication(lean_object* v_decl_1150_, lean_object* v_k_1151_, lean_object* v_name_1152_, lean_object* v_numParams_1153_, lean_object* v_args_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_){
_start:
{
lean_object* v_fvarId_1161_; lean_object* v_binderName_1162_; lean_object* v_type_1163_; lean_object* v___x_1165_; uint8_t v_isShared_1166_; uint8_t v_isSharedCheck_1226_; 
v_fvarId_1161_ = lean_ctor_get(v_decl_1150_, 0);
v_binderName_1162_ = lean_ctor_get(v_decl_1150_, 1);
v_type_1163_ = lean_ctor_get(v_decl_1150_, 2);
v_isSharedCheck_1226_ = !lean_is_exclusive(v_decl_1150_);
if (v_isSharedCheck_1226_ == 0)
{
lean_object* v_unused_1227_; 
v_unused_1227_ = lean_ctor_get(v_decl_1150_, 3);
lean_dec(v_unused_1227_);
v___x_1165_ = v_decl_1150_;
v_isShared_1166_ = v_isSharedCheck_1226_;
goto v_resetjp_1164_;
}
else
{
lean_inc(v_type_1163_);
lean_inc(v_binderName_1162_);
lean_inc(v_fvarId_1161_);
lean_dec(v_decl_1150_);
v___x_1165_ = lean_box(0);
v_isShared_1166_ = v_isSharedCheck_1226_;
goto v_resetjp_1164_;
}
v_resetjp_1164_:
{
uint8_t v___x_1167_; lean_object* v___x_1168_; 
v___x_1167_ = 0;
v___x_1168_ = l_Lean_Compiler_LCNF_toImpureType(v_type_1163_, v___x_1167_, v_a_1158_, v_a_1159_);
if (lean_obj_tag(v___x_1168_) == 0)
{
lean_object* v_a_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; uint8_t v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; 
v_a_1169_ = lean_ctor_get(v___x_1168_, 0);
lean_inc(v_a_1169_);
lean_dec_ref(v___x_1168_);
v___x_1170_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_1153_);
v___x_1171_ = l_Array_extract___redArg(v_args_1154_, v___x_1170_, v_numParams_1153_);
v___x_1172_ = 1;
v___x_1173_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkOverApplication___closed__0));
lean_inc(v_binderName_1162_);
v___x_1174_ = l_Lean_Name_str___override(v_binderName_1162_, v___x_1173_);
v___x_1175_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__8, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__8_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__8);
v___x_1176_ = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(v___x_1176_, 0, v_name_1152_);
lean_ctor_set(v___x_1176_, 1, v___x_1171_);
v___x_1177_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_1172_, v___x_1174_, v___x_1175_, v___x_1176_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1159_);
if (lean_obj_tag(v___x_1177_) == 0)
{
lean_object* v_a_1178_; lean_object* v_fvarId_1179_; lean_object* v___x_1180_; lean_object* v_lctx_1181_; lean_object* v_nextIdx_1182_; lean_object* v___x_1184_; uint8_t v_isShared_1185_; uint8_t v_isSharedCheck_1209_; 
v_a_1178_ = lean_ctor_get(v___x_1177_, 0);
lean_inc(v_a_1178_);
lean_dec_ref(v___x_1177_);
v_fvarId_1179_ = lean_ctor_get(v_a_1178_, 0);
v___x_1180_ = lean_st_ref_take(v_a_1157_);
v_lctx_1181_ = lean_ctor_get(v___x_1180_, 0);
v_nextIdx_1182_ = lean_ctor_get(v___x_1180_, 1);
v_isSharedCheck_1209_ = !lean_is_exclusive(v___x_1180_);
if (v_isSharedCheck_1209_ == 0)
{
v___x_1184_ = v___x_1180_;
v_isShared_1185_ = v_isSharedCheck_1209_;
goto v_resetjp_1183_;
}
else
{
lean_inc(v_nextIdx_1182_);
lean_inc(v_lctx_1181_);
lean_dec(v___x_1180_);
v___x_1184_ = lean_box(0);
v_isShared_1185_ = v_isSharedCheck_1209_;
goto v_resetjp_1183_;
}
v_resetjp_1183_:
{
lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1191_; 
v___x_1186_ = lean_array_get_size(v_args_1154_);
v___x_1187_ = l_Array_extract___redArg(v_args_1154_, v_numParams_1153_, v___x_1186_);
lean_inc(v_fvarId_1179_);
v___x_1188_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1188_, 0, v_fvarId_1179_);
lean_ctor_set(v___x_1188_, 1, v___x_1187_);
v___x_1189_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_boxed(v_a_1169_);
lean_dec(v_a_1169_);
if (v_isShared_1166_ == 0)
{
lean_ctor_set(v___x_1165_, 3, v___x_1188_);
lean_ctor_set(v___x_1165_, 2, v___x_1189_);
v___x_1191_ = v___x_1165_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1208_; 
v_reuseFailAlloc_1208_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1208_, 0, v_fvarId_1161_);
lean_ctor_set(v_reuseFailAlloc_1208_, 1, v_binderName_1162_);
lean_ctor_set(v_reuseFailAlloc_1208_, 2, v___x_1189_);
lean_ctor_set(v_reuseFailAlloc_1208_, 3, v___x_1188_);
v___x_1191_ = v_reuseFailAlloc_1208_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
lean_object* v___x_1192_; lean_object* v___x_1194_; 
lean_inc_ref(v___x_1191_);
v___x_1192_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_1172_, v_lctx_1181_, v___x_1191_);
if (v_isShared_1185_ == 0)
{
lean_ctor_set(v___x_1184_, 0, v___x_1192_);
v___x_1194_ = v___x_1184_;
goto v_reusejp_1193_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v___x_1192_);
lean_ctor_set(v_reuseFailAlloc_1207_, 1, v_nextIdx_1182_);
v___x_1194_ = v_reuseFailAlloc_1207_;
goto v_reusejp_1193_;
}
v_reusejp_1193_:
{
lean_object* v___x_1195_; lean_object* v___x_1196_; 
v___x_1195_ = lean_st_ref_set(v_a_1157_, v___x_1194_);
v___x_1196_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_k_1151_, v_a_1155_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1159_);
if (lean_obj_tag(v___x_1196_) == 0)
{
lean_object* v_a_1197_; lean_object* v___x_1199_; uint8_t v_isShared_1200_; uint8_t v_isSharedCheck_1206_; 
v_a_1197_ = lean_ctor_get(v___x_1196_, 0);
v_isSharedCheck_1206_ = !lean_is_exclusive(v___x_1196_);
if (v_isSharedCheck_1206_ == 0)
{
v___x_1199_ = v___x_1196_;
v_isShared_1200_ = v_isSharedCheck_1206_;
goto v_resetjp_1198_;
}
else
{
lean_inc(v_a_1197_);
lean_dec(v___x_1196_);
v___x_1199_ = lean_box(0);
v_isShared_1200_ = v_isSharedCheck_1206_;
goto v_resetjp_1198_;
}
v_resetjp_1198_:
{
lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1204_; 
v___x_1201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1201_, 0, v___x_1191_);
lean_ctor_set(v___x_1201_, 1, v_a_1197_);
v___x_1202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1202_, 0, v_a_1178_);
lean_ctor_set(v___x_1202_, 1, v___x_1201_);
if (v_isShared_1200_ == 0)
{
lean_ctor_set(v___x_1199_, 0, v___x_1202_);
v___x_1204_ = v___x_1199_;
goto v_reusejp_1203_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v___x_1202_);
v___x_1204_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1203_;
}
v_reusejp_1203_:
{
return v___x_1204_;
}
}
}
else
{
lean_dec_ref(v___x_1191_);
lean_dec(v_a_1178_);
return v___x_1196_;
}
}
}
}
}
else
{
lean_object* v_a_1210_; lean_object* v___x_1212_; uint8_t v_isShared_1213_; uint8_t v_isSharedCheck_1217_; 
lean_dec(v_a_1169_);
lean_del_object(v___x_1165_);
lean_dec(v_binderName_1162_);
lean_dec(v_fvarId_1161_);
lean_dec(v_numParams_1153_);
lean_dec_ref(v_k_1151_);
v_a_1210_ = lean_ctor_get(v___x_1177_, 0);
v_isSharedCheck_1217_ = !lean_is_exclusive(v___x_1177_);
if (v_isSharedCheck_1217_ == 0)
{
v___x_1212_ = v___x_1177_;
v_isShared_1213_ = v_isSharedCheck_1217_;
goto v_resetjp_1211_;
}
else
{
lean_inc(v_a_1210_);
lean_dec(v___x_1177_);
v___x_1212_ = lean_box(0);
v_isShared_1213_ = v_isSharedCheck_1217_;
goto v_resetjp_1211_;
}
v_resetjp_1211_:
{
lean_object* v___x_1215_; 
if (v_isShared_1213_ == 0)
{
v___x_1215_ = v___x_1212_;
goto v_reusejp_1214_;
}
else
{
lean_object* v_reuseFailAlloc_1216_; 
v_reuseFailAlloc_1216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1216_, 0, v_a_1210_);
v___x_1215_ = v_reuseFailAlloc_1216_;
goto v_reusejp_1214_;
}
v_reusejp_1214_:
{
return v___x_1215_;
}
}
}
}
else
{
lean_object* v_a_1218_; lean_object* v___x_1220_; uint8_t v_isShared_1221_; uint8_t v_isSharedCheck_1225_; 
lean_del_object(v___x_1165_);
lean_dec(v_binderName_1162_);
lean_dec(v_fvarId_1161_);
lean_dec(v_numParams_1153_);
lean_dec(v_name_1152_);
lean_dec_ref(v_k_1151_);
v_a_1218_ = lean_ctor_get(v___x_1168_, 0);
v_isSharedCheck_1225_ = !lean_is_exclusive(v___x_1168_);
if (v_isSharedCheck_1225_ == 0)
{
v___x_1220_ = v___x_1168_;
v_isShared_1221_ = v_isSharedCheck_1225_;
goto v_resetjp_1219_;
}
else
{
lean_inc(v_a_1218_);
lean_dec(v___x_1168_);
v___x_1220_ = lean_box(0);
v_isShared_1221_ = v_isSharedCheck_1225_;
goto v_resetjp_1219_;
}
v_resetjp_1219_:
{
lean_object* v___x_1223_; 
if (v_isShared_1221_ == 0)
{
v___x_1223_ = v___x_1220_;
goto v_reusejp_1222_;
}
else
{
lean_object* v_reuseFailAlloc_1224_; 
v_reuseFailAlloc_1224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1224_, 0, v_a_1218_);
v___x_1223_ = v_reuseFailAlloc_1224_;
goto v_reusejp_1222_;
}
v_reusejp_1222_:
{
return v___x_1223_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkFap(lean_object* v_decl_1228_, lean_object* v_k_1229_, lean_object* v_name_1230_, lean_object* v_args_1231_, lean_object* v_a_1232_, lean_object* v_a_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_, lean_object* v_a_1236_){
_start:
{
lean_object* v_fvarId_1238_; lean_object* v_binderName_1239_; lean_object* v_type_1240_; lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1260_; 
v_fvarId_1238_ = lean_ctor_get(v_decl_1228_, 0);
v_binderName_1239_ = lean_ctor_get(v_decl_1228_, 1);
v_type_1240_ = lean_ctor_get(v_decl_1228_, 2);
v_isSharedCheck_1260_ = !lean_is_exclusive(v_decl_1228_);
if (v_isSharedCheck_1260_ == 0)
{
lean_object* v_unused_1261_; 
v_unused_1261_ = lean_ctor_get(v_decl_1228_, 3);
lean_dec(v_unused_1261_);
v___x_1242_ = v_decl_1228_;
v_isShared_1243_ = v_isSharedCheck_1260_;
goto v_resetjp_1241_;
}
else
{
lean_inc(v_type_1240_);
lean_inc(v_binderName_1239_);
lean_inc(v_fvarId_1238_);
lean_dec(v_decl_1228_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1260_;
goto v_resetjp_1241_;
}
v_resetjp_1241_:
{
uint8_t v___x_1244_; lean_object* v___x_1245_; 
v___x_1244_ = 0;
v___x_1245_ = l_Lean_Compiler_LCNF_toImpureType(v_type_1240_, v___x_1244_, v_a_1235_, v_a_1236_);
if (lean_obj_tag(v___x_1245_) == 0)
{
lean_object* v_a_1246_; lean_object* v___x_1247_; lean_object* v___x_1249_; 
v_a_1246_ = lean_ctor_get(v___x_1245_, 0);
lean_inc(v_a_1246_);
lean_dec_ref(v___x_1245_);
v___x_1247_ = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(v___x_1247_, 0, v_name_1230_);
lean_ctor_set(v___x_1247_, 1, v_args_1231_);
if (v_isShared_1243_ == 0)
{
lean_ctor_set(v___x_1242_, 3, v___x_1247_);
lean_ctor_set(v___x_1242_, 2, v_a_1246_);
v___x_1249_ = v___x_1242_;
goto v_reusejp_1248_;
}
else
{
lean_object* v_reuseFailAlloc_1251_; 
v_reuseFailAlloc_1251_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1251_, 0, v_fvarId_1238_);
lean_ctor_set(v_reuseFailAlloc_1251_, 1, v_binderName_1239_);
lean_ctor_set(v_reuseFailAlloc_1251_, 2, v_a_1246_);
lean_ctor_set(v_reuseFailAlloc_1251_, 3, v___x_1247_);
v___x_1249_ = v_reuseFailAlloc_1251_;
goto v_reusejp_1248_;
}
v_reusejp_1248_:
{
lean_object* v___x_1250_; 
v___x_1250_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueLet(v_k_1229_, v___x_1249_, v_a_1232_, v_a_1233_, v_a_1234_, v_a_1235_, v_a_1236_);
return v___x_1250_;
}
}
else
{
lean_object* v_a_1252_; lean_object* v___x_1254_; uint8_t v_isShared_1255_; uint8_t v_isSharedCheck_1259_; 
lean_del_object(v___x_1242_);
lean_dec(v_binderName_1239_);
lean_dec(v_fvarId_1238_);
lean_dec_ref(v_args_1231_);
lean_dec(v_name_1230_);
lean_dec_ref(v_k_1229_);
v_a_1252_ = lean_ctor_get(v___x_1245_, 0);
v_isSharedCheck_1259_ = !lean_is_exclusive(v___x_1245_);
if (v_isSharedCheck_1259_ == 0)
{
v___x_1254_ = v___x_1245_;
v_isShared_1255_ = v_isSharedCheck_1259_;
goto v_resetjp_1253_;
}
else
{
lean_inc(v_a_1252_);
lean_dec(v___x_1245_);
v___x_1254_ = lean_box(0);
v_isShared_1255_ = v_isSharedCheck_1259_;
goto v_resetjp_1253_;
}
v_resetjp_1253_:
{
lean_object* v___x_1257_; 
if (v_isShared_1255_ == 0)
{
v___x_1257_ = v___x_1254_;
goto v_reusejp_1256_;
}
else
{
lean_object* v_reuseFailAlloc_1258_; 
v_reuseFailAlloc_1258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1258_, 0, v_a_1252_);
v___x_1257_ = v_reuseFailAlloc_1258_;
goto v_reusejp_1256_;
}
v_reusejp_1256_:
{
return v___x_1257_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkPap(lean_object* v_decl_1262_, lean_object* v_k_1263_, lean_object* v_name_1264_, lean_object* v_args_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_){
_start:
{
lean_object* v_fvarId_1272_; lean_object* v_binderName_1273_; lean_object* v___x_1275_; uint8_t v_isShared_1276_; uint8_t v_isSharedCheck_1283_; 
v_fvarId_1272_ = lean_ctor_get(v_decl_1262_, 0);
v_binderName_1273_ = lean_ctor_get(v_decl_1262_, 1);
v_isSharedCheck_1283_ = !lean_is_exclusive(v_decl_1262_);
if (v_isSharedCheck_1283_ == 0)
{
lean_object* v_unused_1284_; lean_object* v_unused_1285_; 
v_unused_1284_ = lean_ctor_get(v_decl_1262_, 3);
lean_dec(v_unused_1284_);
v_unused_1285_ = lean_ctor_get(v_decl_1262_, 2);
lean_dec(v_unused_1285_);
v___x_1275_ = v_decl_1262_;
v_isShared_1276_ = v_isSharedCheck_1283_;
goto v_resetjp_1274_;
}
else
{
lean_inc(v_binderName_1273_);
lean_inc(v_fvarId_1272_);
lean_dec(v_decl_1262_);
v___x_1275_ = lean_box(0);
v_isShared_1276_ = v_isSharedCheck_1283_;
goto v_resetjp_1274_;
}
v_resetjp_1274_:
{
lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1280_; 
v___x_1277_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__8, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__8_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__8);
v___x_1278_ = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(v___x_1278_, 0, v_name_1264_);
lean_ctor_set(v___x_1278_, 1, v_args_1265_);
if (v_isShared_1276_ == 0)
{
lean_ctor_set(v___x_1275_, 3, v___x_1278_);
lean_ctor_set(v___x_1275_, 2, v___x_1277_);
v___x_1280_ = v___x_1275_;
goto v_reusejp_1279_;
}
else
{
lean_object* v_reuseFailAlloc_1282_; 
v_reuseFailAlloc_1282_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1282_, 0, v_fvarId_1272_);
lean_ctor_set(v_reuseFailAlloc_1282_, 1, v_binderName_1273_);
lean_ctor_set(v_reuseFailAlloc_1282_, 2, v___x_1277_);
lean_ctor_set(v_reuseFailAlloc_1282_, 3, v___x_1278_);
v___x_1280_ = v_reuseFailAlloc_1282_;
goto v_reusejp_1279_;
}
v_reusejp_1279_:
{
lean_object* v___x_1281_; 
v___x_1281_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueLet(v_k_1263_, v___x_1280_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_);
return v___x_1281_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkApplication(lean_object* v_decl_1286_, lean_object* v_k_1287_, lean_object* v_name_1288_, lean_object* v_numParams_1289_, lean_object* v_args_1290_, lean_object* v_a_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_){
_start:
{
lean_object* v_numArgs_1297_; uint8_t v___x_1298_; 
v_numArgs_1297_ = lean_array_get_size(v_args_1290_);
v___x_1298_ = lean_nat_dec_lt(v_numArgs_1297_, v_numParams_1289_);
if (v___x_1298_ == 0)
{
uint8_t v___x_1299_; 
v___x_1299_ = lean_nat_dec_eq(v_numArgs_1297_, v_numParams_1289_);
if (v___x_1299_ == 0)
{
lean_object* v___x_1300_; 
v___x_1300_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkOverApplication(v_decl_1286_, v_k_1287_, v_name_1288_, v_numParams_1289_, v_args_1290_, v_a_1291_, v_a_1292_, v_a_1293_, v_a_1294_, v_a_1295_);
lean_dec_ref(v_args_1290_);
return v___x_1300_;
}
else
{
lean_object* v___x_1301_; 
lean_dec(v_numParams_1289_);
v___x_1301_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkFap(v_decl_1286_, v_k_1287_, v_name_1288_, v_args_1290_, v_a_1291_, v_a_1292_, v_a_1293_, v_a_1294_, v_a_1295_);
return v___x_1301_;
}
}
else
{
lean_object* v___x_1302_; 
lean_dec(v_numParams_1289_);
v___x_1302_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkPap(v_decl_1286_, v_k_1287_, v_name_1288_, v_args_1290_, v_a_1291_, v_a_1292_, v_a_1293_, v_a_1294_, v_a_1295_);
return v___x_1302_;
}
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__4(void){
_start:
{
lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; 
v___x_1304_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__3));
v___x_1305_ = lean_unsigned_to_nat(14u);
v___x_1306_ = lean_unsigned_to_nat(185u);
v___x_1307_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__0));
v___x_1308_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__0));
v___x_1309_ = l_mkPanicMessageWithDecl(v___x_1308_, v___x_1307_, v___x_1306_, v___x_1305_, v___x_1304_);
return v___x_1309_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__9(void){
_start:
{
lean_object* v___x_1316_; lean_object* v___x_1317_; 
v___x_1316_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__2, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__2);
v___x_1317_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_1317_, 0, v___x_1316_);
return v___x_1317_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet(lean_object* v_decl_1326_, lean_object* v_k_1327_, lean_object* v_a_1328_, lean_object* v_a_1329_, lean_object* v_a_1330_, lean_object* v_a_1331_, lean_object* v_a_1332_){
_start:
{
lean_object* v___y_1335_; lean_object* v___y_1336_; lean_object* v___y_1337_; lean_object* v___y_1338_; lean_object* v___y_1339_; lean_object* v___x_1342_; lean_object* v_fvarId_1343_; lean_object* v_binderName_1344_; lean_object* v_type_1345_; lean_object* v_value_1346_; lean_object* v_subst_1347_; lean_object* v___x_1349_; uint8_t v_isShared_1350_; uint8_t v_isSharedCheck_1800_; 
v___x_1342_ = lean_st_ref_get(v_a_1328_);
v_fvarId_1343_ = lean_ctor_get(v_decl_1326_, 0);
v_binderName_1344_ = lean_ctor_get(v_decl_1326_, 1);
v_type_1345_ = lean_ctor_get(v_decl_1326_, 2);
v_value_1346_ = lean_ctor_get(v_decl_1326_, 3);
v_subst_1347_ = lean_ctor_get(v___x_1342_, 0);
v_isSharedCheck_1800_ = !lean_is_exclusive(v___x_1342_);
if (v_isSharedCheck_1800_ == 0)
{
lean_object* v_unused_1801_; 
v_unused_1801_ = lean_ctor_get(v___x_1342_, 1);
lean_dec(v_unused_1801_);
v___x_1349_ = v___x_1342_;
v_isShared_1350_ = v_isSharedCheck_1800_;
goto v_resetjp_1348_;
}
else
{
lean_inc(v_subst_1347_);
lean_dec(v___x_1342_);
v___x_1349_ = lean_box(0);
v_isShared_1350_ = v_isSharedCheck_1800_;
goto v_resetjp_1348_;
}
v___jp_1334_:
{
lean_object* v___x_1340_; lean_object* v___x_1341_; 
v___x_1340_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__2, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__2);
v___x_1341_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0(v___x_1340_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_);
return v___x_1341_;
}
v_resetjp_1348_:
{
uint8_t v___x_1351_; uint8_t v___x_1352_; lean_object* v___x_1353_; 
v___x_1351_ = 0;
v___x_1352_ = 1;
lean_inc(v_value_1346_);
v___x_1353_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(v___x_1351_, v_subst_1347_, v_value_1346_, v___x_1352_);
lean_dec_ref(v_subst_1347_);
switch(lean_obj_tag(v___x_1353_))
{
case 0:
{
lean_object* v___x_1355_; uint8_t v_isShared_1356_; uint8_t v_isSharedCheck_1370_; 
lean_inc(v_binderName_1344_);
lean_inc(v_fvarId_1343_);
lean_del_object(v___x_1349_);
v_isSharedCheck_1370_ = !lean_is_exclusive(v_decl_1326_);
if (v_isSharedCheck_1370_ == 0)
{
lean_object* v_unused_1371_; lean_object* v_unused_1372_; lean_object* v_unused_1373_; lean_object* v_unused_1374_; 
v_unused_1371_ = lean_ctor_get(v_decl_1326_, 3);
lean_dec(v_unused_1371_);
v_unused_1372_ = lean_ctor_get(v_decl_1326_, 2);
lean_dec(v_unused_1372_);
v_unused_1373_ = lean_ctor_get(v_decl_1326_, 1);
lean_dec(v_unused_1373_);
v_unused_1374_ = lean_ctor_get(v_decl_1326_, 0);
lean_dec(v_unused_1374_);
v___x_1355_ = v_decl_1326_;
v_isShared_1356_ = v_isSharedCheck_1370_;
goto v_resetjp_1354_;
}
else
{
lean_dec(v_decl_1326_);
v___x_1355_ = lean_box(0);
v_isShared_1356_ = v_isSharedCheck_1370_;
goto v_resetjp_1354_;
}
v_resetjp_1354_:
{
lean_object* v_value_1357_; lean_object* v___x_1359_; uint8_t v_isShared_1360_; uint8_t v_isSharedCheck_1369_; 
v_value_1357_ = lean_ctor_get(v___x_1353_, 0);
v_isSharedCheck_1369_ = !lean_is_exclusive(v___x_1353_);
if (v_isSharedCheck_1369_ == 0)
{
v___x_1359_ = v___x_1353_;
v_isShared_1360_ = v_isSharedCheck_1369_;
goto v_resetjp_1358_;
}
else
{
lean_inc(v_value_1357_);
lean_dec(v___x_1353_);
v___x_1359_ = lean_box(0);
v_isShared_1360_ = v_isSharedCheck_1369_;
goto v_resetjp_1358_;
}
v_resetjp_1358_:
{
lean_object* v___x_1361_; lean_object* v___x_1363_; 
v___x_1361_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType(v_value_1357_);
if (v_isShared_1360_ == 0)
{
v___x_1363_ = v___x_1359_;
goto v_reusejp_1362_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v_value_1357_);
v___x_1363_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1362_;
}
v_reusejp_1362_:
{
lean_object* v___x_1365_; 
if (v_isShared_1356_ == 0)
{
lean_ctor_set(v___x_1355_, 3, v___x_1363_);
lean_ctor_set(v___x_1355_, 2, v___x_1361_);
v___x_1365_ = v___x_1355_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1367_; 
v_reuseFailAlloc_1367_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1367_, 0, v_fvarId_1343_);
lean_ctor_set(v_reuseFailAlloc_1367_, 1, v_binderName_1344_);
lean_ctor_set(v_reuseFailAlloc_1367_, 2, v___x_1361_);
lean_ctor_set(v_reuseFailAlloc_1367_, 3, v___x_1363_);
v___x_1365_ = v_reuseFailAlloc_1367_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
lean_object* v___x_1366_; 
v___x_1366_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueLet(v_k_1327_, v___x_1365_, v_a_1328_, v_a_1329_, v_a_1330_, v_a_1331_, v_a_1332_);
return v___x_1366_;
}
}
}
}
}
case 1:
{
lean_object* v___x_1375_; 
lean_inc(v_fvarId_1343_);
lean_del_object(v___x_1349_);
lean_dec_ref(v_decl_1326_);
v___x_1375_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueErased(v_k_1327_, v_fvarId_1343_, v_a_1328_, v_a_1329_, v_a_1330_, v_a_1331_, v_a_1332_);
return v___x_1375_;
}
case 2:
{
lean_object* v___x_1377_; uint8_t v_isShared_1378_; uint8_t v_isSharedCheck_1478_; 
lean_inc(v_binderName_1344_);
lean_inc(v_fvarId_1343_);
lean_del_object(v___x_1349_);
v_isSharedCheck_1478_ = !lean_is_exclusive(v_decl_1326_);
if (v_isSharedCheck_1478_ == 0)
{
lean_object* v_unused_1479_; lean_object* v_unused_1480_; lean_object* v_unused_1481_; lean_object* v_unused_1482_; 
v_unused_1479_ = lean_ctor_get(v_decl_1326_, 3);
lean_dec(v_unused_1479_);
v_unused_1480_ = lean_ctor_get(v_decl_1326_, 2);
lean_dec(v_unused_1480_);
v_unused_1481_ = lean_ctor_get(v_decl_1326_, 1);
lean_dec(v_unused_1481_);
v_unused_1482_ = lean_ctor_get(v_decl_1326_, 0);
lean_dec(v_unused_1482_);
v___x_1377_ = v_decl_1326_;
v_isShared_1378_ = v_isSharedCheck_1478_;
goto v_resetjp_1376_;
}
else
{
lean_dec(v_decl_1326_);
v___x_1377_ = lean_box(0);
v_isShared_1378_ = v_isSharedCheck_1478_;
goto v_resetjp_1376_;
}
v_resetjp_1376_:
{
lean_object* v_typeName_1379_; lean_object* v_idx_1380_; lean_object* v_struct_1381_; lean_object* v___x_1382_; 
v_typeName_1379_ = lean_ctor_get(v___x_1353_, 0);
lean_inc(v_typeName_1379_);
v_idx_1380_ = lean_ctor_get(v___x_1353_, 1);
lean_inc(v_idx_1380_);
v_struct_1381_ = lean_ctor_get(v___x_1353_, 2);
lean_inc(v_struct_1381_);
lean_dec_ref(v___x_1353_);
lean_inc(v_typeName_1379_);
v___x_1382_ = l_Lean_Compiler_LCNF_hasTrivialImpureStructure_x3f(v_typeName_1379_, v_a_1331_, v_a_1332_);
if (lean_obj_tag(v___x_1382_) == 0)
{
lean_object* v_a_1383_; 
v_a_1383_ = lean_ctor_get(v___x_1382_, 0);
lean_inc(v_a_1383_);
lean_dec_ref(v___x_1382_);
if (lean_obj_tag(v_a_1383_) == 1)
{
lean_object* v_val_1384_; lean_object* v___x_1386_; uint8_t v_isShared_1387_; uint8_t v_isSharedCheck_1420_; 
lean_dec(v_typeName_1379_);
lean_del_object(v___x_1377_);
lean_dec(v_binderName_1344_);
v_val_1384_ = lean_ctor_get(v_a_1383_, 0);
v_isSharedCheck_1420_ = !lean_is_exclusive(v_a_1383_);
if (v_isSharedCheck_1420_ == 0)
{
v___x_1386_ = v_a_1383_;
v_isShared_1387_ = v_isSharedCheck_1420_;
goto v_resetjp_1385_;
}
else
{
lean_inc(v_val_1384_);
lean_dec(v_a_1383_);
v___x_1386_ = lean_box(0);
v_isShared_1387_ = v_isSharedCheck_1420_;
goto v_resetjp_1385_;
}
v_resetjp_1385_:
{
lean_object* v_fieldIdx_1388_; uint8_t v___x_1389_; 
v_fieldIdx_1388_ = lean_ctor_get(v_val_1384_, 2);
lean_inc(v_fieldIdx_1388_);
lean_dec(v_val_1384_);
v___x_1389_ = lean_nat_dec_eq(v_fieldIdx_1388_, v_idx_1380_);
lean_dec(v_idx_1380_);
lean_dec(v_fieldIdx_1388_);
if (v___x_1389_ == 0)
{
lean_object* v___x_1390_; lean_object* v_subst_1391_; lean_object* v_jpParamMask_1392_; lean_object* v___x_1394_; uint8_t v_isShared_1395_; uint8_t v_isSharedCheck_1403_; 
lean_del_object(v___x_1386_);
lean_dec(v_struct_1381_);
v___x_1390_ = lean_st_ref_take(v_a_1328_);
v_subst_1391_ = lean_ctor_get(v___x_1390_, 0);
v_jpParamMask_1392_ = lean_ctor_get(v___x_1390_, 1);
v_isSharedCheck_1403_ = !lean_is_exclusive(v___x_1390_);
if (v_isSharedCheck_1403_ == 0)
{
v___x_1394_ = v___x_1390_;
v_isShared_1395_ = v_isSharedCheck_1403_;
goto v_resetjp_1393_;
}
else
{
lean_inc(v_jpParamMask_1392_);
lean_inc(v_subst_1391_);
lean_dec(v___x_1390_);
v___x_1394_ = lean_box(0);
v_isShared_1395_ = v_isSharedCheck_1403_;
goto v_resetjp_1393_;
}
v_resetjp_1393_:
{
lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1399_; 
v___x_1396_ = lean_box(0);
v___x_1397_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v_subst_1391_, v_fvarId_1343_, v___x_1396_);
if (v_isShared_1395_ == 0)
{
lean_ctor_set(v___x_1394_, 0, v___x_1397_);
v___x_1399_ = v___x_1394_;
goto v_reusejp_1398_;
}
else
{
lean_object* v_reuseFailAlloc_1402_; 
v_reuseFailAlloc_1402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1402_, 0, v___x_1397_);
lean_ctor_set(v_reuseFailAlloc_1402_, 1, v_jpParamMask_1392_);
v___x_1399_ = v_reuseFailAlloc_1402_;
goto v_reusejp_1398_;
}
v_reusejp_1398_:
{
lean_object* v___x_1400_; lean_object* v___x_1401_; 
v___x_1400_ = lean_st_ref_set(v_a_1328_, v___x_1399_);
v___x_1401_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_k_1327_, v_a_1328_, v_a_1329_, v_a_1330_, v_a_1331_, v_a_1332_);
return v___x_1401_;
}
}
}
else
{
lean_object* v___x_1404_; lean_object* v_subst_1405_; lean_object* v_jpParamMask_1406_; lean_object* v___x_1408_; uint8_t v_isShared_1409_; uint8_t v_isSharedCheck_1419_; 
v___x_1404_ = lean_st_ref_take(v_a_1328_);
v_subst_1405_ = lean_ctor_get(v___x_1404_, 0);
v_jpParamMask_1406_ = lean_ctor_get(v___x_1404_, 1);
v_isSharedCheck_1419_ = !lean_is_exclusive(v___x_1404_);
if (v_isSharedCheck_1419_ == 0)
{
v___x_1408_ = v___x_1404_;
v_isShared_1409_ = v_isSharedCheck_1419_;
goto v_resetjp_1407_;
}
else
{
lean_inc(v_jpParamMask_1406_);
lean_inc(v_subst_1405_);
lean_dec(v___x_1404_);
v___x_1408_ = lean_box(0);
v_isShared_1409_ = v_isSharedCheck_1419_;
goto v_resetjp_1407_;
}
v_resetjp_1407_:
{
lean_object* v___x_1411_; 
if (v_isShared_1387_ == 0)
{
lean_ctor_set(v___x_1386_, 0, v_struct_1381_);
v___x_1411_ = v___x_1386_;
goto v_reusejp_1410_;
}
else
{
lean_object* v_reuseFailAlloc_1418_; 
v_reuseFailAlloc_1418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1418_, 0, v_struct_1381_);
v___x_1411_ = v_reuseFailAlloc_1418_;
goto v_reusejp_1410_;
}
v_reusejp_1410_:
{
lean_object* v___x_1412_; lean_object* v___x_1414_; 
v___x_1412_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v_subst_1405_, v_fvarId_1343_, v___x_1411_);
if (v_isShared_1409_ == 0)
{
lean_ctor_set(v___x_1408_, 0, v___x_1412_);
v___x_1414_ = v___x_1408_;
goto v_reusejp_1413_;
}
else
{
lean_object* v_reuseFailAlloc_1417_; 
v_reuseFailAlloc_1417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1417_, 0, v___x_1412_);
lean_ctor_set(v_reuseFailAlloc_1417_, 1, v_jpParamMask_1406_);
v___x_1414_ = v_reuseFailAlloc_1417_;
goto v_reusejp_1413_;
}
v_reusejp_1413_:
{
lean_object* v___x_1415_; lean_object* v___x_1416_; 
v___x_1415_ = lean_st_ref_set(v_a_1328_, v___x_1414_);
v___x_1416_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_k_1327_, v_a_1328_, v_a_1329_, v_a_1330_, v_a_1331_, v_a_1332_);
return v___x_1416_;
}
}
}
}
}
}
else
{
lean_object* v___x_1421_; lean_object* v_subst_1422_; lean_object* v___x_1423_; 
lean_dec(v_a_1383_);
v___x_1421_ = lean_st_ref_get(v_a_1328_);
v_subst_1422_ = lean_ctor_get(v___x_1421_, 0);
lean_inc_ref(v_subst_1422_);
lean_dec(v___x_1421_);
v___x_1423_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_subst_1422_, v_struct_1381_, v___x_1352_);
lean_dec_ref(v_subst_1422_);
if (lean_obj_tag(v___x_1423_) == 0)
{
lean_object* v_fvarId_1424_; lean_object* v___x_1425_; lean_object* v_env_1426_; uint8_t v___x_1427_; lean_object* v___x_1428_; 
v_fvarId_1424_ = lean_ctor_get(v___x_1423_, 0);
lean_inc(v_fvarId_1424_);
lean_dec_ref(v___x_1423_);
v___x_1425_ = lean_st_ref_get(v_a_1332_);
v_env_1426_ = lean_ctor_get(v___x_1425_, 0);
lean_inc_ref(v_env_1426_);
lean_dec(v___x_1425_);
v___x_1427_ = 0;
v___x_1428_ = l_Lean_Environment_find_x3f(v_env_1426_, v_typeName_1379_, v___x_1427_);
if (lean_obj_tag(v___x_1428_) == 1)
{
lean_object* v_val_1429_; 
v_val_1429_ = lean_ctor_get(v___x_1428_, 0);
lean_inc(v_val_1429_);
lean_dec_ref(v___x_1428_);
if (lean_obj_tag(v_val_1429_) == 5)
{
lean_object* v_val_1430_; lean_object* v_ctors_1431_; 
v_val_1430_ = lean_ctor_get(v_val_1429_, 0);
lean_inc_ref(v_val_1430_);
lean_dec_ref(v_val_1429_);
v_ctors_1431_ = lean_ctor_get(v_val_1430_, 4);
lean_inc(v_ctors_1431_);
lean_dec_ref(v_val_1430_);
if (lean_obj_tag(v_ctors_1431_) == 1)
{
lean_object* v_tail_1432_; 
v_tail_1432_ = lean_ctor_get(v_ctors_1431_, 1);
if (lean_obj_tag(v_tail_1432_) == 0)
{
lean_object* v_head_1433_; lean_object* v___x_1434_; 
v_head_1433_ = lean_ctor_get(v_ctors_1431_, 0);
lean_inc(v_head_1433_);
lean_dec_ref(v_ctors_1431_);
v___x_1434_ = l_Lean_Compiler_LCNF_getCtorLayout(v_head_1433_, v_a_1331_, v_a_1332_);
if (lean_obj_tag(v___x_1434_) == 0)
{
lean_object* v_a_1435_; lean_object* v_ctorInfo_1436_; lean_object* v_fieldInfo_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v_fst_1441_; 
v_a_1435_ = lean_ctor_get(v___x_1434_, 0);
lean_inc(v_a_1435_);
lean_dec_ref(v___x_1434_);
v_ctorInfo_1436_ = lean_ctor_get(v_a_1435_, 0);
lean_inc_ref(v_ctorInfo_1436_);
v_fieldInfo_1437_ = lean_ctor_get(v_a_1435_, 1);
lean_inc_ref(v_fieldInfo_1437_);
lean_dec(v_a_1435_);
v___x_1438_ = lean_box(0);
v___x_1439_ = lean_array_get(v___x_1438_, v_fieldInfo_1437_, v_idx_1380_);
lean_dec(v_idx_1380_);
lean_dec_ref(v_fieldInfo_1437_);
v___x_1440_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj(v_fvarId_1424_, v_ctorInfo_1436_, v___x_1439_);
lean_dec_ref(v_ctorInfo_1436_);
v_fst_1441_ = lean_ctor_get(v___x_1440_, 0);
lean_inc(v_fst_1441_);
if (lean_obj_tag(v_fst_1441_) == 1)
{
lean_object* v___x_1442_; 
lean_dec_ref(v___x_1440_);
lean_del_object(v___x_1377_);
lean_dec(v_binderName_1344_);
v___x_1442_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueErased(v_k_1327_, v_fvarId_1343_, v_a_1328_, v_a_1329_, v_a_1330_, v_a_1331_, v_a_1332_);
return v___x_1442_;
}
else
{
lean_object* v_snd_1443_; lean_object* v___x_1445_; 
v_snd_1443_ = lean_ctor_get(v___x_1440_, 1);
lean_inc(v_snd_1443_);
lean_dec_ref(v___x_1440_);
if (v_isShared_1378_ == 0)
{
lean_ctor_set(v___x_1377_, 3, v_fst_1441_);
lean_ctor_set(v___x_1377_, 2, v_snd_1443_);
v___x_1445_ = v___x_1377_;
goto v_reusejp_1444_;
}
else
{
lean_object* v_reuseFailAlloc_1447_; 
v_reuseFailAlloc_1447_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1447_, 0, v_fvarId_1343_);
lean_ctor_set(v_reuseFailAlloc_1447_, 1, v_binderName_1344_);
lean_ctor_set(v_reuseFailAlloc_1447_, 2, v_snd_1443_);
lean_ctor_set(v_reuseFailAlloc_1447_, 3, v_fst_1441_);
v___x_1445_ = v_reuseFailAlloc_1447_;
goto v_reusejp_1444_;
}
v_reusejp_1444_:
{
lean_object* v___x_1446_; 
v___x_1446_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueLet(v_k_1327_, v___x_1445_, v_a_1328_, v_a_1329_, v_a_1330_, v_a_1331_, v_a_1332_);
return v___x_1446_;
}
}
}
else
{
lean_object* v_a_1448_; lean_object* v___x_1450_; uint8_t v_isShared_1451_; uint8_t v_isSharedCheck_1455_; 
lean_dec(v_fvarId_1424_);
lean_dec(v_idx_1380_);
lean_del_object(v___x_1377_);
lean_dec(v_binderName_1344_);
lean_dec(v_fvarId_1343_);
lean_dec_ref(v_k_1327_);
v_a_1448_ = lean_ctor_get(v___x_1434_, 0);
v_isSharedCheck_1455_ = !lean_is_exclusive(v___x_1434_);
if (v_isSharedCheck_1455_ == 0)
{
v___x_1450_ = v___x_1434_;
v_isShared_1451_ = v_isSharedCheck_1455_;
goto v_resetjp_1449_;
}
else
{
lean_inc(v_a_1448_);
lean_dec(v___x_1434_);
v___x_1450_ = lean_box(0);
v_isShared_1451_ = v_isSharedCheck_1455_;
goto v_resetjp_1449_;
}
v_resetjp_1449_:
{
lean_object* v___x_1453_; 
if (v_isShared_1451_ == 0)
{
v___x_1453_ = v___x_1450_;
goto v_reusejp_1452_;
}
else
{
lean_object* v_reuseFailAlloc_1454_; 
v_reuseFailAlloc_1454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1454_, 0, v_a_1448_);
v___x_1453_ = v_reuseFailAlloc_1454_;
goto v_reusejp_1452_;
}
v_reusejp_1452_:
{
return v___x_1453_;
}
}
}
}
else
{
lean_dec_ref(v_ctors_1431_);
lean_dec(v_fvarId_1424_);
lean_dec(v_idx_1380_);
lean_del_object(v___x_1377_);
lean_dec(v_binderName_1344_);
lean_dec(v_fvarId_1343_);
lean_dec_ref(v_k_1327_);
v___y_1335_ = v_a_1328_;
v___y_1336_ = v_a_1329_;
v___y_1337_ = v_a_1330_;
v___y_1338_ = v_a_1331_;
v___y_1339_ = v_a_1332_;
goto v___jp_1334_;
}
}
else
{
lean_dec(v_ctors_1431_);
lean_dec(v_fvarId_1424_);
lean_dec(v_idx_1380_);
lean_del_object(v___x_1377_);
lean_dec(v_binderName_1344_);
lean_dec(v_fvarId_1343_);
lean_dec_ref(v_k_1327_);
v___y_1335_ = v_a_1328_;
v___y_1336_ = v_a_1329_;
v___y_1337_ = v_a_1330_;
v___y_1338_ = v_a_1331_;
v___y_1339_ = v_a_1332_;
goto v___jp_1334_;
}
}
else
{
lean_dec(v_val_1429_);
lean_dec(v_fvarId_1424_);
lean_dec(v_idx_1380_);
lean_del_object(v___x_1377_);
lean_dec(v_binderName_1344_);
lean_dec(v_fvarId_1343_);
lean_dec_ref(v_k_1327_);
v___y_1335_ = v_a_1328_;
v___y_1336_ = v_a_1329_;
v___y_1337_ = v_a_1330_;
v___y_1338_ = v_a_1331_;
v___y_1339_ = v_a_1332_;
goto v___jp_1334_;
}
}
else
{
lean_dec(v___x_1428_);
lean_dec(v_fvarId_1424_);
lean_dec(v_idx_1380_);
lean_del_object(v___x_1377_);
lean_dec(v_binderName_1344_);
lean_dec(v_fvarId_1343_);
lean_dec_ref(v_k_1327_);
v___y_1335_ = v_a_1328_;
v___y_1336_ = v_a_1329_;
v___y_1337_ = v_a_1330_;
v___y_1338_ = v_a_1331_;
v___y_1339_ = v_a_1332_;
goto v___jp_1334_;
}
}
else
{
lean_object* v___x_1456_; lean_object* v_subst_1457_; lean_object* v_jpParamMask_1458_; lean_object* v___x_1460_; uint8_t v_isShared_1461_; uint8_t v_isSharedCheck_1469_; 
lean_dec(v_idx_1380_);
lean_dec(v_typeName_1379_);
lean_del_object(v___x_1377_);
lean_dec(v_binderName_1344_);
v___x_1456_ = lean_st_ref_take(v_a_1328_);
v_subst_1457_ = lean_ctor_get(v___x_1456_, 0);
v_jpParamMask_1458_ = lean_ctor_get(v___x_1456_, 1);
v_isSharedCheck_1469_ = !lean_is_exclusive(v___x_1456_);
if (v_isSharedCheck_1469_ == 0)
{
v___x_1460_ = v___x_1456_;
v_isShared_1461_ = v_isSharedCheck_1469_;
goto v_resetjp_1459_;
}
else
{
lean_inc(v_jpParamMask_1458_);
lean_inc(v_subst_1457_);
lean_dec(v___x_1456_);
v___x_1460_ = lean_box(0);
v_isShared_1461_ = v_isSharedCheck_1469_;
goto v_resetjp_1459_;
}
v_resetjp_1459_:
{
lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1465_; 
v___x_1462_ = lean_box(0);
v___x_1463_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v_subst_1457_, v_fvarId_1343_, v___x_1462_);
if (v_isShared_1461_ == 0)
{
lean_ctor_set(v___x_1460_, 0, v___x_1463_);
v___x_1465_ = v___x_1460_;
goto v_reusejp_1464_;
}
else
{
lean_object* v_reuseFailAlloc_1468_; 
v_reuseFailAlloc_1468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1468_, 0, v___x_1463_);
lean_ctor_set(v_reuseFailAlloc_1468_, 1, v_jpParamMask_1458_);
v___x_1465_ = v_reuseFailAlloc_1468_;
goto v_reusejp_1464_;
}
v_reusejp_1464_:
{
lean_object* v___x_1466_; lean_object* v___x_1467_; 
v___x_1466_ = lean_st_ref_set(v_a_1328_, v___x_1465_);
v___x_1467_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_k_1327_, v_a_1328_, v_a_1329_, v_a_1330_, v_a_1331_, v_a_1332_);
return v___x_1467_;
}
}
}
}
}
else
{
lean_object* v_a_1470_; lean_object* v___x_1472_; uint8_t v_isShared_1473_; uint8_t v_isSharedCheck_1477_; 
lean_dec(v_struct_1381_);
lean_dec(v_idx_1380_);
lean_dec(v_typeName_1379_);
lean_del_object(v___x_1377_);
lean_dec(v_binderName_1344_);
lean_dec(v_fvarId_1343_);
lean_dec_ref(v_k_1327_);
v_a_1470_ = lean_ctor_get(v___x_1382_, 0);
v_isSharedCheck_1477_ = !lean_is_exclusive(v___x_1382_);
if (v_isSharedCheck_1477_ == 0)
{
v___x_1472_ = v___x_1382_;
v_isShared_1473_ = v_isSharedCheck_1477_;
goto v_resetjp_1471_;
}
else
{
lean_inc(v_a_1470_);
lean_dec(v___x_1382_);
v___x_1472_ = lean_box(0);
v_isShared_1473_ = v_isSharedCheck_1477_;
goto v_resetjp_1471_;
}
v_resetjp_1471_:
{
lean_object* v___x_1475_; 
if (v_isShared_1473_ == 0)
{
v___x_1475_ = v___x_1472_;
goto v_reusejp_1474_;
}
else
{
lean_object* v_reuseFailAlloc_1476_; 
v_reuseFailAlloc_1476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1476_, 0, v_a_1470_);
v___x_1475_ = v_reuseFailAlloc_1476_;
goto v_reusejp_1474_;
}
v_reusejp_1474_:
{
return v___x_1475_;
}
}
}
}
}
case 3:
{
lean_object* v_declName_1483_; lean_object* v_args_1484_; size_t v_sz_1485_; size_t v___x_1486_; lean_object* v___x_1487_; 
v_declName_1483_ = lean_ctor_get(v___x_1353_, 0);
lean_inc(v_declName_1483_);
v_args_1484_ = lean_ctor_get(v___x_1353_, 2);
lean_inc_ref(v_args_1484_);
lean_dec_ref(v___x_1353_);
v_sz_1485_ = lean_array_size(v_args_1484_);
v___x_1486_ = ((size_t)0ULL);
lean_inc_ref(v_args_1484_);
v___x_1487_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__11___redArg(v_sz_1485_, v___x_1486_, v_args_1484_, v_a_1328_);
if (lean_obj_tag(v___x_1487_) == 0)
{
lean_object* v_a_1488_; lean_object* v___x_1489_; 
v_a_1488_ = lean_ctor_get(v___x_1487_, 0);
lean_inc(v_a_1488_);
lean_dec_ref(v___x_1487_);
lean_inc(v_declName_1483_);
v___x_1489_ = l_Lean_Compiler_LCNF_getImpureSignature_x3f___redArg(v_declName_1483_, v_a_1332_);
if (lean_obj_tag(v___x_1489_) == 0)
{
lean_object* v_a_1490_; 
v_a_1490_ = lean_ctor_get(v___x_1489_, 0);
lean_inc(v_a_1490_);
lean_dec_ref(v___x_1489_);
if (lean_obj_tag(v_a_1490_) == 1)
{
lean_object* v_val_1491_; lean_object* v_params_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; 
lean_dec_ref(v_args_1484_);
lean_del_object(v___x_1349_);
v_val_1491_ = lean_ctor_get(v_a_1490_, 0);
lean_inc(v_val_1491_);
lean_dec_ref(v_a_1490_);
v_params_1492_ = lean_ctor_get(v_val_1491_, 3);
lean_inc_ref(v_params_1492_);
lean_dec(v_val_1491_);
v___x_1493_ = lean_array_get_size(v_params_1492_);
lean_dec_ref(v_params_1492_);
v___x_1494_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkApplication(v_decl_1326_, v_k_1327_, v_declName_1483_, v___x_1493_, v_a_1488_, v_a_1328_, v_a_1329_, v_a_1330_, v_a_1331_, v_a_1332_);
return v___x_1494_;
}
else
{
lean_object* v___x_1495_; 
lean_dec(v_a_1490_);
lean_inc(v_declName_1483_);
v___x_1495_ = l_Lean_Compiler_LCNF_getMonoDecl_x3f___redArg(v_declName_1483_, v_a_1332_);
if (lean_obj_tag(v___x_1495_) == 0)
{
lean_object* v_a_1496_; 
v_a_1496_ = lean_ctor_get(v___x_1495_, 0);
lean_inc(v_a_1496_);
lean_dec_ref(v___x_1495_);
if (lean_obj_tag(v_a_1496_) == 1)
{
lean_object* v_val_1497_; lean_object* v_toSignature_1498_; lean_object* v_params_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; 
lean_dec_ref(v_args_1484_);
lean_del_object(v___x_1349_);
v_val_1497_ = lean_ctor_get(v_a_1496_, 0);
lean_inc(v_val_1497_);
lean_dec_ref(v_a_1496_);
v_toSignature_1498_ = lean_ctor_get(v_val_1497_, 0);
lean_inc_ref(v_toSignature_1498_);
lean_dec(v_val_1497_);
v_params_1499_ = lean_ctor_get(v_toSignature_1498_, 3);
lean_inc_ref(v_params_1499_);
lean_dec_ref(v_toSignature_1498_);
v___x_1500_ = lean_array_get_size(v_params_1499_);
lean_dec_ref(v_params_1499_);
v___x_1501_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkApplication(v_decl_1326_, v_k_1327_, v_declName_1483_, v___x_1500_, v_a_1488_, v_a_1328_, v_a_1329_, v_a_1330_, v_a_1331_, v_a_1332_);
return v___x_1501_;
}
else
{
lean_object* v___x_1502_; lean_object* v_env_1503_; uint8_t v___x_1504_; lean_object* v___x_1505_; 
lean_dec(v_a_1496_);
v___x_1502_ = lean_st_ref_get(v_a_1332_);
v_env_1503_ = lean_ctor_get(v___x_1502_, 0);
lean_inc_ref(v_env_1503_);
lean_dec(v___x_1502_);
v___x_1504_ = 0;
lean_inc(v_declName_1483_);
v___x_1505_ = l_Lean_Environment_find_x3f(v_env_1503_, v_declName_1483_, v___x_1504_);
if (lean_obj_tag(v___x_1505_) == 0)
{
lean_object* v___x_1506_; lean_object* v___x_1507_; 
lean_dec(v_a_1488_);
lean_dec_ref(v_args_1484_);
lean_dec(v_declName_1483_);
lean_del_object(v___x_1349_);
lean_dec_ref(v_k_1327_);
lean_dec_ref(v_decl_1326_);
v___x_1506_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__4, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__4_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__4);
v___x_1507_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0(v___x_1506_, v_a_1328_, v_a_1329_, v_a_1330_, v_a_1331_, v_a_1332_);
return v___x_1507_;
}
else
{
lean_object* v_val_1508_; 
v_val_1508_ = lean_ctor_get(v___x_1505_, 0);
lean_inc(v_val_1508_);
lean_dec_ref(v___x_1505_);
switch(lean_obj_tag(v_val_1508_))
{
case 0:
{
lean_object* v___x_1510_; uint8_t v_isShared_1511_; uint8_t v_isSharedCheck_1524_; 
lean_dec(v_a_1488_);
lean_dec_ref(v_args_1484_);
lean_dec_ref(v_k_1327_);
lean_dec_ref(v_decl_1326_);
v_isSharedCheck_1524_ = !lean_is_exclusive(v_val_1508_);
if (v_isSharedCheck_1524_ == 0)
{
lean_object* v_unused_1525_; 
v_unused_1525_ = lean_ctor_get(v_val_1508_, 0);
lean_dec(v_unused_1525_);
v___x_1510_ = v_val_1508_;
v_isShared_1511_ = v_isSharedCheck_1524_;
goto v_resetjp_1509_;
}
else
{
lean_dec(v_val_1508_);
v___x_1510_ = lean_box(0);
v_isShared_1511_ = v_isSharedCheck_1524_;
goto v_resetjp_1509_;
}
v_resetjp_1509_:
{
lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1515_; 
v___x_1512_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__6));
v___x_1513_ = l_Lean_Name_toString(v_declName_1483_, v___x_1352_);
if (v_isShared_1511_ == 0)
{
lean_ctor_set_tag(v___x_1510_, 3);
lean_ctor_set(v___x_1510_, 0, v___x_1513_);
v___x_1515_ = v___x_1510_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1523_; 
v_reuseFailAlloc_1523_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1523_, 0, v___x_1513_);
v___x_1515_ = v_reuseFailAlloc_1523_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
lean_object* v___x_1517_; 
if (v_isShared_1350_ == 0)
{
lean_ctor_set_tag(v___x_1349_, 5);
lean_ctor_set(v___x_1349_, 1, v___x_1515_);
lean_ctor_set(v___x_1349_, 0, v___x_1512_);
v___x_1517_ = v___x_1349_;
goto v_reusejp_1516_;
}
else
{
lean_object* v_reuseFailAlloc_1522_; 
v_reuseFailAlloc_1522_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1522_, 0, v___x_1512_);
lean_ctor_set(v_reuseFailAlloc_1522_, 1, v___x_1515_);
v___x_1517_ = v_reuseFailAlloc_1522_;
goto v_reusejp_1516_;
}
v_reusejp_1516_:
{
lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; 
v___x_1518_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__8));
v___x_1519_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1519_, 0, v___x_1517_);
lean_ctor_set(v___x_1519_, 1, v___x_1518_);
v___x_1520_ = l_Lean_MessageData_ofFormat(v___x_1519_);
v___x_1521_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg(v___x_1520_, v_a_1329_, v_a_1330_, v_a_1331_, v_a_1332_);
return v___x_1521_;
}
}
}
}
case 2:
{
lean_object* v___x_1527_; uint8_t v_isShared_1528_; uint8_t v_isSharedCheck_1541_; 
lean_dec(v_a_1488_);
lean_dec_ref(v_args_1484_);
lean_dec_ref(v_k_1327_);
lean_dec_ref(v_decl_1326_);
v_isSharedCheck_1541_ = !lean_is_exclusive(v_val_1508_);
if (v_isSharedCheck_1541_ == 0)
{
lean_object* v_unused_1542_; 
v_unused_1542_ = lean_ctor_get(v_val_1508_, 0);
lean_dec(v_unused_1542_);
v___x_1527_ = v_val_1508_;
v_isShared_1528_ = v_isSharedCheck_1541_;
goto v_resetjp_1526_;
}
else
{
lean_dec(v_val_1508_);
v___x_1527_ = lean_box(0);
v_isShared_1528_ = v_isSharedCheck_1541_;
goto v_resetjp_1526_;
}
v_resetjp_1526_:
{
lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1532_; 
v___x_1529_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__6));
v___x_1530_ = l_Lean_Name_toString(v_declName_1483_, v___x_1352_);
if (v_isShared_1528_ == 0)
{
lean_ctor_set_tag(v___x_1527_, 3);
lean_ctor_set(v___x_1527_, 0, v___x_1530_);
v___x_1532_ = v___x_1527_;
goto v_reusejp_1531_;
}
else
{
lean_object* v_reuseFailAlloc_1540_; 
v_reuseFailAlloc_1540_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1540_, 0, v___x_1530_);
v___x_1532_ = v_reuseFailAlloc_1540_;
goto v_reusejp_1531_;
}
v_reusejp_1531_:
{
lean_object* v___x_1534_; 
if (v_isShared_1350_ == 0)
{
lean_ctor_set_tag(v___x_1349_, 5);
lean_ctor_set(v___x_1349_, 1, v___x_1532_);
lean_ctor_set(v___x_1349_, 0, v___x_1529_);
v___x_1534_ = v___x_1349_;
goto v_reusejp_1533_;
}
else
{
lean_object* v_reuseFailAlloc_1539_; 
v_reuseFailAlloc_1539_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1539_, 0, v___x_1529_);
lean_ctor_set(v_reuseFailAlloc_1539_, 1, v___x_1532_);
v___x_1534_ = v_reuseFailAlloc_1539_;
goto v_reusejp_1533_;
}
v_reusejp_1533_:
{
lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; 
v___x_1535_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__8));
v___x_1536_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1536_, 0, v___x_1534_);
lean_ctor_set(v___x_1536_, 1, v___x_1535_);
v___x_1537_ = l_Lean_MessageData_ofFormat(v___x_1536_);
v___x_1538_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg(v___x_1537_, v_a_1329_, v_a_1330_, v_a_1331_, v_a_1332_);
return v___x_1538_;
}
}
}
}
case 4:
{
lean_object* v___x_1544_; uint8_t v_isShared_1545_; uint8_t v_isSharedCheck_1558_; 
lean_dec(v_a_1488_);
lean_dec_ref(v_args_1484_);
lean_dec_ref(v_k_1327_);
lean_dec_ref(v_decl_1326_);
v_isSharedCheck_1558_ = !lean_is_exclusive(v_val_1508_);
if (v_isSharedCheck_1558_ == 0)
{
lean_object* v_unused_1559_; 
v_unused_1559_ = lean_ctor_get(v_val_1508_, 0);
lean_dec(v_unused_1559_);
v___x_1544_ = v_val_1508_;
v_isShared_1545_ = v_isSharedCheck_1558_;
goto v_resetjp_1543_;
}
else
{
lean_dec(v_val_1508_);
v___x_1544_ = lean_box(0);
v_isShared_1545_ = v_isSharedCheck_1558_;
goto v_resetjp_1543_;
}
v_resetjp_1543_:
{
lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1549_; 
v___x_1546_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__6));
v___x_1547_ = l_Lean_Name_toString(v_declName_1483_, v___x_1352_);
if (v_isShared_1545_ == 0)
{
lean_ctor_set_tag(v___x_1544_, 3);
lean_ctor_set(v___x_1544_, 0, v___x_1547_);
v___x_1549_ = v___x_1544_;
goto v_reusejp_1548_;
}
else
{
lean_object* v_reuseFailAlloc_1557_; 
v_reuseFailAlloc_1557_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1557_, 0, v___x_1547_);
v___x_1549_ = v_reuseFailAlloc_1557_;
goto v_reusejp_1548_;
}
v_reusejp_1548_:
{
lean_object* v___x_1551_; 
if (v_isShared_1350_ == 0)
{
lean_ctor_set_tag(v___x_1349_, 5);
lean_ctor_set(v___x_1349_, 1, v___x_1549_);
lean_ctor_set(v___x_1349_, 0, v___x_1546_);
v___x_1551_ = v___x_1349_;
goto v_reusejp_1550_;
}
else
{
lean_object* v_reuseFailAlloc_1556_; 
v_reuseFailAlloc_1556_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1556_, 0, v___x_1546_);
lean_ctor_set(v_reuseFailAlloc_1556_, 1, v___x_1549_);
v___x_1551_ = v_reuseFailAlloc_1556_;
goto v_reusejp_1550_;
}
v_reusejp_1550_:
{
lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; 
v___x_1552_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__8));
v___x_1553_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1553_, 0, v___x_1551_);
lean_ctor_set(v___x_1553_, 1, v___x_1552_);
v___x_1554_ = l_Lean_MessageData_ofFormat(v___x_1553_);
v___x_1555_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg(v___x_1554_, v_a_1329_, v_a_1330_, v_a_1331_, v_a_1332_);
return v___x_1555_;
}
}
}
}
case 5:
{
lean_object* v___x_1561_; uint8_t v_isShared_1562_; uint8_t v_isSharedCheck_1575_; 
lean_dec(v_a_1488_);
lean_dec_ref(v_args_1484_);
lean_dec_ref(v_k_1327_);
lean_dec_ref(v_decl_1326_);
v_isSharedCheck_1575_ = !lean_is_exclusive(v_val_1508_);
if (v_isSharedCheck_1575_ == 0)
{
lean_object* v_unused_1576_; 
v_unused_1576_ = lean_ctor_get(v_val_1508_, 0);
lean_dec(v_unused_1576_);
v___x_1561_ = v_val_1508_;
v_isShared_1562_ = v_isSharedCheck_1575_;
goto v_resetjp_1560_;
}
else
{
lean_dec(v_val_1508_);
v___x_1561_ = lean_box(0);
v_isShared_1562_ = v_isSharedCheck_1575_;
goto v_resetjp_1560_;
}
v_resetjp_1560_:
{
lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1566_; 
v___x_1563_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__6));
v___x_1564_ = l_Lean_Name_toString(v_declName_1483_, v___x_1352_);
if (v_isShared_1562_ == 0)
{
lean_ctor_set_tag(v___x_1561_, 3);
lean_ctor_set(v___x_1561_, 0, v___x_1564_);
v___x_1566_ = v___x_1561_;
goto v_reusejp_1565_;
}
else
{
lean_object* v_reuseFailAlloc_1574_; 
v_reuseFailAlloc_1574_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1574_, 0, v___x_1564_);
v___x_1566_ = v_reuseFailAlloc_1574_;
goto v_reusejp_1565_;
}
v_reusejp_1565_:
{
lean_object* v___x_1568_; 
if (v_isShared_1350_ == 0)
{
lean_ctor_set_tag(v___x_1349_, 5);
lean_ctor_set(v___x_1349_, 1, v___x_1566_);
lean_ctor_set(v___x_1349_, 0, v___x_1563_);
v___x_1568_ = v___x_1349_;
goto v_reusejp_1567_;
}
else
{
lean_object* v_reuseFailAlloc_1573_; 
v_reuseFailAlloc_1573_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1573_, 0, v___x_1563_);
lean_ctor_set(v_reuseFailAlloc_1573_, 1, v___x_1566_);
v___x_1568_ = v_reuseFailAlloc_1573_;
goto v_reusejp_1567_;
}
v_reusejp_1567_:
{
lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; 
v___x_1569_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__8));
v___x_1570_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1570_, 0, v___x_1568_);
lean_ctor_set(v___x_1570_, 1, v___x_1569_);
v___x_1571_ = l_Lean_MessageData_ofFormat(v___x_1570_);
v___x_1572_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg(v___x_1571_, v_a_1329_, v_a_1330_, v_a_1331_, v_a_1332_);
return v___x_1572_;
}
}
}
}
case 6:
{
lean_object* v_val_1577_; lean_object* v___x_1579_; uint8_t v_isShared_1580_; uint8_t v_isSharedCheck_1712_; 
v_val_1577_ = lean_ctor_get(v_val_1508_, 0);
v_isSharedCheck_1712_ = !lean_is_exclusive(v_val_1508_);
if (v_isSharedCheck_1712_ == 0)
{
v___x_1579_ = v_val_1508_;
v_isShared_1580_ = v_isSharedCheck_1712_;
goto v_resetjp_1578_;
}
else
{
lean_inc(v_val_1577_);
lean_dec(v_val_1508_);
v___x_1579_ = lean_box(0);
v_isShared_1580_ = v_isSharedCheck_1712_;
goto v_resetjp_1578_;
}
v_resetjp_1578_:
{
lean_object* v_induct_1581_; lean_object* v_cidx_1582_; lean_object* v_numParams_1583_; lean_object* v___x_1584_; 
v_induct_1581_ = lean_ctor_get(v_val_1577_, 1);
lean_inc(v_induct_1581_);
v_cidx_1582_ = lean_ctor_get(v_val_1577_, 2);
lean_inc(v_cidx_1582_);
v_numParams_1583_ = lean_ctor_get(v_val_1577_, 3);
lean_inc(v_numParams_1583_);
lean_dec_ref(v_val_1577_);
lean_inc(v_induct_1581_);
v___x_1584_ = l_Lean_Compiler_LCNF_hasTrivialImpureStructure_x3f(v_induct_1581_, v_a_1331_, v_a_1332_);
if (lean_obj_tag(v___x_1584_) == 0)
{
lean_object* v_a_1585_; 
v_a_1585_ = lean_ctor_get(v___x_1584_, 0);
lean_inc(v_a_1585_);
lean_dec_ref(v___x_1584_);
if (lean_obj_tag(v_a_1585_) == 1)
{
lean_object* v_val_1586_; lean_object* v___x_1587_; lean_object* v_numParams_1588_; lean_object* v_fieldIdx_1589_; lean_object* v_subst_1590_; lean_object* v_jpParamMask_1591_; lean_object* v___x_1593_; uint8_t v_isShared_1594_; uint8_t v_isSharedCheck_1604_; 
lean_inc(v_fvarId_1343_);
lean_dec(v_numParams_1583_);
lean_dec(v_cidx_1582_);
lean_dec(v_induct_1581_);
lean_del_object(v___x_1579_);
lean_dec(v_a_1488_);
lean_dec(v_declName_1483_);
lean_del_object(v___x_1349_);
lean_dec_ref(v_decl_1326_);
v_val_1586_ = lean_ctor_get(v_a_1585_, 0);
lean_inc(v_val_1586_);
lean_dec_ref(v_a_1585_);
v___x_1587_ = lean_st_ref_take(v_a_1328_);
v_numParams_1588_ = lean_ctor_get(v_val_1586_, 1);
lean_inc(v_numParams_1588_);
v_fieldIdx_1589_ = lean_ctor_get(v_val_1586_, 2);
lean_inc(v_fieldIdx_1589_);
lean_dec(v_val_1586_);
v_subst_1590_ = lean_ctor_get(v___x_1587_, 0);
v_jpParamMask_1591_ = lean_ctor_get(v___x_1587_, 1);
v_isSharedCheck_1604_ = !lean_is_exclusive(v___x_1587_);
if (v_isSharedCheck_1604_ == 0)
{
v___x_1593_ = v___x_1587_;
v_isShared_1594_ = v_isSharedCheck_1604_;
goto v_resetjp_1592_;
}
else
{
lean_inc(v_jpParamMask_1591_);
lean_inc(v_subst_1590_);
lean_dec(v___x_1587_);
v___x_1593_ = lean_box(0);
v_isShared_1594_ = v_isSharedCheck_1604_;
goto v_resetjp_1592_;
}
v_resetjp_1592_:
{
lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1600_; 
v___x_1595_ = lean_box(0);
v___x_1596_ = lean_nat_add(v_numParams_1588_, v_fieldIdx_1589_);
lean_dec(v_fieldIdx_1589_);
lean_dec(v_numParams_1588_);
v___x_1597_ = lean_array_get(v___x_1595_, v_args_1484_, v___x_1596_);
lean_dec(v___x_1596_);
lean_dec_ref(v_args_1484_);
v___x_1598_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v_subst_1590_, v_fvarId_1343_, v___x_1597_);
if (v_isShared_1594_ == 0)
{
lean_ctor_set(v___x_1593_, 0, v___x_1598_);
v___x_1600_ = v___x_1593_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1603_; 
v_reuseFailAlloc_1603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1603_, 0, v___x_1598_);
lean_ctor_set(v_reuseFailAlloc_1603_, 1, v_jpParamMask_1591_);
v___x_1600_ = v_reuseFailAlloc_1603_;
goto v_reusejp_1599_;
}
v_reusejp_1599_:
{
lean_object* v___x_1601_; lean_object* v___x_1602_; 
v___x_1601_ = lean_st_ref_set(v_a_1328_, v___x_1600_);
v___x_1602_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_k_1327_, v_a_1328_, v_a_1329_, v_a_1330_, v_a_1331_, v_a_1332_);
return v___x_1602_;
}
}
}
else
{
lean_object* v___x_1605_; 
lean_dec(v_a_1585_);
lean_dec_ref(v_args_1484_);
v___x_1605_ = l_Lean_Compiler_LCNF_nameToImpureType(v_induct_1581_, v_a_1331_, v_a_1332_);
if (lean_obj_tag(v___x_1605_) == 0)
{
lean_object* v_a_1606_; uint8_t v___x_1607_; 
v_a_1606_ = lean_ctor_get(v___x_1605_, 0);
lean_inc(v_a_1606_);
lean_dec_ref(v___x_1605_);
v___x_1607_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar(v_a_1606_);
if (v___x_1607_ == 0)
{
lean_object* v___x_1608_; 
lean_dec(v_a_1606_);
lean_dec(v_cidx_1582_);
lean_del_object(v___x_1579_);
v___x_1608_ = l_Lean_Compiler_LCNF_getCtorLayout(v_declName_1483_, v_a_1331_, v_a_1332_);
if (lean_obj_tag(v___x_1608_) == 0)
{
lean_object* v_a_1609_; lean_object* v___x_1611_; uint8_t v_isShared_1612_; uint8_t v_isSharedCheck_1671_; 
v_a_1609_ = lean_ctor_get(v___x_1608_, 0);
v_isSharedCheck_1671_ = !lean_is_exclusive(v___x_1608_);
if (v_isSharedCheck_1671_ == 0)
{
v___x_1611_ = v___x_1608_;
v_isShared_1612_ = v_isSharedCheck_1671_;
goto v_resetjp_1610_;
}
else
{
lean_inc(v_a_1609_);
lean_dec(v___x_1608_);
v___x_1611_ = lean_box(0);
v_isShared_1612_ = v_isSharedCheck_1671_;
goto v_resetjp_1610_;
}
v_resetjp_1610_:
{
lean_object* v_ctorInfo_1618_; lean_object* v_fieldInfo_1619_; lean_object* v___x_1621_; uint8_t v_isShared_1622_; uint8_t v_isSharedCheck_1670_; 
v_ctorInfo_1618_ = lean_ctor_get(v_a_1609_, 0);
v_fieldInfo_1619_ = lean_ctor_get(v_a_1609_, 1);
v_isSharedCheck_1670_ = !lean_is_exclusive(v_a_1609_);
if (v_isSharedCheck_1670_ == 0)
{
v___x_1621_ = v_a_1609_;
v_isShared_1622_ = v_isSharedCheck_1670_;
goto v_resetjp_1620_;
}
else
{
lean_inc(v_fieldInfo_1619_);
lean_inc(v_ctorInfo_1618_);
lean_dec(v_a_1609_);
v___x_1621_ = lean_box(0);
v_isShared_1622_ = v_isSharedCheck_1670_;
goto v_resetjp_1620_;
}
v___jp_1613_:
{
lean_object* v___x_1614_; lean_object* v___x_1616_; 
v___x_1614_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__9, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__9_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__9);
if (v_isShared_1612_ == 0)
{
lean_ctor_set(v___x_1611_, 0, v___x_1614_);
v___x_1616_ = v___x_1611_;
goto v_reusejp_1615_;
}
else
{
lean_object* v_reuseFailAlloc_1617_; 
v_reuseFailAlloc_1617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1617_, 0, v___x_1614_);
v___x_1616_ = v_reuseFailAlloc_1617_;
goto v_reusejp_1615_;
}
v_reusejp_1615_:
{
return v___x_1616_;
}
}
v_resetjp_1620_:
{
lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; uint8_t v___x_1627_; 
v___x_1623_ = lean_array_get_size(v_a_1488_);
v___x_1624_ = l_Array_extract___redArg(v_a_1488_, v_numParams_1583_, v___x_1623_);
lean_dec(v_a_1488_);
v___x_1625_ = lean_array_get_size(v___x_1624_);
v___x_1626_ = lean_array_get_size(v_fieldInfo_1619_);
v___x_1627_ = lean_nat_dec_eq(v___x_1625_, v___x_1626_);
if (v___x_1627_ == 0)
{
lean_dec_ref(v___x_1624_);
lean_del_object(v___x_1621_);
lean_dec_ref(v_fieldInfo_1619_);
lean_dec_ref(v_ctorInfo_1618_);
lean_del_object(v___x_1349_);
lean_dec_ref(v_k_1327_);
lean_dec_ref(v_decl_1326_);
goto v___jp_1613_;
}
else
{
if (v___x_1607_ == 0)
{
lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; 
lean_del_object(v___x_1611_);
v___x_1628_ = lean_unsigned_to_nat(0u);
v___x_1629_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__5));
v___x_1630_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___redArg(v___x_1626_, v_fieldInfo_1619_, v___x_1624_, v___x_1628_, v___x_1629_);
if (lean_obj_tag(v___x_1630_) == 0)
{
lean_object* v_a_1631_; lean_object* v___x_1632_; lean_object* v_lctx_1633_; lean_object* v_nextIdx_1634_; lean_object* v___x_1636_; uint8_t v_isShared_1637_; uint8_t v_isSharedCheck_1661_; 
v_a_1631_ = lean_ctor_get(v___x_1630_, 0);
lean_inc(v_a_1631_);
lean_dec_ref(v___x_1630_);
v___x_1632_ = lean_st_ref_take(v_a_1330_);
v_lctx_1633_ = lean_ctor_get(v___x_1632_, 0);
v_nextIdx_1634_ = lean_ctor_get(v___x_1632_, 1);
v_isSharedCheck_1661_ = !lean_is_exclusive(v___x_1632_);
if (v_isSharedCheck_1661_ == 0)
{
v___x_1636_ = v___x_1632_;
v_isShared_1637_ = v_isSharedCheck_1661_;
goto v_resetjp_1635_;
}
else
{
lean_inc(v_nextIdx_1634_);
lean_inc(v_lctx_1633_);
lean_dec(v___x_1632_);
v___x_1636_ = lean_box(0);
v_isShared_1637_ = v_isSharedCheck_1661_;
goto v_resetjp_1635_;
}
v_resetjp_1635_:
{
lean_object* v___x_1638_; uint8_t v___x_1639_; lean_object* v___x_1641_; 
v___x_1638_ = l_Lean_Compiler_LCNF_CtorInfo_type(v_ctorInfo_1618_);
v___x_1639_ = 1;
lean_inc_ref(v_ctorInfo_1618_);
if (v_isShared_1622_ == 0)
{
lean_ctor_set_tag(v___x_1621_, 5);
lean_ctor_set(v___x_1621_, 1, v_a_1631_);
v___x_1641_ = v___x_1621_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1660_; 
v_reuseFailAlloc_1660_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1660_, 0, v_ctorInfo_1618_);
lean_ctor_set(v_reuseFailAlloc_1660_, 1, v_a_1631_);
v___x_1641_ = v_reuseFailAlloc_1660_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1645_; 
lean_inc(v_binderName_1344_);
lean_inc(v_fvarId_1343_);
v___x_1642_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1642_, 0, v_fvarId_1343_);
lean_ctor_set(v___x_1642_, 1, v_binderName_1344_);
lean_ctor_set(v___x_1642_, 2, v___x_1638_);
lean_ctor_set(v___x_1642_, 3, v___x_1641_);
lean_inc_ref(v___x_1642_);
v___x_1643_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_1639_, v_lctx_1633_, v___x_1642_);
if (v_isShared_1637_ == 0)
{
lean_ctor_set(v___x_1636_, 0, v___x_1643_);
v___x_1645_ = v___x_1636_;
goto v_reusejp_1644_;
}
else
{
lean_object* v_reuseFailAlloc_1659_; 
v_reuseFailAlloc_1659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1659_, 0, v___x_1643_);
lean_ctor_set(v_reuseFailAlloc_1659_, 1, v_nextIdx_1634_);
v___x_1645_ = v_reuseFailAlloc_1659_;
goto v_reusejp_1644_;
}
v_reusejp_1644_:
{
lean_object* v___x_1646_; lean_object* v___x_1647_; 
v___x_1646_ = lean_st_ref_set(v_a_1330_, v___x_1645_);
v___x_1647_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields(v_decl_1326_, v_k_1327_, v_ctorInfo_1618_, v_fieldInfo_1619_, v___x_1624_, v_a_1328_, v_a_1329_, v_a_1330_, v_a_1331_, v_a_1332_);
lean_dec_ref(v___x_1624_);
lean_dec_ref(v_fieldInfo_1619_);
lean_dec_ref(v_ctorInfo_1618_);
if (lean_obj_tag(v___x_1647_) == 0)
{
lean_object* v_a_1648_; lean_object* v___x_1650_; uint8_t v_isShared_1651_; uint8_t v_isSharedCheck_1658_; 
v_a_1648_ = lean_ctor_get(v___x_1647_, 0);
v_isSharedCheck_1658_ = !lean_is_exclusive(v___x_1647_);
if (v_isSharedCheck_1658_ == 0)
{
v___x_1650_ = v___x_1647_;
v_isShared_1651_ = v_isSharedCheck_1658_;
goto v_resetjp_1649_;
}
else
{
lean_inc(v_a_1648_);
lean_dec(v___x_1647_);
v___x_1650_ = lean_box(0);
v_isShared_1651_ = v_isSharedCheck_1658_;
goto v_resetjp_1649_;
}
v_resetjp_1649_:
{
lean_object* v___x_1653_; 
if (v_isShared_1350_ == 0)
{
lean_ctor_set(v___x_1349_, 1, v_a_1648_);
lean_ctor_set(v___x_1349_, 0, v___x_1642_);
v___x_1653_ = v___x_1349_;
goto v_reusejp_1652_;
}
else
{
lean_object* v_reuseFailAlloc_1657_; 
v_reuseFailAlloc_1657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1657_, 0, v___x_1642_);
lean_ctor_set(v_reuseFailAlloc_1657_, 1, v_a_1648_);
v___x_1653_ = v_reuseFailAlloc_1657_;
goto v_reusejp_1652_;
}
v_reusejp_1652_:
{
lean_object* v___x_1655_; 
if (v_isShared_1651_ == 0)
{
lean_ctor_set(v___x_1650_, 0, v___x_1653_);
v___x_1655_ = v___x_1650_;
goto v_reusejp_1654_;
}
else
{
lean_object* v_reuseFailAlloc_1656_; 
v_reuseFailAlloc_1656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1656_, 0, v___x_1653_);
v___x_1655_ = v_reuseFailAlloc_1656_;
goto v_reusejp_1654_;
}
v_reusejp_1654_:
{
return v___x_1655_;
}
}
}
}
else
{
lean_dec_ref(v___x_1642_);
lean_del_object(v___x_1349_);
return v___x_1647_;
}
}
}
}
}
else
{
lean_object* v_a_1662_; lean_object* v___x_1664_; uint8_t v_isShared_1665_; uint8_t v_isSharedCheck_1669_; 
lean_dec_ref(v___x_1624_);
lean_del_object(v___x_1621_);
lean_dec_ref(v_fieldInfo_1619_);
lean_dec_ref(v_ctorInfo_1618_);
lean_del_object(v___x_1349_);
lean_dec_ref(v_k_1327_);
lean_dec_ref(v_decl_1326_);
v_a_1662_ = lean_ctor_get(v___x_1630_, 0);
v_isSharedCheck_1669_ = !lean_is_exclusive(v___x_1630_);
if (v_isSharedCheck_1669_ == 0)
{
v___x_1664_ = v___x_1630_;
v_isShared_1665_ = v_isSharedCheck_1669_;
goto v_resetjp_1663_;
}
else
{
lean_inc(v_a_1662_);
lean_dec(v___x_1630_);
v___x_1664_ = lean_box(0);
v_isShared_1665_ = v_isSharedCheck_1669_;
goto v_resetjp_1663_;
}
v_resetjp_1663_:
{
lean_object* v___x_1667_; 
if (v_isShared_1665_ == 0)
{
v___x_1667_ = v___x_1664_;
goto v_reusejp_1666_;
}
else
{
lean_object* v_reuseFailAlloc_1668_; 
v_reuseFailAlloc_1668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1668_, 0, v_a_1662_);
v___x_1667_ = v_reuseFailAlloc_1668_;
goto v_reusejp_1666_;
}
v_reusejp_1666_:
{
return v___x_1667_;
}
}
}
}
else
{
lean_dec_ref(v___x_1624_);
lean_del_object(v___x_1621_);
lean_dec_ref(v_fieldInfo_1619_);
lean_dec_ref(v_ctorInfo_1618_);
lean_del_object(v___x_1349_);
lean_dec_ref(v_k_1327_);
lean_dec_ref(v_decl_1326_);
goto v___jp_1613_;
}
}
}
}
}
else
{
lean_object* v_a_1672_; lean_object* v___x_1674_; uint8_t v_isShared_1675_; uint8_t v_isSharedCheck_1679_; 
lean_dec(v_numParams_1583_);
lean_dec(v_a_1488_);
lean_del_object(v___x_1349_);
lean_dec_ref(v_k_1327_);
lean_dec_ref(v_decl_1326_);
v_a_1672_ = lean_ctor_get(v___x_1608_, 0);
v_isSharedCheck_1679_ = !lean_is_exclusive(v___x_1608_);
if (v_isSharedCheck_1679_ == 0)
{
v___x_1674_ = v___x_1608_;
v_isShared_1675_ = v_isSharedCheck_1679_;
goto v_resetjp_1673_;
}
else
{
lean_inc(v_a_1672_);
lean_dec(v___x_1608_);
v___x_1674_ = lean_box(0);
v_isShared_1675_ = v_isSharedCheck_1679_;
goto v_resetjp_1673_;
}
v_resetjp_1673_:
{
lean_object* v___x_1677_; 
if (v_isShared_1675_ == 0)
{
v___x_1677_ = v___x_1674_;
goto v_reusejp_1676_;
}
else
{
lean_object* v_reuseFailAlloc_1678_; 
v_reuseFailAlloc_1678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1678_, 0, v_a_1672_);
v___x_1677_ = v_reuseFailAlloc_1678_;
goto v_reusejp_1676_;
}
v_reusejp_1676_:
{
return v___x_1677_;
}
}
}
}
else
{
lean_object* v___x_1681_; uint8_t v_isShared_1682_; uint8_t v_isSharedCheck_1691_; 
lean_inc(v_binderName_1344_);
lean_inc(v_fvarId_1343_);
lean_dec(v_numParams_1583_);
lean_dec(v_a_1488_);
lean_dec(v_declName_1483_);
lean_del_object(v___x_1349_);
v_isSharedCheck_1691_ = !lean_is_exclusive(v_decl_1326_);
if (v_isSharedCheck_1691_ == 0)
{
lean_object* v_unused_1692_; lean_object* v_unused_1693_; lean_object* v_unused_1694_; lean_object* v_unused_1695_; 
v_unused_1692_ = lean_ctor_get(v_decl_1326_, 3);
lean_dec(v_unused_1692_);
v_unused_1693_ = lean_ctor_get(v_decl_1326_, 2);
lean_dec(v_unused_1693_);
v_unused_1694_ = lean_ctor_get(v_decl_1326_, 1);
lean_dec(v_unused_1694_);
v_unused_1695_ = lean_ctor_get(v_decl_1326_, 0);
lean_dec(v_unused_1695_);
v___x_1681_ = v_decl_1326_;
v_isShared_1682_ = v_isSharedCheck_1691_;
goto v_resetjp_1680_;
}
else
{
lean_dec(v_decl_1326_);
v___x_1681_ = lean_box(0);
v_isShared_1682_ = v_isSharedCheck_1691_;
goto v_resetjp_1680_;
}
v_resetjp_1680_:
{
lean_object* v___x_1683_; lean_object* v___x_1685_; 
v___x_1683_ = l_Lean_Compiler_LCNF_LitValue_impureTypeScalarNumLit(v_a_1606_, v_cidx_1582_);
lean_dec(v_cidx_1582_);
if (v_isShared_1580_ == 0)
{
lean_ctor_set_tag(v___x_1579_, 0);
lean_ctor_set(v___x_1579_, 0, v___x_1683_);
v___x_1685_ = v___x_1579_;
goto v_reusejp_1684_;
}
else
{
lean_object* v_reuseFailAlloc_1690_; 
v_reuseFailAlloc_1690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1690_, 0, v___x_1683_);
v___x_1685_ = v_reuseFailAlloc_1690_;
goto v_reusejp_1684_;
}
v_reusejp_1684_:
{
lean_object* v___x_1687_; 
if (v_isShared_1682_ == 0)
{
lean_ctor_set(v___x_1681_, 3, v___x_1685_);
lean_ctor_set(v___x_1681_, 2, v_a_1606_);
v___x_1687_ = v___x_1681_;
goto v_reusejp_1686_;
}
else
{
lean_object* v_reuseFailAlloc_1689_; 
v_reuseFailAlloc_1689_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1689_, 0, v_fvarId_1343_);
lean_ctor_set(v_reuseFailAlloc_1689_, 1, v_binderName_1344_);
lean_ctor_set(v_reuseFailAlloc_1689_, 2, v_a_1606_);
lean_ctor_set(v_reuseFailAlloc_1689_, 3, v___x_1685_);
v___x_1687_ = v_reuseFailAlloc_1689_;
goto v_reusejp_1686_;
}
v_reusejp_1686_:
{
lean_object* v___x_1688_; 
v___x_1688_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueLet(v_k_1327_, v___x_1687_, v_a_1328_, v_a_1329_, v_a_1330_, v_a_1331_, v_a_1332_);
return v___x_1688_;
}
}
}
}
}
else
{
lean_object* v_a_1696_; lean_object* v___x_1698_; uint8_t v_isShared_1699_; uint8_t v_isSharedCheck_1703_; 
lean_dec(v_numParams_1583_);
lean_dec(v_cidx_1582_);
lean_del_object(v___x_1579_);
lean_dec(v_a_1488_);
lean_dec(v_declName_1483_);
lean_del_object(v___x_1349_);
lean_dec_ref(v_k_1327_);
lean_dec_ref(v_decl_1326_);
v_a_1696_ = lean_ctor_get(v___x_1605_, 0);
v_isSharedCheck_1703_ = !lean_is_exclusive(v___x_1605_);
if (v_isSharedCheck_1703_ == 0)
{
v___x_1698_ = v___x_1605_;
v_isShared_1699_ = v_isSharedCheck_1703_;
goto v_resetjp_1697_;
}
else
{
lean_inc(v_a_1696_);
lean_dec(v___x_1605_);
v___x_1698_ = lean_box(0);
v_isShared_1699_ = v_isSharedCheck_1703_;
goto v_resetjp_1697_;
}
v_resetjp_1697_:
{
lean_object* v___x_1701_; 
if (v_isShared_1699_ == 0)
{
v___x_1701_ = v___x_1698_;
goto v_reusejp_1700_;
}
else
{
lean_object* v_reuseFailAlloc_1702_; 
v_reuseFailAlloc_1702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1702_, 0, v_a_1696_);
v___x_1701_ = v_reuseFailAlloc_1702_;
goto v_reusejp_1700_;
}
v_reusejp_1700_:
{
return v___x_1701_;
}
}
}
}
}
else
{
lean_object* v_a_1704_; lean_object* v___x_1706_; uint8_t v_isShared_1707_; uint8_t v_isSharedCheck_1711_; 
lean_dec(v_numParams_1583_);
lean_dec(v_cidx_1582_);
lean_dec(v_induct_1581_);
lean_del_object(v___x_1579_);
lean_dec(v_a_1488_);
lean_dec_ref(v_args_1484_);
lean_dec(v_declName_1483_);
lean_del_object(v___x_1349_);
lean_dec_ref(v_k_1327_);
lean_dec_ref(v_decl_1326_);
v_a_1704_ = lean_ctor_get(v___x_1584_, 0);
v_isSharedCheck_1711_ = !lean_is_exclusive(v___x_1584_);
if (v_isSharedCheck_1711_ == 0)
{
v___x_1706_ = v___x_1584_;
v_isShared_1707_ = v_isSharedCheck_1711_;
goto v_resetjp_1705_;
}
else
{
lean_inc(v_a_1704_);
lean_dec(v___x_1584_);
v___x_1706_ = lean_box(0);
v_isShared_1707_ = v_isSharedCheck_1711_;
goto v_resetjp_1705_;
}
v_resetjp_1705_:
{
lean_object* v___x_1709_; 
if (v_isShared_1707_ == 0)
{
v___x_1709_ = v___x_1706_;
goto v_reusejp_1708_;
}
else
{
lean_object* v_reuseFailAlloc_1710_; 
v_reuseFailAlloc_1710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1710_, 0, v_a_1704_);
v___x_1709_ = v_reuseFailAlloc_1710_;
goto v_reusejp_1708_;
}
v_reusejp_1708_:
{
return v___x_1709_;
}
}
}
}
}
case 7:
{
lean_object* v___x_1714_; uint8_t v_isShared_1715_; uint8_t v_isSharedCheck_1728_; 
lean_dec(v_a_1488_);
lean_dec_ref(v_args_1484_);
lean_dec_ref(v_k_1327_);
lean_dec_ref(v_decl_1326_);
v_isSharedCheck_1728_ = !lean_is_exclusive(v_val_1508_);
if (v_isSharedCheck_1728_ == 0)
{
lean_object* v_unused_1729_; 
v_unused_1729_ = lean_ctor_get(v_val_1508_, 0);
lean_dec(v_unused_1729_);
v___x_1714_ = v_val_1508_;
v_isShared_1715_ = v_isSharedCheck_1728_;
goto v_resetjp_1713_;
}
else
{
lean_dec(v_val_1508_);
v___x_1714_ = lean_box(0);
v_isShared_1715_ = v_isSharedCheck_1728_;
goto v_resetjp_1713_;
}
v_resetjp_1713_:
{
lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1719_; 
v___x_1716_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__11));
v___x_1717_ = l_Lean_Name_toString(v_declName_1483_, v___x_1352_);
if (v_isShared_1715_ == 0)
{
lean_ctor_set_tag(v___x_1714_, 3);
lean_ctor_set(v___x_1714_, 0, v___x_1717_);
v___x_1719_ = v___x_1714_;
goto v_reusejp_1718_;
}
else
{
lean_object* v_reuseFailAlloc_1727_; 
v_reuseFailAlloc_1727_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1727_, 0, v___x_1717_);
v___x_1719_ = v_reuseFailAlloc_1727_;
goto v_reusejp_1718_;
}
v_reusejp_1718_:
{
lean_object* v___x_1721_; 
if (v_isShared_1350_ == 0)
{
lean_ctor_set_tag(v___x_1349_, 5);
lean_ctor_set(v___x_1349_, 1, v___x_1719_);
lean_ctor_set(v___x_1349_, 0, v___x_1716_);
v___x_1721_ = v___x_1349_;
goto v_reusejp_1720_;
}
else
{
lean_object* v_reuseFailAlloc_1726_; 
v_reuseFailAlloc_1726_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1726_, 0, v___x_1716_);
lean_ctor_set(v_reuseFailAlloc_1726_, 1, v___x_1719_);
v___x_1721_ = v_reuseFailAlloc_1726_;
goto v_reusejp_1720_;
}
v_reusejp_1720_:
{
lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; 
v___x_1722_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__13));
v___x_1723_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1723_, 0, v___x_1721_);
lean_ctor_set(v___x_1723_, 1, v___x_1722_);
v___x_1724_ = l_Lean_MessageData_ofFormat(v___x_1723_);
v___x_1725_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg(v___x_1724_, v_a_1329_, v_a_1330_, v_a_1331_, v_a_1332_);
return v___x_1725_;
}
}
}
}
default: 
{
lean_object* v___x_1730_; 
lean_dec(v_val_1508_);
lean_dec_ref(v_args_1484_);
lean_del_object(v___x_1349_);
v___x_1730_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkFap(v_decl_1326_, v_k_1327_, v_declName_1483_, v_a_1488_, v_a_1328_, v_a_1329_, v_a_1330_, v_a_1331_, v_a_1332_);
return v___x_1730_;
}
}
}
}
}
else
{
lean_object* v_a_1731_; lean_object* v___x_1733_; uint8_t v_isShared_1734_; uint8_t v_isSharedCheck_1738_; 
lean_dec(v_a_1488_);
lean_dec_ref(v_args_1484_);
lean_dec(v_declName_1483_);
lean_del_object(v___x_1349_);
lean_dec_ref(v_k_1327_);
lean_dec_ref(v_decl_1326_);
v_a_1731_ = lean_ctor_get(v___x_1495_, 0);
v_isSharedCheck_1738_ = !lean_is_exclusive(v___x_1495_);
if (v_isSharedCheck_1738_ == 0)
{
v___x_1733_ = v___x_1495_;
v_isShared_1734_ = v_isSharedCheck_1738_;
goto v_resetjp_1732_;
}
else
{
lean_inc(v_a_1731_);
lean_dec(v___x_1495_);
v___x_1733_ = lean_box(0);
v_isShared_1734_ = v_isSharedCheck_1738_;
goto v_resetjp_1732_;
}
v_resetjp_1732_:
{
lean_object* v___x_1736_; 
if (v_isShared_1734_ == 0)
{
v___x_1736_ = v___x_1733_;
goto v_reusejp_1735_;
}
else
{
lean_object* v_reuseFailAlloc_1737_; 
v_reuseFailAlloc_1737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1737_, 0, v_a_1731_);
v___x_1736_ = v_reuseFailAlloc_1737_;
goto v_reusejp_1735_;
}
v_reusejp_1735_:
{
return v___x_1736_;
}
}
}
}
}
else
{
lean_object* v_a_1739_; lean_object* v___x_1741_; uint8_t v_isShared_1742_; uint8_t v_isSharedCheck_1746_; 
lean_dec(v_a_1488_);
lean_dec_ref(v_args_1484_);
lean_dec(v_declName_1483_);
lean_del_object(v___x_1349_);
lean_dec_ref(v_k_1327_);
lean_dec_ref(v_decl_1326_);
v_a_1739_ = lean_ctor_get(v___x_1489_, 0);
v_isSharedCheck_1746_ = !lean_is_exclusive(v___x_1489_);
if (v_isSharedCheck_1746_ == 0)
{
v___x_1741_ = v___x_1489_;
v_isShared_1742_ = v_isSharedCheck_1746_;
goto v_resetjp_1740_;
}
else
{
lean_inc(v_a_1739_);
lean_dec(v___x_1489_);
v___x_1741_ = lean_box(0);
v_isShared_1742_ = v_isSharedCheck_1746_;
goto v_resetjp_1740_;
}
v_resetjp_1740_:
{
lean_object* v___x_1744_; 
if (v_isShared_1742_ == 0)
{
v___x_1744_ = v___x_1741_;
goto v_reusejp_1743_;
}
else
{
lean_object* v_reuseFailAlloc_1745_; 
v_reuseFailAlloc_1745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1745_, 0, v_a_1739_);
v___x_1744_ = v_reuseFailAlloc_1745_;
goto v_reusejp_1743_;
}
v_reusejp_1743_:
{
return v___x_1744_;
}
}
}
}
else
{
lean_object* v_a_1747_; lean_object* v___x_1749_; uint8_t v_isShared_1750_; uint8_t v_isSharedCheck_1754_; 
lean_dec_ref(v_args_1484_);
lean_dec(v_declName_1483_);
lean_del_object(v___x_1349_);
lean_dec_ref(v_k_1327_);
lean_dec_ref(v_decl_1326_);
v_a_1747_ = lean_ctor_get(v___x_1487_, 0);
v_isSharedCheck_1754_ = !lean_is_exclusive(v___x_1487_);
if (v_isSharedCheck_1754_ == 0)
{
v___x_1749_ = v___x_1487_;
v_isShared_1750_ = v_isSharedCheck_1754_;
goto v_resetjp_1748_;
}
else
{
lean_inc(v_a_1747_);
lean_dec(v___x_1487_);
v___x_1749_ = lean_box(0);
v_isShared_1750_ = v_isSharedCheck_1754_;
goto v_resetjp_1748_;
}
v_resetjp_1748_:
{
lean_object* v___x_1752_; 
if (v_isShared_1750_ == 0)
{
v___x_1752_ = v___x_1749_;
goto v_reusejp_1751_;
}
else
{
lean_object* v_reuseFailAlloc_1753_; 
v_reuseFailAlloc_1753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1753_, 0, v_a_1747_);
v___x_1752_ = v_reuseFailAlloc_1753_;
goto v_reusejp_1751_;
}
v_reusejp_1751_:
{
return v___x_1752_;
}
}
}
}
default: 
{
lean_object* v___x_1756_; uint8_t v_isShared_1757_; uint8_t v_isSharedCheck_1795_; 
lean_inc_ref(v_type_1345_);
lean_inc(v_binderName_1344_);
lean_inc(v_fvarId_1343_);
lean_del_object(v___x_1349_);
v_isSharedCheck_1795_ = !lean_is_exclusive(v_decl_1326_);
if (v_isSharedCheck_1795_ == 0)
{
lean_object* v_unused_1796_; lean_object* v_unused_1797_; lean_object* v_unused_1798_; lean_object* v_unused_1799_; 
v_unused_1796_ = lean_ctor_get(v_decl_1326_, 3);
lean_dec(v_unused_1796_);
v_unused_1797_ = lean_ctor_get(v_decl_1326_, 2);
lean_dec(v_unused_1797_);
v_unused_1798_ = lean_ctor_get(v_decl_1326_, 1);
lean_dec(v_unused_1798_);
v_unused_1799_ = lean_ctor_get(v_decl_1326_, 0);
lean_dec(v_unused_1799_);
v___x_1756_ = v_decl_1326_;
v_isShared_1757_ = v_isSharedCheck_1795_;
goto v_resetjp_1755_;
}
else
{
lean_dec(v_decl_1326_);
v___x_1756_ = lean_box(0);
v_isShared_1757_ = v_isSharedCheck_1795_;
goto v_resetjp_1755_;
}
v_resetjp_1755_:
{
lean_object* v_fvarId_1758_; lean_object* v_args_1759_; lean_object* v___x_1761_; uint8_t v_isShared_1762_; uint8_t v_isSharedCheck_1794_; 
v_fvarId_1758_ = lean_ctor_get(v___x_1353_, 0);
v_args_1759_ = lean_ctor_get(v___x_1353_, 1);
v_isSharedCheck_1794_ = !lean_is_exclusive(v___x_1353_);
if (v_isSharedCheck_1794_ == 0)
{
v___x_1761_ = v___x_1353_;
v_isShared_1762_ = v_isSharedCheck_1794_;
goto v_resetjp_1760_;
}
else
{
lean_inc(v_args_1759_);
lean_inc(v_fvarId_1758_);
lean_dec(v___x_1353_);
v___x_1761_ = lean_box(0);
v_isShared_1762_ = v_isSharedCheck_1794_;
goto v_resetjp_1760_;
}
v_resetjp_1760_:
{
size_t v_sz_1763_; size_t v___x_1764_; lean_object* v___x_1765_; 
v_sz_1763_ = lean_array_size(v_args_1759_);
v___x_1764_ = ((size_t)0ULL);
v___x_1765_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__11___redArg(v_sz_1763_, v___x_1764_, v_args_1759_, v_a_1328_);
if (lean_obj_tag(v___x_1765_) == 0)
{
lean_object* v_a_1766_; uint8_t v___x_1767_; lean_object* v___x_1768_; 
v_a_1766_ = lean_ctor_get(v___x_1765_, 0);
lean_inc(v_a_1766_);
lean_dec_ref(v___x_1765_);
v___x_1767_ = 0;
v___x_1768_ = l_Lean_Compiler_LCNF_toImpureType(v_type_1345_, v___x_1767_, v_a_1331_, v_a_1332_);
if (lean_obj_tag(v___x_1768_) == 0)
{
lean_object* v_a_1769_; lean_object* v___x_1770_; lean_object* v___x_1772_; 
v_a_1769_ = lean_ctor_get(v___x_1768_, 0);
lean_inc(v_a_1769_);
lean_dec_ref(v___x_1768_);
v___x_1770_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_boxed(v_a_1769_);
lean_dec(v_a_1769_);
if (v_isShared_1762_ == 0)
{
lean_ctor_set(v___x_1761_, 1, v_a_1766_);
v___x_1772_ = v___x_1761_;
goto v_reusejp_1771_;
}
else
{
lean_object* v_reuseFailAlloc_1777_; 
v_reuseFailAlloc_1777_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1777_, 0, v_fvarId_1758_);
lean_ctor_set(v_reuseFailAlloc_1777_, 1, v_a_1766_);
v___x_1772_ = v_reuseFailAlloc_1777_;
goto v_reusejp_1771_;
}
v_reusejp_1771_:
{
lean_object* v___x_1774_; 
if (v_isShared_1757_ == 0)
{
lean_ctor_set(v___x_1756_, 3, v___x_1772_);
lean_ctor_set(v___x_1756_, 2, v___x_1770_);
v___x_1774_ = v___x_1756_;
goto v_reusejp_1773_;
}
else
{
lean_object* v_reuseFailAlloc_1776_; 
v_reuseFailAlloc_1776_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1776_, 0, v_fvarId_1343_);
lean_ctor_set(v_reuseFailAlloc_1776_, 1, v_binderName_1344_);
lean_ctor_set(v_reuseFailAlloc_1776_, 2, v___x_1770_);
lean_ctor_set(v_reuseFailAlloc_1776_, 3, v___x_1772_);
v___x_1774_ = v_reuseFailAlloc_1776_;
goto v_reusejp_1773_;
}
v_reusejp_1773_:
{
lean_object* v___x_1775_; 
v___x_1775_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueLet(v_k_1327_, v___x_1774_, v_a_1328_, v_a_1329_, v_a_1330_, v_a_1331_, v_a_1332_);
return v___x_1775_;
}
}
}
else
{
lean_object* v_a_1778_; lean_object* v___x_1780_; uint8_t v_isShared_1781_; uint8_t v_isSharedCheck_1785_; 
lean_dec(v_a_1766_);
lean_del_object(v___x_1761_);
lean_dec(v_fvarId_1758_);
lean_del_object(v___x_1756_);
lean_dec(v_binderName_1344_);
lean_dec(v_fvarId_1343_);
lean_dec_ref(v_k_1327_);
v_a_1778_ = lean_ctor_get(v___x_1768_, 0);
v_isSharedCheck_1785_ = !lean_is_exclusive(v___x_1768_);
if (v_isSharedCheck_1785_ == 0)
{
v___x_1780_ = v___x_1768_;
v_isShared_1781_ = v_isSharedCheck_1785_;
goto v_resetjp_1779_;
}
else
{
lean_inc(v_a_1778_);
lean_dec(v___x_1768_);
v___x_1780_ = lean_box(0);
v_isShared_1781_ = v_isSharedCheck_1785_;
goto v_resetjp_1779_;
}
v_resetjp_1779_:
{
lean_object* v___x_1783_; 
if (v_isShared_1781_ == 0)
{
v___x_1783_ = v___x_1780_;
goto v_reusejp_1782_;
}
else
{
lean_object* v_reuseFailAlloc_1784_; 
v_reuseFailAlloc_1784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1784_, 0, v_a_1778_);
v___x_1783_ = v_reuseFailAlloc_1784_;
goto v_reusejp_1782_;
}
v_reusejp_1782_:
{
return v___x_1783_;
}
}
}
}
else
{
lean_object* v_a_1786_; lean_object* v___x_1788_; uint8_t v_isShared_1789_; uint8_t v_isSharedCheck_1793_; 
lean_del_object(v___x_1761_);
lean_dec(v_fvarId_1758_);
lean_del_object(v___x_1756_);
lean_dec_ref(v_type_1345_);
lean_dec(v_binderName_1344_);
lean_dec(v_fvarId_1343_);
lean_dec_ref(v_k_1327_);
v_a_1786_ = lean_ctor_get(v___x_1765_, 0);
v_isSharedCheck_1793_ = !lean_is_exclusive(v___x_1765_);
if (v_isSharedCheck_1793_ == 0)
{
v___x_1788_ = v___x_1765_;
v_isShared_1789_ = v_isSharedCheck_1793_;
goto v_resetjp_1787_;
}
else
{
lean_inc(v_a_1786_);
lean_dec(v___x_1765_);
v___x_1788_ = lean_box(0);
v_isShared_1789_ = v_isSharedCheck_1793_;
goto v_resetjp_1787_;
}
v_resetjp_1787_:
{
lean_object* v___x_1791_; 
if (v_isShared_1789_ == 0)
{
v___x_1791_ = v___x_1788_;
goto v_reusejp_1790_;
}
else
{
lean_object* v_reuseFailAlloc_1792_; 
v_reuseFailAlloc_1792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1792_, 0, v_a_1786_);
v___x_1791_ = v_reuseFailAlloc_1792_;
goto v_reusejp_1790_;
}
v_reusejp_1790_:
{
return v___x_1791_;
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
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__2(void){
_start:
{
lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; 
v___x_1804_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__1));
v___x_1805_ = lean_unsigned_to_nat(15u);
v___x_1806_ = lean_unsigned_to_nat(272u);
v___x_1807_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__0));
v___x_1808_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__0));
v___x_1809_ = l_mkPanicMessageWithDecl(v___x_1808_, v___x_1807_, v___x_1806_, v___x_1805_, v___x_1804_);
return v___x_1809_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__4(void){
_start:
{
lean_object* v___x_1812_; 
v___x_1812_ = l_Array_instInhabited(lean_box(0));
return v___x_1812_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__7(void){
_start:
{
lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; 
v___x_1814_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__6));
v___x_1815_ = lean_unsigned_to_nat(6u);
v___x_1816_ = lean_unsigned_to_nat(251u);
v___x_1817_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__0));
v___x_1818_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__0));
v___x_1819_ = l_mkPanicMessageWithDecl(v___x_1818_, v___x_1817_, v___x_1816_, v___x_1815_, v___x_1814_);
return v___x_1819_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__8(void){
_start:
{
uint8_t v___x_1820_; lean_object* v___x_1821_; 
v___x_1820_ = 0;
v___x_1821_ = l_Lean_Compiler_LCNF_instInhabitedAlt_default__1(v___x_1820_);
return v___x_1821_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__10(void){
_start:
{
lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; 
v___x_1823_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__9));
v___x_1824_ = lean_unsigned_to_nat(6u);
v___x_1825_ = lean_unsigned_to_nat(253u);
v___x_1826_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__0));
v___x_1827_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__0));
v___x_1828_ = l_mkPanicMessageWithDecl(v___x_1827_, v___x_1826_, v___x_1825_, v___x_1824_, v___x_1823_);
return v___x_1828_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__12(void){
_start:
{
lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; 
v___x_1830_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__11));
v___x_1831_ = lean_unsigned_to_nat(6u);
v___x_1832_ = lean_unsigned_to_nat(254u);
v___x_1833_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__0));
v___x_1834_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__0));
v___x_1835_ = l_mkPanicMessageWithDecl(v___x_1834_, v___x_1833_, v___x_1832_, v___x_1831_, v___x_1830_);
return v___x_1835_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__14(void){
_start:
{
lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; 
v___x_1837_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__13));
v___x_1838_ = lean_unsigned_to_nat(45u);
v___x_1839_ = lean_unsigned_to_nat(252u);
v___x_1840_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__0));
v___x_1841_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__0));
v___x_1842_ = l_mkPanicMessageWithDecl(v___x_1841_, v___x_1840_, v___x_1839_, v___x_1838_, v___x_1837_);
return v___x_1842_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop___closed__2(void){
_start:
{
lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; 
v___x_1845_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop___closed__1));
v___x_1846_ = lean_unsigned_to_nat(18u);
v___x_1847_ = lean_unsigned_to_nat(293u);
v___x_1848_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop___closed__0));
v___x_1849_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__0));
v___x_1850_ = l_mkPanicMessageWithDecl(v___x_1849_, v___x_1848_, v___x_1847_, v___x_1846_, v___x_1845_);
return v___x_1850_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop(lean_object* v_discr_1851_, lean_object* v_k_1852_, lean_object* v_ctorInfo_1853_, lean_object* v_params_1854_, lean_object* v_fields_1855_, lean_object* v_i_1856_, lean_object* v_a_1857_, lean_object* v_a_1858_, lean_object* v_a_1859_, lean_object* v_a_1860_, lean_object* v_a_1861_){
_start:
{
lean_object* v___y_1864_; lean_object* v___y_1865_; lean_object* v___y_1866_; lean_object* v___y_1867_; lean_object* v___y_1868_; lean_object* v___y_1872_; lean_object* v___y_1873_; lean_object* v___y_1933_; lean_object* v___x_1939_; uint8_t v___x_1940_; 
v___x_1939_ = lean_array_get_size(v_params_1854_);
v___x_1940_ = lean_nat_dec_lt(v_i_1856_, v___x_1939_);
if (v___x_1940_ == 0)
{
lean_object* v___x_1941_; 
v___x_1941_ = lean_box(0);
v___y_1933_ = v___x_1941_;
goto v___jp_1932_;
}
else
{
lean_object* v___x_1942_; lean_object* v___x_1943_; 
v___x_1942_ = lean_array_fget_borrowed(v_params_1854_, v_i_1856_);
lean_inc(v___x_1942_);
v___x_1943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1943_, 0, v___x_1942_);
v___y_1933_ = v___x_1943_;
goto v___jp_1932_;
}
v___jp_1863_:
{
lean_object* v___x_1869_; lean_object* v___x_1870_; 
v___x_1869_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop___closed__2, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop___closed__2);
v___x_1870_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0(v___x_1869_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_);
return v___x_1870_;
}
v___jp_1871_:
{
if (lean_obj_tag(v___y_1872_) == 0)
{
lean_dec(v_i_1856_);
lean_dec(v_discr_1851_);
if (lean_obj_tag(v___y_1873_) == 0)
{
lean_object* v___x_1874_; 
v___x_1874_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_k_1852_, v_a_1857_, v_a_1858_, v_a_1859_, v_a_1860_, v_a_1861_);
return v___x_1874_;
}
else
{
lean_dec(v___y_1873_);
lean_dec_ref(v_k_1852_);
v___y_1864_ = v_a_1857_;
v___y_1865_ = v_a_1858_;
v___y_1866_ = v_a_1859_;
v___y_1867_ = v_a_1860_;
v___y_1868_ = v_a_1861_;
goto v___jp_1863_;
}
}
else
{
if (lean_obj_tag(v___y_1873_) == 1)
{
lean_object* v_val_1875_; lean_object* v_val_1876_; lean_object* v___x_1877_; lean_object* v_fst_1878_; 
v_val_1875_ = lean_ctor_get(v___y_1872_, 0);
lean_inc(v_val_1875_);
lean_dec_ref(v___y_1872_);
v_val_1876_ = lean_ctor_get(v___y_1873_, 0);
lean_inc(v_val_1876_);
lean_dec_ref(v___y_1873_);
lean_inc(v_discr_1851_);
v___x_1877_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj(v_discr_1851_, v_ctorInfo_1853_, v_val_1876_);
v_fst_1878_ = lean_ctor_get(v___x_1877_, 0);
lean_inc(v_fst_1878_);
if (lean_obj_tag(v_fst_1878_) == 1)
{
lean_object* v___x_1879_; lean_object* v_fvarId_1880_; lean_object* v_subst_1881_; lean_object* v_jpParamMask_1882_; lean_object* v___x_1884_; uint8_t v_isShared_1885_; uint8_t v_isSharedCheck_1895_; 
lean_dec_ref(v___x_1877_);
v___x_1879_ = lean_st_ref_take(v_a_1857_);
v_fvarId_1880_ = lean_ctor_get(v_val_1875_, 0);
lean_inc(v_fvarId_1880_);
lean_dec(v_val_1875_);
v_subst_1881_ = lean_ctor_get(v___x_1879_, 0);
v_jpParamMask_1882_ = lean_ctor_get(v___x_1879_, 1);
v_isSharedCheck_1895_ = !lean_is_exclusive(v___x_1879_);
if (v_isSharedCheck_1895_ == 0)
{
v___x_1884_ = v___x_1879_;
v_isShared_1885_ = v_isSharedCheck_1895_;
goto v_resetjp_1883_;
}
else
{
lean_inc(v_jpParamMask_1882_);
lean_inc(v_subst_1881_);
lean_dec(v___x_1879_);
v___x_1884_ = lean_box(0);
v_isShared_1885_ = v_isSharedCheck_1895_;
goto v_resetjp_1883_;
}
v_resetjp_1883_:
{
lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1889_; 
v___x_1886_ = lean_box(0);
v___x_1887_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v_subst_1881_, v_fvarId_1880_, v___x_1886_);
if (v_isShared_1885_ == 0)
{
lean_ctor_set(v___x_1884_, 0, v___x_1887_);
v___x_1889_ = v___x_1884_;
goto v_reusejp_1888_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v___x_1887_);
lean_ctor_set(v_reuseFailAlloc_1894_, 1, v_jpParamMask_1882_);
v___x_1889_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1888_;
}
v_reusejp_1888_:
{
lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; 
v___x_1890_ = lean_st_ref_set(v_a_1857_, v___x_1889_);
v___x_1891_ = lean_unsigned_to_nat(1u);
v___x_1892_ = lean_nat_add(v_i_1856_, v___x_1891_);
lean_dec(v_i_1856_);
v_i_1856_ = v___x_1892_;
goto _start;
}
}
}
else
{
lean_object* v_snd_1896_; lean_object* v___x_1898_; uint8_t v_isShared_1899_; uint8_t v_isSharedCheck_1930_; 
v_snd_1896_ = lean_ctor_get(v___x_1877_, 1);
v_isSharedCheck_1930_ = !lean_is_exclusive(v___x_1877_);
if (v_isSharedCheck_1930_ == 0)
{
lean_object* v_unused_1931_; 
v_unused_1931_ = lean_ctor_get(v___x_1877_, 0);
lean_dec(v_unused_1931_);
v___x_1898_ = v___x_1877_;
v_isShared_1899_ = v_isSharedCheck_1930_;
goto v_resetjp_1897_;
}
else
{
lean_inc(v_snd_1896_);
lean_dec(v___x_1877_);
v___x_1898_ = lean_box(0);
v_isShared_1899_ = v_isSharedCheck_1930_;
goto v_resetjp_1897_;
}
v_resetjp_1897_:
{
lean_object* v___x_1900_; lean_object* v_fvarId_1901_; lean_object* v_binderName_1902_; lean_object* v_lctx_1903_; lean_object* v_nextIdx_1904_; lean_object* v___x_1906_; uint8_t v_isShared_1907_; uint8_t v_isSharedCheck_1929_; 
v___x_1900_ = lean_st_ref_take(v_a_1859_);
v_fvarId_1901_ = lean_ctor_get(v_val_1875_, 0);
lean_inc(v_fvarId_1901_);
v_binderName_1902_ = lean_ctor_get(v_val_1875_, 1);
lean_inc(v_binderName_1902_);
lean_dec(v_val_1875_);
v_lctx_1903_ = lean_ctor_get(v___x_1900_, 0);
v_nextIdx_1904_ = lean_ctor_get(v___x_1900_, 1);
v_isSharedCheck_1929_ = !lean_is_exclusive(v___x_1900_);
if (v_isSharedCheck_1929_ == 0)
{
v___x_1906_ = v___x_1900_;
v_isShared_1907_ = v_isSharedCheck_1929_;
goto v_resetjp_1905_;
}
else
{
lean_inc(v_nextIdx_1904_);
lean_inc(v_lctx_1903_);
lean_dec(v___x_1900_);
v___x_1906_ = lean_box(0);
v_isShared_1907_ = v_isSharedCheck_1929_;
goto v_resetjp_1905_;
}
v_resetjp_1905_:
{
uint8_t v___x_1908_; lean_object* v_decl_1909_; lean_object* v___x_1910_; lean_object* v___x_1912_; 
v___x_1908_ = 1;
v_decl_1909_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_decl_1909_, 0, v_fvarId_1901_);
lean_ctor_set(v_decl_1909_, 1, v_binderName_1902_);
lean_ctor_set(v_decl_1909_, 2, v_snd_1896_);
lean_ctor_set(v_decl_1909_, 3, v_fst_1878_);
lean_inc_ref(v_decl_1909_);
v___x_1910_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_1908_, v_lctx_1903_, v_decl_1909_);
if (v_isShared_1907_ == 0)
{
lean_ctor_set(v___x_1906_, 0, v___x_1910_);
v___x_1912_ = v___x_1906_;
goto v_reusejp_1911_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v___x_1910_);
lean_ctor_set(v_reuseFailAlloc_1928_, 1, v_nextIdx_1904_);
v___x_1912_ = v_reuseFailAlloc_1928_;
goto v_reusejp_1911_;
}
v_reusejp_1911_:
{
lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; 
v___x_1913_ = lean_st_ref_set(v_a_1859_, v___x_1912_);
v___x_1914_ = lean_unsigned_to_nat(1u);
v___x_1915_ = lean_nat_add(v_i_1856_, v___x_1914_);
lean_dec(v_i_1856_);
v___x_1916_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop(v_discr_1851_, v_k_1852_, v_ctorInfo_1853_, v_params_1854_, v_fields_1855_, v___x_1915_, v_a_1857_, v_a_1858_, v_a_1859_, v_a_1860_, v_a_1861_);
if (lean_obj_tag(v___x_1916_) == 0)
{
lean_object* v_a_1917_; lean_object* v___x_1919_; uint8_t v_isShared_1920_; uint8_t v_isSharedCheck_1927_; 
v_a_1917_ = lean_ctor_get(v___x_1916_, 0);
v_isSharedCheck_1927_ = !lean_is_exclusive(v___x_1916_);
if (v_isSharedCheck_1927_ == 0)
{
v___x_1919_ = v___x_1916_;
v_isShared_1920_ = v_isSharedCheck_1927_;
goto v_resetjp_1918_;
}
else
{
lean_inc(v_a_1917_);
lean_dec(v___x_1916_);
v___x_1919_ = lean_box(0);
v_isShared_1920_ = v_isSharedCheck_1927_;
goto v_resetjp_1918_;
}
v_resetjp_1918_:
{
lean_object* v___x_1922_; 
if (v_isShared_1899_ == 0)
{
lean_ctor_set(v___x_1898_, 1, v_a_1917_);
lean_ctor_set(v___x_1898_, 0, v_decl_1909_);
v___x_1922_ = v___x_1898_;
goto v_reusejp_1921_;
}
else
{
lean_object* v_reuseFailAlloc_1926_; 
v_reuseFailAlloc_1926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1926_, 0, v_decl_1909_);
lean_ctor_set(v_reuseFailAlloc_1926_, 1, v_a_1917_);
v___x_1922_ = v_reuseFailAlloc_1926_;
goto v_reusejp_1921_;
}
v_reusejp_1921_:
{
lean_object* v___x_1924_; 
if (v_isShared_1920_ == 0)
{
lean_ctor_set(v___x_1919_, 0, v___x_1922_);
v___x_1924_ = v___x_1919_;
goto v_reusejp_1923_;
}
else
{
lean_object* v_reuseFailAlloc_1925_; 
v_reuseFailAlloc_1925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1925_, 0, v___x_1922_);
v___x_1924_ = v_reuseFailAlloc_1925_;
goto v_reusejp_1923_;
}
v_reusejp_1923_:
{
return v___x_1924_;
}
}
}
}
else
{
lean_dec_ref(v_decl_1909_);
lean_del_object(v___x_1898_);
return v___x_1916_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___y_1872_);
lean_dec(v___y_1873_);
lean_dec(v_i_1856_);
lean_dec_ref(v_k_1852_);
lean_dec(v_discr_1851_);
v___y_1864_ = v_a_1857_;
v___y_1865_ = v_a_1858_;
v___y_1866_ = v_a_1859_;
v___y_1867_ = v_a_1860_;
v___y_1868_ = v_a_1861_;
goto v___jp_1863_;
}
}
}
v___jp_1932_:
{
lean_object* v___x_1934_; uint8_t v___x_1935_; 
v___x_1934_ = lean_array_get_size(v_fields_1855_);
v___x_1935_ = lean_nat_dec_lt(v_i_1856_, v___x_1934_);
if (v___x_1935_ == 0)
{
lean_object* v___x_1936_; 
v___x_1936_ = lean_box(0);
v___y_1872_ = v___y_1933_;
v___y_1873_ = v___x_1936_;
goto v___jp_1871_;
}
else
{
lean_object* v___x_1937_; lean_object* v___x_1938_; 
v___x_1937_ = lean_array_fget_borrowed(v_fields_1855_, v_i_1856_);
lean_inc(v___x_1937_);
v___x_1938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1938_, 0, v___x_1937_);
v___y_1872_ = v___y_1933_;
v___y_1873_ = v___x_1938_;
goto v___jp_1871_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure(lean_object* v_discr_1944_, lean_object* v_alt_1945_, lean_object* v_a_1946_, lean_object* v_a_1947_, lean_object* v_a_1948_, lean_object* v_a_1949_, lean_object* v_a_1950_){
_start:
{
if (lean_obj_tag(v_alt_1945_) == 0)
{
lean_object* v_ctorName_1952_; lean_object* v_params_1953_; lean_object* v_code_1954_; lean_object* v___x_1955_; 
v_ctorName_1952_ = lean_ctor_get(v_alt_1945_, 0);
lean_inc(v_ctorName_1952_);
v_params_1953_ = lean_ctor_get(v_alt_1945_, 1);
lean_inc_ref(v_params_1953_);
v_code_1954_ = lean_ctor_get(v_alt_1945_, 2);
lean_inc_ref(v_code_1954_);
lean_dec_ref(v_alt_1945_);
v___x_1955_ = l_Lean_Compiler_LCNF_getCtorLayout(v_ctorName_1952_, v_a_1949_, v_a_1950_);
if (lean_obj_tag(v___x_1955_) == 0)
{
lean_object* v_a_1956_; lean_object* v_ctorInfo_1957_; lean_object* v_fieldInfo_1958_; lean_object* v___x_1960_; uint8_t v_isShared_1961_; uint8_t v_isSharedCheck_1983_; 
v_a_1956_ = lean_ctor_get(v___x_1955_, 0);
lean_inc(v_a_1956_);
lean_dec_ref(v___x_1955_);
v_ctorInfo_1957_ = lean_ctor_get(v_a_1956_, 0);
v_fieldInfo_1958_ = lean_ctor_get(v_a_1956_, 1);
v_isSharedCheck_1983_ = !lean_is_exclusive(v_a_1956_);
if (v_isSharedCheck_1983_ == 0)
{
v___x_1960_ = v_a_1956_;
v_isShared_1961_ = v_isSharedCheck_1983_;
goto v_resetjp_1959_;
}
else
{
lean_inc(v_fieldInfo_1958_);
lean_inc(v_ctorInfo_1957_);
lean_dec(v_a_1956_);
v___x_1960_ = lean_box(0);
v_isShared_1961_ = v_isSharedCheck_1983_;
goto v_resetjp_1959_;
}
v_resetjp_1959_:
{
lean_object* v___x_1962_; lean_object* v___x_1963_; 
v___x_1962_ = lean_unsigned_to_nat(0u);
v___x_1963_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop(v_discr_1944_, v_code_1954_, v_ctorInfo_1957_, v_params_1953_, v_fieldInfo_1958_, v___x_1962_, v_a_1946_, v_a_1947_, v_a_1948_, v_a_1949_, v_a_1950_);
lean_dec_ref(v_fieldInfo_1958_);
lean_dec_ref(v_params_1953_);
if (lean_obj_tag(v___x_1963_) == 0)
{
lean_object* v_a_1964_; lean_object* v___x_1966_; uint8_t v_isShared_1967_; uint8_t v_isSharedCheck_1974_; 
v_a_1964_ = lean_ctor_get(v___x_1963_, 0);
v_isSharedCheck_1974_ = !lean_is_exclusive(v___x_1963_);
if (v_isSharedCheck_1974_ == 0)
{
v___x_1966_ = v___x_1963_;
v_isShared_1967_ = v_isSharedCheck_1974_;
goto v_resetjp_1965_;
}
else
{
lean_inc(v_a_1964_);
lean_dec(v___x_1963_);
v___x_1966_ = lean_box(0);
v_isShared_1967_ = v_isSharedCheck_1974_;
goto v_resetjp_1965_;
}
v_resetjp_1965_:
{
lean_object* v___x_1969_; 
if (v_isShared_1961_ == 0)
{
lean_ctor_set_tag(v___x_1960_, 1);
lean_ctor_set(v___x_1960_, 1, v_a_1964_);
v___x_1969_ = v___x_1960_;
goto v_reusejp_1968_;
}
else
{
lean_object* v_reuseFailAlloc_1973_; 
v_reuseFailAlloc_1973_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1973_, 0, v_ctorInfo_1957_);
lean_ctor_set(v_reuseFailAlloc_1973_, 1, v_a_1964_);
v___x_1969_ = v_reuseFailAlloc_1973_;
goto v_reusejp_1968_;
}
v_reusejp_1968_:
{
lean_object* v___x_1971_; 
if (v_isShared_1967_ == 0)
{
lean_ctor_set(v___x_1966_, 0, v___x_1969_);
v___x_1971_ = v___x_1966_;
goto v_reusejp_1970_;
}
else
{
lean_object* v_reuseFailAlloc_1972_; 
v_reuseFailAlloc_1972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1972_, 0, v___x_1969_);
v___x_1971_ = v_reuseFailAlloc_1972_;
goto v_reusejp_1970_;
}
v_reusejp_1970_:
{
return v___x_1971_;
}
}
}
}
else
{
lean_object* v_a_1975_; lean_object* v___x_1977_; uint8_t v_isShared_1978_; uint8_t v_isSharedCheck_1982_; 
lean_del_object(v___x_1960_);
lean_dec_ref(v_ctorInfo_1957_);
v_a_1975_ = lean_ctor_get(v___x_1963_, 0);
v_isSharedCheck_1982_ = !lean_is_exclusive(v___x_1963_);
if (v_isSharedCheck_1982_ == 0)
{
v___x_1977_ = v___x_1963_;
v_isShared_1978_ = v_isSharedCheck_1982_;
goto v_resetjp_1976_;
}
else
{
lean_inc(v_a_1975_);
lean_dec(v___x_1963_);
v___x_1977_ = lean_box(0);
v_isShared_1978_ = v_isSharedCheck_1982_;
goto v_resetjp_1976_;
}
v_resetjp_1976_:
{
lean_object* v___x_1980_; 
if (v_isShared_1978_ == 0)
{
v___x_1980_ = v___x_1977_;
goto v_reusejp_1979_;
}
else
{
lean_object* v_reuseFailAlloc_1981_; 
v_reuseFailAlloc_1981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1981_, 0, v_a_1975_);
v___x_1980_ = v_reuseFailAlloc_1981_;
goto v_reusejp_1979_;
}
v_reusejp_1979_:
{
return v___x_1980_;
}
}
}
}
}
else
{
lean_object* v_a_1984_; lean_object* v___x_1986_; uint8_t v_isShared_1987_; uint8_t v_isSharedCheck_1991_; 
lean_dec_ref(v_code_1954_);
lean_dec_ref(v_params_1953_);
lean_dec(v_discr_1944_);
v_a_1984_ = lean_ctor_get(v___x_1955_, 0);
v_isSharedCheck_1991_ = !lean_is_exclusive(v___x_1955_);
if (v_isSharedCheck_1991_ == 0)
{
v___x_1986_ = v___x_1955_;
v_isShared_1987_ = v_isSharedCheck_1991_;
goto v_resetjp_1985_;
}
else
{
lean_inc(v_a_1984_);
lean_dec(v___x_1955_);
v___x_1986_ = lean_box(0);
v_isShared_1987_ = v_isSharedCheck_1991_;
goto v_resetjp_1985_;
}
v_resetjp_1985_:
{
lean_object* v___x_1989_; 
if (v_isShared_1987_ == 0)
{
v___x_1989_ = v___x_1986_;
goto v_reusejp_1988_;
}
else
{
lean_object* v_reuseFailAlloc_1990_; 
v_reuseFailAlloc_1990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1990_, 0, v_a_1984_);
v___x_1989_ = v_reuseFailAlloc_1990_;
goto v_reusejp_1988_;
}
v_reusejp_1988_:
{
return v___x_1989_;
}
}
}
}
else
{
lean_object* v_code_1992_; lean_object* v___x_1994_; uint8_t v_isShared_1995_; uint8_t v_isSharedCheck_2016_; 
lean_dec(v_discr_1944_);
v_code_1992_ = lean_ctor_get(v_alt_1945_, 0);
v_isSharedCheck_2016_ = !lean_is_exclusive(v_alt_1945_);
if (v_isSharedCheck_2016_ == 0)
{
v___x_1994_ = v_alt_1945_;
v_isShared_1995_ = v_isSharedCheck_2016_;
goto v_resetjp_1993_;
}
else
{
lean_inc(v_code_1992_);
lean_dec(v_alt_1945_);
v___x_1994_ = lean_box(0);
v_isShared_1995_ = v_isSharedCheck_2016_;
goto v_resetjp_1993_;
}
v_resetjp_1993_:
{
lean_object* v___x_1996_; 
v___x_1996_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_code_1992_, v_a_1946_, v_a_1947_, v_a_1948_, v_a_1949_, v_a_1950_);
if (lean_obj_tag(v___x_1996_) == 0)
{
lean_object* v_a_1997_; lean_object* v___x_1999_; uint8_t v_isShared_2000_; uint8_t v_isSharedCheck_2007_; 
v_a_1997_ = lean_ctor_get(v___x_1996_, 0);
v_isSharedCheck_2007_ = !lean_is_exclusive(v___x_1996_);
if (v_isSharedCheck_2007_ == 0)
{
v___x_1999_ = v___x_1996_;
v_isShared_2000_ = v_isSharedCheck_2007_;
goto v_resetjp_1998_;
}
else
{
lean_inc(v_a_1997_);
lean_dec(v___x_1996_);
v___x_1999_ = lean_box(0);
v_isShared_2000_ = v_isSharedCheck_2007_;
goto v_resetjp_1998_;
}
v_resetjp_1998_:
{
lean_object* v___x_2002_; 
if (v_isShared_1995_ == 0)
{
lean_ctor_set(v___x_1994_, 0, v_a_1997_);
v___x_2002_ = v___x_1994_;
goto v_reusejp_2001_;
}
else
{
lean_object* v_reuseFailAlloc_2006_; 
v_reuseFailAlloc_2006_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2006_, 0, v_a_1997_);
v___x_2002_ = v_reuseFailAlloc_2006_;
goto v_reusejp_2001_;
}
v_reusejp_2001_:
{
lean_object* v___x_2004_; 
if (v_isShared_2000_ == 0)
{
lean_ctor_set(v___x_1999_, 0, v___x_2002_);
v___x_2004_ = v___x_1999_;
goto v_reusejp_2003_;
}
else
{
lean_object* v_reuseFailAlloc_2005_; 
v_reuseFailAlloc_2005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2005_, 0, v___x_2002_);
v___x_2004_ = v_reuseFailAlloc_2005_;
goto v_reusejp_2003_;
}
v_reusejp_2003_:
{
return v___x_2004_;
}
}
}
}
else
{
lean_object* v_a_2008_; lean_object* v___x_2010_; uint8_t v_isShared_2011_; uint8_t v_isSharedCheck_2015_; 
lean_del_object(v___x_1994_);
v_a_2008_ = lean_ctor_get(v___x_1996_, 0);
v_isSharedCheck_2015_ = !lean_is_exclusive(v___x_1996_);
if (v_isSharedCheck_2015_ == 0)
{
v___x_2010_ = v___x_1996_;
v_isShared_2011_ = v_isSharedCheck_2015_;
goto v_resetjp_2009_;
}
else
{
lean_inc(v_a_2008_);
lean_dec(v___x_1996_);
v___x_2010_ = lean_box(0);
v_isShared_2011_ = v_isSharedCheck_2015_;
goto v_resetjp_2009_;
}
v_resetjp_2009_:
{
lean_object* v___x_2013_; 
if (v_isShared_2011_ == 0)
{
v___x_2013_ = v___x_2010_;
goto v_reusejp_2012_;
}
else
{
lean_object* v_reuseFailAlloc_2014_; 
v_reuseFailAlloc_2014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2014_, 0, v_a_2008_);
v___x_2013_ = v_reuseFailAlloc_2014_;
goto v_reusejp_2012_;
}
v_reusejp_2012_:
{
return v___x_2013_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__8(lean_object* v_fvarId_2017_, size_t v_sz_2018_, size_t v_i_2019_, lean_object* v_bs_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_){
_start:
{
uint8_t v___x_2027_; 
v___x_2027_ = lean_usize_dec_lt(v_i_2019_, v_sz_2018_);
if (v___x_2027_ == 0)
{
lean_object* v___x_2028_; 
lean_dec(v_fvarId_2017_);
v___x_2028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2028_, 0, v_bs_2020_);
return v___x_2028_;
}
else
{
lean_object* v_v_2029_; lean_object* v___x_2030_; 
v_v_2029_ = lean_array_uget_borrowed(v_bs_2020_, v_i_2019_);
lean_inc(v_v_2029_);
lean_inc(v_fvarId_2017_);
v___x_2030_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure(v_fvarId_2017_, v_v_2029_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_);
if (lean_obj_tag(v___x_2030_) == 0)
{
lean_object* v_a_2031_; lean_object* v___x_2032_; lean_object* v_bs_x27_2033_; size_t v___x_2034_; size_t v___x_2035_; lean_object* v___x_2036_; 
v_a_2031_ = lean_ctor_get(v___x_2030_, 0);
lean_inc(v_a_2031_);
lean_dec_ref(v___x_2030_);
v___x_2032_ = lean_unsigned_to_nat(0u);
v_bs_x27_2033_ = lean_array_uset(v_bs_2020_, v_i_2019_, v___x_2032_);
v___x_2034_ = ((size_t)1ULL);
v___x_2035_ = lean_usize_add(v_i_2019_, v___x_2034_);
v___x_2036_ = lean_array_uset(v_bs_x27_2033_, v_i_2019_, v_a_2031_);
v_i_2019_ = v___x_2035_;
v_bs_2020_ = v___x_2036_;
goto _start;
}
else
{
lean_object* v_a_2038_; lean_object* v___x_2040_; uint8_t v_isShared_2041_; uint8_t v_isSharedCheck_2045_; 
lean_dec_ref(v_bs_2020_);
lean_dec(v_fvarId_2017_);
v_a_2038_ = lean_ctor_get(v___x_2030_, 0);
v_isSharedCheck_2045_ = !lean_is_exclusive(v___x_2030_);
if (v_isSharedCheck_2045_ == 0)
{
v___x_2040_ = v___x_2030_;
v_isShared_2041_ = v_isSharedCheck_2045_;
goto v_resetjp_2039_;
}
else
{
lean_inc(v_a_2038_);
lean_dec(v___x_2030_);
v___x_2040_ = lean_box(0);
v_isShared_2041_ = v_isSharedCheck_2045_;
goto v_resetjp_2039_;
}
v_resetjp_2039_:
{
lean_object* v___x_2043_; 
if (v_isShared_2041_ == 0)
{
v___x_2043_ = v___x_2040_;
goto v_reusejp_2042_;
}
else
{
lean_object* v_reuseFailAlloc_2044_; 
v_reuseFailAlloc_2044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2044_, 0, v_a_2038_);
v___x_2043_ = v_reuseFailAlloc_2044_;
goto v_reusejp_2042_;
}
v_reusejp_2042_:
{
return v___x_2043_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(lean_object* v_c_2046_, lean_object* v_a_2047_, lean_object* v_a_2048_, lean_object* v_a_2049_, lean_object* v_a_2050_, lean_object* v_a_2051_){
_start:
{
switch(lean_obj_tag(v_c_2046_))
{
case 0:
{
lean_object* v_decl_2053_; lean_object* v_k_2054_; lean_object* v___x_2055_; 
v_decl_2053_ = lean_ctor_get(v_c_2046_, 0);
lean_inc_ref(v_decl_2053_);
v_k_2054_ = lean_ctor_get(v_c_2046_, 1);
lean_inc_ref(v_k_2054_);
lean_dec_ref(v_c_2046_);
v___x_2055_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet(v_decl_2053_, v_k_2054_, v_a_2047_, v_a_2048_, v_a_2049_, v_a_2050_, v_a_2051_);
return v___x_2055_;
}
case 1:
{
lean_object* v___x_2056_; lean_object* v___x_2057_; 
lean_dec_ref(v_c_2046_);
v___x_2056_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__2, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__2);
v___x_2057_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0(v___x_2056_, v_a_2047_, v_a_2048_, v_a_2049_, v_a_2050_, v_a_2051_);
return v___x_2057_;
}
case 2:
{
lean_object* v_decl_2058_; lean_object* v_k_2059_; lean_object* v___x_2061_; uint8_t v_isShared_2062_; uint8_t v_isSharedCheck_2151_; 
v_decl_2058_ = lean_ctor_get(v_c_2046_, 0);
v_k_2059_ = lean_ctor_get(v_c_2046_, 1);
v_isSharedCheck_2151_ = !lean_is_exclusive(v_c_2046_);
if (v_isSharedCheck_2151_ == 0)
{
v___x_2061_ = v_c_2046_;
v_isShared_2062_ = v_isSharedCheck_2151_;
goto v_resetjp_2060_;
}
else
{
lean_inc(v_k_2059_);
lean_inc(v_decl_2058_);
lean_dec(v_c_2046_);
v___x_2061_ = lean_box(0);
v_isShared_2062_ = v_isSharedCheck_2151_;
goto v_resetjp_2060_;
}
v_resetjp_2060_:
{
lean_object* v_fvarId_2063_; lean_object* v_binderName_2064_; lean_object* v_params_2065_; lean_object* v_type_2066_; lean_object* v_value_2067_; lean_object* v___x_2069_; uint8_t v_isShared_2070_; uint8_t v_isSharedCheck_2150_; 
v_fvarId_2063_ = lean_ctor_get(v_decl_2058_, 0);
v_binderName_2064_ = lean_ctor_get(v_decl_2058_, 1);
v_params_2065_ = lean_ctor_get(v_decl_2058_, 2);
v_type_2066_ = lean_ctor_get(v_decl_2058_, 3);
v_value_2067_ = lean_ctor_get(v_decl_2058_, 4);
v_isSharedCheck_2150_ = !lean_is_exclusive(v_decl_2058_);
if (v_isSharedCheck_2150_ == 0)
{
v___x_2069_ = v_decl_2058_;
v_isShared_2070_ = v_isSharedCheck_2150_;
goto v_resetjp_2068_;
}
else
{
lean_inc(v_value_2067_);
lean_inc(v_type_2066_);
lean_inc(v_params_2065_);
lean_inc(v_binderName_2064_);
lean_inc(v_fvarId_2063_);
lean_dec(v_decl_2058_);
v___x_2069_ = lean_box(0);
v_isShared_2070_ = v_isSharedCheck_2150_;
goto v_resetjp_2068_;
}
v_resetjp_2068_:
{
size_t v_sz_2071_; size_t v___x_2072_; lean_object* v___x_2073_; 
v_sz_2071_ = lean_array_size(v_params_2065_);
v___x_2072_ = ((size_t)0ULL);
v___x_2073_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__2___redArg(v_sz_2071_, v___x_2072_, v_params_2065_, v_a_2047_, v_a_2049_, v_a_2050_, v_a_2051_);
if (lean_obj_tag(v___x_2073_) == 0)
{
lean_object* v_a_2074_; lean_object* v___x_2075_; lean_object* v_subst_2076_; lean_object* v_jpParamMask_2077_; lean_object* v___x_2079_; uint8_t v_isShared_2080_; uint8_t v_isSharedCheck_2141_; 
v_a_2074_ = lean_ctor_get(v___x_2073_, 0);
lean_inc(v_a_2074_);
lean_dec_ref(v___x_2073_);
v___x_2075_ = lean_st_ref_take(v_a_2047_);
v_subst_2076_ = lean_ctor_get(v___x_2075_, 0);
v_jpParamMask_2077_ = lean_ctor_get(v___x_2075_, 1);
v_isSharedCheck_2141_ = !lean_is_exclusive(v___x_2075_);
if (v_isSharedCheck_2141_ == 0)
{
v___x_2079_ = v___x_2075_;
v_isShared_2080_ = v_isSharedCheck_2141_;
goto v_resetjp_2078_;
}
else
{
lean_inc(v_jpParamMask_2077_);
lean_inc(v_subst_2076_);
lean_dec(v___x_2075_);
v___x_2079_ = lean_box(0);
v_isShared_2080_ = v_isSharedCheck_2141_;
goto v_resetjp_2078_;
}
v_resetjp_2078_:
{
size_t v_sz_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2085_; 
v_sz_2081_ = lean_array_size(v_a_2074_);
lean_inc(v_a_2074_);
v___x_2082_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__3(v_sz_2081_, v___x_2072_, v_a_2074_);
lean_inc_ref(v___x_2082_);
lean_inc(v_fvarId_2063_);
v___x_2083_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v_jpParamMask_2077_, v_fvarId_2063_, v___x_2082_);
if (v_isShared_2080_ == 0)
{
lean_ctor_set(v___x_2079_, 1, v___x_2083_);
v___x_2085_ = v___x_2079_;
goto v_reusejp_2084_;
}
else
{
lean_object* v_reuseFailAlloc_2140_; 
v_reuseFailAlloc_2140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2140_, 0, v_subst_2076_);
lean_ctor_set(v_reuseFailAlloc_2140_, 1, v___x_2083_);
v___x_2085_ = v_reuseFailAlloc_2140_;
goto v_reusejp_2084_;
}
v_reusejp_2084_:
{
lean_object* v___x_2086_; lean_object* v___y_2088_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; uint8_t v___x_2134_; 
v___x_2086_ = lean_st_ref_set(v_a_2047_, v___x_2085_);
v___x_2130_ = lean_unsigned_to_nat(0u);
v___x_2131_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__3));
v___x_2132_ = l_Array_zip___redArg(v_a_2074_, v___x_2082_);
lean_dec_ref(v___x_2082_);
v___x_2133_ = lean_array_get_size(v___x_2132_);
v___x_2134_ = lean_nat_dec_lt(v___x_2130_, v___x_2133_);
if (v___x_2134_ == 0)
{
lean_dec_ref(v___x_2132_);
v___y_2088_ = v___x_2131_;
goto v___jp_2087_;
}
else
{
uint8_t v___x_2135_; 
v___x_2135_ = lean_nat_dec_le(v___x_2133_, v___x_2133_);
if (v___x_2135_ == 0)
{
if (v___x_2134_ == 0)
{
lean_dec_ref(v___x_2132_);
v___y_2088_ = v___x_2131_;
goto v___jp_2087_;
}
else
{
size_t v___x_2136_; lean_object* v___x_2137_; 
v___x_2136_ = lean_usize_of_nat(v___x_2133_);
v___x_2137_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__4(v___x_2132_, v___x_2072_, v___x_2136_, v___x_2131_);
lean_dec_ref(v___x_2132_);
v___y_2088_ = v___x_2137_;
goto v___jp_2087_;
}
}
else
{
size_t v___x_2138_; lean_object* v___x_2139_; 
v___x_2138_ = lean_usize_of_nat(v___x_2133_);
v___x_2139_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__4(v___x_2132_, v___x_2072_, v___x_2138_, v___x_2131_);
lean_dec_ref(v___x_2132_);
v___y_2088_ = v___x_2139_;
goto v___jp_2087_;
}
}
v___jp_2087_:
{
lean_object* v___x_2089_; 
v___x_2089_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_value_2067_, v_a_2047_, v_a_2048_, v_a_2049_, v_a_2050_, v_a_2051_);
if (lean_obj_tag(v___x_2089_) == 0)
{
lean_object* v_a_2090_; lean_object* v___x_2091_; 
v_a_2090_ = lean_ctor_get(v___x_2089_, 0);
lean_inc(v_a_2090_);
lean_dec_ref(v___x_2089_);
v___x_2091_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_k_2059_, v_a_2047_, v_a_2048_, v_a_2049_, v_a_2050_, v_a_2051_);
if (lean_obj_tag(v___x_2091_) == 0)
{
lean_object* v_a_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; 
v_a_2092_ = lean_ctor_get(v___x_2091_, 0);
lean_inc(v_a_2092_);
lean_dec_ref(v___x_2091_);
v___x_2093_ = lean_array_get_size(v_a_2074_);
lean_dec(v_a_2074_);
v___x_2094_ = l_Lean_Compiler_LCNF_lowerResultType(v_type_2066_, v___x_2093_, v_a_2050_, v_a_2051_);
lean_dec_ref(v_type_2066_);
if (lean_obj_tag(v___x_2094_) == 0)
{
lean_object* v_a_2095_; lean_object* v___x_2097_; uint8_t v_isShared_2098_; uint8_t v_isSharedCheck_2121_; 
v_a_2095_ = lean_ctor_get(v___x_2094_, 0);
v_isSharedCheck_2121_ = !lean_is_exclusive(v___x_2094_);
if (v_isSharedCheck_2121_ == 0)
{
v___x_2097_ = v___x_2094_;
v_isShared_2098_ = v_isSharedCheck_2121_;
goto v_resetjp_2096_;
}
else
{
lean_inc(v_a_2095_);
lean_dec(v___x_2094_);
v___x_2097_ = lean_box(0);
v_isShared_2098_ = v_isSharedCheck_2121_;
goto v_resetjp_2096_;
}
v_resetjp_2096_:
{
lean_object* v___x_2099_; lean_object* v_lctx_2100_; lean_object* v_nextIdx_2101_; lean_object* v___x_2103_; uint8_t v_isShared_2104_; uint8_t v_isSharedCheck_2120_; 
v___x_2099_ = lean_st_ref_take(v_a_2049_);
v_lctx_2100_ = lean_ctor_get(v___x_2099_, 0);
v_nextIdx_2101_ = lean_ctor_get(v___x_2099_, 1);
v_isSharedCheck_2120_ = !lean_is_exclusive(v___x_2099_);
if (v_isSharedCheck_2120_ == 0)
{
v___x_2103_ = v___x_2099_;
v_isShared_2104_ = v_isSharedCheck_2120_;
goto v_resetjp_2102_;
}
else
{
lean_inc(v_nextIdx_2101_);
lean_inc(v_lctx_2100_);
lean_dec(v___x_2099_);
v___x_2103_ = lean_box(0);
v_isShared_2104_ = v_isSharedCheck_2120_;
goto v_resetjp_2102_;
}
v_resetjp_2102_:
{
uint8_t v___x_2105_; lean_object* v___x_2107_; 
v___x_2105_ = 1;
if (v_isShared_2070_ == 0)
{
lean_ctor_set(v___x_2069_, 4, v_a_2090_);
lean_ctor_set(v___x_2069_, 3, v_a_2095_);
lean_ctor_set(v___x_2069_, 2, v___y_2088_);
v___x_2107_ = v___x_2069_;
goto v_reusejp_2106_;
}
else
{
lean_object* v_reuseFailAlloc_2119_; 
v_reuseFailAlloc_2119_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2119_, 0, v_fvarId_2063_);
lean_ctor_set(v_reuseFailAlloc_2119_, 1, v_binderName_2064_);
lean_ctor_set(v_reuseFailAlloc_2119_, 2, v___y_2088_);
lean_ctor_set(v_reuseFailAlloc_2119_, 3, v_a_2095_);
lean_ctor_set(v_reuseFailAlloc_2119_, 4, v_a_2090_);
v___x_2107_ = v_reuseFailAlloc_2119_;
goto v_reusejp_2106_;
}
v_reusejp_2106_:
{
lean_object* v___x_2108_; lean_object* v___x_2110_; 
lean_inc_ref(v___x_2107_);
v___x_2108_ = l_Lean_Compiler_LCNF_LCtx_addFunDecl(v___x_2105_, v_lctx_2100_, v___x_2107_);
if (v_isShared_2104_ == 0)
{
lean_ctor_set(v___x_2103_, 0, v___x_2108_);
v___x_2110_ = v___x_2103_;
goto v_reusejp_2109_;
}
else
{
lean_object* v_reuseFailAlloc_2118_; 
v_reuseFailAlloc_2118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2118_, 0, v___x_2108_);
lean_ctor_set(v_reuseFailAlloc_2118_, 1, v_nextIdx_2101_);
v___x_2110_ = v_reuseFailAlloc_2118_;
goto v_reusejp_2109_;
}
v_reusejp_2109_:
{
lean_object* v___x_2111_; lean_object* v___x_2113_; 
v___x_2111_ = lean_st_ref_set(v_a_2049_, v___x_2110_);
if (v_isShared_2062_ == 0)
{
lean_ctor_set(v___x_2061_, 1, v_a_2092_);
lean_ctor_set(v___x_2061_, 0, v___x_2107_);
v___x_2113_ = v___x_2061_;
goto v_reusejp_2112_;
}
else
{
lean_object* v_reuseFailAlloc_2117_; 
v_reuseFailAlloc_2117_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2117_, 0, v___x_2107_);
lean_ctor_set(v_reuseFailAlloc_2117_, 1, v_a_2092_);
v___x_2113_ = v_reuseFailAlloc_2117_;
goto v_reusejp_2112_;
}
v_reusejp_2112_:
{
lean_object* v___x_2115_; 
if (v_isShared_2098_ == 0)
{
lean_ctor_set(v___x_2097_, 0, v___x_2113_);
v___x_2115_ = v___x_2097_;
goto v_reusejp_2114_;
}
else
{
lean_object* v_reuseFailAlloc_2116_; 
v_reuseFailAlloc_2116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2116_, 0, v___x_2113_);
v___x_2115_ = v_reuseFailAlloc_2116_;
goto v_reusejp_2114_;
}
v_reusejp_2114_:
{
return v___x_2115_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2122_; lean_object* v___x_2124_; uint8_t v_isShared_2125_; uint8_t v_isSharedCheck_2129_; 
lean_dec(v_a_2092_);
lean_dec(v_a_2090_);
lean_dec_ref(v___y_2088_);
lean_del_object(v___x_2069_);
lean_dec(v_binderName_2064_);
lean_dec(v_fvarId_2063_);
lean_del_object(v___x_2061_);
v_a_2122_ = lean_ctor_get(v___x_2094_, 0);
v_isSharedCheck_2129_ = !lean_is_exclusive(v___x_2094_);
if (v_isSharedCheck_2129_ == 0)
{
v___x_2124_ = v___x_2094_;
v_isShared_2125_ = v_isSharedCheck_2129_;
goto v_resetjp_2123_;
}
else
{
lean_inc(v_a_2122_);
lean_dec(v___x_2094_);
v___x_2124_ = lean_box(0);
v_isShared_2125_ = v_isSharedCheck_2129_;
goto v_resetjp_2123_;
}
v_resetjp_2123_:
{
lean_object* v___x_2127_; 
if (v_isShared_2125_ == 0)
{
v___x_2127_ = v___x_2124_;
goto v_reusejp_2126_;
}
else
{
lean_object* v_reuseFailAlloc_2128_; 
v_reuseFailAlloc_2128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2128_, 0, v_a_2122_);
v___x_2127_ = v_reuseFailAlloc_2128_;
goto v_reusejp_2126_;
}
v_reusejp_2126_:
{
return v___x_2127_;
}
}
}
}
else
{
lean_dec(v_a_2090_);
lean_dec_ref(v___y_2088_);
lean_dec(v_a_2074_);
lean_del_object(v___x_2069_);
lean_dec_ref(v_type_2066_);
lean_dec(v_binderName_2064_);
lean_dec(v_fvarId_2063_);
lean_del_object(v___x_2061_);
return v___x_2091_;
}
}
else
{
lean_dec_ref(v___y_2088_);
lean_dec(v_a_2074_);
lean_del_object(v___x_2069_);
lean_dec_ref(v_type_2066_);
lean_dec(v_binderName_2064_);
lean_dec(v_fvarId_2063_);
lean_del_object(v___x_2061_);
lean_dec_ref(v_k_2059_);
return v___x_2089_;
}
}
}
}
}
else
{
lean_object* v_a_2142_; lean_object* v___x_2144_; uint8_t v_isShared_2145_; uint8_t v_isSharedCheck_2149_; 
lean_del_object(v___x_2069_);
lean_dec_ref(v_value_2067_);
lean_dec_ref(v_type_2066_);
lean_dec(v_binderName_2064_);
lean_dec(v_fvarId_2063_);
lean_del_object(v___x_2061_);
lean_dec_ref(v_k_2059_);
v_a_2142_ = lean_ctor_get(v___x_2073_, 0);
v_isSharedCheck_2149_ = !lean_is_exclusive(v___x_2073_);
if (v_isSharedCheck_2149_ == 0)
{
v___x_2144_ = v___x_2073_;
v_isShared_2145_ = v_isSharedCheck_2149_;
goto v_resetjp_2143_;
}
else
{
lean_inc(v_a_2142_);
lean_dec(v___x_2073_);
v___x_2144_ = lean_box(0);
v_isShared_2145_ = v_isSharedCheck_2149_;
goto v_resetjp_2143_;
}
v_resetjp_2143_:
{
lean_object* v___x_2147_; 
if (v_isShared_2145_ == 0)
{
v___x_2147_ = v___x_2144_;
goto v_reusejp_2146_;
}
else
{
lean_object* v_reuseFailAlloc_2148_; 
v_reuseFailAlloc_2148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2148_, 0, v_a_2142_);
v___x_2147_ = v_reuseFailAlloc_2148_;
goto v_reusejp_2146_;
}
v_reusejp_2146_:
{
return v___x_2147_;
}
}
}
}
}
}
case 3:
{
lean_object* v_fvarId_2152_; lean_object* v_args_2153_; lean_object* v___x_2155_; uint8_t v_isShared_2156_; uint8_t v_isSharedCheck_2190_; 
v_fvarId_2152_ = lean_ctor_get(v_c_2046_, 0);
v_args_2153_ = lean_ctor_get(v_c_2046_, 1);
v_isSharedCheck_2190_ = !lean_is_exclusive(v_c_2046_);
if (v_isSharedCheck_2190_ == 0)
{
v___x_2155_ = v_c_2046_;
v_isShared_2156_ = v_isSharedCheck_2190_;
goto v_resetjp_2154_;
}
else
{
lean_inc(v_args_2153_);
lean_inc(v_fvarId_2152_);
lean_dec(v_c_2046_);
v___x_2155_ = lean_box(0);
v_isShared_2156_ = v_isSharedCheck_2190_;
goto v_resetjp_2154_;
}
v_resetjp_2154_:
{
lean_object* v_a_2158_; lean_object* v___y_2164_; lean_object* v___x_2174_; lean_object* v_jpParamMask_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; uint8_t v___x_2182_; 
v___x_2174_ = lean_st_ref_get(v_a_2047_);
v_jpParamMask_2175_ = lean_ctor_get(v___x_2174_, 1);
lean_inc_ref(v_jpParamMask_2175_);
lean_dec(v___x_2174_);
v___x_2176_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__4, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__4_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__4);
v___x_2177_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5___redArg(v___x_2176_, v_jpParamMask_2175_, v_fvarId_2152_);
lean_dec_ref(v_jpParamMask_2175_);
v___x_2178_ = lean_unsigned_to_nat(0u);
v___x_2179_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__5));
v___x_2180_ = l_Array_zip___redArg(v_args_2153_, v___x_2177_);
lean_dec(v___x_2177_);
lean_dec_ref(v_args_2153_);
v___x_2181_ = lean_array_get_size(v___x_2180_);
v___x_2182_ = lean_nat_dec_lt(v___x_2178_, v___x_2181_);
if (v___x_2182_ == 0)
{
lean_dec_ref(v___x_2180_);
v_a_2158_ = v___x_2179_;
goto v___jp_2157_;
}
else
{
uint8_t v___x_2183_; 
v___x_2183_ = lean_nat_dec_le(v___x_2181_, v___x_2181_);
if (v___x_2183_ == 0)
{
if (v___x_2182_ == 0)
{
lean_dec_ref(v___x_2180_);
v_a_2158_ = v___x_2179_;
goto v___jp_2157_;
}
else
{
size_t v___x_2184_; size_t v___x_2185_; lean_object* v___x_2186_; 
v___x_2184_ = ((size_t)0ULL);
v___x_2185_ = lean_usize_of_nat(v___x_2181_);
v___x_2186_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__6___redArg(v___x_2180_, v___x_2184_, v___x_2185_, v___x_2179_, v_a_2047_);
lean_dec_ref(v___x_2180_);
v___y_2164_ = v___x_2186_;
goto v___jp_2163_;
}
}
else
{
size_t v___x_2187_; size_t v___x_2188_; lean_object* v___x_2189_; 
v___x_2187_ = ((size_t)0ULL);
v___x_2188_ = lean_usize_of_nat(v___x_2181_);
v___x_2189_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__6___redArg(v___x_2180_, v___x_2187_, v___x_2188_, v___x_2179_, v_a_2047_);
lean_dec_ref(v___x_2180_);
v___y_2164_ = v___x_2189_;
goto v___jp_2163_;
}
}
v___jp_2157_:
{
lean_object* v___x_2160_; 
if (v_isShared_2156_ == 0)
{
lean_ctor_set(v___x_2155_, 1, v_a_2158_);
v___x_2160_ = v___x_2155_;
goto v_reusejp_2159_;
}
else
{
lean_object* v_reuseFailAlloc_2162_; 
v_reuseFailAlloc_2162_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2162_, 0, v_fvarId_2152_);
lean_ctor_set(v_reuseFailAlloc_2162_, 1, v_a_2158_);
v___x_2160_ = v_reuseFailAlloc_2162_;
goto v_reusejp_2159_;
}
v_reusejp_2159_:
{
lean_object* v___x_2161_; 
v___x_2161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2161_, 0, v___x_2160_);
return v___x_2161_;
}
}
v___jp_2163_:
{
if (lean_obj_tag(v___y_2164_) == 0)
{
lean_object* v_a_2165_; 
v_a_2165_ = lean_ctor_get(v___y_2164_, 0);
lean_inc(v_a_2165_);
lean_dec_ref(v___y_2164_);
v_a_2158_ = v_a_2165_;
goto v___jp_2157_;
}
else
{
lean_object* v_a_2166_; lean_object* v___x_2168_; uint8_t v_isShared_2169_; uint8_t v_isSharedCheck_2173_; 
lean_del_object(v___x_2155_);
lean_dec(v_fvarId_2152_);
v_a_2166_ = lean_ctor_get(v___y_2164_, 0);
v_isSharedCheck_2173_ = !lean_is_exclusive(v___y_2164_);
if (v_isSharedCheck_2173_ == 0)
{
v___x_2168_ = v___y_2164_;
v_isShared_2169_ = v_isSharedCheck_2173_;
goto v_resetjp_2167_;
}
else
{
lean_inc(v_a_2166_);
lean_dec(v___y_2164_);
v___x_2168_ = lean_box(0);
v_isShared_2169_ = v_isSharedCheck_2173_;
goto v_resetjp_2167_;
}
v_resetjp_2167_:
{
lean_object* v___x_2171_; 
if (v_isShared_2169_ == 0)
{
v___x_2171_ = v___x_2168_;
goto v_reusejp_2170_;
}
else
{
lean_object* v_reuseFailAlloc_2172_; 
v_reuseFailAlloc_2172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2172_, 0, v_a_2166_);
v___x_2171_ = v_reuseFailAlloc_2172_;
goto v_reusejp_2170_;
}
v_reusejp_2170_:
{
return v___x_2171_;
}
}
}
}
}
}
case 4:
{
lean_object* v_cases_2191_; lean_object* v___x_2193_; uint8_t v_isShared_2194_; uint8_t v_isSharedCheck_2302_; 
v_cases_2191_ = lean_ctor_get(v_c_2046_, 0);
v_isSharedCheck_2302_ = !lean_is_exclusive(v_c_2046_);
if (v_isSharedCheck_2302_ == 0)
{
v___x_2193_ = v_c_2046_;
v_isShared_2194_ = v_isSharedCheck_2302_;
goto v_resetjp_2192_;
}
else
{
lean_inc(v_cases_2191_);
lean_dec(v_c_2046_);
v___x_2193_ = lean_box(0);
v_isShared_2194_ = v_isSharedCheck_2302_;
goto v_resetjp_2192_;
}
v_resetjp_2192_:
{
lean_object* v_typeName_2195_; lean_object* v_resultType_2196_; lean_object* v_discr_2197_; lean_object* v_alts_2198_; lean_object* v___x_2200_; uint8_t v_isShared_2201_; uint8_t v_isSharedCheck_2301_; 
v_typeName_2195_ = lean_ctor_get(v_cases_2191_, 0);
v_resultType_2196_ = lean_ctor_get(v_cases_2191_, 1);
v_discr_2197_ = lean_ctor_get(v_cases_2191_, 2);
v_alts_2198_ = lean_ctor_get(v_cases_2191_, 3);
v_isSharedCheck_2301_ = !lean_is_exclusive(v_cases_2191_);
if (v_isSharedCheck_2301_ == 0)
{
v___x_2200_ = v_cases_2191_;
v_isShared_2201_ = v_isSharedCheck_2301_;
goto v_resetjp_2199_;
}
else
{
lean_inc(v_alts_2198_);
lean_inc(v_discr_2197_);
lean_inc(v_resultType_2196_);
lean_inc(v_typeName_2195_);
lean_dec(v_cases_2191_);
v___x_2200_ = lean_box(0);
v_isShared_2201_ = v_isSharedCheck_2301_;
goto v_resetjp_2199_;
}
v_resetjp_2199_:
{
lean_object* v___x_2202_; 
lean_inc(v_typeName_2195_);
v___x_2202_ = l_Lean_Compiler_LCNF_hasTrivialImpureStructure_x3f(v_typeName_2195_, v_a_2050_, v_a_2051_);
if (lean_obj_tag(v___x_2202_) == 0)
{
lean_object* v_a_2203_; 
v_a_2203_ = lean_ctor_get(v___x_2202_, 0);
lean_inc(v_a_2203_);
lean_dec_ref(v___x_2202_);
if (lean_obj_tag(v_a_2203_) == 1)
{
lean_object* v_val_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; uint8_t v___x_2207_; 
lean_del_object(v___x_2200_);
lean_dec_ref(v_resultType_2196_);
lean_dec(v_typeName_2195_);
lean_del_object(v___x_2193_);
v_val_2204_ = lean_ctor_get(v_a_2203_, 0);
lean_inc(v_val_2204_);
lean_dec_ref(v_a_2203_);
v___x_2205_ = lean_array_get_size(v_alts_2198_);
v___x_2206_ = lean_unsigned_to_nat(1u);
v___x_2207_ = lean_nat_dec_eq(v___x_2205_, v___x_2206_);
if (v___x_2207_ == 0)
{
lean_object* v___x_2208_; lean_object* v___x_2209_; 
lean_dec(v_val_2204_);
lean_dec_ref(v_alts_2198_);
lean_dec(v_discr_2197_);
v___x_2208_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__7, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__7_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__7);
v___x_2209_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0(v___x_2208_, v_a_2047_, v_a_2048_, v_a_2049_, v_a_2050_, v_a_2051_);
return v___x_2209_;
}
else
{
lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; 
v___x_2210_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__8, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__8_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__8);
v___x_2211_ = lean_unsigned_to_nat(0u);
v___x_2212_ = lean_array_get(v___x_2210_, v_alts_2198_, v___x_2211_);
lean_dec_ref(v_alts_2198_);
if (lean_obj_tag(v___x_2212_) == 0)
{
lean_object* v_ctorName_2213_; lean_object* v_params_2214_; lean_object* v_code_2215_; lean_object* v_ctorName_2216_; lean_object* v_fieldIdx_2217_; uint8_t v___x_2218_; 
v_ctorName_2213_ = lean_ctor_get(v___x_2212_, 0);
lean_inc(v_ctorName_2213_);
v_params_2214_ = lean_ctor_get(v___x_2212_, 1);
lean_inc_ref(v_params_2214_);
v_code_2215_ = lean_ctor_get(v___x_2212_, 2);
lean_inc_ref(v_code_2215_);
lean_dec_ref(v___x_2212_);
v_ctorName_2216_ = lean_ctor_get(v_val_2204_, 0);
lean_inc(v_ctorName_2216_);
v_fieldIdx_2217_ = lean_ctor_get(v_val_2204_, 2);
lean_inc(v_fieldIdx_2217_);
lean_dec(v_val_2204_);
v___x_2218_ = lean_name_eq(v_ctorName_2213_, v_ctorName_2216_);
lean_dec(v_ctorName_2216_);
lean_dec(v_ctorName_2213_);
if (v___x_2218_ == 0)
{
lean_object* v___x_2219_; lean_object* v___x_2220_; 
lean_dec(v_fieldIdx_2217_);
lean_dec_ref(v_code_2215_);
lean_dec_ref(v_params_2214_);
lean_dec(v_discr_2197_);
v___x_2219_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__10, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__10_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__10);
v___x_2220_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0(v___x_2219_, v_a_2047_, v_a_2048_, v_a_2049_, v_a_2050_, v_a_2051_);
return v___x_2220_;
}
else
{
lean_object* v___x_2221_; uint8_t v___x_2222_; 
v___x_2221_ = lean_array_get_size(v_params_2214_);
v___x_2222_ = lean_nat_dec_lt(v_fieldIdx_2217_, v___x_2221_);
if (v___x_2222_ == 0)
{
lean_object* v___x_2223_; lean_object* v___x_2224_; 
lean_dec(v_fieldIdx_2217_);
lean_dec_ref(v_code_2215_);
lean_dec_ref(v_params_2214_);
lean_dec(v_discr_2197_);
v___x_2223_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__12, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__12_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__12);
v___x_2224_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0(v___x_2223_, v_a_2047_, v_a_2048_, v_a_2049_, v_a_2050_, v_a_2051_);
return v___x_2224_;
}
else
{
lean_object* v___x_2225_; lean_object* v___x_2226_; 
v___x_2225_ = lean_box(0);
v___x_2226_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___redArg(v___x_2221_, v_params_2214_, v_fieldIdx_2217_, v_discr_2197_, v___x_2211_, v___x_2225_, v_a_2047_);
lean_dec(v_fieldIdx_2217_);
lean_dec_ref(v_params_2214_);
if (lean_obj_tag(v___x_2226_) == 0)
{
lean_dec_ref(v___x_2226_);
v_c_2046_ = v_code_2215_;
goto _start;
}
else
{
lean_object* v_a_2228_; lean_object* v___x_2230_; uint8_t v_isShared_2231_; uint8_t v_isSharedCheck_2235_; 
lean_dec_ref(v_code_2215_);
v_a_2228_ = lean_ctor_get(v___x_2226_, 0);
v_isSharedCheck_2235_ = !lean_is_exclusive(v___x_2226_);
if (v_isSharedCheck_2235_ == 0)
{
v___x_2230_ = v___x_2226_;
v_isShared_2231_ = v_isSharedCheck_2235_;
goto v_resetjp_2229_;
}
else
{
lean_inc(v_a_2228_);
lean_dec(v___x_2226_);
v___x_2230_ = lean_box(0);
v_isShared_2231_ = v_isSharedCheck_2235_;
goto v_resetjp_2229_;
}
v_resetjp_2229_:
{
lean_object* v___x_2233_; 
if (v_isShared_2231_ == 0)
{
v___x_2233_ = v___x_2230_;
goto v_reusejp_2232_;
}
else
{
lean_object* v_reuseFailAlloc_2234_; 
v_reuseFailAlloc_2234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2234_, 0, v_a_2228_);
v___x_2233_ = v_reuseFailAlloc_2234_;
goto v_reusejp_2232_;
}
v_reusejp_2232_:
{
return v___x_2233_;
}
}
}
}
}
}
else
{
lean_object* v___x_2236_; lean_object* v___x_2237_; 
lean_dec(v___x_2212_);
lean_dec(v_val_2204_);
lean_dec(v_discr_2197_);
v___x_2236_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__14, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__14_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__14);
v___x_2237_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0(v___x_2236_, v_a_2047_, v_a_2048_, v_a_2049_, v_a_2050_, v_a_2051_);
return v___x_2237_;
}
}
}
else
{
lean_object* v___x_2238_; lean_object* v_subst_2239_; uint8_t v___x_2240_; lean_object* v___x_2241_; 
lean_dec(v_a_2203_);
v___x_2238_ = lean_st_ref_get(v_a_2047_);
v_subst_2239_ = lean_ctor_get(v___x_2238_, 0);
lean_inc_ref(v_subst_2239_);
lean_dec(v___x_2238_);
v___x_2240_ = 1;
v___x_2241_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_subst_2239_, v_discr_2197_, v___x_2240_);
lean_dec_ref(v_subst_2239_);
if (lean_obj_tag(v___x_2241_) == 0)
{
lean_object* v_fvarId_2242_; uint8_t v___x_2243_; lean_object* v___x_2244_; 
v_fvarId_2242_ = lean_ctor_get(v___x_2241_, 0);
lean_inc(v_fvarId_2242_);
lean_dec_ref(v___x_2241_);
v___x_2243_ = 0;
v___x_2244_ = l_Lean_Compiler_LCNF_toImpureType(v_resultType_2196_, v___x_2243_, v_a_2050_, v_a_2051_);
if (lean_obj_tag(v___x_2244_) == 0)
{
lean_object* v_a_2245_; size_t v_sz_2246_; size_t v___x_2247_; lean_object* v___x_2248_; 
v_a_2245_ = lean_ctor_get(v___x_2244_, 0);
lean_inc(v_a_2245_);
lean_dec_ref(v___x_2244_);
v_sz_2246_ = lean_array_size(v_alts_2198_);
v___x_2247_ = ((size_t)0ULL);
lean_inc(v_fvarId_2242_);
v___x_2248_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__8(v_fvarId_2242_, v_sz_2246_, v___x_2247_, v_alts_2198_, v_a_2047_, v_a_2048_, v_a_2049_, v_a_2050_, v_a_2051_);
if (lean_obj_tag(v___x_2248_) == 0)
{
lean_object* v_a_2249_; lean_object* v___x_2250_; 
v_a_2249_ = lean_ctor_get(v___x_2248_, 0);
lean_inc(v_a_2249_);
lean_dec_ref(v___x_2248_);
v___x_2250_ = l_Lean_Compiler_LCNF_nameToImpureType(v_typeName_2195_, v_a_2050_, v_a_2051_);
if (lean_obj_tag(v___x_2250_) == 0)
{
lean_object* v_a_2251_; lean_object* v___x_2253_; uint8_t v_isShared_2254_; uint8_t v_isSharedCheck_2266_; 
v_a_2251_ = lean_ctor_get(v___x_2250_, 0);
v_isSharedCheck_2266_ = !lean_is_exclusive(v___x_2250_);
if (v_isSharedCheck_2266_ == 0)
{
v___x_2253_ = v___x_2250_;
v_isShared_2254_ = v_isSharedCheck_2266_;
goto v_resetjp_2252_;
}
else
{
lean_inc(v_a_2251_);
lean_dec(v___x_2250_);
v___x_2253_ = lean_box(0);
v_isShared_2254_ = v_isSharedCheck_2266_;
goto v_resetjp_2252_;
}
v_resetjp_2252_:
{
lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2258_; 
v___x_2255_ = l_Lean_Expr_getAppFn(v_a_2251_);
lean_dec(v_a_2251_);
v___x_2256_ = l_Lean_Expr_constName_x21(v___x_2255_);
lean_dec_ref(v___x_2255_);
if (v_isShared_2201_ == 0)
{
lean_ctor_set(v___x_2200_, 3, v_a_2249_);
lean_ctor_set(v___x_2200_, 2, v_fvarId_2242_);
lean_ctor_set(v___x_2200_, 1, v_a_2245_);
lean_ctor_set(v___x_2200_, 0, v___x_2256_);
v___x_2258_ = v___x_2200_;
goto v_reusejp_2257_;
}
else
{
lean_object* v_reuseFailAlloc_2265_; 
v_reuseFailAlloc_2265_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2265_, 0, v___x_2256_);
lean_ctor_set(v_reuseFailAlloc_2265_, 1, v_a_2245_);
lean_ctor_set(v_reuseFailAlloc_2265_, 2, v_fvarId_2242_);
lean_ctor_set(v_reuseFailAlloc_2265_, 3, v_a_2249_);
v___x_2258_ = v_reuseFailAlloc_2265_;
goto v_reusejp_2257_;
}
v_reusejp_2257_:
{
lean_object* v___x_2260_; 
if (v_isShared_2194_ == 0)
{
lean_ctor_set(v___x_2193_, 0, v___x_2258_);
v___x_2260_ = v___x_2193_;
goto v_reusejp_2259_;
}
else
{
lean_object* v_reuseFailAlloc_2264_; 
v_reuseFailAlloc_2264_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2264_, 0, v___x_2258_);
v___x_2260_ = v_reuseFailAlloc_2264_;
goto v_reusejp_2259_;
}
v_reusejp_2259_:
{
lean_object* v___x_2262_; 
if (v_isShared_2254_ == 0)
{
lean_ctor_set(v___x_2253_, 0, v___x_2260_);
v___x_2262_ = v___x_2253_;
goto v_reusejp_2261_;
}
else
{
lean_object* v_reuseFailAlloc_2263_; 
v_reuseFailAlloc_2263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2263_, 0, v___x_2260_);
v___x_2262_ = v_reuseFailAlloc_2263_;
goto v_reusejp_2261_;
}
v_reusejp_2261_:
{
return v___x_2262_;
}
}
}
}
}
else
{
lean_object* v_a_2267_; lean_object* v___x_2269_; uint8_t v_isShared_2270_; uint8_t v_isSharedCheck_2274_; 
lean_dec(v_a_2249_);
lean_dec(v_a_2245_);
lean_dec(v_fvarId_2242_);
lean_del_object(v___x_2200_);
lean_del_object(v___x_2193_);
v_a_2267_ = lean_ctor_get(v___x_2250_, 0);
v_isSharedCheck_2274_ = !lean_is_exclusive(v___x_2250_);
if (v_isSharedCheck_2274_ == 0)
{
v___x_2269_ = v___x_2250_;
v_isShared_2270_ = v_isSharedCheck_2274_;
goto v_resetjp_2268_;
}
else
{
lean_inc(v_a_2267_);
lean_dec(v___x_2250_);
v___x_2269_ = lean_box(0);
v_isShared_2270_ = v_isSharedCheck_2274_;
goto v_resetjp_2268_;
}
v_resetjp_2268_:
{
lean_object* v___x_2272_; 
if (v_isShared_2270_ == 0)
{
v___x_2272_ = v___x_2269_;
goto v_reusejp_2271_;
}
else
{
lean_object* v_reuseFailAlloc_2273_; 
v_reuseFailAlloc_2273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2273_, 0, v_a_2267_);
v___x_2272_ = v_reuseFailAlloc_2273_;
goto v_reusejp_2271_;
}
v_reusejp_2271_:
{
return v___x_2272_;
}
}
}
}
else
{
lean_object* v_a_2275_; lean_object* v___x_2277_; uint8_t v_isShared_2278_; uint8_t v_isSharedCheck_2282_; 
lean_dec(v_a_2245_);
lean_dec(v_fvarId_2242_);
lean_del_object(v___x_2200_);
lean_dec(v_typeName_2195_);
lean_del_object(v___x_2193_);
v_a_2275_ = lean_ctor_get(v___x_2248_, 0);
v_isSharedCheck_2282_ = !lean_is_exclusive(v___x_2248_);
if (v_isSharedCheck_2282_ == 0)
{
v___x_2277_ = v___x_2248_;
v_isShared_2278_ = v_isSharedCheck_2282_;
goto v_resetjp_2276_;
}
else
{
lean_inc(v_a_2275_);
lean_dec(v___x_2248_);
v___x_2277_ = lean_box(0);
v_isShared_2278_ = v_isSharedCheck_2282_;
goto v_resetjp_2276_;
}
v_resetjp_2276_:
{
lean_object* v___x_2280_; 
if (v_isShared_2278_ == 0)
{
v___x_2280_ = v___x_2277_;
goto v_reusejp_2279_;
}
else
{
lean_object* v_reuseFailAlloc_2281_; 
v_reuseFailAlloc_2281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2281_, 0, v_a_2275_);
v___x_2280_ = v_reuseFailAlloc_2281_;
goto v_reusejp_2279_;
}
v_reusejp_2279_:
{
return v___x_2280_;
}
}
}
}
else
{
lean_object* v_a_2283_; lean_object* v___x_2285_; uint8_t v_isShared_2286_; uint8_t v_isSharedCheck_2290_; 
lean_dec(v_fvarId_2242_);
lean_del_object(v___x_2200_);
lean_dec_ref(v_alts_2198_);
lean_dec(v_typeName_2195_);
lean_del_object(v___x_2193_);
v_a_2283_ = lean_ctor_get(v___x_2244_, 0);
v_isSharedCheck_2290_ = !lean_is_exclusive(v___x_2244_);
if (v_isSharedCheck_2290_ == 0)
{
v___x_2285_ = v___x_2244_;
v_isShared_2286_ = v_isSharedCheck_2290_;
goto v_resetjp_2284_;
}
else
{
lean_inc(v_a_2283_);
lean_dec(v___x_2244_);
v___x_2285_ = lean_box(0);
v_isShared_2286_ = v_isSharedCheck_2290_;
goto v_resetjp_2284_;
}
v_resetjp_2284_:
{
lean_object* v___x_2288_; 
if (v_isShared_2286_ == 0)
{
v___x_2288_ = v___x_2285_;
goto v_reusejp_2287_;
}
else
{
lean_object* v_reuseFailAlloc_2289_; 
v_reuseFailAlloc_2289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2289_, 0, v_a_2283_);
v___x_2288_ = v_reuseFailAlloc_2289_;
goto v_reusejp_2287_;
}
v_reusejp_2287_:
{
return v___x_2288_;
}
}
}
}
else
{
uint8_t v___x_2291_; lean_object* v___x_2292_; 
lean_del_object(v___x_2200_);
lean_dec_ref(v_alts_2198_);
lean_dec_ref(v_resultType_2196_);
lean_dec(v_typeName_2195_);
lean_del_object(v___x_2193_);
v___x_2291_ = 1;
v___x_2292_ = l_Lean_Compiler_LCNF_mkReturnErased(v___x_2291_, v_a_2048_, v_a_2049_, v_a_2050_, v_a_2051_);
return v___x_2292_;
}
}
}
else
{
lean_object* v_a_2293_; lean_object* v___x_2295_; uint8_t v_isShared_2296_; uint8_t v_isSharedCheck_2300_; 
lean_del_object(v___x_2200_);
lean_dec_ref(v_alts_2198_);
lean_dec(v_discr_2197_);
lean_dec_ref(v_resultType_2196_);
lean_dec(v_typeName_2195_);
lean_del_object(v___x_2193_);
v_a_2293_ = lean_ctor_get(v___x_2202_, 0);
v_isSharedCheck_2300_ = !lean_is_exclusive(v___x_2202_);
if (v_isSharedCheck_2300_ == 0)
{
v___x_2295_ = v___x_2202_;
v_isShared_2296_ = v_isSharedCheck_2300_;
goto v_resetjp_2294_;
}
else
{
lean_inc(v_a_2293_);
lean_dec(v___x_2202_);
v___x_2295_ = lean_box(0);
v_isShared_2296_ = v_isSharedCheck_2300_;
goto v_resetjp_2294_;
}
v_resetjp_2294_:
{
lean_object* v___x_2298_; 
if (v_isShared_2296_ == 0)
{
v___x_2298_ = v___x_2295_;
goto v_reusejp_2297_;
}
else
{
lean_object* v_reuseFailAlloc_2299_; 
v_reuseFailAlloc_2299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2299_, 0, v_a_2293_);
v___x_2298_ = v_reuseFailAlloc_2299_;
goto v_reusejp_2297_;
}
v_reusejp_2297_:
{
return v___x_2298_;
}
}
}
}
}
}
case 5:
{
lean_object* v_fvarId_2303_; lean_object* v___x_2305_; uint8_t v_isShared_2306_; uint8_t v_isSharedCheck_2324_; 
v_fvarId_2303_ = lean_ctor_get(v_c_2046_, 0);
v_isSharedCheck_2324_ = !lean_is_exclusive(v_c_2046_);
if (v_isSharedCheck_2324_ == 0)
{
v___x_2305_ = v_c_2046_;
v_isShared_2306_ = v_isSharedCheck_2324_;
goto v_resetjp_2304_;
}
else
{
lean_inc(v_fvarId_2303_);
lean_dec(v_c_2046_);
v___x_2305_ = lean_box(0);
v_isShared_2306_ = v_isSharedCheck_2324_;
goto v_resetjp_2304_;
}
v_resetjp_2304_:
{
lean_object* v___x_2307_; lean_object* v_subst_2308_; uint8_t v___x_2309_; lean_object* v___x_2310_; 
v___x_2307_ = lean_st_ref_get(v_a_2047_);
v_subst_2308_ = lean_ctor_get(v___x_2307_, 0);
lean_inc_ref(v_subst_2308_);
lean_dec(v___x_2307_);
v___x_2309_ = 1;
v___x_2310_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_subst_2308_, v_fvarId_2303_, v___x_2309_);
lean_dec_ref(v_subst_2308_);
if (lean_obj_tag(v___x_2310_) == 0)
{
lean_object* v_fvarId_2311_; lean_object* v___x_2313_; uint8_t v_isShared_2314_; uint8_t v_isSharedCheck_2321_; 
v_fvarId_2311_ = lean_ctor_get(v___x_2310_, 0);
v_isSharedCheck_2321_ = !lean_is_exclusive(v___x_2310_);
if (v_isSharedCheck_2321_ == 0)
{
v___x_2313_ = v___x_2310_;
v_isShared_2314_ = v_isSharedCheck_2321_;
goto v_resetjp_2312_;
}
else
{
lean_inc(v_fvarId_2311_);
lean_dec(v___x_2310_);
v___x_2313_ = lean_box(0);
v_isShared_2314_ = v_isSharedCheck_2321_;
goto v_resetjp_2312_;
}
v_resetjp_2312_:
{
lean_object* v___x_2316_; 
if (v_isShared_2306_ == 0)
{
lean_ctor_set(v___x_2305_, 0, v_fvarId_2311_);
v___x_2316_ = v___x_2305_;
goto v_reusejp_2315_;
}
else
{
lean_object* v_reuseFailAlloc_2320_; 
v_reuseFailAlloc_2320_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2320_, 0, v_fvarId_2311_);
v___x_2316_ = v_reuseFailAlloc_2320_;
goto v_reusejp_2315_;
}
v_reusejp_2315_:
{
lean_object* v___x_2318_; 
if (v_isShared_2314_ == 0)
{
lean_ctor_set(v___x_2313_, 0, v___x_2316_);
v___x_2318_ = v___x_2313_;
goto v_reusejp_2317_;
}
else
{
lean_object* v_reuseFailAlloc_2319_; 
v_reuseFailAlloc_2319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2319_, 0, v___x_2316_);
v___x_2318_ = v_reuseFailAlloc_2319_;
goto v_reusejp_2317_;
}
v_reusejp_2317_:
{
return v___x_2318_;
}
}
}
}
else
{
uint8_t v___x_2322_; lean_object* v___x_2323_; 
lean_del_object(v___x_2305_);
v___x_2322_ = 1;
v___x_2323_ = l_Lean_Compiler_LCNF_mkReturnErased(v___x_2322_, v_a_2048_, v_a_2049_, v_a_2050_, v_a_2051_);
return v___x_2323_;
}
}
}
default: 
{
lean_object* v_type_2325_; lean_object* v___x_2327_; uint8_t v_isShared_2328_; uint8_t v_isSharedCheck_2350_; 
v_type_2325_ = lean_ctor_get(v_c_2046_, 0);
v_isSharedCheck_2350_ = !lean_is_exclusive(v_c_2046_);
if (v_isSharedCheck_2350_ == 0)
{
v___x_2327_ = v_c_2046_;
v_isShared_2328_ = v_isSharedCheck_2350_;
goto v_resetjp_2326_;
}
else
{
lean_inc(v_type_2325_);
lean_dec(v_c_2046_);
v___x_2327_ = lean_box(0);
v_isShared_2328_ = v_isSharedCheck_2350_;
goto v_resetjp_2326_;
}
v_resetjp_2326_:
{
uint8_t v___x_2329_; lean_object* v___x_2330_; 
v___x_2329_ = 0;
v___x_2330_ = l_Lean_Compiler_LCNF_toImpureType(v_type_2325_, v___x_2329_, v_a_2050_, v_a_2051_);
if (lean_obj_tag(v___x_2330_) == 0)
{
lean_object* v_a_2331_; lean_object* v___x_2333_; uint8_t v_isShared_2334_; uint8_t v_isSharedCheck_2341_; 
v_a_2331_ = lean_ctor_get(v___x_2330_, 0);
v_isSharedCheck_2341_ = !lean_is_exclusive(v___x_2330_);
if (v_isSharedCheck_2341_ == 0)
{
v___x_2333_ = v___x_2330_;
v_isShared_2334_ = v_isSharedCheck_2341_;
goto v_resetjp_2332_;
}
else
{
lean_inc(v_a_2331_);
lean_dec(v___x_2330_);
v___x_2333_ = lean_box(0);
v_isShared_2334_ = v_isSharedCheck_2341_;
goto v_resetjp_2332_;
}
v_resetjp_2332_:
{
lean_object* v___x_2336_; 
if (v_isShared_2328_ == 0)
{
lean_ctor_set(v___x_2327_, 0, v_a_2331_);
v___x_2336_ = v___x_2327_;
goto v_reusejp_2335_;
}
else
{
lean_object* v_reuseFailAlloc_2340_; 
v_reuseFailAlloc_2340_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2340_, 0, v_a_2331_);
v___x_2336_ = v_reuseFailAlloc_2340_;
goto v_reusejp_2335_;
}
v_reusejp_2335_:
{
lean_object* v___x_2338_; 
if (v_isShared_2334_ == 0)
{
lean_ctor_set(v___x_2333_, 0, v___x_2336_);
v___x_2338_ = v___x_2333_;
goto v_reusejp_2337_;
}
else
{
lean_object* v_reuseFailAlloc_2339_; 
v_reuseFailAlloc_2339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2339_, 0, v___x_2336_);
v___x_2338_ = v_reuseFailAlloc_2339_;
goto v_reusejp_2337_;
}
v_reusejp_2337_:
{
return v___x_2338_;
}
}
}
}
else
{
lean_object* v_a_2342_; lean_object* v___x_2344_; uint8_t v_isShared_2345_; uint8_t v_isSharedCheck_2349_; 
lean_del_object(v___x_2327_);
v_a_2342_ = lean_ctor_get(v___x_2330_, 0);
v_isSharedCheck_2349_ = !lean_is_exclusive(v___x_2330_);
if (v_isSharedCheck_2349_ == 0)
{
v___x_2344_ = v___x_2330_;
v_isShared_2345_ = v_isSharedCheck_2349_;
goto v_resetjp_2343_;
}
else
{
lean_inc(v_a_2342_);
lean_dec(v___x_2330_);
v___x_2344_ = lean_box(0);
v_isShared_2345_ = v_isSharedCheck_2349_;
goto v_resetjp_2343_;
}
v_resetjp_2343_:
{
lean_object* v___x_2347_; 
if (v_isShared_2345_ == 0)
{
v___x_2347_ = v___x_2344_;
goto v_reusejp_2346_;
}
else
{
lean_object* v_reuseFailAlloc_2348_; 
v_reuseFailAlloc_2348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2348_, 0, v_a_2342_);
v___x_2347_ = v_reuseFailAlloc_2348_;
goto v_reusejp_2346_;
}
v_reusejp_2346_:
{
return v___x_2347_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields_loop(lean_object* v_decl_2351_, lean_object* v_k_2352_, lean_object* v_ctorInfo_2353_, lean_object* v_fields_2354_, lean_object* v_irArgs_2355_, lean_object* v_i_2356_, lean_object* v_a_2357_, lean_object* v_a_2358_, lean_object* v_a_2359_, lean_object* v_a_2360_, lean_object* v_a_2361_){
_start:
{
lean_object* v___x_2363_; uint8_t v___x_2364_; 
v___x_2363_ = lean_array_get_size(v_irArgs_2355_);
v___x_2364_ = lean_nat_dec_lt(v_i_2356_, v___x_2363_);
if (v___x_2364_ == 0)
{
lean_object* v___x_2365_; 
lean_dec(v_i_2356_);
lean_dec_ref(v_decl_2351_);
v___x_2365_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_k_2352_, v_a_2357_, v_a_2358_, v_a_2359_, v_a_2360_, v_a_2361_);
return v___x_2365_;
}
else
{
lean_object* v___x_2366_; 
v___x_2366_ = lean_array_fget_borrowed(v_irArgs_2355_, v_i_2356_);
if (lean_obj_tag(v___x_2366_) == 0)
{
lean_object* v___x_2367_; lean_object* v___x_2368_; 
v___x_2367_ = lean_unsigned_to_nat(1u);
v___x_2368_ = lean_nat_add(v_i_2356_, v___x_2367_);
lean_dec(v_i_2356_);
v_i_2356_ = v___x_2368_;
goto _start;
}
else
{
lean_object* v_fvarId_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; 
v_fvarId_2370_ = lean_ctor_get(v___x_2366_, 0);
v___x_2371_ = lean_box(0);
v___x_2372_ = lean_array_get_borrowed(v___x_2371_, v_fields_2354_, v_i_2356_);
switch(lean_obj_tag(v___x_2372_))
{
case 1:
{
lean_object* v___x_2373_; lean_object* v___x_2374_; 
v___x_2373_ = lean_unsigned_to_nat(1u);
v___x_2374_ = lean_nat_add(v_i_2356_, v___x_2373_);
lean_dec(v_i_2356_);
v_i_2356_ = v___x_2374_;
goto _start;
}
case 2:
{
lean_object* v_i_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; 
v_i_2376_ = lean_ctor_get(v___x_2372_, 0);
v___x_2377_ = lean_unsigned_to_nat(1u);
v___x_2378_ = lean_nat_add(v_i_2356_, v___x_2377_);
lean_dec(v_i_2356_);
lean_inc_ref(v_decl_2351_);
v___x_2379_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields_loop(v_decl_2351_, v_k_2352_, v_ctorInfo_2353_, v_fields_2354_, v_irArgs_2355_, v___x_2378_, v_a_2357_, v_a_2358_, v_a_2359_, v_a_2360_, v_a_2361_);
if (lean_obj_tag(v___x_2379_) == 0)
{
lean_object* v_a_2380_; lean_object* v___x_2382_; uint8_t v_isShared_2383_; uint8_t v_isSharedCheck_2398_; 
v_a_2380_ = lean_ctor_get(v___x_2379_, 0);
v_isSharedCheck_2398_ = !lean_is_exclusive(v___x_2379_);
if (v_isSharedCheck_2398_ == 0)
{
v___x_2382_ = v___x_2379_;
v_isShared_2383_ = v_isSharedCheck_2398_;
goto v_resetjp_2381_;
}
else
{
lean_inc(v_a_2380_);
lean_dec(v___x_2379_);
v___x_2382_ = lean_box(0);
v_isShared_2383_ = v_isSharedCheck_2398_;
goto v_resetjp_2381_;
}
v_resetjp_2381_:
{
lean_object* v_fvarId_2384_; lean_object* v___x_2386_; uint8_t v_isShared_2387_; uint8_t v_isSharedCheck_2394_; 
v_fvarId_2384_ = lean_ctor_get(v_decl_2351_, 0);
v_isSharedCheck_2394_ = !lean_is_exclusive(v_decl_2351_);
if (v_isSharedCheck_2394_ == 0)
{
lean_object* v_unused_2395_; lean_object* v_unused_2396_; lean_object* v_unused_2397_; 
v_unused_2395_ = lean_ctor_get(v_decl_2351_, 3);
lean_dec(v_unused_2395_);
v_unused_2396_ = lean_ctor_get(v_decl_2351_, 2);
lean_dec(v_unused_2396_);
v_unused_2397_ = lean_ctor_get(v_decl_2351_, 1);
lean_dec(v_unused_2397_);
v___x_2386_ = v_decl_2351_;
v_isShared_2387_ = v_isSharedCheck_2394_;
goto v_resetjp_2385_;
}
else
{
lean_inc(v_fvarId_2384_);
lean_dec(v_decl_2351_);
v___x_2386_ = lean_box(0);
v_isShared_2387_ = v_isSharedCheck_2394_;
goto v_resetjp_2385_;
}
v_resetjp_2385_:
{
lean_object* v___x_2389_; 
lean_inc(v_fvarId_2370_);
lean_inc(v_i_2376_);
if (v_isShared_2387_ == 0)
{
lean_ctor_set_tag(v___x_2386_, 8);
lean_ctor_set(v___x_2386_, 3, v_a_2380_);
lean_ctor_set(v___x_2386_, 2, v_fvarId_2370_);
lean_ctor_set(v___x_2386_, 1, v_i_2376_);
v___x_2389_ = v___x_2386_;
goto v_reusejp_2388_;
}
else
{
lean_object* v_reuseFailAlloc_2393_; 
v_reuseFailAlloc_2393_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2393_, 0, v_fvarId_2384_);
lean_ctor_set(v_reuseFailAlloc_2393_, 1, v_i_2376_);
lean_ctor_set(v_reuseFailAlloc_2393_, 2, v_fvarId_2370_);
lean_ctor_set(v_reuseFailAlloc_2393_, 3, v_a_2380_);
v___x_2389_ = v_reuseFailAlloc_2393_;
goto v_reusejp_2388_;
}
v_reusejp_2388_:
{
lean_object* v___x_2391_; 
if (v_isShared_2383_ == 0)
{
lean_ctor_set(v___x_2382_, 0, v___x_2389_);
v___x_2391_ = v___x_2382_;
goto v_reusejp_2390_;
}
else
{
lean_object* v_reuseFailAlloc_2392_; 
v_reuseFailAlloc_2392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2392_, 0, v___x_2389_);
v___x_2391_ = v_reuseFailAlloc_2392_;
goto v_reusejp_2390_;
}
v_reusejp_2390_:
{
return v___x_2391_;
}
}
}
}
}
else
{
lean_dec_ref(v_decl_2351_);
return v___x_2379_;
}
}
case 3:
{
lean_object* v_offset_2399_; lean_object* v_type_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; 
v_offset_2399_ = lean_ctor_get(v___x_2372_, 1);
v_type_2400_ = lean_ctor_get(v___x_2372_, 2);
v___x_2401_ = lean_unsigned_to_nat(1u);
v___x_2402_ = lean_nat_add(v_i_2356_, v___x_2401_);
lean_dec(v_i_2356_);
lean_inc_ref(v_decl_2351_);
v___x_2403_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields_loop(v_decl_2351_, v_k_2352_, v_ctorInfo_2353_, v_fields_2354_, v_irArgs_2355_, v___x_2402_, v_a_2357_, v_a_2358_, v_a_2359_, v_a_2360_, v_a_2361_);
if (lean_obj_tag(v___x_2403_) == 0)
{
lean_object* v_a_2404_; lean_object* v___x_2406_; uint8_t v_isShared_2407_; uint8_t v_isSharedCheck_2416_; 
v_a_2404_ = lean_ctor_get(v___x_2403_, 0);
v_isSharedCheck_2416_ = !lean_is_exclusive(v___x_2403_);
if (v_isSharedCheck_2416_ == 0)
{
v___x_2406_ = v___x_2403_;
v_isShared_2407_ = v_isSharedCheck_2416_;
goto v_resetjp_2405_;
}
else
{
lean_inc(v_a_2404_);
lean_dec(v___x_2403_);
v___x_2406_ = lean_box(0);
v_isShared_2407_ = v_isSharedCheck_2416_;
goto v_resetjp_2405_;
}
v_resetjp_2405_:
{
lean_object* v_fvarId_2408_; lean_object* v_size_2409_; lean_object* v_usize_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2414_; 
v_fvarId_2408_ = lean_ctor_get(v_decl_2351_, 0);
lean_inc(v_fvarId_2408_);
lean_dec_ref(v_decl_2351_);
v_size_2409_ = lean_ctor_get(v_ctorInfo_2353_, 2);
v_usize_2410_ = lean_ctor_get(v_ctorInfo_2353_, 3);
v___x_2411_ = lean_nat_add(v_size_2409_, v_usize_2410_);
lean_inc_ref(v_type_2400_);
lean_inc(v_fvarId_2370_);
lean_inc(v_offset_2399_);
v___x_2412_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v___x_2412_, 0, v_fvarId_2408_);
lean_ctor_set(v___x_2412_, 1, v___x_2411_);
lean_ctor_set(v___x_2412_, 2, v_offset_2399_);
lean_ctor_set(v___x_2412_, 3, v_fvarId_2370_);
lean_ctor_set(v___x_2412_, 4, v_type_2400_);
lean_ctor_set(v___x_2412_, 5, v_a_2404_);
if (v_isShared_2407_ == 0)
{
lean_ctor_set(v___x_2406_, 0, v___x_2412_);
v___x_2414_ = v___x_2406_;
goto v_reusejp_2413_;
}
else
{
lean_object* v_reuseFailAlloc_2415_; 
v_reuseFailAlloc_2415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2415_, 0, v___x_2412_);
v___x_2414_ = v_reuseFailAlloc_2415_;
goto v_reusejp_2413_;
}
v_reusejp_2413_:
{
return v___x_2414_;
}
}
}
else
{
lean_dec_ref(v_decl_2351_);
return v___x_2403_;
}
}
default: 
{
lean_object* v___x_2417_; lean_object* v___x_2418_; 
v___x_2417_ = lean_unsigned_to_nat(1u);
v___x_2418_ = lean_nat_add(v_i_2356_, v___x_2417_);
lean_dec(v_i_2356_);
v_i_2356_ = v___x_2418_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields(lean_object* v_decl_2420_, lean_object* v_k_2421_, lean_object* v_ctorInfo_2422_, lean_object* v_fields_2423_, lean_object* v_irArgs_2424_, lean_object* v_a_2425_, lean_object* v_a_2426_, lean_object* v_a_2427_, lean_object* v_a_2428_, lean_object* v_a_2429_){
_start:
{
lean_object* v___x_2431_; lean_object* v___x_2432_; 
v___x_2431_ = lean_unsigned_to_nat(0u);
v___x_2432_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields_loop(v_decl_2420_, v_k_2421_, v_ctorInfo_2422_, v_fields_2423_, v_irArgs_2424_, v___x_2431_, v_a_2425_, v_a_2426_, v_a_2427_, v_a_2428_, v_a_2429_);
return v___x_2432_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields___boxed(lean_object* v_decl_2433_, lean_object* v_k_2434_, lean_object* v_ctorInfo_2435_, lean_object* v_fields_2436_, lean_object* v_irArgs_2437_, lean_object* v_a_2438_, lean_object* v_a_2439_, lean_object* v_a_2440_, lean_object* v_a_2441_, lean_object* v_a_2442_, lean_object* v_a_2443_){
_start:
{
lean_object* v_res_2444_; 
v_res_2444_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields(v_decl_2433_, v_k_2434_, v_ctorInfo_2435_, v_fields_2436_, v_irArgs_2437_, v_a_2438_, v_a_2439_, v_a_2440_, v_a_2441_, v_a_2442_);
lean_dec(v_a_2442_);
lean_dec_ref(v_a_2441_);
lean_dec(v_a_2440_);
lean_dec_ref(v_a_2439_);
lean_dec(v_a_2438_);
lean_dec_ref(v_irArgs_2437_);
lean_dec_ref(v_fields_2436_);
lean_dec_ref(v_ctorInfo_2435_);
return v_res_2444_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkPap___boxed(lean_object* v_decl_2445_, lean_object* v_k_2446_, lean_object* v_name_2447_, lean_object* v_args_2448_, lean_object* v_a_2449_, lean_object* v_a_2450_, lean_object* v_a_2451_, lean_object* v_a_2452_, lean_object* v_a_2453_, lean_object* v_a_2454_){
_start:
{
lean_object* v_res_2455_; 
v_res_2455_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkPap(v_decl_2445_, v_k_2446_, v_name_2447_, v_args_2448_, v_a_2449_, v_a_2450_, v_a_2451_, v_a_2452_, v_a_2453_);
lean_dec(v_a_2453_);
lean_dec_ref(v_a_2452_);
lean_dec(v_a_2451_);
lean_dec_ref(v_a_2450_);
lean_dec(v_a_2449_);
return v_res_2455_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkFap___boxed(lean_object* v_decl_2456_, lean_object* v_k_2457_, lean_object* v_name_2458_, lean_object* v_args_2459_, lean_object* v_a_2460_, lean_object* v_a_2461_, lean_object* v_a_2462_, lean_object* v_a_2463_, lean_object* v_a_2464_, lean_object* v_a_2465_){
_start:
{
lean_object* v_res_2466_; 
v_res_2466_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkFap(v_decl_2456_, v_k_2457_, v_name_2458_, v_args_2459_, v_a_2460_, v_a_2461_, v_a_2462_, v_a_2463_, v_a_2464_);
lean_dec(v_a_2464_);
lean_dec_ref(v_a_2463_);
lean_dec(v_a_2462_);
lean_dec_ref(v_a_2461_);
lean_dec(v_a_2460_);
return v_res_2466_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueErased___boxed(lean_object* v_k_2467_, lean_object* v_fvarId_2468_, lean_object* v_a_2469_, lean_object* v_a_2470_, lean_object* v_a_2471_, lean_object* v_a_2472_, lean_object* v_a_2473_, lean_object* v_a_2474_){
_start:
{
lean_object* v_res_2475_; 
v_res_2475_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueErased(v_k_2467_, v_fvarId_2468_, v_a_2469_, v_a_2470_, v_a_2471_, v_a_2472_, v_a_2473_);
lean_dec(v_a_2473_);
lean_dec_ref(v_a_2472_);
lean_dec(v_a_2471_);
lean_dec_ref(v_a_2470_);
lean_dec(v_a_2469_);
return v_res_2475_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkApplication___boxed(lean_object* v_decl_2476_, lean_object* v_k_2477_, lean_object* v_name_2478_, lean_object* v_numParams_2479_, lean_object* v_args_2480_, lean_object* v_a_2481_, lean_object* v_a_2482_, lean_object* v_a_2483_, lean_object* v_a_2484_, lean_object* v_a_2485_, lean_object* v_a_2486_){
_start:
{
lean_object* v_res_2487_; 
v_res_2487_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkApplication(v_decl_2476_, v_k_2477_, v_name_2478_, v_numParams_2479_, v_args_2480_, v_a_2481_, v_a_2482_, v_a_2483_, v_a_2484_, v_a_2485_);
lean_dec(v_a_2485_);
lean_dec_ref(v_a_2484_);
lean_dec(v_a_2483_);
lean_dec_ref(v_a_2482_);
lean_dec(v_a_2481_);
return v_res_2487_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__8___boxed(lean_object* v_fvarId_2488_, lean_object* v_sz_2489_, lean_object* v_i_2490_, lean_object* v_bs_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_){
_start:
{
size_t v_sz_boxed_2498_; size_t v_i_boxed_2499_; lean_object* v_res_2500_; 
v_sz_boxed_2498_ = lean_unbox_usize(v_sz_2489_);
lean_dec(v_sz_2489_);
v_i_boxed_2499_ = lean_unbox_usize(v_i_2490_);
lean_dec(v_i_2490_);
v_res_2500_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__8(v_fvarId_2488_, v_sz_boxed_2498_, v_i_boxed_2499_, v_bs_2491_, v___y_2492_, v___y_2493_, v___y_2494_, v___y_2495_, v___y_2496_);
lean_dec(v___y_2496_);
lean_dec_ref(v___y_2495_);
lean_dec(v___y_2494_);
lean_dec_ref(v___y_2493_);
lean_dec(v___y_2492_);
return v_res_2500_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueLet___boxed(lean_object* v_k_2501_, lean_object* v_decl_2502_, lean_object* v_a_2503_, lean_object* v_a_2504_, lean_object* v_a_2505_, lean_object* v_a_2506_, lean_object* v_a_2507_, lean_object* v_a_2508_){
_start:
{
lean_object* v_res_2509_; 
v_res_2509_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueLet(v_k_2501_, v_decl_2502_, v_a_2503_, v_a_2504_, v_a_2505_, v_a_2506_, v_a_2507_);
lean_dec(v_a_2507_);
lean_dec_ref(v_a_2506_);
lean_dec(v_a_2505_);
lean_dec_ref(v_a_2504_);
lean_dec(v_a_2503_);
return v_res_2509_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure___boxed(lean_object* v_discr_2510_, lean_object* v_alt_2511_, lean_object* v_a_2512_, lean_object* v_a_2513_, lean_object* v_a_2514_, lean_object* v_a_2515_, lean_object* v_a_2516_, lean_object* v_a_2517_){
_start:
{
lean_object* v_res_2518_; 
v_res_2518_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure(v_discr_2510_, v_alt_2511_, v_a_2512_, v_a_2513_, v_a_2514_, v_a_2515_, v_a_2516_);
lean_dec(v_a_2516_);
lean_dec_ref(v_a_2515_);
lean_dec(v_a_2514_);
lean_dec_ref(v_a_2513_);
lean_dec(v_a_2512_);
return v_res_2518_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkOverApplication___boxed(lean_object* v_decl_2519_, lean_object* v_k_2520_, lean_object* v_name_2521_, lean_object* v_numParams_2522_, lean_object* v_args_2523_, lean_object* v_a_2524_, lean_object* v_a_2525_, lean_object* v_a_2526_, lean_object* v_a_2527_, lean_object* v_a_2528_, lean_object* v_a_2529_){
_start:
{
lean_object* v_res_2530_; 
v_res_2530_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkOverApplication(v_decl_2519_, v_k_2520_, v_name_2521_, v_numParams_2522_, v_args_2523_, v_a_2524_, v_a_2525_, v_a_2526_, v_a_2527_, v_a_2528_);
lean_dec(v_a_2528_);
lean_dec_ref(v_a_2527_);
lean_dec(v_a_2526_);
lean_dec_ref(v_a_2525_);
lean_dec(v_a_2524_);
lean_dec_ref(v_args_2523_);
return v_res_2530_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields_loop___boxed(lean_object* v_decl_2531_, lean_object* v_k_2532_, lean_object* v_ctorInfo_2533_, lean_object* v_fields_2534_, lean_object* v_irArgs_2535_, lean_object* v_i_2536_, lean_object* v_a_2537_, lean_object* v_a_2538_, lean_object* v_a_2539_, lean_object* v_a_2540_, lean_object* v_a_2541_, lean_object* v_a_2542_){
_start:
{
lean_object* v_res_2543_; 
v_res_2543_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields_loop(v_decl_2531_, v_k_2532_, v_ctorInfo_2533_, v_fields_2534_, v_irArgs_2535_, v_i_2536_, v_a_2537_, v_a_2538_, v_a_2539_, v_a_2540_, v_a_2541_);
lean_dec(v_a_2541_);
lean_dec_ref(v_a_2540_);
lean_dec(v_a_2539_);
lean_dec_ref(v_a_2538_);
lean_dec(v_a_2537_);
lean_dec_ref(v_irArgs_2535_);
lean_dec_ref(v_fields_2534_);
lean_dec_ref(v_ctorInfo_2533_);
return v_res_2543_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop___boxed(lean_object* v_discr_2544_, lean_object* v_k_2545_, lean_object* v_ctorInfo_2546_, lean_object* v_params_2547_, lean_object* v_fields_2548_, lean_object* v_i_2549_, lean_object* v_a_2550_, lean_object* v_a_2551_, lean_object* v_a_2552_, lean_object* v_a_2553_, lean_object* v_a_2554_, lean_object* v_a_2555_){
_start:
{
lean_object* v_res_2556_; 
v_res_2556_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop(v_discr_2544_, v_k_2545_, v_ctorInfo_2546_, v_params_2547_, v_fields_2548_, v_i_2549_, v_a_2550_, v_a_2551_, v_a_2552_, v_a_2553_, v_a_2554_);
lean_dec(v_a_2554_);
lean_dec_ref(v_a_2553_);
lean_dec(v_a_2552_);
lean_dec_ref(v_a_2551_);
lean_dec(v_a_2550_);
lean_dec_ref(v_fields_2548_);
lean_dec_ref(v_params_2547_);
lean_dec_ref(v_ctorInfo_2546_);
return v_res_2556_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___boxed(lean_object* v_c_2557_, lean_object* v_a_2558_, lean_object* v_a_2559_, lean_object* v_a_2560_, lean_object* v_a_2561_, lean_object* v_a_2562_, lean_object* v_a_2563_){
_start:
{
lean_object* v_res_2564_; 
v_res_2564_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_c_2557_, v_a_2558_, v_a_2559_, v_a_2560_, v_a_2561_, v_a_2562_);
lean_dec(v_a_2562_);
lean_dec_ref(v_a_2561_);
lean_dec(v_a_2560_);
lean_dec_ref(v_a_2559_);
lean_dec(v_a_2558_);
return v_res_2564_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___boxed(lean_object* v_decl_2565_, lean_object* v_k_2566_, lean_object* v_a_2567_, lean_object* v_a_2568_, lean_object* v_a_2569_, lean_object* v_a_2570_, lean_object* v_a_2571_, lean_object* v_a_2572_){
_start:
{
lean_object* v_res_2573_; 
v_res_2573_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet(v_decl_2565_, v_k_2566_, v_a_2567_, v_a_2568_, v_a_2569_, v_a_2570_, v_a_2571_);
lean_dec(v_a_2571_);
lean_dec_ref(v_a_2570_);
lean_dec(v_a_2569_);
lean_dec_ref(v_a_2568_);
lean_dec(v_a_2567_);
return v_res_2573_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12(lean_object* v_00_u03b1_2574_, lean_object* v_msg_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_){
_start:
{
lean_object* v___x_2582_; 
v___x_2582_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg(v_msg_2575_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_);
return v___x_2582_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___boxed(lean_object* v_00_u03b1_2583_, lean_object* v_msg_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_){
_start:
{
lean_object* v_res_2591_; 
v_res_2591_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12(v_00_u03b1_2583_, v_msg_2584_, v___y_2585_, v___y_2586_, v___y_2587_, v___y_2588_, v___y_2589_);
lean_dec(v___y_2589_);
lean_dec_ref(v___y_2588_);
lean_dec(v___y_2587_);
lean_dec_ref(v___y_2586_);
lean_dec(v___y_2585_);
return v_res_2591_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__2(size_t v_sz_2592_, size_t v_i_2593_, lean_object* v_bs_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_){
_start:
{
lean_object* v___x_2601_; 
v___x_2601_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__2___redArg(v_sz_2592_, v_i_2593_, v_bs_2594_, v___y_2595_, v___y_2597_, v___y_2598_, v___y_2599_);
return v___x_2601_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__2___boxed(lean_object* v_sz_2602_, lean_object* v_i_2603_, lean_object* v_bs_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_){
_start:
{
size_t v_sz_boxed_2611_; size_t v_i_boxed_2612_; lean_object* v_res_2613_; 
v_sz_boxed_2611_ = lean_unbox_usize(v_sz_2602_);
lean_dec(v_sz_2602_);
v_i_boxed_2612_ = lean_unbox_usize(v_i_2603_);
lean_dec(v_i_2603_);
v_res_2613_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__2(v_sz_boxed_2611_, v_i_boxed_2612_, v_bs_2604_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_, v___y_2609_);
lean_dec(v___y_2609_);
lean_dec_ref(v___y_2608_);
lean_dec(v___y_2607_);
lean_dec_ref(v___y_2606_);
lean_dec(v___y_2605_);
return v_res_2613_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5(lean_object* v_00_u03b2_2614_, lean_object* v_inst_2615_, lean_object* v_m_2616_, lean_object* v_a_2617_){
_start:
{
lean_object* v___x_2618_; 
v___x_2618_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5___redArg(v_inst_2615_, v_m_2616_, v_a_2617_);
return v___x_2618_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5___boxed(lean_object* v_00_u03b2_2619_, lean_object* v_inst_2620_, lean_object* v_m_2621_, lean_object* v_a_2622_){
_start:
{
lean_object* v_res_2623_; 
v_res_2623_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5(v_00_u03b2_2619_, v_inst_2620_, v_m_2621_, v_a_2622_);
lean_dec(v_a_2622_);
lean_dec_ref(v_m_2621_);
return v_res_2623_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__6(lean_object* v_as_2624_, size_t v_i_2625_, size_t v_stop_2626_, lean_object* v_b_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_){
_start:
{
lean_object* v___x_2634_; 
v___x_2634_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__6___redArg(v_as_2624_, v_i_2625_, v_stop_2626_, v_b_2627_, v___y_2628_);
return v___x_2634_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__6___boxed(lean_object* v_as_2635_, lean_object* v_i_2636_, lean_object* v_stop_2637_, lean_object* v_b_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_){
_start:
{
size_t v_i_boxed_2645_; size_t v_stop_boxed_2646_; lean_object* v_res_2647_; 
v_i_boxed_2645_ = lean_unbox_usize(v_i_2636_);
lean_dec(v_i_2636_);
v_stop_boxed_2646_ = lean_unbox_usize(v_stop_2637_);
lean_dec(v_stop_2637_);
v_res_2647_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__6(v_as_2635_, v_i_boxed_2645_, v_stop_boxed_2646_, v_b_2638_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_);
lean_dec(v___y_2643_);
lean_dec_ref(v___y_2642_);
lean_dec(v___y_2641_);
lean_dec_ref(v___y_2640_);
lean_dec(v___y_2639_);
lean_dec_ref(v_as_2635_);
return v_res_2647_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7(lean_object* v_upperBound_2648_, lean_object* v_params_2649_, lean_object* v___x_2650_, lean_object* v_discr_2651_, lean_object* v_inst_2652_, lean_object* v_R_2653_, lean_object* v_a_2654_, lean_object* v_b_2655_, lean_object* v_c_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_){
_start:
{
lean_object* v___x_2663_; 
v___x_2663_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___redArg(v_upperBound_2648_, v_params_2649_, v___x_2650_, v_discr_2651_, v_a_2654_, v_b_2655_, v___y_2657_);
return v___x_2663_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___boxed(lean_object* v_upperBound_2664_, lean_object* v_params_2665_, lean_object* v___x_2666_, lean_object* v_discr_2667_, lean_object* v_inst_2668_, lean_object* v_R_2669_, lean_object* v_a_2670_, lean_object* v_b_2671_, lean_object* v_c_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_){
_start:
{
lean_object* v_res_2679_; 
v_res_2679_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7(v_upperBound_2664_, v_params_2665_, v___x_2666_, v_discr_2667_, v_inst_2668_, v_R_2669_, v_a_2670_, v_b_2671_, v_c_2672_, v___y_2673_, v___y_2674_, v___y_2675_, v___y_2676_, v___y_2677_);
lean_dec(v___y_2677_);
lean_dec_ref(v___y_2676_);
lean_dec(v___y_2675_);
lean_dec_ref(v___y_2674_);
lean_dec(v___y_2673_);
lean_dec(v___x_2666_);
lean_dec_ref(v_params_2665_);
lean_dec(v_upperBound_2664_);
return v_res_2679_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__11(size_t v_sz_2680_, size_t v_i_2681_, lean_object* v_bs_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_){
_start:
{
lean_object* v___x_2689_; 
v___x_2689_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__11___redArg(v_sz_2680_, v_i_2681_, v_bs_2682_, v___y_2683_);
return v___x_2689_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__11___boxed(lean_object* v_sz_2690_, lean_object* v_i_2691_, lean_object* v_bs_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_){
_start:
{
size_t v_sz_boxed_2699_; size_t v_i_boxed_2700_; lean_object* v_res_2701_; 
v_sz_boxed_2699_ = lean_unbox_usize(v_sz_2690_);
lean_dec(v_sz_2690_);
v_i_boxed_2700_ = lean_unbox_usize(v_i_2691_);
lean_dec(v_i_2691_);
v_res_2701_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__11(v_sz_boxed_2699_, v_i_boxed_2700_, v_bs_2692_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_);
lean_dec(v___y_2697_);
lean_dec_ref(v___y_2696_);
lean_dec(v___y_2695_);
lean_dec_ref(v___y_2694_);
lean_dec(v___y_2693_);
return v_res_2701_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13(lean_object* v_upperBound_2702_, lean_object* v_fieldInfo_2703_, lean_object* v___x_2704_, lean_object* v_inst_2705_, lean_object* v_R_2706_, lean_object* v_a_2707_, lean_object* v_b_2708_, lean_object* v_c_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_){
_start:
{
lean_object* v___x_2716_; 
v___x_2716_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___redArg(v_upperBound_2702_, v_fieldInfo_2703_, v___x_2704_, v_a_2707_, v_b_2708_);
return v___x_2716_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___boxed(lean_object* v_upperBound_2717_, lean_object* v_fieldInfo_2718_, lean_object* v___x_2719_, lean_object* v_inst_2720_, lean_object* v_R_2721_, lean_object* v_a_2722_, lean_object* v_b_2723_, lean_object* v_c_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_){
_start:
{
lean_object* v_res_2731_; 
v_res_2731_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13(v_upperBound_2717_, v_fieldInfo_2718_, v___x_2719_, v_inst_2720_, v_R_2721_, v_a_2722_, v_b_2723_, v_c_2724_, v___y_2725_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2729_);
lean_dec(v___y_2729_);
lean_dec_ref(v___y_2728_);
lean_dec(v___y_2727_);
lean_dec_ref(v___y_2726_);
lean_dec(v___y_2725_);
lean_dec_ref(v___x_2719_);
lean_dec_ref(v_fieldInfo_2718_);
lean_dec(v_upperBound_2717_);
return v_res_2731_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13_spec__17___redArg(lean_object* v_inst_2732_, lean_object* v_msg_2733_){
_start:
{
lean_object* v___x_2734_; 
v___x_2734_ = lean_panic_fn(v_inst_2732_, v_msg_2733_);
return v___x_2734_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13_spec__17(lean_object* v_00_u03b2_2735_, lean_object* v_inst_2736_, lean_object* v_msg_2737_){
_start:
{
lean_object* v___x_2738_; 
v___x_2738_ = lean_panic_fn(v_inst_2736_, v_msg_2737_);
return v___x_2738_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13(lean_object* v_00_u03b2_2739_, lean_object* v_inst_2740_, lean_object* v_a_2741_, lean_object* v_x_2742_){
_start:
{
lean_object* v___x_2743_; 
v___x_2743_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___redArg(v_inst_2740_, v_a_2741_, v_x_2742_);
return v___x_2743_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___boxed(lean_object* v_00_u03b2_2744_, lean_object* v_inst_2745_, lean_object* v_a_2746_, lean_object* v_x_2747_){
_start:
{
lean_object* v_res_2748_; 
v_res_2748_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13(v_00_u03b2_2744_, v_inst_2745_, v_a_2746_, v_x_2747_);
lean_dec(v_x_2747_);
lean_dec(v_a_2746_);
return v_res_2748_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__1(void){
_start:
{
lean_object* v___x_2750_; lean_object* v___x_2751_; 
v___x_2750_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__0));
v___x_2751_ = l_Lean_stringToMessageData(v___x_2750_);
return v___x_2751_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__3(void){
_start:
{
lean_object* v___x_2753_; lean_object* v___x_2754_; 
v___x_2753_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__2));
v___x_2754_ = l_Lean_stringToMessageData(v___x_2753_);
return v___x_2754_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__5(void){
_start:
{
lean_object* v___x_2756_; lean_object* v___x_2757_; 
v___x_2756_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__4));
v___x_2757_ = l_Lean_stringToMessageData(v___x_2756_);
return v___x_2757_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__7(void){
_start:
{
lean_object* v___x_2759_; lean_object* v___x_2760_; 
v___x_2759_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__6));
v___x_2760_ = l_Lean_stringToMessageData(v___x_2759_);
return v___x_2760_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl(lean_object* v_decl_2761_, lean_object* v_a_2762_, lean_object* v_a_2763_, lean_object* v_a_2764_, lean_object* v_a_2765_, lean_object* v_a_2766_){
_start:
{
lean_object* v_toSignature_2768_; lean_object* v_value_2769_; uint8_t v_recursive_2770_; lean_object* v_inlineAttr_x3f_2771_; lean_object* v___x_2773_; uint8_t v_isShared_2774_; uint8_t v_isSharedCheck_2903_; 
v_toSignature_2768_ = lean_ctor_get(v_decl_2761_, 0);
v_value_2769_ = lean_ctor_get(v_decl_2761_, 1);
v_recursive_2770_ = lean_ctor_get_uint8(v_decl_2761_, sizeof(void*)*3);
v_inlineAttr_x3f_2771_ = lean_ctor_get(v_decl_2761_, 2);
v_isSharedCheck_2903_ = !lean_is_exclusive(v_decl_2761_);
if (v_isSharedCheck_2903_ == 0)
{
v___x_2773_ = v_decl_2761_;
v_isShared_2774_ = v_isSharedCheck_2903_;
goto v_resetjp_2772_;
}
else
{
lean_inc(v_inlineAttr_x3f_2771_);
lean_inc(v_value_2769_);
lean_inc(v_toSignature_2768_);
lean_dec(v_decl_2761_);
v___x_2773_ = lean_box(0);
v_isShared_2774_ = v_isSharedCheck_2903_;
goto v_resetjp_2772_;
}
v_resetjp_2772_:
{
lean_object* v_name_2775_; lean_object* v_levelParams_2776_; lean_object* v_type_2777_; lean_object* v_params_2778_; uint8_t v_safe_2779_; lean_object* v___x_2781_; uint8_t v_isShared_2782_; uint8_t v_isSharedCheck_2902_; 
v_name_2775_ = lean_ctor_get(v_toSignature_2768_, 0);
v_levelParams_2776_ = lean_ctor_get(v_toSignature_2768_, 1);
v_type_2777_ = lean_ctor_get(v_toSignature_2768_, 2);
v_params_2778_ = lean_ctor_get(v_toSignature_2768_, 3);
v_safe_2779_ = lean_ctor_get_uint8(v_toSignature_2768_, sizeof(void*)*4);
v_isSharedCheck_2902_ = !lean_is_exclusive(v_toSignature_2768_);
if (v_isSharedCheck_2902_ == 0)
{
v___x_2781_ = v_toSignature_2768_;
v_isShared_2782_ = v_isSharedCheck_2902_;
goto v_resetjp_2780_;
}
else
{
lean_inc(v_params_2778_);
lean_inc(v_type_2777_);
lean_inc(v_levelParams_2776_);
lean_inc(v_name_2775_);
lean_dec(v_toSignature_2768_);
v___x_2781_ = lean_box(0);
v_isShared_2782_ = v_isSharedCheck_2902_;
goto v_resetjp_2780_;
}
v_resetjp_2780_:
{
size_t v_sz_2783_; size_t v___x_2784_; lean_object* v___x_2785_; 
v_sz_2783_ = lean_array_size(v_params_2778_);
v___x_2784_ = ((size_t)0ULL);
lean_inc_ref(v_params_2778_);
v___x_2785_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__2___redArg(v_sz_2783_, v___x_2784_, v_params_2778_, v_a_2762_, v_a_2764_, v_a_2765_, v_a_2766_);
if (lean_obj_tag(v___x_2785_) == 0)
{
lean_object* v_a_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; 
v_a_2786_ = lean_ctor_get(v___x_2785_, 0);
lean_inc(v_a_2786_);
lean_dec_ref(v___x_2785_);
v___x_2787_ = lean_array_get_size(v_params_2778_);
lean_dec_ref(v_params_2778_);
v___x_2788_ = l_Lean_Compiler_LCNF_lowerResultType(v_type_2777_, v___x_2787_, v_a_2765_, v_a_2766_);
lean_dec_ref(v_type_2777_);
if (lean_obj_tag(v___x_2788_) == 0)
{
lean_object* v_a_2789_; lean_object* v___x_2791_; uint8_t v_isShared_2792_; uint8_t v_isSharedCheck_2885_; 
v_a_2789_ = lean_ctor_get(v___x_2788_, 0);
v_isSharedCheck_2885_ = !lean_is_exclusive(v___x_2788_);
if (v_isSharedCheck_2885_ == 0)
{
v___x_2791_ = v___x_2788_;
v_isShared_2792_ = v_isSharedCheck_2885_;
goto v_resetjp_2790_;
}
else
{
lean_inc(v_a_2789_);
lean_dec(v___x_2788_);
v___x_2791_ = lean_box(0);
v_isShared_2792_ = v_isSharedCheck_2885_;
goto v_resetjp_2790_;
}
v_resetjp_2790_:
{
lean_object* v___x_2793_; lean_object* v_env_2794_; lean_object* v___x_2795_; uint8_t v___x_2796_; 
v___x_2793_ = lean_st_ref_get(v_a_2766_);
v_env_2794_ = lean_ctor_get(v___x_2793_, 0);
lean_inc_ref(v_env_2794_);
lean_dec(v___x_2793_);
v___x_2795_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr;
lean_inc(v_name_2775_);
v___x_2796_ = l_Lean_TagAttribute_hasTag(v___x_2795_, v_env_2794_, v_name_2775_);
if (lean_obj_tag(v_value_2769_) == 0)
{
lean_object* v_code_2797_; lean_object* v___x_2799_; uint8_t v_isShared_2800_; uint8_t v_isSharedCheck_2847_; 
lean_del_object(v___x_2791_);
v_code_2797_ = lean_ctor_get(v_value_2769_, 0);
v_isSharedCheck_2847_ = !lean_is_exclusive(v_value_2769_);
if (v_isSharedCheck_2847_ == 0)
{
v___x_2799_ = v_value_2769_;
v_isShared_2800_ = v_isSharedCheck_2847_;
goto v_resetjp_2798_;
}
else
{
lean_inc(v_code_2797_);
lean_dec(v_value_2769_);
v___x_2799_ = lean_box(0);
v_isShared_2800_ = v_isSharedCheck_2847_;
goto v_resetjp_2798_;
}
v_resetjp_2798_:
{
lean_object* v___y_2802_; lean_object* v___y_2803_; lean_object* v___y_2804_; lean_object* v___y_2805_; lean_object* v___y_2806_; 
if (v___x_2796_ == 0)
{
v___y_2802_ = v_a_2762_;
v___y_2803_ = v_a_2763_;
v___y_2804_ = v_a_2764_;
v___y_2805_ = v_a_2765_;
v___y_2806_ = v_a_2766_;
goto v___jp_2801_;
}
else
{
lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v_a_2839_; lean_object* v___x_2841_; uint8_t v_isShared_2842_; uint8_t v_isSharedCheck_2846_; 
lean_del_object(v___x_2799_);
lean_dec_ref(v_code_2797_);
lean_dec(v_a_2789_);
lean_dec(v_a_2786_);
lean_del_object(v___x_2781_);
lean_dec(v_levelParams_2776_);
lean_del_object(v___x_2773_);
lean_dec(v_inlineAttr_x3f_2771_);
v___x_2833_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__1, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__1_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__1);
v___x_2834_ = l_Lean_MessageData_ofName(v_name_2775_);
v___x_2835_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2835_, 0, v___x_2833_);
lean_ctor_set(v___x_2835_, 1, v___x_2834_);
v___x_2836_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__3, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__3);
v___x_2837_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2837_, 0, v___x_2835_);
lean_ctor_set(v___x_2837_, 1, v___x_2836_);
v___x_2838_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg(v___x_2837_, v_a_2763_, v_a_2764_, v_a_2765_, v_a_2766_);
v_a_2839_ = lean_ctor_get(v___x_2838_, 0);
v_isSharedCheck_2846_ = !lean_is_exclusive(v___x_2838_);
if (v_isSharedCheck_2846_ == 0)
{
v___x_2841_ = v___x_2838_;
v_isShared_2842_ = v_isSharedCheck_2846_;
goto v_resetjp_2840_;
}
else
{
lean_inc(v_a_2839_);
lean_dec(v___x_2838_);
v___x_2841_ = lean_box(0);
v_isShared_2842_ = v_isSharedCheck_2846_;
goto v_resetjp_2840_;
}
v_resetjp_2840_:
{
lean_object* v___x_2844_; 
if (v_isShared_2842_ == 0)
{
v___x_2844_ = v___x_2841_;
goto v_reusejp_2843_;
}
else
{
lean_object* v_reuseFailAlloc_2845_; 
v_reuseFailAlloc_2845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2845_, 0, v_a_2839_);
v___x_2844_ = v_reuseFailAlloc_2845_;
goto v_reusejp_2843_;
}
v_reusejp_2843_:
{
return v___x_2844_;
}
}
}
v___jp_2801_:
{
lean_object* v___x_2807_; 
v___x_2807_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_code_2797_, v___y_2802_, v___y_2803_, v___y_2804_, v___y_2805_, v___y_2806_);
if (lean_obj_tag(v___x_2807_) == 0)
{
lean_object* v_a_2808_; lean_object* v___x_2810_; uint8_t v_isShared_2811_; uint8_t v_isSharedCheck_2824_; 
v_a_2808_ = lean_ctor_get(v___x_2807_, 0);
v_isSharedCheck_2824_ = !lean_is_exclusive(v___x_2807_);
if (v_isSharedCheck_2824_ == 0)
{
v___x_2810_ = v___x_2807_;
v_isShared_2811_ = v_isSharedCheck_2824_;
goto v_resetjp_2809_;
}
else
{
lean_inc(v_a_2808_);
lean_dec(v___x_2807_);
v___x_2810_ = lean_box(0);
v_isShared_2811_ = v_isSharedCheck_2824_;
goto v_resetjp_2809_;
}
v_resetjp_2809_:
{
lean_object* v___x_2813_; 
if (v_isShared_2782_ == 0)
{
lean_ctor_set(v___x_2781_, 3, v_a_2786_);
lean_ctor_set(v___x_2781_, 2, v_a_2789_);
v___x_2813_ = v___x_2781_;
goto v_reusejp_2812_;
}
else
{
lean_object* v_reuseFailAlloc_2823_; 
v_reuseFailAlloc_2823_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2823_, 0, v_name_2775_);
lean_ctor_set(v_reuseFailAlloc_2823_, 1, v_levelParams_2776_);
lean_ctor_set(v_reuseFailAlloc_2823_, 2, v_a_2789_);
lean_ctor_set(v_reuseFailAlloc_2823_, 3, v_a_2786_);
lean_ctor_set_uint8(v_reuseFailAlloc_2823_, sizeof(void*)*4, v_safe_2779_);
v___x_2813_ = v_reuseFailAlloc_2823_;
goto v_reusejp_2812_;
}
v_reusejp_2812_:
{
lean_object* v___x_2815_; 
if (v_isShared_2800_ == 0)
{
lean_ctor_set(v___x_2799_, 0, v_a_2808_);
v___x_2815_ = v___x_2799_;
goto v_reusejp_2814_;
}
else
{
lean_object* v_reuseFailAlloc_2822_; 
v_reuseFailAlloc_2822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2822_, 0, v_a_2808_);
v___x_2815_ = v_reuseFailAlloc_2822_;
goto v_reusejp_2814_;
}
v_reusejp_2814_:
{
lean_object* v___x_2817_; 
if (v_isShared_2774_ == 0)
{
lean_ctor_set(v___x_2773_, 1, v___x_2815_);
lean_ctor_set(v___x_2773_, 0, v___x_2813_);
v___x_2817_ = v___x_2773_;
goto v_reusejp_2816_;
}
else
{
lean_object* v_reuseFailAlloc_2821_; 
v_reuseFailAlloc_2821_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2821_, 0, v___x_2813_);
lean_ctor_set(v_reuseFailAlloc_2821_, 1, v___x_2815_);
lean_ctor_set(v_reuseFailAlloc_2821_, 2, v_inlineAttr_x3f_2771_);
lean_ctor_set_uint8(v_reuseFailAlloc_2821_, sizeof(void*)*3, v_recursive_2770_);
v___x_2817_ = v_reuseFailAlloc_2821_;
goto v_reusejp_2816_;
}
v_reusejp_2816_:
{
lean_object* v___x_2819_; 
if (v_isShared_2811_ == 0)
{
lean_ctor_set(v___x_2810_, 0, v___x_2817_);
v___x_2819_ = v___x_2810_;
goto v_reusejp_2818_;
}
else
{
lean_object* v_reuseFailAlloc_2820_; 
v_reuseFailAlloc_2820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2820_, 0, v___x_2817_);
v___x_2819_ = v_reuseFailAlloc_2820_;
goto v_reusejp_2818_;
}
v_reusejp_2818_:
{
return v___x_2819_;
}
}
}
}
}
}
else
{
lean_object* v_a_2825_; lean_object* v___x_2827_; uint8_t v_isShared_2828_; uint8_t v_isSharedCheck_2832_; 
lean_del_object(v___x_2799_);
lean_dec(v_a_2789_);
lean_dec(v_a_2786_);
lean_del_object(v___x_2781_);
lean_dec(v_levelParams_2776_);
lean_dec(v_name_2775_);
lean_del_object(v___x_2773_);
lean_dec(v_inlineAttr_x3f_2771_);
v_a_2825_ = lean_ctor_get(v___x_2807_, 0);
v_isSharedCheck_2832_ = !lean_is_exclusive(v___x_2807_);
if (v_isSharedCheck_2832_ == 0)
{
v___x_2827_ = v___x_2807_;
v_isShared_2828_ = v_isSharedCheck_2832_;
goto v_resetjp_2826_;
}
else
{
lean_inc(v_a_2825_);
lean_dec(v___x_2807_);
v___x_2827_ = lean_box(0);
v_isShared_2828_ = v_isSharedCheck_2832_;
goto v_resetjp_2826_;
}
v_resetjp_2826_:
{
lean_object* v___x_2830_; 
if (v_isShared_2828_ == 0)
{
v___x_2830_ = v___x_2827_;
goto v_reusejp_2829_;
}
else
{
lean_object* v_reuseFailAlloc_2831_; 
v_reuseFailAlloc_2831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2831_, 0, v_a_2825_);
v___x_2830_ = v_reuseFailAlloc_2831_;
goto v_reusejp_2829_;
}
v_reusejp_2829_:
{
return v___x_2830_;
}
}
}
}
}
}
else
{
lean_object* v_externAttrData_2848_; lean_object* v___x_2850_; uint8_t v_isShared_2851_; uint8_t v_isSharedCheck_2884_; 
v_externAttrData_2848_ = lean_ctor_get(v_value_2769_, 0);
v_isSharedCheck_2884_ = !lean_is_exclusive(v_value_2769_);
if (v_isSharedCheck_2884_ == 0)
{
v___x_2850_ = v_value_2769_;
v_isShared_2851_ = v_isSharedCheck_2884_;
goto v_resetjp_2849_;
}
else
{
lean_inc(v_externAttrData_2848_);
lean_dec(v_value_2769_);
v___x_2850_ = lean_box(0);
v_isShared_2851_ = v_isSharedCheck_2884_;
goto v_resetjp_2849_;
}
v_resetjp_2849_:
{
lean_object* v_resultType_2853_; 
if (v___x_2796_ == 0)
{
v_resultType_2853_ = v_a_2789_;
goto v___jp_2852_;
}
else
{
uint8_t v___x_2866_; 
v___x_2866_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar(v_a_2789_);
if (v___x_2866_ == 0)
{
lean_object* v___x_2867_; 
lean_dec(v_a_2789_);
v___x_2867_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__5, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__5_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__5);
v_resultType_2853_ = v___x_2867_;
goto v___jp_2852_;
}
else
{
lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v_a_2876_; lean_object* v___x_2878_; uint8_t v_isShared_2879_; uint8_t v_isSharedCheck_2883_; 
lean_del_object(v___x_2850_);
lean_dec(v_externAttrData_2848_);
lean_del_object(v___x_2791_);
lean_dec(v_a_2786_);
lean_del_object(v___x_2781_);
lean_dec(v_levelParams_2776_);
lean_del_object(v___x_2773_);
lean_dec(v_inlineAttr_x3f_2771_);
v___x_2868_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__5, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__5_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__5);
v___x_2869_ = l_Lean_MessageData_ofName(v_name_2775_);
v___x_2870_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2870_, 0, v___x_2868_);
lean_ctor_set(v___x_2870_, 1, v___x_2869_);
v___x_2871_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__7, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__7_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__7);
v___x_2872_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2872_, 0, v___x_2870_);
lean_ctor_set(v___x_2872_, 1, v___x_2871_);
v___x_2873_ = l_Lean_MessageData_ofExpr(v_a_2789_);
v___x_2874_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2874_, 0, v___x_2872_);
lean_ctor_set(v___x_2874_, 1, v___x_2873_);
v___x_2875_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg(v___x_2874_, v_a_2763_, v_a_2764_, v_a_2765_, v_a_2766_);
v_a_2876_ = lean_ctor_get(v___x_2875_, 0);
v_isSharedCheck_2883_ = !lean_is_exclusive(v___x_2875_);
if (v_isSharedCheck_2883_ == 0)
{
v___x_2878_ = v___x_2875_;
v_isShared_2879_ = v_isSharedCheck_2883_;
goto v_resetjp_2877_;
}
else
{
lean_inc(v_a_2876_);
lean_dec(v___x_2875_);
v___x_2878_ = lean_box(0);
v_isShared_2879_ = v_isSharedCheck_2883_;
goto v_resetjp_2877_;
}
v_resetjp_2877_:
{
lean_object* v___x_2881_; 
if (v_isShared_2879_ == 0)
{
v___x_2881_ = v___x_2878_;
goto v_reusejp_2880_;
}
else
{
lean_object* v_reuseFailAlloc_2882_; 
v_reuseFailAlloc_2882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2882_, 0, v_a_2876_);
v___x_2881_ = v_reuseFailAlloc_2882_;
goto v_reusejp_2880_;
}
v_reusejp_2880_:
{
return v___x_2881_;
}
}
}
}
v___jp_2852_:
{
lean_object* v___x_2855_; 
if (v_isShared_2782_ == 0)
{
lean_ctor_set(v___x_2781_, 3, v_a_2786_);
lean_ctor_set(v___x_2781_, 2, v_resultType_2853_);
v___x_2855_ = v___x_2781_;
goto v_reusejp_2854_;
}
else
{
lean_object* v_reuseFailAlloc_2865_; 
v_reuseFailAlloc_2865_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2865_, 0, v_name_2775_);
lean_ctor_set(v_reuseFailAlloc_2865_, 1, v_levelParams_2776_);
lean_ctor_set(v_reuseFailAlloc_2865_, 2, v_resultType_2853_);
lean_ctor_set(v_reuseFailAlloc_2865_, 3, v_a_2786_);
lean_ctor_set_uint8(v_reuseFailAlloc_2865_, sizeof(void*)*4, v_safe_2779_);
v___x_2855_ = v_reuseFailAlloc_2865_;
goto v_reusejp_2854_;
}
v_reusejp_2854_:
{
lean_object* v___x_2857_; 
if (v_isShared_2851_ == 0)
{
v___x_2857_ = v___x_2850_;
goto v_reusejp_2856_;
}
else
{
lean_object* v_reuseFailAlloc_2864_; 
v_reuseFailAlloc_2864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2864_, 0, v_externAttrData_2848_);
v___x_2857_ = v_reuseFailAlloc_2864_;
goto v_reusejp_2856_;
}
v_reusejp_2856_:
{
lean_object* v___x_2859_; 
if (v_isShared_2774_ == 0)
{
lean_ctor_set(v___x_2773_, 1, v___x_2857_);
lean_ctor_set(v___x_2773_, 0, v___x_2855_);
v___x_2859_ = v___x_2773_;
goto v_reusejp_2858_;
}
else
{
lean_object* v_reuseFailAlloc_2863_; 
v_reuseFailAlloc_2863_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2863_, 0, v___x_2855_);
lean_ctor_set(v_reuseFailAlloc_2863_, 1, v___x_2857_);
lean_ctor_set(v_reuseFailAlloc_2863_, 2, v_inlineAttr_x3f_2771_);
lean_ctor_set_uint8(v_reuseFailAlloc_2863_, sizeof(void*)*3, v_recursive_2770_);
v___x_2859_ = v_reuseFailAlloc_2863_;
goto v_reusejp_2858_;
}
v_reusejp_2858_:
{
lean_object* v___x_2861_; 
if (v_isShared_2792_ == 0)
{
lean_ctor_set(v___x_2791_, 0, v___x_2859_);
v___x_2861_ = v___x_2791_;
goto v_reusejp_2860_;
}
else
{
lean_object* v_reuseFailAlloc_2862_; 
v_reuseFailAlloc_2862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2862_, 0, v___x_2859_);
v___x_2861_ = v_reuseFailAlloc_2862_;
goto v_reusejp_2860_;
}
v_reusejp_2860_:
{
return v___x_2861_;
}
}
}
}
}
}
}
}
}
else
{
lean_object* v_a_2886_; lean_object* v___x_2888_; uint8_t v_isShared_2889_; uint8_t v_isSharedCheck_2893_; 
lean_dec(v_a_2786_);
lean_del_object(v___x_2781_);
lean_dec(v_levelParams_2776_);
lean_dec(v_name_2775_);
lean_del_object(v___x_2773_);
lean_dec(v_inlineAttr_x3f_2771_);
lean_dec_ref(v_value_2769_);
v_a_2886_ = lean_ctor_get(v___x_2788_, 0);
v_isSharedCheck_2893_ = !lean_is_exclusive(v___x_2788_);
if (v_isSharedCheck_2893_ == 0)
{
v___x_2888_ = v___x_2788_;
v_isShared_2889_ = v_isSharedCheck_2893_;
goto v_resetjp_2887_;
}
else
{
lean_inc(v_a_2886_);
lean_dec(v___x_2788_);
v___x_2888_ = lean_box(0);
v_isShared_2889_ = v_isSharedCheck_2893_;
goto v_resetjp_2887_;
}
v_resetjp_2887_:
{
lean_object* v___x_2891_; 
if (v_isShared_2889_ == 0)
{
v___x_2891_ = v___x_2888_;
goto v_reusejp_2890_;
}
else
{
lean_object* v_reuseFailAlloc_2892_; 
v_reuseFailAlloc_2892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2892_, 0, v_a_2886_);
v___x_2891_ = v_reuseFailAlloc_2892_;
goto v_reusejp_2890_;
}
v_reusejp_2890_:
{
return v___x_2891_;
}
}
}
}
else
{
lean_object* v_a_2894_; lean_object* v___x_2896_; uint8_t v_isShared_2897_; uint8_t v_isSharedCheck_2901_; 
lean_del_object(v___x_2781_);
lean_dec_ref(v_params_2778_);
lean_dec_ref(v_type_2777_);
lean_dec(v_levelParams_2776_);
lean_dec(v_name_2775_);
lean_del_object(v___x_2773_);
lean_dec(v_inlineAttr_x3f_2771_);
lean_dec_ref(v_value_2769_);
v_a_2894_ = lean_ctor_get(v___x_2785_, 0);
v_isSharedCheck_2901_ = !lean_is_exclusive(v___x_2785_);
if (v_isSharedCheck_2901_ == 0)
{
v___x_2896_ = v___x_2785_;
v_isShared_2897_ = v_isSharedCheck_2901_;
goto v_resetjp_2895_;
}
else
{
lean_inc(v_a_2894_);
lean_dec(v___x_2785_);
v___x_2896_ = lean_box(0);
v_isShared_2897_ = v_isSharedCheck_2901_;
goto v_resetjp_2895_;
}
v_resetjp_2895_:
{
lean_object* v___x_2899_; 
if (v_isShared_2897_ == 0)
{
v___x_2899_ = v___x_2896_;
goto v_reusejp_2898_;
}
else
{
lean_object* v_reuseFailAlloc_2900_; 
v_reuseFailAlloc_2900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2900_, 0, v_a_2894_);
v___x_2899_ = v_reuseFailAlloc_2900_;
goto v_reusejp_2898_;
}
v_reusejp_2898_:
{
return v___x_2899_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___boxed(lean_object* v_decl_2904_, lean_object* v_a_2905_, lean_object* v_a_2906_, lean_object* v_a_2907_, lean_object* v_a_2908_, lean_object* v_a_2909_, lean_object* v_a_2910_){
_start:
{
lean_object* v_res_2911_; 
v_res_2911_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl(v_decl_2904_, v_a_2905_, v_a_2906_, v_a_2907_, v_a_2908_, v_a_2909_);
lean_dec(v_a_2909_);
lean_dec_ref(v_a_2908_);
lean_dec(v_a_2907_);
lean_dec_ref(v_a_2906_);
lean_dec(v_a_2905_);
return v_res_2911_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_go(lean_object* v_decl_2912_, lean_object* v_a_2913_, lean_object* v_a_2914_, lean_object* v_a_2915_, lean_object* v_a_2916_, lean_object* v_a_2917_){
_start:
{
lean_object* v___x_2919_; 
v___x_2919_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl(v_decl_2912_, v_a_2913_, v_a_2914_, v_a_2915_, v_a_2916_, v_a_2917_);
if (lean_obj_tag(v___x_2919_) == 0)
{
lean_object* v_a_2920_; lean_object* v___x_2921_; 
v_a_2920_ = lean_ctor_get(v___x_2919_, 0);
lean_inc(v_a_2920_);
lean_dec_ref(v___x_2919_);
lean_inc(v_a_2920_);
v___x_2921_ = l_Lean_Compiler_LCNF_Decl_saveImpure___redArg(v_a_2920_, v_a_2917_);
if (lean_obj_tag(v___x_2921_) == 0)
{
lean_object* v___x_2923_; uint8_t v_isShared_2924_; uint8_t v_isSharedCheck_2928_; 
v_isSharedCheck_2928_ = !lean_is_exclusive(v___x_2921_);
if (v_isSharedCheck_2928_ == 0)
{
lean_object* v_unused_2929_; 
v_unused_2929_ = lean_ctor_get(v___x_2921_, 0);
lean_dec(v_unused_2929_);
v___x_2923_ = v___x_2921_;
v_isShared_2924_ = v_isSharedCheck_2928_;
goto v_resetjp_2922_;
}
else
{
lean_dec(v___x_2921_);
v___x_2923_ = lean_box(0);
v_isShared_2924_ = v_isSharedCheck_2928_;
goto v_resetjp_2922_;
}
v_resetjp_2922_:
{
lean_object* v___x_2926_; 
if (v_isShared_2924_ == 0)
{
lean_ctor_set(v___x_2923_, 0, v_a_2920_);
v___x_2926_ = v___x_2923_;
goto v_reusejp_2925_;
}
else
{
lean_object* v_reuseFailAlloc_2927_; 
v_reuseFailAlloc_2927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2927_, 0, v_a_2920_);
v___x_2926_ = v_reuseFailAlloc_2927_;
goto v_reusejp_2925_;
}
v_reusejp_2925_:
{
return v___x_2926_;
}
}
}
else
{
lean_object* v_a_2930_; lean_object* v___x_2932_; uint8_t v_isShared_2933_; uint8_t v_isSharedCheck_2937_; 
lean_dec(v_a_2920_);
v_a_2930_ = lean_ctor_get(v___x_2921_, 0);
v_isSharedCheck_2937_ = !lean_is_exclusive(v___x_2921_);
if (v_isSharedCheck_2937_ == 0)
{
v___x_2932_ = v___x_2921_;
v_isShared_2933_ = v_isSharedCheck_2937_;
goto v_resetjp_2931_;
}
else
{
lean_inc(v_a_2930_);
lean_dec(v___x_2921_);
v___x_2932_ = lean_box(0);
v_isShared_2933_ = v_isSharedCheck_2937_;
goto v_resetjp_2931_;
}
v_resetjp_2931_:
{
lean_object* v___x_2935_; 
if (v_isShared_2933_ == 0)
{
v___x_2935_ = v___x_2932_;
goto v_reusejp_2934_;
}
else
{
lean_object* v_reuseFailAlloc_2936_; 
v_reuseFailAlloc_2936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2936_, 0, v_a_2930_);
v___x_2935_ = v_reuseFailAlloc_2936_;
goto v_reusejp_2934_;
}
v_reusejp_2934_:
{
return v___x_2935_;
}
}
}
}
else
{
return v___x_2919_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_go___boxed(lean_object* v_decl_2938_, lean_object* v_a_2939_, lean_object* v_a_2940_, lean_object* v_a_2941_, lean_object* v_a_2942_, lean_object* v_a_2943_, lean_object* v_a_2944_){
_start:
{
lean_object* v_res_2945_; 
v_res_2945_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_go(v_decl_2938_, v_a_2939_, v_a_2940_, v_a_2941_, v_a_2942_, v_a_2943_);
lean_dec(v_a_2943_);
lean_dec_ref(v_a_2942_);
lean_dec(v_a_2941_);
lean_dec_ref(v_a_2940_);
lean_dec(v_a_2939_);
return v_res_2945_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__0(void){
_start:
{
lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; 
v___x_2946_ = lean_box(0);
v___x_2947_ = lean_unsigned_to_nat(16u);
v___x_2948_ = lean_mk_array(v___x_2947_, v___x_2946_);
return v___x_2948_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__1(void){
_start:
{
lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; 
v___x_2949_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__0, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__0_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__0);
v___x_2950_ = lean_unsigned_to_nat(0u);
v___x_2951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2951_, 0, v___x_2950_);
lean_ctor_set(v___x_2951_, 1, v___x_2949_);
return v___x_2951_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__2(void){
_start:
{
lean_object* v___x_2952_; lean_object* v___x_2953_; 
v___x_2952_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__1, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__1_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__1);
v___x_2953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2953_, 0, v___x_2952_);
lean_ctor_set(v___x_2953_, 1, v___x_2952_);
return v___x_2953_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure(lean_object* v_decl_2954_, lean_object* v_a_2955_, lean_object* v_a_2956_, lean_object* v_a_2957_, lean_object* v_a_2958_){
_start:
{
lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; 
v___x_2960_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__2, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__2);
v___x_2961_ = lean_st_mk_ref(v___x_2960_);
v___x_2962_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_go(v_decl_2954_, v___x_2961_, v_a_2955_, v_a_2956_, v_a_2957_, v_a_2958_);
if (lean_obj_tag(v___x_2962_) == 0)
{
lean_object* v_a_2963_; lean_object* v___x_2965_; uint8_t v_isShared_2966_; uint8_t v_isSharedCheck_2971_; 
v_a_2963_ = lean_ctor_get(v___x_2962_, 0);
v_isSharedCheck_2971_ = !lean_is_exclusive(v___x_2962_);
if (v_isSharedCheck_2971_ == 0)
{
v___x_2965_ = v___x_2962_;
v_isShared_2966_ = v_isSharedCheck_2971_;
goto v_resetjp_2964_;
}
else
{
lean_inc(v_a_2963_);
lean_dec(v___x_2962_);
v___x_2965_ = lean_box(0);
v_isShared_2966_ = v_isSharedCheck_2971_;
goto v_resetjp_2964_;
}
v_resetjp_2964_:
{
lean_object* v___x_2967_; lean_object* v___x_2969_; 
v___x_2967_ = lean_st_ref_get(v___x_2961_);
lean_dec(v___x_2961_);
lean_dec(v___x_2967_);
if (v_isShared_2966_ == 0)
{
v___x_2969_ = v___x_2965_;
goto v_reusejp_2968_;
}
else
{
lean_object* v_reuseFailAlloc_2970_; 
v_reuseFailAlloc_2970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2970_, 0, v_a_2963_);
v___x_2969_ = v_reuseFailAlloc_2970_;
goto v_reusejp_2968_;
}
v_reusejp_2968_:
{
return v___x_2969_;
}
}
}
else
{
lean_dec(v___x_2961_);
return v___x_2962_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___boxed(lean_object* v_decl_2972_, lean_object* v_a_2973_, lean_object* v_a_2974_, lean_object* v_a_2975_, lean_object* v_a_2976_, lean_object* v_a_2977_){
_start:
{
lean_object* v_res_2978_; 
v_res_2978_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure(v_decl_2972_, v_a_2973_, v_a_2974_, v_a_2975_, v_a_2976_);
lean_dec(v_a_2976_);
lean_dec_ref(v_a_2975_);
lean_dec(v_a_2974_);
lean_dec_ref(v_a_2973_);
return v_res_2978_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toImpure_spec__0(size_t v_sz_2979_, size_t v_i_2980_, lean_object* v_bs_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_){
_start:
{
uint8_t v___x_2987_; 
v___x_2987_ = lean_usize_dec_lt(v_i_2980_, v_sz_2979_);
if (v___x_2987_ == 0)
{
lean_object* v___x_2988_; 
v___x_2988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2988_, 0, v_bs_2981_);
return v___x_2988_;
}
else
{
lean_object* v_v_2989_; lean_object* v___x_2990_; 
v_v_2989_ = lean_array_uget_borrowed(v_bs_2981_, v_i_2980_);
lean_inc(v_v_2989_);
v___x_2990_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure(v_v_2989_, v___y_2982_, v___y_2983_, v___y_2984_, v___y_2985_);
if (lean_obj_tag(v___x_2990_) == 0)
{
lean_object* v_a_2991_; lean_object* v___x_2992_; lean_object* v_bs_x27_2993_; size_t v___x_2994_; size_t v___x_2995_; lean_object* v___x_2996_; 
v_a_2991_ = lean_ctor_get(v___x_2990_, 0);
lean_inc(v_a_2991_);
lean_dec_ref(v___x_2990_);
v___x_2992_ = lean_unsigned_to_nat(0u);
v_bs_x27_2993_ = lean_array_uset(v_bs_2981_, v_i_2980_, v___x_2992_);
v___x_2994_ = ((size_t)1ULL);
v___x_2995_ = lean_usize_add(v_i_2980_, v___x_2994_);
v___x_2996_ = lean_array_uset(v_bs_x27_2993_, v_i_2980_, v_a_2991_);
v_i_2980_ = v___x_2995_;
v_bs_2981_ = v___x_2996_;
goto _start;
}
else
{
lean_object* v_a_2998_; lean_object* v___x_3000_; uint8_t v_isShared_3001_; uint8_t v_isSharedCheck_3005_; 
lean_dec_ref(v_bs_2981_);
v_a_2998_ = lean_ctor_get(v___x_2990_, 0);
v_isSharedCheck_3005_ = !lean_is_exclusive(v___x_2990_);
if (v_isSharedCheck_3005_ == 0)
{
v___x_3000_ = v___x_2990_;
v_isShared_3001_ = v_isSharedCheck_3005_;
goto v_resetjp_2999_;
}
else
{
lean_inc(v_a_2998_);
lean_dec(v___x_2990_);
v___x_3000_ = lean_box(0);
v_isShared_3001_ = v_isSharedCheck_3005_;
goto v_resetjp_2999_;
}
v_resetjp_2999_:
{
lean_object* v___x_3003_; 
if (v_isShared_3001_ == 0)
{
v___x_3003_ = v___x_3000_;
goto v_reusejp_3002_;
}
else
{
lean_object* v_reuseFailAlloc_3004_; 
v_reuseFailAlloc_3004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3004_, 0, v_a_2998_);
v___x_3003_ = v_reuseFailAlloc_3004_;
goto v_reusejp_3002_;
}
v_reusejp_3002_:
{
return v___x_3003_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toImpure_spec__0___boxed(lean_object* v_sz_3006_, lean_object* v_i_3007_, lean_object* v_bs_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_, lean_object* v___y_3011_, lean_object* v___y_3012_, lean_object* v___y_3013_){
_start:
{
size_t v_sz_boxed_3014_; size_t v_i_boxed_3015_; lean_object* v_res_3016_; 
v_sz_boxed_3014_ = lean_unbox_usize(v_sz_3006_);
lean_dec(v_sz_3006_);
v_i_boxed_3015_ = lean_unbox_usize(v_i_3007_);
lean_dec(v_i_3007_);
v_res_3016_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toImpure_spec__0(v_sz_boxed_3014_, v_i_boxed_3015_, v_bs_3008_, v___y_3009_, v___y_3010_, v___y_3011_, v___y_3012_);
lean_dec(v___y_3012_);
lean_dec_ref(v___y_3011_);
lean_dec(v___y_3010_);
lean_dec_ref(v___y_3009_);
return v_res_3016_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toImpure___lam__0(lean_object* v_x_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_){
_start:
{
size_t v_sz_3023_; size_t v___x_3024_; lean_object* v___x_3025_; 
v_sz_3023_ = lean_array_size(v_x_3017_);
v___x_3024_ = ((size_t)0ULL);
v___x_3025_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toImpure_spec__0(v_sz_3023_, v___x_3024_, v_x_3017_, v___y_3018_, v___y_3019_, v___y_3020_, v___y_3021_);
return v___x_3025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toImpure___lam__0___boxed(lean_object* v_x_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_){
_start:
{
lean_object* v_res_3032_; 
v_res_3032_ = l_Lean_Compiler_LCNF_toImpure___lam__0(v_x_3026_, v___y_3027_, v___y_3028_, v___y_3029_, v___y_3030_);
lean_dec(v___y_3030_);
lean_dec_ref(v___y_3029_);
lean_dec(v___y_3028_);
lean_dec_ref(v___y_3027_);
return v_res_3032_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3083_; uint8_t v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; 
v___x_3083_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_));
v___x_3084_ = 1;
v___x_3085_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_));
v___x_3086_ = l_Lean_registerTraceClass(v___x_3083_, v___x_3084_, v___x_3085_);
return v___x_3086_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2____boxed(lean_object* v_a_3087_){
_start:
{
lean_object* v_res_3088_; 
v_res_3088_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_();
return v_res_3088_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_ToImpureType(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_PassManager(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_PhaseExt(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Format_Macro(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_ToImpure(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Compiler_LCNF_ToImpureType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_PassManager(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_PhaseExt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Format_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr);
lean_dec_ref(res);
res = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue = _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue);
res = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_LCNF_ToImpure(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Compiler_LCNF_ToImpureType(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_PassManager(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_PhaseExt(uint8_t builtin);
lean_object* initialize_Init_Data_Format_Macro(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_ToImpure(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_ToImpureType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_PassManager(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_PhaseExt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Format_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_ToImpure(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_LCNF_ToImpure(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_LCNF_ToImpure(builtin);
}
#ifdef __cplusplus
}
#endif
