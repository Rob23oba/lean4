// Lean compiler output
// Module: Lean.Compiler.LCNF.CheckRC
// Imports: public import Lean.Compiler.LCNF.PrettyPrinter public import Lean.Compiler.LCNF.CompatibleTypes
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
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_string_length(lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* l_Lean_Compiler_LCNF_getBinderName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Compiler_LCNF_getPurity___redArg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_toLocalContext(lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_addParam(uint8_t, lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isPossibleRef(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Name_reprPrec(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Bool_repr___redArg(uint8_t);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Std_Format_fill(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_CtorInfo_isRef(lean_object*);
lean_object* l_Lean_Compiler_LCNF_getImpureSignature_x3f___redArg(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_addLetDecl(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_addFunDecl(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getFunDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_CtorInfo_isScalar(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_instReprExpr_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr_spec__0_spec__0___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr_spec__0_spec__0_spec__2_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr_spec__0_spec__0(lean_object*, lean_object*);
static const lean_string_object l_Array_repr___at___00Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "#["};
static const lean_object* l_Array_repr___at___00Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr_spec__0___closed__0 = (const lean_object*)&l_Array_repr___at___00Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr_spec__0___closed__0_value;
static const lean_string_object l_Array_repr___at___00Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Array_repr___at___00Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr_spec__0___closed__1 = (const lean_object*)&l_Array_repr___at___00Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr_spec__0___closed__1_value;
static const lean_ctor_object l_Array_repr___at___00Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr_spec__0___closed__1_value)}};
static const lean_object* l_Array_repr___at___00Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr_spec__0___closed__2 = (const lean_object*)&l_Array_repr___at___00Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr_spec__0___closed__2_value;
static const lean_ctor_object l_Array_repr___at___00Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr_spec__0___closed__2_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Array_repr___at___00Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr_spec__0___closed__3 = (const lean_object*)&l_Array_repr___at___00Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr_spec__0___closed__3_value;
static const lean_string_object l_Array_repr___at___00Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Array_repr___at___00Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr_spec__0___closed__4 = (const lean_object*)&l_Array_repr___at___00Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr_spec__0___closed__4_value;
static lean_once_cell_t l_Array_repr___at___00Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_repr___at___00Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr_spec__0___closed__5;
static lean_once_cell_t l_Array_repr___at___00Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr_spec__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_repr___at___00Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr_spec__0___closed__6;
static const lean_ctor_object l_Array_repr___at___00Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr_spec__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr_spec__0___closed__0_value)}};
static const lean_object* l_Array_repr___at___00Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr_spec__0___closed__7 = (const lean_object*)&l_Array_repr___at___00Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr_spec__0___closed__7_value;
static const lean_ctor_object l_Array_repr___at___00Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr_spec__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr_spec__0___closed__4_value)}};
static const lean_object* l_Array_repr___at___00Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr_spec__0___closed__8 = (const lean_object*)&l_Array_repr___at___00Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr_spec__0___closed__8_value;
static const lean_string_object l_Array_repr___at___00Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr_spec__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "#[]"};
static const lean_object* l_Array_repr___at___00Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr_spec__0___closed__9 = (const lean_object*)&l_Array_repr___at___00Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr_spec__0___closed__9_value;
static const lean_ctor_object l_Array_repr___at___00Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr_spec__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr_spec__0___closed__9_value)}};
static const lean_object* l_Array_repr___at___00Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr_spec__0___closed__10 = (const lean_object*)&l_Array_repr___at___00Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr_spec__0___closed__10_value;
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr_spec__0(lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr___redArg___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr___redArg___closed__0_value;
static const lean_string_object l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "rc"};
static const lean_object* l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr___redArg___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr___redArg___closed__1_value)}};
static const lean_object* l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr___redArg___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr___redArg___closed__2_value)}};
static const lean_object* l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr___redArg___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr___redArg___closed__3_value;
static const lean_string_object l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr___redArg___closed__4 = (const lean_object*)&l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr___redArg___closed__4_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr___redArg___closed__4_value)}};
static const lean_object* l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr___redArg___closed__5 = (const lean_object*)&l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr___redArg___closed__5_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr___redArg___closed__3_value),((lean_object*)&l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr___redArg___closed__6 = (const lean_object*)&l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr___redArg___closed__6_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr___redArg___closed__7;
static const lean_string_object l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "borrowed"};
static const lean_object* l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr___redArg___closed__8 = (const lean_object*)&l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr___redArg___closed__8_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr___redArg___closed__8_value)}};
static const lean_object* l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr___redArg___closed__9 = (const lean_object*)&l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr___redArg___closed__9_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr___redArg___closed__10;
static const lean_string_object l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "parents"};
static const lean_object* l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr___redArg___closed__11 = (const lean_object*)&l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr___redArg___closed__11_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr___redArg___closed__11_value)}};
static const lean_object* l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr___redArg___closed__12 = (const lean_object*)&l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr___redArg___closed__12_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr___redArg___closed__13;
static const lean_string_object l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "children"};
static const lean_object* l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr___redArg___closed__14 = (const lean_object*)&l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr___redArg___closed__14_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr___redArg___closed__14_value)}};
static const lean_object* l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr___redArg___closed__15 = (const lean_object*)&l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr___redArg___closed__15_value;
static const lean_string_object l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr___redArg___closed__16 = (const lean_object*)&l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr___redArg___closed__16_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr___redArg___closed__17;
static lean_once_cell_t l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr___redArg___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr___redArg___closed__18;
static const lean_ctor_object l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr___redArg___closed__0_value)}};
static const lean_object* l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr___redArg___closed__19 = (const lean_object*)&l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr___redArg___closed__19_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr___redArg___closed__16_value)}};
static const lean_object* l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr___redArg___closed__20 = (const lean_object*)&l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr___redArg___closed__20_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo = (const lean_object*)&l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo___closed__0_value;
static const lean_array_object l_Lean_Compiler_LCNF_Check_Impure_deadInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Compiler_LCNF_Check_Impure_deadInfo___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_Check_Impure_deadInfo___closed__0_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Check_Impure_deadInfo___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Check_Impure_deadInfo___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Impure_deadInfo;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_Check_Impure_isDead_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_Check_Impure_isDead_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Impure_isDead___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Impure_isDead___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Impure_isDead(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Impure_isDead___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_Check_Impure_isDead_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_Check_Impure_isDead_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Check_Impure_maybeKill_spec__1___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Check_Impure_maybeKill_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Impure_maybeKill(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Impure_maybeKill_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Impure_maybeKill_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Impure_maybeKill___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Check_Impure_maybeKill_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Check_Impure_maybeKill_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Impure_kill_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Impure_kill_spec__1___redArg___closed__0;
static lean_once_cell_t l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Impure_kill_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Impure_kill_spec__1___redArg___closed__1;
static lean_once_cell_t l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Impure_kill_spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Impure_kill_spec__1___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Impure_kill_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Impure_kill_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Impure_kill_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Impure_kill_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_Check_Impure_kill_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_Check_Impure_kill_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_Check_Impure_kill_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_Check_Impure_kill_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_Check_Impure_kill___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "Can't delete a borrowed value"};
static const lean_object* l_Lean_Compiler_LCNF_Check_Impure_kill___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_Check_Impure_kill___closed__0_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Check_Impure_kill___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Check_Impure_kill___closed__1;
static const lean_string_object l_Lean_Compiler_LCNF_Check_Impure_kill___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Can't delete a scalar value"};
static const lean_object* l_Lean_Compiler_LCNF_Check_Impure_kill___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_Check_Impure_kill___closed__2_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Check_Impure_kill___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Check_Impure_kill___closed__3;
static const lean_string_object l_Lean_Compiler_LCNF_Check_Impure_kill___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Can't delete an erased value"};
static const lean_object* l_Lean_Compiler_LCNF_Check_Impure_kill___closed__4 = (const lean_object*)&l_Lean_Compiler_LCNF_Check_Impure_kill___closed__4_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Check_Impure_kill___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Check_Impure_kill___closed__5;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Impure_kill(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Impure_kill___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_Check_Impure_kill_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_Check_Impure_kill_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_Check_Impure_kill_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_Check_Impure_kill_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Compiler_LCNF_Check_Impure_makeScalar_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Compiler_LCNF_Check_Impure_makeScalar_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Impure_makeScalar___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Impure_makeScalar___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Impure_makeScalar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Impure_makeScalar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Compiler_LCNF_Check_Impure_makeScalar_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Compiler_LCNF_Check_Impure_makeScalar_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Lean_Compiler_LCNF_Check_Impure_consume_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Lean_Compiler_LCNF_Check_Impure_consume_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_Check_Impure_consume___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Failed to consume "};
static const lean_object* l_Lean_Compiler_LCNF_Check_Impure_consume___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_Check_Impure_consume___closed__0_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Check_Impure_consume___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Check_Impure_consume___closed__1;
static const lean_string_object l_Lean_Compiler_LCNF_Check_Impure_consume___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l_Lean_Compiler_LCNF_Check_Impure_consume___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_Check_Impure_consume___closed__2_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Check_Impure_consume___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Check_Impure_consume___closed__3;
static const lean_string_object l_Lean_Compiler_LCNF_Check_Impure_consume___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = " times, only "};
static const lean_object* l_Lean_Compiler_LCNF_Check_Impure_consume___closed__4 = (const lean_object*)&l_Lean_Compiler_LCNF_Check_Impure_consume___closed__4_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Check_Impure_consume___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Check_Impure_consume___closed__5;
static const lean_string_object l_Lean_Compiler_LCNF_Check_Impure_consume___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = " reference count available"};
static const lean_object* l_Lean_Compiler_LCNF_Check_Impure_consume___closed__6 = (const lean_object*)&l_Lean_Compiler_LCNF_Check_Impure_consume___closed__6_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Check_Impure_consume___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Check_Impure_consume___closed__7;
static const lean_string_object l_Lean_Compiler_LCNF_Check_Impure_consume___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = " times, potential use after free"};
static const lean_object* l_Lean_Compiler_LCNF_Check_Impure_consume___closed__8 = (const lean_object*)&l_Lean_Compiler_LCNF_Check_Impure_consume___closed__8_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Check_Impure_consume___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Check_Impure_consume___closed__9;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Impure_consume(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Impure_consume___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_Check_Impure_useVar___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "Can't use "};
static const lean_object* l_Lean_Compiler_LCNF_Check_Impure_useVar___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_Check_Impure_useVar___closed__0_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Check_Impure_useVar___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Check_Impure_useVar___closed__1;
static const lean_string_object l_Lean_Compiler_LCNF_Check_Impure_useVar___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = ", potential use after free"};
static const lean_object* l_Lean_Compiler_LCNF_Check_Impure_useVar___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_Check_Impure_useVar___closed__2_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Check_Impure_useVar___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Check_Impure_useVar___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Impure_useVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Impure_useVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_Check_Impure_checkShared___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Can't write into "};
static const lean_object* l_Lean_Compiler_LCNF_Check_Impure_checkShared___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_Check_Impure_checkShared___closed__0_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Check_Impure_checkShared___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Check_Impure_checkShared___closed__1;
static const lean_string_object l_Lean_Compiler_LCNF_Check_Impure_checkShared___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = ", variable has a reference count of at least "};
static const lean_object* l_Lean_Compiler_LCNF_Check_Impure_checkShared___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_Check_Impure_checkShared___closed__2_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Check_Impure_checkShared___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Check_Impure_checkShared___closed__3;
static const lean_string_object l_Lean_Compiler_LCNF_Check_Impure_checkShared___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "Can't write into borrowed value "};
static const lean_object* l_Lean_Compiler_LCNF_Check_Impure_checkShared___closed__4 = (const lean_object*)&l_Lean_Compiler_LCNF_Check_Impure_checkShared___closed__4_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Check_Impure_checkShared___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Check_Impure_checkShared___closed__5;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Impure_checkShared(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Impure_checkShared___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Lean_Compiler_LCNF_Check_Impure_inc_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Lean_Compiler_LCNF_Check_Impure_inc_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_Check_Impure_inc___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Can't increment "};
static const lean_object* l_Lean_Compiler_LCNF_Check_Impure_inc___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_Check_Impure_inc___closed__0_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Check_Impure_inc___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Check_Impure_inc___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Impure_inc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Impure_inc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Impure_consumeArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Impure_consumeArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Impure_useArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Impure_useArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Check_Impure_checkLeaks_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Detected RC leak: "};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Check_Impure_checkLeaks_spec__0___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Check_Impure_checkLeaks_spec__0___redArg___closed__0_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Check_Impure_checkLeaks_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Check_Impure_checkLeaks_spec__0___redArg___closed__1;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Check_Impure_checkLeaks_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = " still has an RC of at least "};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Check_Impure_checkLeaks_spec__0___redArg___closed__2 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Check_Impure_checkLeaks_spec__0___redArg___closed__2_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Check_Impure_checkLeaks_spec__0___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Check_Impure_checkLeaks_spec__0___redArg___closed__3;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Check_Impure_checkLeaks_spec__0___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = " upon return"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Check_Impure_checkLeaks_spec__0___redArg___closed__4 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Check_Impure_checkLeaks_spec__0___redArg___closed__4_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Check_Impure_checkLeaks_spec__0___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Check_Impure_checkLeaks_spec__0___redArg___closed__5;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Check_Impure_checkLeaks_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Check_Impure_checkLeaks_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Impure_checkLeaks(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Impure_checkLeaks___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Check_Impure_checkLeaks_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Check_Impure_checkLeaks_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Compiler_LCNF_Check_Impure_addOwned___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Check_Impure_addOwned___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Impure_addOwned___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Impure_addOwned___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Impure_addOwned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Impure_addOwned___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Lean_Compiler_LCNF_Check_Impure_addChild_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Impure_addChild___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Impure_addChild___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Impure_addChild(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Impure_addChild___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_Check_Impure_addBorrowed_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_Check_Impure_addBorrowed_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Compiler_LCNF_Check_Impure_addBorrowed_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Compiler_LCNF_Check_Impure_addBorrowed_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Impure_addBorrowed_spec__1___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Impure_addBorrowed_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Impure_addBorrowed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Impure_addBorrowed___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Impure_addBorrowed_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Impure_addBorrowed_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Impure_checkLetDecl_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Impure_checkLetDecl_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Impure_checkLetDecl_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Impure_checkLetDecl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Impure_checkLetDecl_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Impure_checkLetDecl_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_Check_Impure_checkLetDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Array"};
static const lean_object* l_Lean_Compiler_LCNF_Check_Impure_checkLetDecl___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_Check_Impure_checkLetDecl___closed__0_value;
static const lean_string_object l_Lean_Compiler_LCNF_Check_Impure_checkLetDecl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "getInternalBorrowed"};
static const lean_object* l_Lean_Compiler_LCNF_Check_Impure_checkLetDecl___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_Check_Impure_checkLetDecl___closed__1_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Check_Impure_checkLetDecl___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_Check_Impure_checkLetDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(81, 46, 193, 1, 46, 43, 107, 121)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_Check_Impure_checkLetDecl___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_Check_Impure_checkLetDecl___closed__2_value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_Check_Impure_checkLetDecl___closed__1_value),LEAN_SCALAR_PTR_LITERAL(109, 149, 133, 58, 23, 222, 178, 51)}};
static const lean_object* l_Lean_Compiler_LCNF_Check_Impure_checkLetDecl___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_Check_Impure_checkLetDecl___closed__2_value;
static const lean_string_object l_Lean_Compiler_LCNF_Check_Impure_checkLetDecl___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "get!InternalBorrowed"};
static const lean_object* l_Lean_Compiler_LCNF_Check_Impure_checkLetDecl___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_Check_Impure_checkLetDecl___closed__3_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Check_Impure_checkLetDecl___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_Check_Impure_checkLetDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(81, 46, 193, 1, 46, 43, 107, 121)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_Check_Impure_checkLetDecl___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_Check_Impure_checkLetDecl___closed__4_value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_Check_Impure_checkLetDecl___closed__3_value),LEAN_SCALAR_PTR_LITERAL(133, 131, 217, 159, 167, 207, 74, 149)}};
static const lean_object* l_Lean_Compiler_LCNF_Check_Impure_checkLetDecl___closed__4 = (const lean_object*)&l_Lean_Compiler_LCNF_Check_Impure_checkLetDecl___closed__4_value;
static const lean_string_object l_Lean_Compiler_LCNF_Check_Impure_checkLetDecl___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "ugetBorrowed"};
static const lean_object* l_Lean_Compiler_LCNF_Check_Impure_checkLetDecl___closed__5 = (const lean_object*)&l_Lean_Compiler_LCNF_Check_Impure_checkLetDecl___closed__5_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Check_Impure_checkLetDecl___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_Check_Impure_checkLetDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(81, 46, 193, 1, 46, 43, 107, 121)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_Check_Impure_checkLetDecl___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_Check_Impure_checkLetDecl___closed__6_value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_Check_Impure_checkLetDecl___closed__5_value),LEAN_SCALAR_PTR_LITERAL(152, 167, 221, 233, 168, 102, 210, 8)}};
static const lean_object* l_Lean_Compiler_LCNF_Check_Impure_checkLetDecl___closed__6 = (const lean_object*)&l_Lean_Compiler_LCNF_Check_Impure_checkLetDecl___closed__6_value;
static const lean_string_object l_Lean_Compiler_LCNF_Check_Impure_checkLetDecl___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Argument count mismatch for "};
static const lean_object* l_Lean_Compiler_LCNF_Check_Impure_checkLetDecl___closed__7 = (const lean_object*)&l_Lean_Compiler_LCNF_Check_Impure_checkLetDecl___closed__7_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Check_Impure_checkLetDecl___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Check_Impure_checkLetDecl___closed__8;
static const lean_string_object l_Lean_Compiler_LCNF_Check_Impure_checkLetDecl___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = ": expected "};
static const lean_object* l_Lean_Compiler_LCNF_Check_Impure_checkLetDecl___closed__9 = (const lean_object*)&l_Lean_Compiler_LCNF_Check_Impure_checkLetDecl___closed__9_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Check_Impure_checkLetDecl___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Check_Impure_checkLetDecl___closed__10;
static const lean_string_object l_Lean_Compiler_LCNF_Check_Impure_checkLetDecl___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = " arguments but got "};
static const lean_object* l_Lean_Compiler_LCNF_Check_Impure_checkLetDecl___closed__11 = (const lean_object*)&l_Lean_Compiler_LCNF_Check_Impure_checkLetDecl___closed__11_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Check_Impure_checkLetDecl___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Check_Impure_checkLetDecl___closed__12;
static const lean_string_object l_Lean_Compiler_LCNF_Check_Impure_checkLetDecl___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "Can't find impure signature for "};
static const lean_object* l_Lean_Compiler_LCNF_Check_Impure_checkLetDecl___closed__13 = (const lean_object*)&l_Lean_Compiler_LCNF_Check_Impure_checkLetDecl___closed__13_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Check_Impure_checkLetDecl___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Check_Impure_checkLetDecl___closed__14;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Impure_checkLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Impure_checkLetDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Check_Impure_check_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Check_Impure_check_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Check_Impure_check_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Check_Impure_check_spec__0_spec__1_spec__2_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Check_Impure_check_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Check_Impure_check_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Check_Impure_check_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Impure_check_spec__1___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Impure_check_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_Check_Impure_check___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "Join point argument count mismatch: expected "};
static const lean_object* l_Lean_Compiler_LCNF_Check_Impure_check___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_Check_Impure_check___closed__0_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Check_Impure_check___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Check_Impure_check___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Impure_check(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Impure_check_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Impure_check_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Impure_check___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Check_Impure_check_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Impure_check_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Impure_check_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Check_Impure_check_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Check_Impure_check_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Check_Impure_check_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Check_Impure_check_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Check_Impure_check_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Check_Impure_check_spec__0_spec__1_spec__2_spec__5(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Compiler_LCNF_Check_Impure_addParam___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Compiler_LCNF_Check_Impure_addParam___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_Check_Impure_addParam___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Impure_addParam(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Impure_addParam___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_Check_Impure_instReprParam_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "fvarId"};
static const lean_object* l_Lean_Compiler_LCNF_Check_Impure_instReprParam_repr___redArg___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_Check_Impure_instReprParam_repr___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Check_Impure_instReprParam_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_Check_Impure_instReprParam_repr___redArg___closed__0_value)}};
static const lean_object* l_Lean_Compiler_LCNF_Check_Impure_instReprParam_repr___redArg___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_Check_Impure_instReprParam_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Check_Impure_instReprParam_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_Check_Impure_instReprParam_repr___redArg___closed__1_value)}};
static const lean_object* l_Lean_Compiler_LCNF_Check_Impure_instReprParam_repr___redArg___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_Check_Impure_instReprParam_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Check_Impure_instReprParam_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_Check_Impure_instReprParam_repr___redArg___closed__2_value),((lean_object*)&l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_Compiler_LCNF_Check_Impure_instReprParam_repr___redArg___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_Check_Impure_instReprParam_repr___redArg___closed__3_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Check_Impure_instReprParam_repr___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Check_Impure_instReprParam_repr___redArg___closed__4;
static const lean_string_object l_Lean_Compiler_LCNF_Check_Impure_instReprParam_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "binderName"};
static const lean_object* l_Lean_Compiler_LCNF_Check_Impure_instReprParam_repr___redArg___closed__5 = (const lean_object*)&l_Lean_Compiler_LCNF_Check_Impure_instReprParam_repr___redArg___closed__5_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Check_Impure_instReprParam_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_Check_Impure_instReprParam_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_Compiler_LCNF_Check_Impure_instReprParam_repr___redArg___closed__6 = (const lean_object*)&l_Lean_Compiler_LCNF_Check_Impure_instReprParam_repr___redArg___closed__6_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Check_Impure_instReprParam_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Check_Impure_instReprParam_repr___redArg___closed__7;
static const lean_string_object l_Lean_Compiler_LCNF_Check_Impure_instReprParam_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "type"};
static const lean_object* l_Lean_Compiler_LCNF_Check_Impure_instReprParam_repr___redArg___closed__8 = (const lean_object*)&l_Lean_Compiler_LCNF_Check_Impure_instReprParam_repr___redArg___closed__8_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Check_Impure_instReprParam_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_Check_Impure_instReprParam_repr___redArg___closed__8_value)}};
static const lean_object* l_Lean_Compiler_LCNF_Check_Impure_instReprParam_repr___redArg___closed__9 = (const lean_object*)&l_Lean_Compiler_LCNF_Check_Impure_instReprParam_repr___redArg___closed__9_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Check_Impure_instReprParam_repr___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Check_Impure_instReprParam_repr___redArg___closed__10;
static const lean_string_object l_Lean_Compiler_LCNF_Check_Impure_instReprParam_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "borrow"};
static const lean_object* l_Lean_Compiler_LCNF_Check_Impure_instReprParam_repr___redArg___closed__11 = (const lean_object*)&l_Lean_Compiler_LCNF_Check_Impure_instReprParam_repr___redArg___closed__11_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Check_Impure_instReprParam_repr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_Check_Impure_instReprParam_repr___redArg___closed__11_value)}};
static const lean_object* l_Lean_Compiler_LCNF_Check_Impure_instReprParam_repr___redArg___closed__12 = (const lean_object*)&l_Lean_Compiler_LCNF_Check_Impure_instReprParam_repr___redArg___closed__12_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Impure_instReprParam_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Impure_instReprParam_repr(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Impure_instReprParam_repr___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Impure_instReprParam(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Impure_instReprParam___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_Check_Impure_checkDecl_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_Check_Impure_checkDecl_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_Check_Impure_checkDecl_spec__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_Check_Impure_checkDecl_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Impure_checkDecl_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Impure_checkDecl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Impure_checkDecl___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Impure_checkDecl___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Impure_checkDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Impure_checkDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Compiler_LCNF_Decl_checkRC___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Decl_checkRC___closed__0;
static lean_once_cell_t l_Lean_Compiler_LCNF_Decl_checkRC___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Decl_checkRC___closed__1;
static lean_once_cell_t l_Lean_Compiler_LCNF_Decl_checkRC___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Decl_checkRC___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_checkRC(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_checkRC___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr_spec__1(lean_object* v_a_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_nat_to_int(v_a_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr_spec__0_spec__0___lam__0(lean_object* v___y_3_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_4_ = lean_unsigned_to_nat(0u);
v___x_5_ = l_Lean_Name_reprPrec(v___y_3_, v___x_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr_spec__0_spec__0_spec__2_spec__3(lean_object* v_x_6_, lean_object* v_x_7_, lean_object* v_x_8_){
_start:
{
if (lean_obj_tag(v_x_8_) == 0)
{
lean_dec(v_x_6_);
return v_x_7_;
}
else
{
lean_object* v_head_9_; lean_object* v_tail_10_; lean_object* v___x_12_; uint8_t v_isShared_13_; uint8_t v_isSharedCheck_21_; 
v_head_9_ = lean_ctor_get(v_x_8_, 0);
v_tail_10_ = lean_ctor_get(v_x_8_, 1);
v_isSharedCheck_21_ = !lean_is_exclusive(v_x_8_);
if (v_isSharedCheck_21_ == 0)
{
v___x_12_ = v_x_8_;
v_isShared_13_ = v_isSharedCheck_21_;
goto v_resetjp_11_;
}
else
{
lean_inc(v_tail_10_);
lean_inc(v_head_9_);
lean_dec(v_x_8_);
v___x_12_ = lean_box(0);
v_isShared_13_ = v_isSharedCheck_21_;
goto v_resetjp_11_;
}
v_resetjp_11_:
{
lean_object* v___x_15_; 
lean_inc(v_x_6_);
if (v_isShared_13_ == 0)
{
lean_ctor_set_tag(v___x_12_, 5);
lean_ctor_set(v___x_12_, 1, v_x_6_);
lean_ctor_set(v___x_12_, 0, v_x_7_);
v___x_15_ = v___x_12_;
goto v_reusejp_14_;
}
else
{
lean_object* v_reuseFailAlloc_20_; 
v_reuseFailAlloc_20_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_20_, 0, v_x_7_);
lean_ctor_set(v_reuseFailAlloc_20_, 1, v_x_6_);
v___x_15_ = v_reuseFailAlloc_20_;
goto v_reusejp_14_;
}
v_reusejp_14_:
{
lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; 
v___x_16_ = lean_unsigned_to_nat(0u);
v___x_17_ = l_Lean_Name_reprPrec(v_head_9_, v___x_16_);
v___x_18_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_18_, 0, v___x_15_);
lean_ctor_set(v___x_18_, 1, v___x_17_);
v_x_7_ = v___x_18_;
v_x_8_ = v_tail_10_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr_spec__0_spec__0_spec__2(lean_object* v_x_22_, lean_object* v_x_23_, lean_object* v_x_24_){
_start:
{
if (lean_obj_tag(v_x_24_) == 0)
{
lean_dec(v_x_22_);
return v_x_23_;
}
else
{
lean_object* v_head_25_; lean_object* v_tail_26_; lean_object* v___x_28_; uint8_t v_isShared_29_; uint8_t v_isSharedCheck_37_; 
v_head_25_ = lean_ctor_get(v_x_24_, 0);
v_tail_26_ = lean_ctor_get(v_x_24_, 1);
v_isSharedCheck_37_ = !lean_is_exclusive(v_x_24_);
if (v_isSharedCheck_37_ == 0)
{
v___x_28_ = v_x_24_;
v_isShared_29_ = v_isSharedCheck_37_;
goto v_resetjp_27_;
}
else
{
lean_inc(v_tail_26_);
lean_inc(v_head_25_);
lean_dec(v_x_24_);
v___x_28_ = lean_box(0);
v_isShared_29_ = v_isSharedCheck_37_;
goto v_resetjp_27_;
}
v_resetjp_27_:
{
lean_object* v___x_31_; 
lean_inc(v_x_22_);
if (v_isShared_29_ == 0)
{
lean_ctor_set_tag(v___x_28_, 5);
lean_ctor_set(v___x_28_, 1, v_x_22_);
lean_ctor_set(v___x_28_, 0, v_x_23_);
v___x_31_ = v___x_28_;
goto v_reusejp_30_;
}
else
{
lean_object* v_reuseFailAlloc_36_; 
v_reuseFailAlloc_36_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_36_, 0, v_x_23_);
lean_ctor_set(v_reuseFailAlloc_36_, 1, v_x_22_);
v___x_31_ = v_reuseFailAlloc_36_;
goto v_reusejp_30_;
}
v_reusejp_30_:
{
lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; 
v___x_32_ = lean_unsigned_to_nat(0u);
v___x_33_ = l_Lean_Name_reprPrec(v_head_25_, v___x_32_);
v___x_34_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_34_, 0, v___x_31_);
lean_ctor_set(v___x_34_, 1, v___x_33_);
v___x_35_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr_spec__0_spec__0_spec__2_spec__3(v_x_22_, v___x_34_, v_tail_26_);
return v___x_35_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr_spec__0_spec__0(lean_object* v_x_38_, lean_object* v_x_39_){
_start:
{
if (lean_obj_tag(v_x_38_) == 0)
{
lean_object* v___x_40_; 
lean_dec(v_x_39_);
v___x_40_ = lean_box(0);
return v___x_40_;
}
else
{
lean_object* v_tail_41_; 
v_tail_41_ = lean_ctor_get(v_x_38_, 1);
if (lean_obj_tag(v_tail_41_) == 0)
{
lean_object* v_head_42_; lean_object* v___x_43_; 
lean_dec(v_x_39_);
v_head_42_ = lean_ctor_get(v_x_38_, 0);
lean_inc(v_head_42_);
lean_dec_ref(v_x_38_);
v___x_43_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr_spec__0_spec__0___lam__0(v_head_42_);
return v___x_43_;
}
else
{
lean_object* v_head_44_; lean_object* v___x_45_; lean_object* v___x_46_; 
lean_inc(v_tail_41_);
v_head_44_ = lean_ctor_get(v_x_38_, 0);
lean_inc(v_head_44_);
lean_dec_ref(v_x_38_);
v___x_45_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr_spec__0_spec__0___lam__0(v_head_44_);
v___x_46_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr_spec__0_spec__0_spec__2(v_x_39_, v___x_45_, v_tail_41_);
return v___x_46_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr_spec__0___closed__5(void){
_start:
{
lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_55_ = ((lean_object*)(l_Array_repr___at___00Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr_spec__0___closed__0));
v___x_56_ = lean_string_length(v___x_55_);
return v___x_56_;
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr_spec__0___closed__6(void){
_start:
{
lean_object* v___x_57_; lean_object* v___x_58_; 
v___x_57_ = lean_obj_once(&l_Array_repr___at___00Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr_spec__0___closed__5, &l_Array_repr___at___00Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr_spec__0___closed__5_once, _init_l_Array_repr___at___00Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr_spec__0___closed__5);
v___x_58_ = lean_nat_to_int(v___x_57_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr_spec__0(lean_object* v_xs_66_){
_start:
{
lean_object* v___x_67_; lean_object* v___x_68_; uint8_t v___x_69_; 
v___x_67_ = lean_array_get_size(v_xs_66_);
v___x_68_ = lean_unsigned_to_nat(0u);
v___x_69_ = lean_nat_dec_eq(v___x_67_, v___x_68_);
if (v___x_69_ == 0)
{
lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; 
v___x_70_ = lean_array_to_list(v_xs_66_);
v___x_71_ = ((lean_object*)(l_Array_repr___at___00Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr_spec__0___closed__3));
v___x_72_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr_spec__0_spec__0(v___x_70_, v___x_71_);
v___x_73_ = lean_obj_once(&l_Array_repr___at___00Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr_spec__0___closed__6, &l_Array_repr___at___00Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr_spec__0___closed__6_once, _init_l_Array_repr___at___00Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr_spec__0___closed__6);
v___x_74_ = ((lean_object*)(l_Array_repr___at___00Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr_spec__0___closed__7));
v___x_75_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_75_, 0, v___x_74_);
lean_ctor_set(v___x_75_, 1, v___x_72_);
v___x_76_ = ((lean_object*)(l_Array_repr___at___00Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr_spec__0___closed__8));
v___x_77_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_77_, 0, v___x_75_);
lean_ctor_set(v___x_77_, 1, v___x_76_);
v___x_78_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_78_, 0, v___x_73_);
lean_ctor_set(v___x_78_, 1, v___x_77_);
v___x_79_ = l_Std_Format_fill(v___x_78_);
return v___x_79_;
}
else
{
lean_object* v___x_80_; 
lean_dec_ref(v_xs_66_);
v___x_80_ = ((lean_object*)(l_Array_repr___at___00Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr_spec__0___closed__10));
return v___x_80_;
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_94_ = lean_unsigned_to_nat(6u);
v___x_95_ = lean_nat_to_int(v___x_94_);
return v___x_95_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_99_; lean_object* v___x_100_; 
v___x_99_ = lean_unsigned_to_nat(12u);
v___x_100_ = lean_nat_to_int(v___x_99_);
return v___x_100_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr___redArg___closed__13(void){
_start:
{
lean_object* v___x_104_; lean_object* v___x_105_; 
v___x_104_ = lean_unsigned_to_nat(11u);
v___x_105_ = lean_nat_to_int(v___x_104_);
return v___x_105_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr___redArg___closed__17(void){
_start:
{
lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_110_ = ((lean_object*)(l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr___redArg___closed__0));
v___x_111_ = lean_string_length(v___x_110_);
return v___x_111_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr___redArg___closed__18(void){
_start:
{
lean_object* v___x_112_; lean_object* v___x_113_; 
v___x_112_ = lean_obj_once(&l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr___redArg___closed__17, &l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr___redArg___closed__17_once, _init_l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr___redArg___closed__17);
v___x_113_ = lean_nat_to_int(v___x_112_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr___redArg(lean_object* v_x_118_){
_start:
{
lean_object* v_rc_119_; uint8_t v_borrowed_120_; lean_object* v_parents_121_; lean_object* v_children_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; uint8_t v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; 
v_rc_119_ = lean_ctor_get(v_x_118_, 0);
lean_inc(v_rc_119_);
v_borrowed_120_ = lean_ctor_get_uint8(v_x_118_, sizeof(void*)*3);
v_parents_121_ = lean_ctor_get(v_x_118_, 1);
lean_inc_ref(v_parents_121_);
v_children_122_ = lean_ctor_get(v_x_118_, 2);
lean_inc_ref(v_children_122_);
lean_dec_ref(v_x_118_);
v___x_123_ = ((lean_object*)(l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr___redArg___closed__5));
v___x_124_ = ((lean_object*)(l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr___redArg___closed__6));
v___x_125_ = lean_obj_once(&l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr___redArg___closed__7, &l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr___redArg___closed__7_once, _init_l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr___redArg___closed__7);
v___x_126_ = l_Nat_reprFast(v_rc_119_);
v___x_127_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_127_, 0, v___x_126_);
v___x_128_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_128_, 0, v___x_125_);
lean_ctor_set(v___x_128_, 1, v___x_127_);
v___x_129_ = 0;
v___x_130_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_130_, 0, v___x_128_);
lean_ctor_set_uint8(v___x_130_, sizeof(void*)*1, v___x_129_);
v___x_131_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_131_, 0, v___x_124_);
lean_ctor_set(v___x_131_, 1, v___x_130_);
v___x_132_ = ((lean_object*)(l_Array_repr___at___00Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr_spec__0___closed__2));
v___x_133_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_133_, 0, v___x_131_);
lean_ctor_set(v___x_133_, 1, v___x_132_);
v___x_134_ = lean_box(1);
v___x_135_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_135_, 0, v___x_133_);
lean_ctor_set(v___x_135_, 1, v___x_134_);
v___x_136_ = ((lean_object*)(l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr___redArg___closed__9));
v___x_137_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_137_, 0, v___x_135_);
lean_ctor_set(v___x_137_, 1, v___x_136_);
v___x_138_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_138_, 0, v___x_137_);
lean_ctor_set(v___x_138_, 1, v___x_123_);
v___x_139_ = lean_obj_once(&l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr___redArg___closed__10, &l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr___redArg___closed__10_once, _init_l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr___redArg___closed__10);
v___x_140_ = l_Bool_repr___redArg(v_borrowed_120_);
v___x_141_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_141_, 0, v___x_139_);
lean_ctor_set(v___x_141_, 1, v___x_140_);
v___x_142_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_142_, 0, v___x_141_);
lean_ctor_set_uint8(v___x_142_, sizeof(void*)*1, v___x_129_);
v___x_143_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_143_, 0, v___x_138_);
lean_ctor_set(v___x_143_, 1, v___x_142_);
v___x_144_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_144_, 0, v___x_143_);
lean_ctor_set(v___x_144_, 1, v___x_132_);
v___x_145_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_145_, 0, v___x_144_);
lean_ctor_set(v___x_145_, 1, v___x_134_);
v___x_146_ = ((lean_object*)(l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr___redArg___closed__12));
v___x_147_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_147_, 0, v___x_145_);
lean_ctor_set(v___x_147_, 1, v___x_146_);
v___x_148_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_148_, 0, v___x_147_);
lean_ctor_set(v___x_148_, 1, v___x_123_);
v___x_149_ = lean_obj_once(&l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr___redArg___closed__13, &l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr___redArg___closed__13_once, _init_l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr___redArg___closed__13);
v___x_150_ = l_Array_repr___at___00Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr_spec__0(v_parents_121_);
v___x_151_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_151_, 0, v___x_149_);
lean_ctor_set(v___x_151_, 1, v___x_150_);
v___x_152_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_152_, 0, v___x_151_);
lean_ctor_set_uint8(v___x_152_, sizeof(void*)*1, v___x_129_);
v___x_153_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_153_, 0, v___x_148_);
lean_ctor_set(v___x_153_, 1, v___x_152_);
v___x_154_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_154_, 0, v___x_153_);
lean_ctor_set(v___x_154_, 1, v___x_132_);
v___x_155_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_155_, 0, v___x_154_);
lean_ctor_set(v___x_155_, 1, v___x_134_);
v___x_156_ = ((lean_object*)(l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr___redArg___closed__15));
v___x_157_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_157_, 0, v___x_155_);
lean_ctor_set(v___x_157_, 1, v___x_156_);
v___x_158_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_158_, 0, v___x_157_);
lean_ctor_set(v___x_158_, 1, v___x_123_);
v___x_159_ = l_Array_repr___at___00Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr_spec__0(v_children_122_);
v___x_160_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_160_, 0, v___x_139_);
lean_ctor_set(v___x_160_, 1, v___x_159_);
v___x_161_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_161_, 0, v___x_160_);
lean_ctor_set_uint8(v___x_161_, sizeof(void*)*1, v___x_129_);
v___x_162_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_162_, 0, v___x_158_);
lean_ctor_set(v___x_162_, 1, v___x_161_);
v___x_163_ = lean_obj_once(&l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr___redArg___closed__18, &l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr___redArg___closed__18_once, _init_l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr___redArg___closed__18);
v___x_164_ = ((lean_object*)(l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr___redArg___closed__19));
v___x_165_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_165_, 0, v___x_164_);
lean_ctor_set(v___x_165_, 1, v___x_162_);
v___x_166_ = ((lean_object*)(l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr___redArg___closed__20));
v___x_167_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_167_, 0, v___x_165_);
lean_ctor_set(v___x_167_, 1, v___x_166_);
v___x_168_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_168_, 0, v___x_163_);
lean_ctor_set(v___x_168_, 1, v___x_167_);
v___x_169_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_169_, 0, v___x_168_);
lean_ctor_set_uint8(v___x_169_, sizeof(void*)*1, v___x_129_);
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr(lean_object* v_x_170_, lean_object* v_prec_171_){
_start:
{
lean_object* v___x_172_; 
v___x_172_ = l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr___redArg(v_x_170_);
return v___x_172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr___boxed(lean_object* v_x_173_, lean_object* v_prec_174_){
_start:
{
lean_object* v_res_175_; 
v_res_175_ = l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr(v_x_173_, v_prec_174_);
lean_dec(v_prec_174_);
return v_res_175_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Check_Impure_deadInfo___closed__1(void){
_start:
{
lean_object* v___x_180_; uint8_t v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_180_ = ((lean_object*)(l_Lean_Compiler_LCNF_Check_Impure_deadInfo___closed__0));
v___x_181_ = 0;
v___x_182_ = lean_unsigned_to_nat(0u);
v___x_183_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_183_, 0, v___x_182_);
lean_ctor_set(v___x_183_, 1, v___x_180_);
lean_ctor_set(v___x_183_, 2, v___x_180_);
lean_ctor_set_uint8(v___x_183_, sizeof(void*)*3, v___x_181_);
return v___x_183_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Check_Impure_deadInfo(void){
_start:
{
lean_object* v___x_184_; 
v___x_184_ = lean_obj_once(&l_Lean_Compiler_LCNF_Check_Impure_deadInfo___closed__1, &l_Lean_Compiler_LCNF_Check_Impure_deadInfo___closed__1_once, _init_l_Lean_Compiler_LCNF_Check_Impure_deadInfo___closed__1);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_Check_Impure_isDead_spec__0___redArg(lean_object* v_t_185_, lean_object* v_k_186_){
_start:
{
if (lean_obj_tag(v_t_185_) == 0)
{
lean_object* v_k_187_; lean_object* v_v_188_; lean_object* v_l_189_; lean_object* v_r_190_; uint8_t v___x_191_; 
v_k_187_ = lean_ctor_get(v_t_185_, 1);
v_v_188_ = lean_ctor_get(v_t_185_, 2);
v_l_189_ = lean_ctor_get(v_t_185_, 3);
v_r_190_ = lean_ctor_get(v_t_185_, 4);
v___x_191_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_186_, v_k_187_);
switch(v___x_191_)
{
case 0:
{
v_t_185_ = v_l_189_;
goto _start;
}
case 1:
{
lean_object* v___x_193_; 
lean_inc(v_v_188_);
v___x_193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_193_, 0, v_v_188_);
return v___x_193_;
}
default: 
{
v_t_185_ = v_r_190_;
goto _start;
}
}
}
else
{
lean_object* v___x_195_; 
v___x_195_ = lean_box(0);
return v___x_195_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_Check_Impure_isDead_spec__0___redArg___boxed(lean_object* v_t_196_, lean_object* v_k_197_){
_start:
{
lean_object* v_res_198_; 
v_res_198_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_Check_Impure_isDead_spec__0___redArg(v_t_196_, v_k_197_);
lean_dec(v_k_197_);
lean_dec(v_t_196_);
return v_res_198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Impure_isDead___redArg(lean_object* v_v_199_, lean_object* v_a_200_){
_start:
{
lean_object* v___x_202_; lean_object* v_rc_203_; lean_object* v___x_204_; 
v___x_202_ = lean_st_ref_get(v_a_200_);
v_rc_203_ = lean_ctor_get(v___x_202_, 0);
lean_inc(v_rc_203_);
lean_dec(v___x_202_);
v___x_204_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_Check_Impure_isDead_spec__0___redArg(v_rc_203_, v_v_199_);
lean_dec(v_rc_203_);
if (lean_obj_tag(v___x_204_) == 1)
{
lean_object* v_val_205_; lean_object* v___x_207_; uint8_t v_isShared_208_; uint8_t v_isSharedCheck_222_; 
v_val_205_ = lean_ctor_get(v___x_204_, 0);
v_isSharedCheck_222_ = !lean_is_exclusive(v___x_204_);
if (v_isSharedCheck_222_ == 0)
{
v___x_207_ = v___x_204_;
v_isShared_208_ = v_isSharedCheck_222_;
goto v_resetjp_206_;
}
else
{
lean_inc(v_val_205_);
lean_dec(v___x_204_);
v___x_207_ = lean_box(0);
v_isShared_208_ = v_isSharedCheck_222_;
goto v_resetjp_206_;
}
v_resetjp_206_:
{
uint8_t v_borrowed_209_; 
v_borrowed_209_ = lean_ctor_get_uint8(v_val_205_, sizeof(void*)*3);
if (v_borrowed_209_ == 0)
{
lean_object* v_rc_210_; lean_object* v___x_211_; uint8_t v___x_212_; lean_object* v___x_213_; lean_object* v___x_215_; 
v_rc_210_ = lean_ctor_get(v_val_205_, 0);
lean_inc(v_rc_210_);
lean_dec(v_val_205_);
v___x_211_ = lean_unsigned_to_nat(0u);
v___x_212_ = lean_nat_dec_eq(v_rc_210_, v___x_211_);
lean_dec(v_rc_210_);
v___x_213_ = lean_box(v___x_212_);
if (v_isShared_208_ == 0)
{
lean_ctor_set_tag(v___x_207_, 0);
lean_ctor_set(v___x_207_, 0, v___x_213_);
v___x_215_ = v___x_207_;
goto v_reusejp_214_;
}
else
{
lean_object* v_reuseFailAlloc_216_; 
v_reuseFailAlloc_216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_216_, 0, v___x_213_);
v___x_215_ = v_reuseFailAlloc_216_;
goto v_reusejp_214_;
}
v_reusejp_214_:
{
return v___x_215_;
}
}
else
{
uint8_t v___x_217_; lean_object* v___x_218_; lean_object* v___x_220_; 
lean_dec(v_val_205_);
v___x_217_ = 0;
v___x_218_ = lean_box(v___x_217_);
if (v_isShared_208_ == 0)
{
lean_ctor_set_tag(v___x_207_, 0);
lean_ctor_set(v___x_207_, 0, v___x_218_);
v___x_220_ = v___x_207_;
goto v_reusejp_219_;
}
else
{
lean_object* v_reuseFailAlloc_221_; 
v_reuseFailAlloc_221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_221_, 0, v___x_218_);
v___x_220_ = v_reuseFailAlloc_221_;
goto v_reusejp_219_;
}
v_reusejp_219_:
{
return v___x_220_;
}
}
}
}
else
{
uint8_t v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; 
lean_dec(v___x_204_);
v___x_223_ = 0;
v___x_224_ = lean_box(v___x_223_);
v___x_225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_225_, 0, v___x_224_);
return v___x_225_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Impure_isDead___redArg___boxed(lean_object* v_v_226_, lean_object* v_a_227_, lean_object* v_a_228_){
_start:
{
lean_object* v_res_229_; 
v_res_229_ = l_Lean_Compiler_LCNF_Check_Impure_isDead___redArg(v_v_226_, v_a_227_);
lean_dec(v_a_227_);
lean_dec(v_v_226_);
return v_res_229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Impure_isDead(lean_object* v_v_230_, lean_object* v_a_231_, lean_object* v_a_232_, lean_object* v_a_233_, lean_object* v_a_234_, lean_object* v_a_235_){
_start:
{
lean_object* v___x_237_; 
v___x_237_ = l_Lean_Compiler_LCNF_Check_Impure_isDead___redArg(v_v_230_, v_a_231_);
return v___x_237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Impure_isDead___boxed(lean_object* v_v_238_, lean_object* v_a_239_, lean_object* v_a_240_, lean_object* v_a_241_, lean_object* v_a_242_, lean_object* v_a_243_, lean_object* v_a_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l_Lean_Compiler_LCNF_Check_Impure_isDead(v_v_238_, v_a_239_, v_a_240_, v_a_241_, v_a_242_, v_a_243_);
lean_dec(v_a_243_);
lean_dec_ref(v_a_242_);
lean_dec(v_a_241_);
lean_dec_ref(v_a_240_);
lean_dec(v_a_239_);
lean_dec(v_v_238_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_Check_Impure_isDead_spec__0(lean_object* v_00_u03b4_246_, lean_object* v_t_247_, lean_object* v_k_248_){
_start:
{
lean_object* v___x_249_; 
v___x_249_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_Check_Impure_isDead_spec__0___redArg(v_t_247_, v_k_248_);
return v___x_249_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_Check_Impure_isDead_spec__0___boxed(lean_object* v_00_u03b4_250_, lean_object* v_t_251_, lean_object* v_k_252_){
_start:
{
lean_object* v_res_253_; 
v_res_253_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_Check_Impure_isDead_spec__0(v_00_u03b4_250_, v_t_251_, v_k_252_);
lean_dec(v_k_252_);
lean_dec(v_t_251_);
return v_res_253_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Check_Impure_maybeKill_spec__1___redArg(lean_object* v_as_254_, size_t v_i_255_, size_t v_stop_256_, lean_object* v___y_257_){
_start:
{
uint8_t v___x_259_; 
v___x_259_ = lean_usize_dec_eq(v_i_255_, v_stop_256_);
if (v___x_259_ == 0)
{
lean_object* v___x_260_; lean_object* v___x_261_; 
v___x_260_ = lean_array_uget_borrowed(v_as_254_, v_i_255_);
v___x_261_ = l_Lean_Compiler_LCNF_Check_Impure_isDead___redArg(v___x_260_, v___y_257_);
if (lean_obj_tag(v___x_261_) == 0)
{
lean_object* v_a_262_; lean_object* v___x_264_; uint8_t v_isShared_265_; uint8_t v_isSharedCheck_273_; 
v_a_262_ = lean_ctor_get(v___x_261_, 0);
v_isSharedCheck_273_ = !lean_is_exclusive(v___x_261_);
if (v_isSharedCheck_273_ == 0)
{
v___x_264_ = v___x_261_;
v_isShared_265_ = v_isSharedCheck_273_;
goto v_resetjp_263_;
}
else
{
lean_inc(v_a_262_);
lean_dec(v___x_261_);
v___x_264_ = lean_box(0);
v_isShared_265_ = v_isSharedCheck_273_;
goto v_resetjp_263_;
}
v_resetjp_263_:
{
uint8_t v___x_266_; 
v___x_266_ = lean_unbox(v_a_262_);
if (v___x_266_ == 0)
{
size_t v___x_267_; size_t v___x_268_; 
lean_del_object(v___x_264_);
lean_dec(v_a_262_);
v___x_267_ = ((size_t)1ULL);
v___x_268_ = lean_usize_add(v_i_255_, v___x_267_);
v_i_255_ = v___x_268_;
goto _start;
}
else
{
lean_object* v___x_271_; 
if (v_isShared_265_ == 0)
{
v___x_271_ = v___x_264_;
goto v_reusejp_270_;
}
else
{
lean_object* v_reuseFailAlloc_272_; 
v_reuseFailAlloc_272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_272_, 0, v_a_262_);
v___x_271_ = v_reuseFailAlloc_272_;
goto v_reusejp_270_;
}
v_reusejp_270_:
{
return v___x_271_;
}
}
}
}
else
{
return v___x_261_;
}
}
else
{
uint8_t v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_274_ = 0;
v___x_275_ = lean_box(v___x_274_);
v___x_276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_276_, 0, v___x_275_);
return v___x_276_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Check_Impure_maybeKill_spec__1___redArg___boxed(lean_object* v_as_277_, lean_object* v_i_278_, lean_object* v_stop_279_, lean_object* v___y_280_, lean_object* v___y_281_){
_start:
{
size_t v_i_boxed_282_; size_t v_stop_boxed_283_; lean_object* v_res_284_; 
v_i_boxed_282_ = lean_unbox_usize(v_i_278_);
lean_dec(v_i_278_);
v_stop_boxed_283_ = lean_unbox_usize(v_stop_279_);
lean_dec(v_stop_279_);
v_res_284_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Check_Impure_maybeKill_spec__1___redArg(v_as_277_, v_i_boxed_282_, v_stop_boxed_283_, v___y_280_);
lean_dec(v___y_280_);
lean_dec_ref(v_as_277_);
return v_res_284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Impure_maybeKill(lean_object* v_v_285_, lean_object* v_a_286_, lean_object* v_a_287_, lean_object* v_a_288_, lean_object* v_a_289_, lean_object* v_a_290_){
_start:
{
lean_object* v___x_295_; lean_object* v_rc_296_; lean_object* v___x_297_; 
v___x_295_ = lean_st_ref_get(v_a_286_);
v_rc_296_ = lean_ctor_get(v___x_295_, 0);
lean_inc(v_rc_296_);
lean_dec(v___x_295_);
v___x_297_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_Check_Impure_isDead_spec__0___redArg(v_rc_296_, v_v_285_);
lean_dec(v_rc_296_);
if (lean_obj_tag(v___x_297_) == 1)
{
lean_object* v_val_298_; lean_object* v___x_300_; uint8_t v_isShared_301_; uint8_t v_isSharedCheck_353_; 
v_val_298_ = lean_ctor_get(v___x_297_, 0);
v_isSharedCheck_353_ = !lean_is_exclusive(v___x_297_);
if (v_isSharedCheck_353_ == 0)
{
v___x_300_ = v___x_297_;
v_isShared_301_ = v_isSharedCheck_353_;
goto v_resetjp_299_;
}
else
{
lean_inc(v_val_298_);
lean_dec(v___x_297_);
v___x_300_ = lean_box(0);
v_isShared_301_ = v_isSharedCheck_353_;
goto v_resetjp_299_;
}
v_resetjp_299_:
{
lean_object* v_rc_302_; uint8_t v_borrowed_303_; lean_object* v_parents_304_; lean_object* v_children_305_; lean_object* v___x_332_; uint8_t v___x_333_; 
v_rc_302_ = lean_ctor_get(v_val_298_, 0);
lean_inc(v_rc_302_);
v_borrowed_303_ = lean_ctor_get_uint8(v_val_298_, sizeof(void*)*3);
v_parents_304_ = lean_ctor_get(v_val_298_, 1);
lean_inc_ref(v_parents_304_);
v_children_305_ = lean_ctor_get(v_val_298_, 2);
lean_inc_ref(v_children_305_);
lean_dec(v_val_298_);
v___x_332_ = lean_unsigned_to_nat(0u);
v___x_333_ = lean_nat_dec_lt(v___x_332_, v_rc_302_);
lean_dec(v_rc_302_);
if (v___x_333_ == 0)
{
lean_del_object(v___x_300_);
if (v_borrowed_303_ == 0)
{
lean_dec_ref(v_parents_304_);
goto v___jp_306_;
}
else
{
lean_object* v___x_334_; uint8_t v___x_335_; 
v___x_334_ = lean_array_get_size(v_parents_304_);
v___x_335_ = lean_nat_dec_lt(v___x_332_, v___x_334_);
if (v___x_335_ == 0)
{
lean_dec_ref(v_children_305_);
lean_dec_ref(v_parents_304_);
lean_dec(v_v_285_);
goto v___jp_292_;
}
else
{
if (v___x_335_ == 0)
{
lean_dec_ref(v_children_305_);
lean_dec_ref(v_parents_304_);
lean_dec(v_v_285_);
goto v___jp_292_;
}
else
{
size_t v___x_336_; size_t v___x_337_; lean_object* v___x_338_; 
v___x_336_ = ((size_t)0ULL);
v___x_337_ = lean_usize_of_nat(v___x_334_);
v___x_338_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Check_Impure_maybeKill_spec__1___redArg(v_parents_304_, v___x_336_, v___x_337_, v_a_286_);
lean_dec_ref(v_parents_304_);
if (lean_obj_tag(v___x_338_) == 0)
{
lean_object* v_a_339_; uint8_t v___x_340_; 
v_a_339_ = lean_ctor_get(v___x_338_, 0);
lean_inc(v_a_339_);
lean_dec_ref(v___x_338_);
v___x_340_ = lean_unbox(v_a_339_);
lean_dec(v_a_339_);
if (v___x_340_ == 0)
{
lean_dec_ref(v_children_305_);
lean_dec(v_v_285_);
goto v___jp_292_;
}
else
{
goto v___jp_306_;
}
}
else
{
lean_object* v_a_341_; lean_object* v___x_343_; uint8_t v_isShared_344_; uint8_t v_isSharedCheck_348_; 
lean_dec_ref(v_children_305_);
lean_dec(v_v_285_);
v_a_341_ = lean_ctor_get(v___x_338_, 0);
v_isSharedCheck_348_ = !lean_is_exclusive(v___x_338_);
if (v_isSharedCheck_348_ == 0)
{
v___x_343_ = v___x_338_;
v_isShared_344_ = v_isSharedCheck_348_;
goto v_resetjp_342_;
}
else
{
lean_inc(v_a_341_);
lean_dec(v___x_338_);
v___x_343_ = lean_box(0);
v_isShared_344_ = v_isSharedCheck_348_;
goto v_resetjp_342_;
}
v_resetjp_342_:
{
lean_object* v___x_346_; 
if (v_isShared_344_ == 0)
{
v___x_346_ = v___x_343_;
goto v_reusejp_345_;
}
else
{
lean_object* v_reuseFailAlloc_347_; 
v_reuseFailAlloc_347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_347_, 0, v_a_341_);
v___x_346_ = v_reuseFailAlloc_347_;
goto v_reusejp_345_;
}
v_reusejp_345_:
{
return v___x_346_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_349_; lean_object* v___x_351_; 
lean_dec_ref(v_children_305_);
lean_dec_ref(v_parents_304_);
lean_dec(v_v_285_);
v___x_349_ = lean_box(0);
if (v_isShared_301_ == 0)
{
lean_ctor_set_tag(v___x_300_, 0);
lean_ctor_set(v___x_300_, 0, v___x_349_);
v___x_351_ = v___x_300_;
goto v_reusejp_350_;
}
else
{
lean_object* v_reuseFailAlloc_352_; 
v_reuseFailAlloc_352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_352_, 0, v___x_349_);
v___x_351_ = v_reuseFailAlloc_352_;
goto v_reusejp_350_;
}
v_reusejp_350_:
{
return v___x_351_;
}
}
v___jp_306_:
{
lean_object* v___x_307_; lean_object* v_rc_308_; lean_object* v_subst_309_; lean_object* v___x_311_; uint8_t v_isShared_312_; uint8_t v_isSharedCheck_331_; 
v___x_307_ = lean_st_ref_take(v_a_286_);
v_rc_308_ = lean_ctor_get(v___x_307_, 0);
v_subst_309_ = lean_ctor_get(v___x_307_, 1);
v_isSharedCheck_331_ = !lean_is_exclusive(v___x_307_);
if (v_isSharedCheck_331_ == 0)
{
v___x_311_ = v___x_307_;
v_isShared_312_ = v_isSharedCheck_331_;
goto v_resetjp_310_;
}
else
{
lean_inc(v_subst_309_);
lean_inc(v_rc_308_);
lean_dec(v___x_307_);
v___x_311_ = lean_box(0);
v_isShared_312_ = v_isSharedCheck_331_;
goto v_resetjp_310_;
}
v_resetjp_310_:
{
lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_316_; 
v___x_313_ = l_Lean_Compiler_LCNF_Check_Impure_deadInfo;
v___x_314_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_v_285_, v___x_313_, v_rc_308_);
if (v_isShared_312_ == 0)
{
lean_ctor_set(v___x_311_, 0, v___x_314_);
v___x_316_ = v___x_311_;
goto v_reusejp_315_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v___x_314_);
lean_ctor_set(v_reuseFailAlloc_330_, 1, v_subst_309_);
v___x_316_ = v_reuseFailAlloc_330_;
goto v_reusejp_315_;
}
v_reusejp_315_:
{
lean_object* v___x_317_; lean_object* v___x_318_; size_t v_sz_319_; size_t v___x_320_; lean_object* v___x_321_; 
v___x_317_ = lean_st_ref_set(v_a_286_, v___x_316_);
v___x_318_ = lean_box(0);
v_sz_319_ = lean_array_size(v_children_305_);
v___x_320_ = ((size_t)0ULL);
v___x_321_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Impure_maybeKill_spec__0(v_children_305_, v_sz_319_, v___x_320_, v___x_318_, v_a_286_, v_a_287_, v_a_288_, v_a_289_, v_a_290_);
lean_dec_ref(v_children_305_);
if (lean_obj_tag(v___x_321_) == 0)
{
lean_object* v___x_323_; uint8_t v_isShared_324_; uint8_t v_isSharedCheck_328_; 
v_isSharedCheck_328_ = !lean_is_exclusive(v___x_321_);
if (v_isSharedCheck_328_ == 0)
{
lean_object* v_unused_329_; 
v_unused_329_ = lean_ctor_get(v___x_321_, 0);
lean_dec(v_unused_329_);
v___x_323_ = v___x_321_;
v_isShared_324_ = v_isSharedCheck_328_;
goto v_resetjp_322_;
}
else
{
lean_dec(v___x_321_);
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_328_;
goto v_resetjp_322_;
}
v_resetjp_322_:
{
lean_object* v___x_326_; 
if (v_isShared_324_ == 0)
{
lean_ctor_set(v___x_323_, 0, v___x_318_);
v___x_326_ = v___x_323_;
goto v_reusejp_325_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v___x_318_);
v___x_326_ = v_reuseFailAlloc_327_;
goto v_reusejp_325_;
}
v_reusejp_325_:
{
return v___x_326_;
}
}
}
else
{
return v___x_321_;
}
}
}
}
}
}
else
{
lean_object* v___x_354_; lean_object* v___x_355_; 
lean_dec(v___x_297_);
lean_dec(v_v_285_);
v___x_354_ = lean_box(0);
v___x_355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_355_, 0, v___x_354_);
return v___x_355_;
}
v___jp_292_:
{
lean_object* v___x_293_; lean_object* v___x_294_; 
v___x_293_ = lean_box(0);
v___x_294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_294_, 0, v___x_293_);
return v___x_294_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Impure_maybeKill_spec__0(lean_object* v_as_356_, size_t v_sz_357_, size_t v_i_358_, lean_object* v_b_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_){
_start:
{
uint8_t v___x_366_; 
v___x_366_ = lean_usize_dec_lt(v_i_358_, v_sz_357_);
if (v___x_366_ == 0)
{
lean_object* v___x_367_; 
v___x_367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_367_, 0, v_b_359_);
return v___x_367_;
}
else
{
lean_object* v_a_368_; lean_object* v___x_369_; 
v_a_368_ = lean_array_uget_borrowed(v_as_356_, v_i_358_);
lean_inc(v_a_368_);
v___x_369_ = l_Lean_Compiler_LCNF_Check_Impure_maybeKill(v_a_368_, v___y_360_, v___y_361_, v___y_362_, v___y_363_, v___y_364_);
if (lean_obj_tag(v___x_369_) == 0)
{
lean_object* v___x_370_; size_t v___x_371_; size_t v___x_372_; 
lean_dec_ref(v___x_369_);
v___x_370_ = lean_box(0);
v___x_371_ = ((size_t)1ULL);
v___x_372_ = lean_usize_add(v_i_358_, v___x_371_);
v_i_358_ = v___x_372_;
v_b_359_ = v___x_370_;
goto _start;
}
else
{
return v___x_369_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Impure_maybeKill_spec__0___boxed(lean_object* v_as_374_, lean_object* v_sz_375_, lean_object* v_i_376_, lean_object* v_b_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_){
_start:
{
size_t v_sz_boxed_384_; size_t v_i_boxed_385_; lean_object* v_res_386_; 
v_sz_boxed_384_ = lean_unbox_usize(v_sz_375_);
lean_dec(v_sz_375_);
v_i_boxed_385_ = lean_unbox_usize(v_i_376_);
lean_dec(v_i_376_);
v_res_386_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Impure_maybeKill_spec__0(v_as_374_, v_sz_boxed_384_, v_i_boxed_385_, v_b_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_);
lean_dec(v___y_382_);
lean_dec_ref(v___y_381_);
lean_dec(v___y_380_);
lean_dec_ref(v___y_379_);
lean_dec(v___y_378_);
lean_dec_ref(v_as_374_);
return v_res_386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Impure_maybeKill___boxed(lean_object* v_v_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_, lean_object* v_a_393_){
_start:
{
lean_object* v_res_394_; 
v_res_394_ = l_Lean_Compiler_LCNF_Check_Impure_maybeKill(v_v_387_, v_a_388_, v_a_389_, v_a_390_, v_a_391_, v_a_392_);
lean_dec(v_a_392_);
lean_dec_ref(v_a_391_);
lean_dec(v_a_390_);
lean_dec_ref(v_a_389_);
lean_dec(v_a_388_);
return v_res_394_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Check_Impure_maybeKill_spec__1(lean_object* v_as_395_, size_t v_i_396_, size_t v_stop_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_){
_start:
{
lean_object* v___x_404_; 
v___x_404_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Check_Impure_maybeKill_spec__1___redArg(v_as_395_, v_i_396_, v_stop_397_, v___y_398_);
return v___x_404_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Check_Impure_maybeKill_spec__1___boxed(lean_object* v_as_405_, lean_object* v_i_406_, lean_object* v_stop_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_){
_start:
{
size_t v_i_boxed_414_; size_t v_stop_boxed_415_; lean_object* v_res_416_; 
v_i_boxed_414_ = lean_unbox_usize(v_i_406_);
lean_dec(v_i_406_);
v_stop_boxed_415_ = lean_unbox_usize(v_stop_407_);
lean_dec(v_stop_407_);
v_res_416_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Check_Impure_maybeKill_spec__1(v_as_405_, v_i_boxed_414_, v_stop_boxed_415_, v___y_408_, v___y_409_, v___y_410_, v___y_411_, v___y_412_);
lean_dec(v___y_412_);
lean_dec_ref(v___y_411_);
lean_dec(v___y_410_);
lean_dec_ref(v___y_409_);
lean_dec(v___y_408_);
lean_dec_ref(v_as_405_);
return v_res_416_;
}
}
static lean_object* _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Impure_kill_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_417_; 
v___x_417_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_417_;
}
}
static lean_object* _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Impure_kill_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_418_; lean_object* v___x_419_; 
v___x_418_ = lean_obj_once(&l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Impure_kill_spec__1___redArg___closed__0, &l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Impure_kill_spec__1___redArg___closed__0_once, _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Impure_kill_spec__1___redArg___closed__0);
v___x_419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_419_, 0, v___x_418_);
return v___x_419_;
}
}
static lean_object* _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Impure_kill_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_420_ = lean_obj_once(&l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Impure_kill_spec__1___redArg___closed__1, &l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Impure_kill_spec__1___redArg___closed__1_once, _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Impure_kill_spec__1___redArg___closed__1);
v___x_421_ = lean_unsigned_to_nat(0u);
v___x_422_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_422_, 0, v___x_421_);
lean_ctor_set(v___x_422_, 1, v___x_421_);
lean_ctor_set(v___x_422_, 2, v___x_421_);
lean_ctor_set(v___x_422_, 3, v___x_420_);
lean_ctor_set(v___x_422_, 4, v___x_420_);
lean_ctor_set(v___x_422_, 5, v___x_420_);
lean_ctor_set(v___x_422_, 6, v___x_420_);
lean_ctor_set(v___x_422_, 7, v___x_420_);
lean_ctor_set(v___x_422_, 8, v___x_420_);
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Impure_kill_spec__1___redArg(lean_object* v_msg_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_){
_start:
{
lean_object* v_options_429_; lean_object* v_ref_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; 
v_options_429_ = lean_ctor_get(v___y_426_, 2);
v_ref_430_ = lean_ctor_get(v___y_426_, 5);
v___x_431_ = lean_st_ref_get(v___y_427_);
v___x_432_ = lean_st_ref_get(v___y_425_);
v___x_433_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_424_);
if (lean_obj_tag(v___x_433_) == 0)
{
lean_object* v_a_434_; lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_456_; 
v_a_434_ = lean_ctor_get(v___x_433_, 0);
v_isSharedCheck_456_ = !lean_is_exclusive(v___x_433_);
if (v_isSharedCheck_456_ == 0)
{
v___x_436_ = v___x_433_;
v_isShared_437_ = v_isSharedCheck_456_;
goto v_resetjp_435_;
}
else
{
lean_inc(v_a_434_);
lean_dec(v___x_433_);
v___x_436_ = lean_box(0);
v_isShared_437_ = v_isSharedCheck_456_;
goto v_resetjp_435_;
}
v_resetjp_435_:
{
lean_object* v_env_438_; lean_object* v_lctx_439_; lean_object* v___x_441_; uint8_t v_isShared_442_; uint8_t v_isSharedCheck_454_; 
v_env_438_ = lean_ctor_get(v___x_431_, 0);
lean_inc_ref(v_env_438_);
lean_dec(v___x_431_);
v_lctx_439_ = lean_ctor_get(v___x_432_, 0);
v_isSharedCheck_454_ = !lean_is_exclusive(v___x_432_);
if (v_isSharedCheck_454_ == 0)
{
lean_object* v_unused_455_; 
v_unused_455_ = lean_ctor_get(v___x_432_, 1);
lean_dec(v_unused_455_);
v___x_441_ = v___x_432_;
v_isShared_442_ = v_isSharedCheck_454_;
goto v_resetjp_440_;
}
else
{
lean_inc(v_lctx_439_);
lean_dec(v___x_432_);
v___x_441_ = lean_box(0);
v_isShared_442_ = v_isSharedCheck_454_;
goto v_resetjp_440_;
}
v_resetjp_440_:
{
uint8_t v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_448_; 
v___x_443_ = lean_unbox(v_a_434_);
lean_dec(v_a_434_);
v___x_444_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_439_, v___x_443_);
lean_dec_ref(v_lctx_439_);
v___x_445_ = lean_obj_once(&l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Impure_kill_spec__1___redArg___closed__2, &l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Impure_kill_spec__1___redArg___closed__2_once, _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Impure_kill_spec__1___redArg___closed__2);
lean_inc_ref(v_options_429_);
v___x_446_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_446_, 0, v_env_438_);
lean_ctor_set(v___x_446_, 1, v___x_445_);
lean_ctor_set(v___x_446_, 2, v___x_444_);
lean_ctor_set(v___x_446_, 3, v_options_429_);
if (v_isShared_442_ == 0)
{
lean_ctor_set_tag(v___x_441_, 3);
lean_ctor_set(v___x_441_, 1, v_msg_423_);
lean_ctor_set(v___x_441_, 0, v___x_446_);
v___x_448_ = v___x_441_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v___x_446_);
lean_ctor_set(v_reuseFailAlloc_453_, 1, v_msg_423_);
v___x_448_ = v_reuseFailAlloc_453_;
goto v_reusejp_447_;
}
v_reusejp_447_:
{
lean_object* v___x_449_; lean_object* v___x_451_; 
lean_inc(v_ref_430_);
v___x_449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_449_, 0, v_ref_430_);
lean_ctor_set(v___x_449_, 1, v___x_448_);
if (v_isShared_437_ == 0)
{
lean_ctor_set_tag(v___x_436_, 1);
lean_ctor_set(v___x_436_, 0, v___x_449_);
v___x_451_ = v___x_436_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v___x_449_);
v___x_451_ = v_reuseFailAlloc_452_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
return v___x_451_;
}
}
}
}
}
else
{
lean_object* v_a_457_; lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_464_; 
lean_dec(v___x_432_);
lean_dec(v___x_431_);
lean_dec_ref(v_msg_423_);
v_a_457_ = lean_ctor_get(v___x_433_, 0);
v_isSharedCheck_464_ = !lean_is_exclusive(v___x_433_);
if (v_isSharedCheck_464_ == 0)
{
v___x_459_ = v___x_433_;
v_isShared_460_ = v_isSharedCheck_464_;
goto v_resetjp_458_;
}
else
{
lean_inc(v_a_457_);
lean_dec(v___x_433_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_464_;
goto v_resetjp_458_;
}
v_resetjp_458_:
{
lean_object* v___x_462_; 
if (v_isShared_460_ == 0)
{
v___x_462_ = v___x_459_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v_a_457_);
v___x_462_ = v_reuseFailAlloc_463_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
return v___x_462_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Impure_kill_spec__1___redArg___boxed(lean_object* v_msg_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_){
_start:
{
lean_object* v_res_471_; 
v_res_471_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Impure_kill_spec__1___redArg(v_msg_465_, v___y_466_, v___y_467_, v___y_468_, v___y_469_);
lean_dec(v___y_469_);
lean_dec_ref(v___y_468_);
lean_dec(v___y_467_);
lean_dec_ref(v___y_466_);
return v_res_471_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Impure_kill_spec__1(lean_object* v_00_u03b1_472_, lean_object* v_msg_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_){
_start:
{
lean_object* v___x_480_; 
v___x_480_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Impure_kill_spec__1___redArg(v_msg_473_, v___y_475_, v___y_476_, v___y_477_, v___y_478_);
return v___x_480_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Impure_kill_spec__1___boxed(lean_object* v_00_u03b1_481_, lean_object* v_msg_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_){
_start:
{
lean_object* v_res_489_; 
v_res_489_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Impure_kill_spec__1(v_00_u03b1_481_, v_msg_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_);
lean_dec(v___y_487_);
lean_dec_ref(v___y_486_);
lean_dec(v___y_485_);
lean_dec_ref(v___y_484_);
lean_dec(v___y_483_);
return v_res_489_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_Check_Impure_kill_spec__0_spec__0___redArg(lean_object* v_a_490_, lean_object* v_fallback_491_, lean_object* v_x_492_){
_start:
{
if (lean_obj_tag(v_x_492_) == 0)
{
lean_inc(v_fallback_491_);
return v_fallback_491_;
}
else
{
lean_object* v_key_493_; lean_object* v_value_494_; lean_object* v_tail_495_; uint8_t v___x_496_; 
v_key_493_ = lean_ctor_get(v_x_492_, 0);
v_value_494_ = lean_ctor_get(v_x_492_, 1);
v_tail_495_ = lean_ctor_get(v_x_492_, 2);
v___x_496_ = l_Lean_instBEqFVarId_beq(v_key_493_, v_a_490_);
if (v___x_496_ == 0)
{
v_x_492_ = v_tail_495_;
goto _start;
}
else
{
lean_inc(v_value_494_);
return v_value_494_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_Check_Impure_kill_spec__0_spec__0___redArg___boxed(lean_object* v_a_498_, lean_object* v_fallback_499_, lean_object* v_x_500_){
_start:
{
lean_object* v_res_501_; 
v_res_501_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_Check_Impure_kill_spec__0_spec__0___redArg(v_a_498_, v_fallback_499_, v_x_500_);
lean_dec(v_x_500_);
lean_dec(v_fallback_499_);
lean_dec(v_a_498_);
return v_res_501_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_Check_Impure_kill_spec__0___redArg(lean_object* v_m_502_, lean_object* v_a_503_, lean_object* v_fallback_504_){
_start:
{
lean_object* v_buckets_505_; lean_object* v___x_506_; uint64_t v___x_507_; uint64_t v___x_508_; uint64_t v___x_509_; uint64_t v_fold_510_; uint64_t v___x_511_; uint64_t v___x_512_; uint64_t v___x_513_; size_t v___x_514_; size_t v___x_515_; size_t v___x_516_; size_t v___x_517_; size_t v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; 
v_buckets_505_ = lean_ctor_get(v_m_502_, 1);
v___x_506_ = lean_array_get_size(v_buckets_505_);
v___x_507_ = l_Lean_instHashableFVarId_hash(v_a_503_);
v___x_508_ = 32ULL;
v___x_509_ = lean_uint64_shift_right(v___x_507_, v___x_508_);
v_fold_510_ = lean_uint64_xor(v___x_507_, v___x_509_);
v___x_511_ = 16ULL;
v___x_512_ = lean_uint64_shift_right(v_fold_510_, v___x_511_);
v___x_513_ = lean_uint64_xor(v_fold_510_, v___x_512_);
v___x_514_ = lean_uint64_to_usize(v___x_513_);
v___x_515_ = lean_usize_of_nat(v___x_506_);
v___x_516_ = ((size_t)1ULL);
v___x_517_ = lean_usize_sub(v___x_515_, v___x_516_);
v___x_518_ = lean_usize_land(v___x_514_, v___x_517_);
v___x_519_ = lean_array_uget_borrowed(v_buckets_505_, v___x_518_);
v___x_520_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_Check_Impure_kill_spec__0_spec__0___redArg(v_a_503_, v_fallback_504_, v___x_519_);
return v___x_520_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_Check_Impure_kill_spec__0___redArg___boxed(lean_object* v_m_521_, lean_object* v_a_522_, lean_object* v_fallback_523_){
_start:
{
lean_object* v_res_524_; 
v_res_524_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_Check_Impure_kill_spec__0___redArg(v_m_521_, v_a_522_, v_fallback_523_);
lean_dec(v_fallback_523_);
lean_dec(v_a_522_);
lean_dec_ref(v_m_521_);
return v_res_524_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Check_Impure_kill___closed__1(void){
_start:
{
lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_526_ = ((lean_object*)(l_Lean_Compiler_LCNF_Check_Impure_kill___closed__0));
v___x_527_ = l_Lean_stringToMessageData(v___x_526_);
return v___x_527_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Check_Impure_kill___closed__3(void){
_start:
{
lean_object* v___x_529_; lean_object* v___x_530_; 
v___x_529_ = ((lean_object*)(l_Lean_Compiler_LCNF_Check_Impure_kill___closed__2));
v___x_530_ = l_Lean_stringToMessageData(v___x_529_);
return v___x_530_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Check_Impure_kill___closed__5(void){
_start:
{
lean_object* v___x_532_; lean_object* v___x_533_; 
v___x_532_ = ((lean_object*)(l_Lean_Compiler_LCNF_Check_Impure_kill___closed__4));
v___x_533_ = l_Lean_stringToMessageData(v___x_532_);
return v___x_533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Impure_kill(lean_object* v_v_534_, lean_object* v_a_535_, lean_object* v_a_536_, lean_object* v_a_537_, lean_object* v_a_538_, lean_object* v_a_539_){
_start:
{
lean_object* v___x_541_; lean_object* v_subst_542_; lean_object* v___x_543_; lean_object* v___x_544_; 
v___x_541_ = lean_st_ref_get(v_a_535_);
v_subst_542_ = lean_ctor_get(v___x_541_, 1);
lean_inc_ref(v_subst_542_);
lean_dec(v___x_541_);
lean_inc(v_v_534_);
v___x_543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_543_, 0, v_v_534_);
v___x_544_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_Check_Impure_kill_spec__0___redArg(v_subst_542_, v_v_534_, v___x_543_);
lean_dec_ref(v___x_543_);
lean_dec(v_v_534_);
lean_dec_ref(v_subst_542_);
if (lean_obj_tag(v___x_544_) == 1)
{
lean_object* v_fvarId_545_; lean_object* v___x_546_; lean_object* v_rc_547_; lean_object* v___x_548_; 
v_fvarId_545_ = lean_ctor_get(v___x_544_, 0);
lean_inc(v_fvarId_545_);
lean_dec_ref(v___x_544_);
v___x_546_ = lean_st_ref_get(v_a_535_);
v_rc_547_ = lean_ctor_get(v___x_546_, 0);
lean_inc(v_rc_547_);
lean_dec(v___x_546_);
v___x_548_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_Check_Impure_isDead_spec__0___redArg(v_rc_547_, v_fvarId_545_);
lean_dec(v_rc_547_);
if (lean_obj_tag(v___x_548_) == 1)
{
lean_object* v_val_549_; uint8_t v_borrowed_550_; lean_object* v_children_551_; lean_object* v___y_553_; lean_object* v___y_554_; lean_object* v___y_555_; lean_object* v___y_556_; lean_object* v___y_557_; 
v_val_549_ = lean_ctor_get(v___x_548_, 0);
lean_inc(v_val_549_);
lean_dec_ref(v___x_548_);
v_borrowed_550_ = lean_ctor_get_uint8(v_val_549_, sizeof(void*)*3);
v_children_551_ = lean_ctor_get(v_val_549_, 2);
lean_inc_ref(v_children_551_);
lean_dec(v_val_549_);
if (v_borrowed_550_ == 0)
{
v___y_553_ = v_a_535_;
v___y_554_ = v_a_536_;
v___y_555_ = v_a_537_;
v___y_556_ = v_a_538_;
v___y_557_ = v_a_539_;
goto v___jp_552_;
}
else
{
lean_object* v___x_583_; lean_object* v___x_584_; 
lean_dec_ref(v_children_551_);
lean_dec(v_fvarId_545_);
v___x_583_ = lean_obj_once(&l_Lean_Compiler_LCNF_Check_Impure_kill___closed__1, &l_Lean_Compiler_LCNF_Check_Impure_kill___closed__1_once, _init_l_Lean_Compiler_LCNF_Check_Impure_kill___closed__1);
v___x_584_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Impure_kill_spec__1___redArg(v___x_583_, v_a_536_, v_a_537_, v_a_538_, v_a_539_);
return v___x_584_;
}
v___jp_552_:
{
lean_object* v___x_558_; lean_object* v_rc_559_; lean_object* v_subst_560_; lean_object* v___x_562_; uint8_t v_isShared_563_; uint8_t v_isSharedCheck_582_; 
v___x_558_ = lean_st_ref_take(v___y_553_);
v_rc_559_ = lean_ctor_get(v___x_558_, 0);
v_subst_560_ = lean_ctor_get(v___x_558_, 1);
v_isSharedCheck_582_ = !lean_is_exclusive(v___x_558_);
if (v_isSharedCheck_582_ == 0)
{
v___x_562_ = v___x_558_;
v_isShared_563_ = v_isSharedCheck_582_;
goto v_resetjp_561_;
}
else
{
lean_inc(v_subst_560_);
lean_inc(v_rc_559_);
lean_dec(v___x_558_);
v___x_562_ = lean_box(0);
v_isShared_563_ = v_isSharedCheck_582_;
goto v_resetjp_561_;
}
v_resetjp_561_:
{
lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_567_; 
v___x_564_ = l_Lean_Compiler_LCNF_Check_Impure_deadInfo;
v___x_565_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_545_, v___x_564_, v_rc_559_);
if (v_isShared_563_ == 0)
{
lean_ctor_set(v___x_562_, 0, v___x_565_);
v___x_567_ = v___x_562_;
goto v_reusejp_566_;
}
else
{
lean_object* v_reuseFailAlloc_581_; 
v_reuseFailAlloc_581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_581_, 0, v___x_565_);
lean_ctor_set(v_reuseFailAlloc_581_, 1, v_subst_560_);
v___x_567_ = v_reuseFailAlloc_581_;
goto v_reusejp_566_;
}
v_reusejp_566_:
{
lean_object* v___x_568_; lean_object* v___x_569_; size_t v_sz_570_; size_t v___x_571_; lean_object* v___x_572_; 
v___x_568_ = lean_st_ref_set(v___y_553_, v___x_567_);
v___x_569_ = lean_box(0);
v_sz_570_ = lean_array_size(v_children_551_);
v___x_571_ = ((size_t)0ULL);
v___x_572_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Impure_maybeKill_spec__0(v_children_551_, v_sz_570_, v___x_571_, v___x_569_, v___y_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_);
lean_dec_ref(v_children_551_);
if (lean_obj_tag(v___x_572_) == 0)
{
lean_object* v___x_574_; uint8_t v_isShared_575_; uint8_t v_isSharedCheck_579_; 
v_isSharedCheck_579_ = !lean_is_exclusive(v___x_572_);
if (v_isSharedCheck_579_ == 0)
{
lean_object* v_unused_580_; 
v_unused_580_ = lean_ctor_get(v___x_572_, 0);
lean_dec(v_unused_580_);
v___x_574_ = v___x_572_;
v_isShared_575_ = v_isSharedCheck_579_;
goto v_resetjp_573_;
}
else
{
lean_dec(v___x_572_);
v___x_574_ = lean_box(0);
v_isShared_575_ = v_isSharedCheck_579_;
goto v_resetjp_573_;
}
v_resetjp_573_:
{
lean_object* v___x_577_; 
if (v_isShared_575_ == 0)
{
lean_ctor_set(v___x_574_, 0, v___x_569_);
v___x_577_ = v___x_574_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v___x_569_);
v___x_577_ = v_reuseFailAlloc_578_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
return v___x_577_;
}
}
}
else
{
return v___x_572_;
}
}
}
}
}
else
{
lean_object* v___x_585_; lean_object* v___x_586_; 
lean_dec(v___x_548_);
lean_dec(v_fvarId_545_);
v___x_585_ = lean_obj_once(&l_Lean_Compiler_LCNF_Check_Impure_kill___closed__3, &l_Lean_Compiler_LCNF_Check_Impure_kill___closed__3_once, _init_l_Lean_Compiler_LCNF_Check_Impure_kill___closed__3);
v___x_586_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Impure_kill_spec__1___redArg(v___x_585_, v_a_536_, v_a_537_, v_a_538_, v_a_539_);
return v___x_586_;
}
}
else
{
lean_object* v___x_587_; lean_object* v___x_588_; 
lean_dec(v___x_544_);
v___x_587_ = lean_obj_once(&l_Lean_Compiler_LCNF_Check_Impure_kill___closed__5, &l_Lean_Compiler_LCNF_Check_Impure_kill___closed__5_once, _init_l_Lean_Compiler_LCNF_Check_Impure_kill___closed__5);
v___x_588_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Impure_kill_spec__1___redArg(v___x_587_, v_a_536_, v_a_537_, v_a_538_, v_a_539_);
return v___x_588_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Impure_kill___boxed(lean_object* v_v_589_, lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_, lean_object* v_a_593_, lean_object* v_a_594_, lean_object* v_a_595_){
_start:
{
lean_object* v_res_596_; 
v_res_596_ = l_Lean_Compiler_LCNF_Check_Impure_kill(v_v_589_, v_a_590_, v_a_591_, v_a_592_, v_a_593_, v_a_594_);
lean_dec(v_a_594_);
lean_dec_ref(v_a_593_);
lean_dec(v_a_592_);
lean_dec_ref(v_a_591_);
lean_dec(v_a_590_);
return v_res_596_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_Check_Impure_kill_spec__0(lean_object* v_00_u03b2_597_, lean_object* v_m_598_, lean_object* v_a_599_, lean_object* v_fallback_600_){
_start:
{
lean_object* v___x_601_; 
v___x_601_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_Check_Impure_kill_spec__0___redArg(v_m_598_, v_a_599_, v_fallback_600_);
return v___x_601_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_Check_Impure_kill_spec__0___boxed(lean_object* v_00_u03b2_602_, lean_object* v_m_603_, lean_object* v_a_604_, lean_object* v_fallback_605_){
_start:
{
lean_object* v_res_606_; 
v_res_606_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_Check_Impure_kill_spec__0(v_00_u03b2_602_, v_m_603_, v_a_604_, v_fallback_605_);
lean_dec(v_fallback_605_);
lean_dec(v_a_604_);
lean_dec_ref(v_m_603_);
return v_res_606_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_Check_Impure_kill_spec__0_spec__0(lean_object* v_00_u03b2_607_, lean_object* v_a_608_, lean_object* v_fallback_609_, lean_object* v_x_610_){
_start:
{
lean_object* v___x_611_; 
v___x_611_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_Check_Impure_kill_spec__0_spec__0___redArg(v_a_608_, v_fallback_609_, v_x_610_);
return v___x_611_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_Check_Impure_kill_spec__0_spec__0___boxed(lean_object* v_00_u03b2_612_, lean_object* v_a_613_, lean_object* v_fallback_614_, lean_object* v_x_615_){
_start:
{
lean_object* v_res_616_; 
v_res_616_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_Check_Impure_kill_spec__0_spec__0(v_00_u03b2_612_, v_a_613_, v_fallback_614_, v_x_615_);
lean_dec(v_x_615_);
lean_dec(v_fallback_614_);
lean_dec(v_a_613_);
return v_res_616_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Compiler_LCNF_Check_Impure_makeScalar_spec__0___redArg(lean_object* v_k_617_, lean_object* v_t_618_){
_start:
{
if (lean_obj_tag(v_t_618_) == 0)
{
lean_object* v_k_619_; lean_object* v_v_620_; lean_object* v_l_621_; lean_object* v_r_622_; lean_object* v___x_624_; uint8_t v_isShared_625_; uint8_t v_isSharedCheck_1276_; 
v_k_619_ = lean_ctor_get(v_t_618_, 1);
v_v_620_ = lean_ctor_get(v_t_618_, 2);
v_l_621_ = lean_ctor_get(v_t_618_, 3);
v_r_622_ = lean_ctor_get(v_t_618_, 4);
v_isSharedCheck_1276_ = !lean_is_exclusive(v_t_618_);
if (v_isSharedCheck_1276_ == 0)
{
lean_object* v_unused_1277_; 
v_unused_1277_ = lean_ctor_get(v_t_618_, 0);
lean_dec(v_unused_1277_);
v___x_624_ = v_t_618_;
v_isShared_625_ = v_isSharedCheck_1276_;
goto v_resetjp_623_;
}
else
{
lean_inc(v_r_622_);
lean_inc(v_l_621_);
lean_inc(v_v_620_);
lean_inc(v_k_619_);
lean_dec(v_t_618_);
v___x_624_ = lean_box(0);
v_isShared_625_ = v_isSharedCheck_1276_;
goto v_resetjp_623_;
}
v_resetjp_623_:
{
uint8_t v___x_626_; 
v___x_626_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_617_, v_k_619_);
switch(v___x_626_)
{
case 0:
{
lean_object* v_impl_627_; lean_object* v___x_628_; 
v_impl_627_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Compiler_LCNF_Check_Impure_makeScalar_spec__0___redArg(v_k_617_, v_l_621_);
v___x_628_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_627_) == 0)
{
if (lean_obj_tag(v_r_622_) == 0)
{
lean_object* v_size_629_; lean_object* v_size_630_; lean_object* v_k_631_; lean_object* v_v_632_; lean_object* v_l_633_; lean_object* v_r_634_; lean_object* v___x_635_; lean_object* v___x_636_; uint8_t v___x_637_; 
v_size_629_ = lean_ctor_get(v_impl_627_, 0);
lean_inc(v_size_629_);
v_size_630_ = lean_ctor_get(v_r_622_, 0);
v_k_631_ = lean_ctor_get(v_r_622_, 1);
v_v_632_ = lean_ctor_get(v_r_622_, 2);
v_l_633_ = lean_ctor_get(v_r_622_, 3);
lean_inc(v_l_633_);
v_r_634_ = lean_ctor_get(v_r_622_, 4);
v___x_635_ = lean_unsigned_to_nat(3u);
v___x_636_ = lean_nat_mul(v___x_635_, v_size_629_);
v___x_637_ = lean_nat_dec_lt(v___x_636_, v_size_630_);
lean_dec(v___x_636_);
if (v___x_637_ == 0)
{
lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_641_; 
lean_dec(v_l_633_);
v___x_638_ = lean_nat_add(v___x_628_, v_size_629_);
lean_dec(v_size_629_);
v___x_639_ = lean_nat_add(v___x_638_, v_size_630_);
lean_dec(v___x_638_);
if (v_isShared_625_ == 0)
{
lean_ctor_set(v___x_624_, 3, v_impl_627_);
lean_ctor_set(v___x_624_, 0, v___x_639_);
v___x_641_ = v___x_624_;
goto v_reusejp_640_;
}
else
{
lean_object* v_reuseFailAlloc_642_; 
v_reuseFailAlloc_642_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_642_, 0, v___x_639_);
lean_ctor_set(v_reuseFailAlloc_642_, 1, v_k_619_);
lean_ctor_set(v_reuseFailAlloc_642_, 2, v_v_620_);
lean_ctor_set(v_reuseFailAlloc_642_, 3, v_impl_627_);
lean_ctor_set(v_reuseFailAlloc_642_, 4, v_r_622_);
v___x_641_ = v_reuseFailAlloc_642_;
goto v_reusejp_640_;
}
v_reusejp_640_:
{
return v___x_641_;
}
}
else
{
lean_object* v___x_644_; uint8_t v_isShared_645_; uint8_t v_isSharedCheck_706_; 
lean_inc(v_r_634_);
lean_inc(v_v_632_);
lean_inc(v_k_631_);
lean_inc(v_size_630_);
v_isSharedCheck_706_ = !lean_is_exclusive(v_r_622_);
if (v_isSharedCheck_706_ == 0)
{
lean_object* v_unused_707_; lean_object* v_unused_708_; lean_object* v_unused_709_; lean_object* v_unused_710_; lean_object* v_unused_711_; 
v_unused_707_ = lean_ctor_get(v_r_622_, 4);
lean_dec(v_unused_707_);
v_unused_708_ = lean_ctor_get(v_r_622_, 3);
lean_dec(v_unused_708_);
v_unused_709_ = lean_ctor_get(v_r_622_, 2);
lean_dec(v_unused_709_);
v_unused_710_ = lean_ctor_get(v_r_622_, 1);
lean_dec(v_unused_710_);
v_unused_711_ = lean_ctor_get(v_r_622_, 0);
lean_dec(v_unused_711_);
v___x_644_ = v_r_622_;
v_isShared_645_ = v_isSharedCheck_706_;
goto v_resetjp_643_;
}
else
{
lean_dec(v_r_622_);
v___x_644_ = lean_box(0);
v_isShared_645_ = v_isSharedCheck_706_;
goto v_resetjp_643_;
}
v_resetjp_643_:
{
lean_object* v_size_646_; lean_object* v_k_647_; lean_object* v_v_648_; lean_object* v_l_649_; lean_object* v_r_650_; lean_object* v_size_651_; lean_object* v___x_652_; lean_object* v___x_653_; uint8_t v___x_654_; 
v_size_646_ = lean_ctor_get(v_l_633_, 0);
v_k_647_ = lean_ctor_get(v_l_633_, 1);
v_v_648_ = lean_ctor_get(v_l_633_, 2);
v_l_649_ = lean_ctor_get(v_l_633_, 3);
v_r_650_ = lean_ctor_get(v_l_633_, 4);
v_size_651_ = lean_ctor_get(v_r_634_, 0);
v___x_652_ = lean_unsigned_to_nat(2u);
v___x_653_ = lean_nat_mul(v___x_652_, v_size_651_);
v___x_654_ = lean_nat_dec_lt(v_size_646_, v___x_653_);
lean_dec(v___x_653_);
if (v___x_654_ == 0)
{
lean_object* v___x_656_; uint8_t v_isShared_657_; uint8_t v_isSharedCheck_682_; 
lean_inc(v_r_650_);
lean_inc(v_l_649_);
lean_inc(v_v_648_);
lean_inc(v_k_647_);
v_isSharedCheck_682_ = !lean_is_exclusive(v_l_633_);
if (v_isSharedCheck_682_ == 0)
{
lean_object* v_unused_683_; lean_object* v_unused_684_; lean_object* v_unused_685_; lean_object* v_unused_686_; lean_object* v_unused_687_; 
v_unused_683_ = lean_ctor_get(v_l_633_, 4);
lean_dec(v_unused_683_);
v_unused_684_ = lean_ctor_get(v_l_633_, 3);
lean_dec(v_unused_684_);
v_unused_685_ = lean_ctor_get(v_l_633_, 2);
lean_dec(v_unused_685_);
v_unused_686_ = lean_ctor_get(v_l_633_, 1);
lean_dec(v_unused_686_);
v_unused_687_ = lean_ctor_get(v_l_633_, 0);
lean_dec(v_unused_687_);
v___x_656_ = v_l_633_;
v_isShared_657_ = v_isSharedCheck_682_;
goto v_resetjp_655_;
}
else
{
lean_dec(v_l_633_);
v___x_656_ = lean_box(0);
v_isShared_657_ = v_isSharedCheck_682_;
goto v_resetjp_655_;
}
v_resetjp_655_:
{
lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___y_661_; lean_object* v___y_662_; lean_object* v___y_663_; lean_object* v___y_672_; 
v___x_658_ = lean_nat_add(v___x_628_, v_size_629_);
lean_dec(v_size_629_);
v___x_659_ = lean_nat_add(v___x_658_, v_size_630_);
lean_dec(v_size_630_);
if (lean_obj_tag(v_l_649_) == 0)
{
lean_object* v_size_680_; 
v_size_680_ = lean_ctor_get(v_l_649_, 0);
lean_inc(v_size_680_);
v___y_672_ = v_size_680_;
goto v___jp_671_;
}
else
{
lean_object* v___x_681_; 
v___x_681_ = lean_unsigned_to_nat(0u);
v___y_672_ = v___x_681_;
goto v___jp_671_;
}
v___jp_660_:
{
lean_object* v___x_664_; lean_object* v___x_666_; 
v___x_664_ = lean_nat_add(v___y_662_, v___y_663_);
lean_dec(v___y_663_);
lean_dec(v___y_662_);
if (v_isShared_657_ == 0)
{
lean_ctor_set(v___x_656_, 4, v_r_634_);
lean_ctor_set(v___x_656_, 3, v_r_650_);
lean_ctor_set(v___x_656_, 2, v_v_632_);
lean_ctor_set(v___x_656_, 1, v_k_631_);
lean_ctor_set(v___x_656_, 0, v___x_664_);
v___x_666_ = v___x_656_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v___x_664_);
lean_ctor_set(v_reuseFailAlloc_670_, 1, v_k_631_);
lean_ctor_set(v_reuseFailAlloc_670_, 2, v_v_632_);
lean_ctor_set(v_reuseFailAlloc_670_, 3, v_r_650_);
lean_ctor_set(v_reuseFailAlloc_670_, 4, v_r_634_);
v___x_666_ = v_reuseFailAlloc_670_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
lean_object* v___x_668_; 
if (v_isShared_645_ == 0)
{
lean_ctor_set(v___x_644_, 4, v___x_666_);
lean_ctor_set(v___x_644_, 3, v___y_661_);
lean_ctor_set(v___x_644_, 2, v_v_648_);
lean_ctor_set(v___x_644_, 1, v_k_647_);
lean_ctor_set(v___x_644_, 0, v___x_659_);
v___x_668_ = v___x_644_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v___x_659_);
lean_ctor_set(v_reuseFailAlloc_669_, 1, v_k_647_);
lean_ctor_set(v_reuseFailAlloc_669_, 2, v_v_648_);
lean_ctor_set(v_reuseFailAlloc_669_, 3, v___y_661_);
lean_ctor_set(v_reuseFailAlloc_669_, 4, v___x_666_);
v___x_668_ = v_reuseFailAlloc_669_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
return v___x_668_;
}
}
}
v___jp_671_:
{
lean_object* v___x_673_; lean_object* v___x_675_; 
v___x_673_ = lean_nat_add(v___x_658_, v___y_672_);
lean_dec(v___y_672_);
lean_dec(v___x_658_);
if (v_isShared_625_ == 0)
{
lean_ctor_set(v___x_624_, 4, v_l_649_);
lean_ctor_set(v___x_624_, 3, v_impl_627_);
lean_ctor_set(v___x_624_, 0, v___x_673_);
v___x_675_ = v___x_624_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v___x_673_);
lean_ctor_set(v_reuseFailAlloc_679_, 1, v_k_619_);
lean_ctor_set(v_reuseFailAlloc_679_, 2, v_v_620_);
lean_ctor_set(v_reuseFailAlloc_679_, 3, v_impl_627_);
lean_ctor_set(v_reuseFailAlloc_679_, 4, v_l_649_);
v___x_675_ = v_reuseFailAlloc_679_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
lean_object* v___x_676_; 
v___x_676_ = lean_nat_add(v___x_628_, v_size_651_);
if (lean_obj_tag(v_r_650_) == 0)
{
lean_object* v_size_677_; 
v_size_677_ = lean_ctor_get(v_r_650_, 0);
lean_inc(v_size_677_);
v___y_661_ = v___x_675_;
v___y_662_ = v___x_676_;
v___y_663_ = v_size_677_;
goto v___jp_660_;
}
else
{
lean_object* v___x_678_; 
v___x_678_ = lean_unsigned_to_nat(0u);
v___y_661_ = v___x_675_;
v___y_662_ = v___x_676_;
v___y_663_ = v___x_678_;
goto v___jp_660_;
}
}
}
}
}
else
{
lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_692_; 
lean_del_object(v___x_624_);
v___x_688_ = lean_nat_add(v___x_628_, v_size_629_);
lean_dec(v_size_629_);
v___x_689_ = lean_nat_add(v___x_688_, v_size_630_);
lean_dec(v_size_630_);
v___x_690_ = lean_nat_add(v___x_688_, v_size_646_);
lean_dec(v___x_688_);
lean_inc_ref(v_impl_627_);
if (v_isShared_645_ == 0)
{
lean_ctor_set(v___x_644_, 4, v_l_633_);
lean_ctor_set(v___x_644_, 3, v_impl_627_);
lean_ctor_set(v___x_644_, 2, v_v_620_);
lean_ctor_set(v___x_644_, 1, v_k_619_);
lean_ctor_set(v___x_644_, 0, v___x_690_);
v___x_692_ = v___x_644_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v___x_690_);
lean_ctor_set(v_reuseFailAlloc_705_, 1, v_k_619_);
lean_ctor_set(v_reuseFailAlloc_705_, 2, v_v_620_);
lean_ctor_set(v_reuseFailAlloc_705_, 3, v_impl_627_);
lean_ctor_set(v_reuseFailAlloc_705_, 4, v_l_633_);
v___x_692_ = v_reuseFailAlloc_705_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
lean_object* v___x_694_; uint8_t v_isShared_695_; uint8_t v_isSharedCheck_699_; 
v_isSharedCheck_699_ = !lean_is_exclusive(v_impl_627_);
if (v_isSharedCheck_699_ == 0)
{
lean_object* v_unused_700_; lean_object* v_unused_701_; lean_object* v_unused_702_; lean_object* v_unused_703_; lean_object* v_unused_704_; 
v_unused_700_ = lean_ctor_get(v_impl_627_, 4);
lean_dec(v_unused_700_);
v_unused_701_ = lean_ctor_get(v_impl_627_, 3);
lean_dec(v_unused_701_);
v_unused_702_ = lean_ctor_get(v_impl_627_, 2);
lean_dec(v_unused_702_);
v_unused_703_ = lean_ctor_get(v_impl_627_, 1);
lean_dec(v_unused_703_);
v_unused_704_ = lean_ctor_get(v_impl_627_, 0);
lean_dec(v_unused_704_);
v___x_694_ = v_impl_627_;
v_isShared_695_ = v_isSharedCheck_699_;
goto v_resetjp_693_;
}
else
{
lean_dec(v_impl_627_);
v___x_694_ = lean_box(0);
v_isShared_695_ = v_isSharedCheck_699_;
goto v_resetjp_693_;
}
v_resetjp_693_:
{
lean_object* v___x_697_; 
if (v_isShared_695_ == 0)
{
lean_ctor_set(v___x_694_, 4, v_r_634_);
lean_ctor_set(v___x_694_, 3, v___x_692_);
lean_ctor_set(v___x_694_, 2, v_v_632_);
lean_ctor_set(v___x_694_, 1, v_k_631_);
lean_ctor_set(v___x_694_, 0, v___x_689_);
v___x_697_ = v___x_694_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v___x_689_);
lean_ctor_set(v_reuseFailAlloc_698_, 1, v_k_631_);
lean_ctor_set(v_reuseFailAlloc_698_, 2, v_v_632_);
lean_ctor_set(v_reuseFailAlloc_698_, 3, v___x_692_);
lean_ctor_set(v_reuseFailAlloc_698_, 4, v_r_634_);
v___x_697_ = v_reuseFailAlloc_698_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
return v___x_697_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_712_; lean_object* v___x_713_; lean_object* v___x_715_; 
v_size_712_ = lean_ctor_get(v_impl_627_, 0);
lean_inc(v_size_712_);
v___x_713_ = lean_nat_add(v___x_628_, v_size_712_);
lean_dec(v_size_712_);
if (v_isShared_625_ == 0)
{
lean_ctor_set(v___x_624_, 3, v_impl_627_);
lean_ctor_set(v___x_624_, 0, v___x_713_);
v___x_715_ = v___x_624_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v___x_713_);
lean_ctor_set(v_reuseFailAlloc_716_, 1, v_k_619_);
lean_ctor_set(v_reuseFailAlloc_716_, 2, v_v_620_);
lean_ctor_set(v_reuseFailAlloc_716_, 3, v_impl_627_);
lean_ctor_set(v_reuseFailAlloc_716_, 4, v_r_622_);
v___x_715_ = v_reuseFailAlloc_716_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
return v___x_715_;
}
}
}
else
{
if (lean_obj_tag(v_r_622_) == 0)
{
lean_object* v_l_717_; 
v_l_717_ = lean_ctor_get(v_r_622_, 3);
lean_inc(v_l_717_);
if (lean_obj_tag(v_l_717_) == 0)
{
lean_object* v_r_718_; 
v_r_718_ = lean_ctor_get(v_r_622_, 4);
lean_inc(v_r_718_);
if (lean_obj_tag(v_r_718_) == 0)
{
lean_object* v_size_719_; lean_object* v_k_720_; lean_object* v_v_721_; lean_object* v___x_723_; uint8_t v_isShared_724_; uint8_t v_isSharedCheck_734_; 
v_size_719_ = lean_ctor_get(v_r_622_, 0);
v_k_720_ = lean_ctor_get(v_r_622_, 1);
v_v_721_ = lean_ctor_get(v_r_622_, 2);
v_isSharedCheck_734_ = !lean_is_exclusive(v_r_622_);
if (v_isSharedCheck_734_ == 0)
{
lean_object* v_unused_735_; lean_object* v_unused_736_; 
v_unused_735_ = lean_ctor_get(v_r_622_, 4);
lean_dec(v_unused_735_);
v_unused_736_ = lean_ctor_get(v_r_622_, 3);
lean_dec(v_unused_736_);
v___x_723_ = v_r_622_;
v_isShared_724_ = v_isSharedCheck_734_;
goto v_resetjp_722_;
}
else
{
lean_inc(v_v_721_);
lean_inc(v_k_720_);
lean_inc(v_size_719_);
lean_dec(v_r_622_);
v___x_723_ = lean_box(0);
v_isShared_724_ = v_isSharedCheck_734_;
goto v_resetjp_722_;
}
v_resetjp_722_:
{
lean_object* v_size_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_729_; 
v_size_725_ = lean_ctor_get(v_l_717_, 0);
v___x_726_ = lean_nat_add(v___x_628_, v_size_719_);
lean_dec(v_size_719_);
v___x_727_ = lean_nat_add(v___x_628_, v_size_725_);
if (v_isShared_724_ == 0)
{
lean_ctor_set(v___x_723_, 4, v_l_717_);
lean_ctor_set(v___x_723_, 3, v_impl_627_);
lean_ctor_set(v___x_723_, 2, v_v_620_);
lean_ctor_set(v___x_723_, 1, v_k_619_);
lean_ctor_set(v___x_723_, 0, v___x_727_);
v___x_729_ = v___x_723_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v___x_727_);
lean_ctor_set(v_reuseFailAlloc_733_, 1, v_k_619_);
lean_ctor_set(v_reuseFailAlloc_733_, 2, v_v_620_);
lean_ctor_set(v_reuseFailAlloc_733_, 3, v_impl_627_);
lean_ctor_set(v_reuseFailAlloc_733_, 4, v_l_717_);
v___x_729_ = v_reuseFailAlloc_733_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
lean_object* v___x_731_; 
if (v_isShared_625_ == 0)
{
lean_ctor_set(v___x_624_, 4, v_r_718_);
lean_ctor_set(v___x_624_, 3, v___x_729_);
lean_ctor_set(v___x_624_, 2, v_v_721_);
lean_ctor_set(v___x_624_, 1, v_k_720_);
lean_ctor_set(v___x_624_, 0, v___x_726_);
v___x_731_ = v___x_624_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v___x_726_);
lean_ctor_set(v_reuseFailAlloc_732_, 1, v_k_720_);
lean_ctor_set(v_reuseFailAlloc_732_, 2, v_v_721_);
lean_ctor_set(v_reuseFailAlloc_732_, 3, v___x_729_);
lean_ctor_set(v_reuseFailAlloc_732_, 4, v_r_718_);
v___x_731_ = v_reuseFailAlloc_732_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
return v___x_731_;
}
}
}
}
else
{
lean_object* v_k_737_; lean_object* v_v_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_761_; 
v_k_737_ = lean_ctor_get(v_r_622_, 1);
v_v_738_ = lean_ctor_get(v_r_622_, 2);
v_isSharedCheck_761_ = !lean_is_exclusive(v_r_622_);
if (v_isSharedCheck_761_ == 0)
{
lean_object* v_unused_762_; lean_object* v_unused_763_; lean_object* v_unused_764_; 
v_unused_762_ = lean_ctor_get(v_r_622_, 4);
lean_dec(v_unused_762_);
v_unused_763_ = lean_ctor_get(v_r_622_, 3);
lean_dec(v_unused_763_);
v_unused_764_ = lean_ctor_get(v_r_622_, 0);
lean_dec(v_unused_764_);
v___x_740_ = v_r_622_;
v_isShared_741_ = v_isSharedCheck_761_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_v_738_);
lean_inc(v_k_737_);
lean_dec(v_r_622_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_761_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
lean_object* v_k_742_; lean_object* v_v_743_; lean_object* v___x_745_; uint8_t v_isShared_746_; uint8_t v_isSharedCheck_757_; 
v_k_742_ = lean_ctor_get(v_l_717_, 1);
v_v_743_ = lean_ctor_get(v_l_717_, 2);
v_isSharedCheck_757_ = !lean_is_exclusive(v_l_717_);
if (v_isSharedCheck_757_ == 0)
{
lean_object* v_unused_758_; lean_object* v_unused_759_; lean_object* v_unused_760_; 
v_unused_758_ = lean_ctor_get(v_l_717_, 4);
lean_dec(v_unused_758_);
v_unused_759_ = lean_ctor_get(v_l_717_, 3);
lean_dec(v_unused_759_);
v_unused_760_ = lean_ctor_get(v_l_717_, 0);
lean_dec(v_unused_760_);
v___x_745_ = v_l_717_;
v_isShared_746_ = v_isSharedCheck_757_;
goto v_resetjp_744_;
}
else
{
lean_inc(v_v_743_);
lean_inc(v_k_742_);
lean_dec(v_l_717_);
v___x_745_ = lean_box(0);
v_isShared_746_ = v_isSharedCheck_757_;
goto v_resetjp_744_;
}
v_resetjp_744_:
{
lean_object* v___x_747_; lean_object* v___x_749_; 
v___x_747_ = lean_unsigned_to_nat(3u);
if (v_isShared_746_ == 0)
{
lean_ctor_set(v___x_745_, 4, v_r_718_);
lean_ctor_set(v___x_745_, 3, v_r_718_);
lean_ctor_set(v___x_745_, 2, v_v_620_);
lean_ctor_set(v___x_745_, 1, v_k_619_);
lean_ctor_set(v___x_745_, 0, v___x_628_);
v___x_749_ = v___x_745_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v___x_628_);
lean_ctor_set(v_reuseFailAlloc_756_, 1, v_k_619_);
lean_ctor_set(v_reuseFailAlloc_756_, 2, v_v_620_);
lean_ctor_set(v_reuseFailAlloc_756_, 3, v_r_718_);
lean_ctor_set(v_reuseFailAlloc_756_, 4, v_r_718_);
v___x_749_ = v_reuseFailAlloc_756_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
lean_object* v___x_751_; 
if (v_isShared_741_ == 0)
{
lean_ctor_set(v___x_740_, 3, v_r_718_);
lean_ctor_set(v___x_740_, 0, v___x_628_);
v___x_751_ = v___x_740_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v___x_628_);
lean_ctor_set(v_reuseFailAlloc_755_, 1, v_k_737_);
lean_ctor_set(v_reuseFailAlloc_755_, 2, v_v_738_);
lean_ctor_set(v_reuseFailAlloc_755_, 3, v_r_718_);
lean_ctor_set(v_reuseFailAlloc_755_, 4, v_r_718_);
v___x_751_ = v_reuseFailAlloc_755_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
lean_object* v___x_753_; 
if (v_isShared_625_ == 0)
{
lean_ctor_set(v___x_624_, 4, v___x_751_);
lean_ctor_set(v___x_624_, 3, v___x_749_);
lean_ctor_set(v___x_624_, 2, v_v_743_);
lean_ctor_set(v___x_624_, 1, v_k_742_);
lean_ctor_set(v___x_624_, 0, v___x_747_);
v___x_753_ = v___x_624_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v___x_747_);
lean_ctor_set(v_reuseFailAlloc_754_, 1, v_k_742_);
lean_ctor_set(v_reuseFailAlloc_754_, 2, v_v_743_);
lean_ctor_set(v_reuseFailAlloc_754_, 3, v___x_749_);
lean_ctor_set(v_reuseFailAlloc_754_, 4, v___x_751_);
v___x_753_ = v_reuseFailAlloc_754_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
return v___x_753_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_765_; 
v_r_765_ = lean_ctor_get(v_r_622_, 4);
lean_inc(v_r_765_);
if (lean_obj_tag(v_r_765_) == 0)
{
lean_object* v_k_766_; lean_object* v_v_767_; lean_object* v___x_769_; uint8_t v_isShared_770_; uint8_t v_isSharedCheck_778_; 
v_k_766_ = lean_ctor_get(v_r_622_, 1);
v_v_767_ = lean_ctor_get(v_r_622_, 2);
v_isSharedCheck_778_ = !lean_is_exclusive(v_r_622_);
if (v_isSharedCheck_778_ == 0)
{
lean_object* v_unused_779_; lean_object* v_unused_780_; lean_object* v_unused_781_; 
v_unused_779_ = lean_ctor_get(v_r_622_, 4);
lean_dec(v_unused_779_);
v_unused_780_ = lean_ctor_get(v_r_622_, 3);
lean_dec(v_unused_780_);
v_unused_781_ = lean_ctor_get(v_r_622_, 0);
lean_dec(v_unused_781_);
v___x_769_ = v_r_622_;
v_isShared_770_ = v_isSharedCheck_778_;
goto v_resetjp_768_;
}
else
{
lean_inc(v_v_767_);
lean_inc(v_k_766_);
lean_dec(v_r_622_);
v___x_769_ = lean_box(0);
v_isShared_770_ = v_isSharedCheck_778_;
goto v_resetjp_768_;
}
v_resetjp_768_:
{
lean_object* v___x_771_; lean_object* v___x_773_; 
v___x_771_ = lean_unsigned_to_nat(3u);
if (v_isShared_770_ == 0)
{
lean_ctor_set(v___x_769_, 4, v_l_717_);
lean_ctor_set(v___x_769_, 2, v_v_620_);
lean_ctor_set(v___x_769_, 1, v_k_619_);
lean_ctor_set(v___x_769_, 0, v___x_628_);
v___x_773_ = v___x_769_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v___x_628_);
lean_ctor_set(v_reuseFailAlloc_777_, 1, v_k_619_);
lean_ctor_set(v_reuseFailAlloc_777_, 2, v_v_620_);
lean_ctor_set(v_reuseFailAlloc_777_, 3, v_l_717_);
lean_ctor_set(v_reuseFailAlloc_777_, 4, v_l_717_);
v___x_773_ = v_reuseFailAlloc_777_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
lean_object* v___x_775_; 
if (v_isShared_625_ == 0)
{
lean_ctor_set(v___x_624_, 4, v_r_765_);
lean_ctor_set(v___x_624_, 3, v___x_773_);
lean_ctor_set(v___x_624_, 2, v_v_767_);
lean_ctor_set(v___x_624_, 1, v_k_766_);
lean_ctor_set(v___x_624_, 0, v___x_771_);
v___x_775_ = v___x_624_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v___x_771_);
lean_ctor_set(v_reuseFailAlloc_776_, 1, v_k_766_);
lean_ctor_set(v_reuseFailAlloc_776_, 2, v_v_767_);
lean_ctor_set(v_reuseFailAlloc_776_, 3, v___x_773_);
lean_ctor_set(v_reuseFailAlloc_776_, 4, v_r_765_);
v___x_775_ = v_reuseFailAlloc_776_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
return v___x_775_;
}
}
}
}
else
{
lean_object* v_size_782_; lean_object* v_k_783_; lean_object* v_v_784_; lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_795_; 
v_size_782_ = lean_ctor_get(v_r_622_, 0);
v_k_783_ = lean_ctor_get(v_r_622_, 1);
v_v_784_ = lean_ctor_get(v_r_622_, 2);
v_isSharedCheck_795_ = !lean_is_exclusive(v_r_622_);
if (v_isSharedCheck_795_ == 0)
{
lean_object* v_unused_796_; lean_object* v_unused_797_; 
v_unused_796_ = lean_ctor_get(v_r_622_, 4);
lean_dec(v_unused_796_);
v_unused_797_ = lean_ctor_get(v_r_622_, 3);
lean_dec(v_unused_797_);
v___x_786_ = v_r_622_;
v_isShared_787_ = v_isSharedCheck_795_;
goto v_resetjp_785_;
}
else
{
lean_inc(v_v_784_);
lean_inc(v_k_783_);
lean_inc(v_size_782_);
lean_dec(v_r_622_);
v___x_786_ = lean_box(0);
v_isShared_787_ = v_isSharedCheck_795_;
goto v_resetjp_785_;
}
v_resetjp_785_:
{
lean_object* v___x_789_; 
if (v_isShared_787_ == 0)
{
lean_ctor_set(v___x_786_, 3, v_r_765_);
v___x_789_ = v___x_786_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v_size_782_);
lean_ctor_set(v_reuseFailAlloc_794_, 1, v_k_783_);
lean_ctor_set(v_reuseFailAlloc_794_, 2, v_v_784_);
lean_ctor_set(v_reuseFailAlloc_794_, 3, v_r_765_);
lean_ctor_set(v_reuseFailAlloc_794_, 4, v_r_765_);
v___x_789_ = v_reuseFailAlloc_794_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
lean_object* v___x_790_; lean_object* v___x_792_; 
v___x_790_ = lean_unsigned_to_nat(2u);
if (v_isShared_625_ == 0)
{
lean_ctor_set(v___x_624_, 4, v___x_789_);
lean_ctor_set(v___x_624_, 3, v_r_765_);
lean_ctor_set(v___x_624_, 0, v___x_790_);
v___x_792_ = v___x_624_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v___x_790_);
lean_ctor_set(v_reuseFailAlloc_793_, 1, v_k_619_);
lean_ctor_set(v_reuseFailAlloc_793_, 2, v_v_620_);
lean_ctor_set(v_reuseFailAlloc_793_, 3, v_r_765_);
lean_ctor_set(v_reuseFailAlloc_793_, 4, v___x_789_);
v___x_792_ = v_reuseFailAlloc_793_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
return v___x_792_;
}
}
}
}
}
}
else
{
lean_object* v___x_799_; 
if (v_isShared_625_ == 0)
{
lean_ctor_set(v___x_624_, 3, v_r_622_);
lean_ctor_set(v___x_624_, 0, v___x_628_);
v___x_799_ = v___x_624_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v___x_628_);
lean_ctor_set(v_reuseFailAlloc_800_, 1, v_k_619_);
lean_ctor_set(v_reuseFailAlloc_800_, 2, v_v_620_);
lean_ctor_set(v_reuseFailAlloc_800_, 3, v_r_622_);
lean_ctor_set(v_reuseFailAlloc_800_, 4, v_r_622_);
v___x_799_ = v_reuseFailAlloc_800_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
return v___x_799_;
}
}
}
}
case 1:
{
lean_del_object(v___x_624_);
lean_dec(v_v_620_);
lean_dec(v_k_619_);
if (lean_obj_tag(v_l_621_) == 0)
{
if (lean_obj_tag(v_r_622_) == 0)
{
lean_object* v_size_801_; lean_object* v_k_802_; lean_object* v_v_803_; lean_object* v_l_804_; lean_object* v_r_805_; lean_object* v_size_806_; lean_object* v_k_807_; lean_object* v_v_808_; lean_object* v_l_809_; lean_object* v_r_810_; lean_object* v___x_811_; uint8_t v___x_812_; 
v_size_801_ = lean_ctor_get(v_l_621_, 0);
v_k_802_ = lean_ctor_get(v_l_621_, 1);
v_v_803_ = lean_ctor_get(v_l_621_, 2);
v_l_804_ = lean_ctor_get(v_l_621_, 3);
v_r_805_ = lean_ctor_get(v_l_621_, 4);
lean_inc(v_r_805_);
v_size_806_ = lean_ctor_get(v_r_622_, 0);
v_k_807_ = lean_ctor_get(v_r_622_, 1);
v_v_808_ = lean_ctor_get(v_r_622_, 2);
v_l_809_ = lean_ctor_get(v_r_622_, 3);
lean_inc(v_l_809_);
v_r_810_ = lean_ctor_get(v_r_622_, 4);
v___x_811_ = lean_unsigned_to_nat(1u);
v___x_812_ = lean_nat_dec_lt(v_size_801_, v_size_806_);
if (v___x_812_ == 0)
{
lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_948_; 
lean_inc(v_l_804_);
lean_inc(v_v_803_);
lean_inc(v_k_802_);
v_isSharedCheck_948_ = !lean_is_exclusive(v_l_621_);
if (v_isSharedCheck_948_ == 0)
{
lean_object* v_unused_949_; lean_object* v_unused_950_; lean_object* v_unused_951_; lean_object* v_unused_952_; lean_object* v_unused_953_; 
v_unused_949_ = lean_ctor_get(v_l_621_, 4);
lean_dec(v_unused_949_);
v_unused_950_ = lean_ctor_get(v_l_621_, 3);
lean_dec(v_unused_950_);
v_unused_951_ = lean_ctor_get(v_l_621_, 2);
lean_dec(v_unused_951_);
v_unused_952_ = lean_ctor_get(v_l_621_, 1);
lean_dec(v_unused_952_);
v_unused_953_ = lean_ctor_get(v_l_621_, 0);
lean_dec(v_unused_953_);
v___x_814_ = v_l_621_;
v_isShared_815_ = v_isSharedCheck_948_;
goto v_resetjp_813_;
}
else
{
lean_dec(v_l_621_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_948_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
lean_object* v___x_816_; lean_object* v_tree_817_; 
v___x_816_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_802_, v_v_803_, v_l_804_, v_r_805_);
v_tree_817_ = lean_ctor_get(v___x_816_, 2);
lean_inc(v_tree_817_);
if (lean_obj_tag(v_tree_817_) == 0)
{
lean_object* v_k_818_; lean_object* v_v_819_; lean_object* v_size_820_; lean_object* v___x_821_; lean_object* v___x_822_; uint8_t v___x_823_; 
v_k_818_ = lean_ctor_get(v___x_816_, 0);
lean_inc(v_k_818_);
v_v_819_ = lean_ctor_get(v___x_816_, 1);
lean_inc(v_v_819_);
lean_dec_ref(v___x_816_);
v_size_820_ = lean_ctor_get(v_tree_817_, 0);
v___x_821_ = lean_unsigned_to_nat(3u);
v___x_822_ = lean_nat_mul(v___x_821_, v_size_820_);
v___x_823_ = lean_nat_dec_lt(v___x_822_, v_size_806_);
lean_dec(v___x_822_);
if (v___x_823_ == 0)
{
lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_827_; 
lean_dec(v_l_809_);
v___x_824_ = lean_nat_add(v___x_811_, v_size_820_);
v___x_825_ = lean_nat_add(v___x_824_, v_size_806_);
lean_dec(v___x_824_);
if (v_isShared_815_ == 0)
{
lean_ctor_set(v___x_814_, 4, v_r_622_);
lean_ctor_set(v___x_814_, 3, v_tree_817_);
lean_ctor_set(v___x_814_, 2, v_v_819_);
lean_ctor_set(v___x_814_, 1, v_k_818_);
lean_ctor_set(v___x_814_, 0, v___x_825_);
v___x_827_ = v___x_814_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_828_; 
v_reuseFailAlloc_828_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_828_, 0, v___x_825_);
lean_ctor_set(v_reuseFailAlloc_828_, 1, v_k_818_);
lean_ctor_set(v_reuseFailAlloc_828_, 2, v_v_819_);
lean_ctor_set(v_reuseFailAlloc_828_, 3, v_tree_817_);
lean_ctor_set(v_reuseFailAlloc_828_, 4, v_r_622_);
v___x_827_ = v_reuseFailAlloc_828_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
return v___x_827_;
}
}
else
{
lean_object* v___x_830_; uint8_t v_isShared_831_; uint8_t v_isSharedCheck_883_; 
lean_inc(v_r_810_);
lean_inc(v_v_808_);
lean_inc(v_k_807_);
lean_inc(v_size_806_);
v_isSharedCheck_883_ = !lean_is_exclusive(v_r_622_);
if (v_isSharedCheck_883_ == 0)
{
lean_object* v_unused_884_; lean_object* v_unused_885_; lean_object* v_unused_886_; lean_object* v_unused_887_; lean_object* v_unused_888_; 
v_unused_884_ = lean_ctor_get(v_r_622_, 4);
lean_dec(v_unused_884_);
v_unused_885_ = lean_ctor_get(v_r_622_, 3);
lean_dec(v_unused_885_);
v_unused_886_ = lean_ctor_get(v_r_622_, 2);
lean_dec(v_unused_886_);
v_unused_887_ = lean_ctor_get(v_r_622_, 1);
lean_dec(v_unused_887_);
v_unused_888_ = lean_ctor_get(v_r_622_, 0);
lean_dec(v_unused_888_);
v___x_830_ = v_r_622_;
v_isShared_831_ = v_isSharedCheck_883_;
goto v_resetjp_829_;
}
else
{
lean_dec(v_r_622_);
v___x_830_ = lean_box(0);
v_isShared_831_ = v_isSharedCheck_883_;
goto v_resetjp_829_;
}
v_resetjp_829_:
{
lean_object* v_size_832_; lean_object* v_k_833_; lean_object* v_v_834_; lean_object* v_l_835_; lean_object* v_r_836_; lean_object* v_size_837_; lean_object* v___x_838_; lean_object* v___x_839_; uint8_t v___x_840_; 
v_size_832_ = lean_ctor_get(v_l_809_, 0);
v_k_833_ = lean_ctor_get(v_l_809_, 1);
v_v_834_ = lean_ctor_get(v_l_809_, 2);
v_l_835_ = lean_ctor_get(v_l_809_, 3);
v_r_836_ = lean_ctor_get(v_l_809_, 4);
v_size_837_ = lean_ctor_get(v_r_810_, 0);
v___x_838_ = lean_unsigned_to_nat(2u);
v___x_839_ = lean_nat_mul(v___x_838_, v_size_837_);
v___x_840_ = lean_nat_dec_lt(v_size_832_, v___x_839_);
lean_dec(v___x_839_);
if (v___x_840_ == 0)
{
lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_868_; 
lean_inc(v_r_836_);
lean_inc(v_l_835_);
lean_inc(v_v_834_);
lean_inc(v_k_833_);
v_isSharedCheck_868_ = !lean_is_exclusive(v_l_809_);
if (v_isSharedCheck_868_ == 0)
{
lean_object* v_unused_869_; lean_object* v_unused_870_; lean_object* v_unused_871_; lean_object* v_unused_872_; lean_object* v_unused_873_; 
v_unused_869_ = lean_ctor_get(v_l_809_, 4);
lean_dec(v_unused_869_);
v_unused_870_ = lean_ctor_get(v_l_809_, 3);
lean_dec(v_unused_870_);
v_unused_871_ = lean_ctor_get(v_l_809_, 2);
lean_dec(v_unused_871_);
v_unused_872_ = lean_ctor_get(v_l_809_, 1);
lean_dec(v_unused_872_);
v_unused_873_ = lean_ctor_get(v_l_809_, 0);
lean_dec(v_unused_873_);
v___x_842_ = v_l_809_;
v_isShared_843_ = v_isSharedCheck_868_;
goto v_resetjp_841_;
}
else
{
lean_dec(v_l_809_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_868_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___y_847_; lean_object* v___y_848_; lean_object* v___y_849_; lean_object* v___y_858_; 
v___x_844_ = lean_nat_add(v___x_811_, v_size_820_);
v___x_845_ = lean_nat_add(v___x_844_, v_size_806_);
lean_dec(v_size_806_);
if (lean_obj_tag(v_l_835_) == 0)
{
lean_object* v_size_866_; 
v_size_866_ = lean_ctor_get(v_l_835_, 0);
lean_inc(v_size_866_);
v___y_858_ = v_size_866_;
goto v___jp_857_;
}
else
{
lean_object* v___x_867_; 
v___x_867_ = lean_unsigned_to_nat(0u);
v___y_858_ = v___x_867_;
goto v___jp_857_;
}
v___jp_846_:
{
lean_object* v___x_850_; lean_object* v___x_852_; 
v___x_850_ = lean_nat_add(v___y_847_, v___y_849_);
lean_dec(v___y_849_);
lean_dec(v___y_847_);
if (v_isShared_843_ == 0)
{
lean_ctor_set(v___x_842_, 4, v_r_810_);
lean_ctor_set(v___x_842_, 3, v_r_836_);
lean_ctor_set(v___x_842_, 2, v_v_808_);
lean_ctor_set(v___x_842_, 1, v_k_807_);
lean_ctor_set(v___x_842_, 0, v___x_850_);
v___x_852_ = v___x_842_;
goto v_reusejp_851_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v___x_850_);
lean_ctor_set(v_reuseFailAlloc_856_, 1, v_k_807_);
lean_ctor_set(v_reuseFailAlloc_856_, 2, v_v_808_);
lean_ctor_set(v_reuseFailAlloc_856_, 3, v_r_836_);
lean_ctor_set(v_reuseFailAlloc_856_, 4, v_r_810_);
v___x_852_ = v_reuseFailAlloc_856_;
goto v_reusejp_851_;
}
v_reusejp_851_:
{
lean_object* v___x_854_; 
if (v_isShared_831_ == 0)
{
lean_ctor_set(v___x_830_, 4, v___x_852_);
lean_ctor_set(v___x_830_, 3, v___y_848_);
lean_ctor_set(v___x_830_, 2, v_v_834_);
lean_ctor_set(v___x_830_, 1, v_k_833_);
lean_ctor_set(v___x_830_, 0, v___x_845_);
v___x_854_ = v___x_830_;
goto v_reusejp_853_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v___x_845_);
lean_ctor_set(v_reuseFailAlloc_855_, 1, v_k_833_);
lean_ctor_set(v_reuseFailAlloc_855_, 2, v_v_834_);
lean_ctor_set(v_reuseFailAlloc_855_, 3, v___y_848_);
lean_ctor_set(v_reuseFailAlloc_855_, 4, v___x_852_);
v___x_854_ = v_reuseFailAlloc_855_;
goto v_reusejp_853_;
}
v_reusejp_853_:
{
return v___x_854_;
}
}
}
v___jp_857_:
{
lean_object* v___x_859_; lean_object* v___x_861_; 
v___x_859_ = lean_nat_add(v___x_844_, v___y_858_);
lean_dec(v___y_858_);
lean_dec(v___x_844_);
if (v_isShared_815_ == 0)
{
lean_ctor_set(v___x_814_, 4, v_l_835_);
lean_ctor_set(v___x_814_, 3, v_tree_817_);
lean_ctor_set(v___x_814_, 2, v_v_819_);
lean_ctor_set(v___x_814_, 1, v_k_818_);
lean_ctor_set(v___x_814_, 0, v___x_859_);
v___x_861_ = v___x_814_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v___x_859_);
lean_ctor_set(v_reuseFailAlloc_865_, 1, v_k_818_);
lean_ctor_set(v_reuseFailAlloc_865_, 2, v_v_819_);
lean_ctor_set(v_reuseFailAlloc_865_, 3, v_tree_817_);
lean_ctor_set(v_reuseFailAlloc_865_, 4, v_l_835_);
v___x_861_ = v_reuseFailAlloc_865_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
lean_object* v___x_862_; 
v___x_862_ = lean_nat_add(v___x_811_, v_size_837_);
if (lean_obj_tag(v_r_836_) == 0)
{
lean_object* v_size_863_; 
v_size_863_ = lean_ctor_get(v_r_836_, 0);
lean_inc(v_size_863_);
v___y_847_ = v___x_862_;
v___y_848_ = v___x_861_;
v___y_849_ = v_size_863_;
goto v___jp_846_;
}
else
{
lean_object* v___x_864_; 
v___x_864_ = lean_unsigned_to_nat(0u);
v___y_847_ = v___x_862_;
v___y_848_ = v___x_861_;
v___y_849_ = v___x_864_;
goto v___jp_846_;
}
}
}
}
}
else
{
lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_878_; 
v___x_874_ = lean_nat_add(v___x_811_, v_size_820_);
v___x_875_ = lean_nat_add(v___x_874_, v_size_806_);
lean_dec(v_size_806_);
v___x_876_ = lean_nat_add(v___x_874_, v_size_832_);
lean_dec(v___x_874_);
if (v_isShared_831_ == 0)
{
lean_ctor_set(v___x_830_, 4, v_l_809_);
lean_ctor_set(v___x_830_, 3, v_tree_817_);
lean_ctor_set(v___x_830_, 2, v_v_819_);
lean_ctor_set(v___x_830_, 1, v_k_818_);
lean_ctor_set(v___x_830_, 0, v___x_876_);
v___x_878_ = v___x_830_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v___x_876_);
lean_ctor_set(v_reuseFailAlloc_882_, 1, v_k_818_);
lean_ctor_set(v_reuseFailAlloc_882_, 2, v_v_819_);
lean_ctor_set(v_reuseFailAlloc_882_, 3, v_tree_817_);
lean_ctor_set(v_reuseFailAlloc_882_, 4, v_l_809_);
v___x_878_ = v_reuseFailAlloc_882_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
lean_object* v___x_880_; 
if (v_isShared_815_ == 0)
{
lean_ctor_set(v___x_814_, 4, v_r_810_);
lean_ctor_set(v___x_814_, 3, v___x_878_);
lean_ctor_set(v___x_814_, 2, v_v_808_);
lean_ctor_set(v___x_814_, 1, v_k_807_);
lean_ctor_set(v___x_814_, 0, v___x_875_);
v___x_880_ = v___x_814_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v___x_875_);
lean_ctor_set(v_reuseFailAlloc_881_, 1, v_k_807_);
lean_ctor_set(v_reuseFailAlloc_881_, 2, v_v_808_);
lean_ctor_set(v_reuseFailAlloc_881_, 3, v___x_878_);
lean_ctor_set(v_reuseFailAlloc_881_, 4, v_r_810_);
v___x_880_ = v_reuseFailAlloc_881_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
return v___x_880_;
}
}
}
}
}
}
else
{
lean_object* v___x_890_; uint8_t v_isShared_891_; uint8_t v_isSharedCheck_942_; 
lean_inc(v_r_810_);
lean_inc(v_v_808_);
lean_inc(v_k_807_);
lean_inc(v_size_806_);
v_isSharedCheck_942_ = !lean_is_exclusive(v_r_622_);
if (v_isSharedCheck_942_ == 0)
{
lean_object* v_unused_943_; lean_object* v_unused_944_; lean_object* v_unused_945_; lean_object* v_unused_946_; lean_object* v_unused_947_; 
v_unused_943_ = lean_ctor_get(v_r_622_, 4);
lean_dec(v_unused_943_);
v_unused_944_ = lean_ctor_get(v_r_622_, 3);
lean_dec(v_unused_944_);
v_unused_945_ = lean_ctor_get(v_r_622_, 2);
lean_dec(v_unused_945_);
v_unused_946_ = lean_ctor_get(v_r_622_, 1);
lean_dec(v_unused_946_);
v_unused_947_ = lean_ctor_get(v_r_622_, 0);
lean_dec(v_unused_947_);
v___x_890_ = v_r_622_;
v_isShared_891_ = v_isSharedCheck_942_;
goto v_resetjp_889_;
}
else
{
lean_dec(v_r_622_);
v___x_890_ = lean_box(0);
v_isShared_891_ = v_isSharedCheck_942_;
goto v_resetjp_889_;
}
v_resetjp_889_:
{
if (lean_obj_tag(v_l_809_) == 0)
{
if (lean_obj_tag(v_r_810_) == 0)
{
lean_object* v_k_892_; lean_object* v_v_893_; lean_object* v_size_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_898_; 
v_k_892_ = lean_ctor_get(v___x_816_, 0);
lean_inc(v_k_892_);
v_v_893_ = lean_ctor_get(v___x_816_, 1);
lean_inc(v_v_893_);
lean_dec_ref(v___x_816_);
v_size_894_ = lean_ctor_get(v_l_809_, 0);
v___x_895_ = lean_nat_add(v___x_811_, v_size_806_);
lean_dec(v_size_806_);
v___x_896_ = lean_nat_add(v___x_811_, v_size_894_);
if (v_isShared_891_ == 0)
{
lean_ctor_set(v___x_890_, 4, v_l_809_);
lean_ctor_set(v___x_890_, 3, v_tree_817_);
lean_ctor_set(v___x_890_, 2, v_v_893_);
lean_ctor_set(v___x_890_, 1, v_k_892_);
lean_ctor_set(v___x_890_, 0, v___x_896_);
v___x_898_ = v___x_890_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v___x_896_);
lean_ctor_set(v_reuseFailAlloc_902_, 1, v_k_892_);
lean_ctor_set(v_reuseFailAlloc_902_, 2, v_v_893_);
lean_ctor_set(v_reuseFailAlloc_902_, 3, v_tree_817_);
lean_ctor_set(v_reuseFailAlloc_902_, 4, v_l_809_);
v___x_898_ = v_reuseFailAlloc_902_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
lean_object* v___x_900_; 
if (v_isShared_815_ == 0)
{
lean_ctor_set(v___x_814_, 4, v_r_810_);
lean_ctor_set(v___x_814_, 3, v___x_898_);
lean_ctor_set(v___x_814_, 2, v_v_808_);
lean_ctor_set(v___x_814_, 1, v_k_807_);
lean_ctor_set(v___x_814_, 0, v___x_895_);
v___x_900_ = v___x_814_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v___x_895_);
lean_ctor_set(v_reuseFailAlloc_901_, 1, v_k_807_);
lean_ctor_set(v_reuseFailAlloc_901_, 2, v_v_808_);
lean_ctor_set(v_reuseFailAlloc_901_, 3, v___x_898_);
lean_ctor_set(v_reuseFailAlloc_901_, 4, v_r_810_);
v___x_900_ = v_reuseFailAlloc_901_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
return v___x_900_;
}
}
}
else
{
lean_object* v_k_903_; lean_object* v_v_904_; lean_object* v_k_905_; lean_object* v_v_906_; lean_object* v___x_908_; uint8_t v_isShared_909_; uint8_t v_isSharedCheck_920_; 
lean_dec(v_size_806_);
v_k_903_ = lean_ctor_get(v___x_816_, 0);
lean_inc(v_k_903_);
v_v_904_ = lean_ctor_get(v___x_816_, 1);
lean_inc(v_v_904_);
lean_dec_ref(v___x_816_);
v_k_905_ = lean_ctor_get(v_l_809_, 1);
v_v_906_ = lean_ctor_get(v_l_809_, 2);
v_isSharedCheck_920_ = !lean_is_exclusive(v_l_809_);
if (v_isSharedCheck_920_ == 0)
{
lean_object* v_unused_921_; lean_object* v_unused_922_; lean_object* v_unused_923_; 
v_unused_921_ = lean_ctor_get(v_l_809_, 4);
lean_dec(v_unused_921_);
v_unused_922_ = lean_ctor_get(v_l_809_, 3);
lean_dec(v_unused_922_);
v_unused_923_ = lean_ctor_get(v_l_809_, 0);
lean_dec(v_unused_923_);
v___x_908_ = v_l_809_;
v_isShared_909_ = v_isSharedCheck_920_;
goto v_resetjp_907_;
}
else
{
lean_inc(v_v_906_);
lean_inc(v_k_905_);
lean_dec(v_l_809_);
v___x_908_ = lean_box(0);
v_isShared_909_ = v_isSharedCheck_920_;
goto v_resetjp_907_;
}
v_resetjp_907_:
{
lean_object* v___x_910_; lean_object* v___x_912_; 
v___x_910_ = lean_unsigned_to_nat(3u);
if (v_isShared_909_ == 0)
{
lean_ctor_set(v___x_908_, 4, v_r_810_);
lean_ctor_set(v___x_908_, 3, v_r_810_);
lean_ctor_set(v___x_908_, 2, v_v_904_);
lean_ctor_set(v___x_908_, 1, v_k_903_);
lean_ctor_set(v___x_908_, 0, v___x_811_);
v___x_912_ = v___x_908_;
goto v_reusejp_911_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v___x_811_);
lean_ctor_set(v_reuseFailAlloc_919_, 1, v_k_903_);
lean_ctor_set(v_reuseFailAlloc_919_, 2, v_v_904_);
lean_ctor_set(v_reuseFailAlloc_919_, 3, v_r_810_);
lean_ctor_set(v_reuseFailAlloc_919_, 4, v_r_810_);
v___x_912_ = v_reuseFailAlloc_919_;
goto v_reusejp_911_;
}
v_reusejp_911_:
{
lean_object* v___x_914_; 
if (v_isShared_891_ == 0)
{
lean_ctor_set(v___x_890_, 3, v_r_810_);
lean_ctor_set(v___x_890_, 0, v___x_811_);
v___x_914_ = v___x_890_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_918_; 
v_reuseFailAlloc_918_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_918_, 0, v___x_811_);
lean_ctor_set(v_reuseFailAlloc_918_, 1, v_k_807_);
lean_ctor_set(v_reuseFailAlloc_918_, 2, v_v_808_);
lean_ctor_set(v_reuseFailAlloc_918_, 3, v_r_810_);
lean_ctor_set(v_reuseFailAlloc_918_, 4, v_r_810_);
v___x_914_ = v_reuseFailAlloc_918_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
lean_object* v___x_916_; 
if (v_isShared_815_ == 0)
{
lean_ctor_set(v___x_814_, 4, v___x_914_);
lean_ctor_set(v___x_814_, 3, v___x_912_);
lean_ctor_set(v___x_814_, 2, v_v_906_);
lean_ctor_set(v___x_814_, 1, v_k_905_);
lean_ctor_set(v___x_814_, 0, v___x_910_);
v___x_916_ = v___x_814_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v___x_910_);
lean_ctor_set(v_reuseFailAlloc_917_, 1, v_k_905_);
lean_ctor_set(v_reuseFailAlloc_917_, 2, v_v_906_);
lean_ctor_set(v_reuseFailAlloc_917_, 3, v___x_912_);
lean_ctor_set(v_reuseFailAlloc_917_, 4, v___x_914_);
v___x_916_ = v_reuseFailAlloc_917_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
return v___x_916_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_810_) == 0)
{
lean_object* v_k_924_; lean_object* v_v_925_; lean_object* v___x_926_; lean_object* v___x_928_; 
lean_dec(v_size_806_);
v_k_924_ = lean_ctor_get(v___x_816_, 0);
lean_inc(v_k_924_);
v_v_925_ = lean_ctor_get(v___x_816_, 1);
lean_inc(v_v_925_);
lean_dec_ref(v___x_816_);
v___x_926_ = lean_unsigned_to_nat(3u);
if (v_isShared_891_ == 0)
{
lean_ctor_set(v___x_890_, 4, v_l_809_);
lean_ctor_set(v___x_890_, 2, v_v_925_);
lean_ctor_set(v___x_890_, 1, v_k_924_);
lean_ctor_set(v___x_890_, 0, v___x_811_);
v___x_928_ = v___x_890_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v___x_811_);
lean_ctor_set(v_reuseFailAlloc_932_, 1, v_k_924_);
lean_ctor_set(v_reuseFailAlloc_932_, 2, v_v_925_);
lean_ctor_set(v_reuseFailAlloc_932_, 3, v_l_809_);
lean_ctor_set(v_reuseFailAlloc_932_, 4, v_l_809_);
v___x_928_ = v_reuseFailAlloc_932_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
lean_object* v___x_930_; 
if (v_isShared_815_ == 0)
{
lean_ctor_set(v___x_814_, 4, v_r_810_);
lean_ctor_set(v___x_814_, 3, v___x_928_);
lean_ctor_set(v___x_814_, 2, v_v_808_);
lean_ctor_set(v___x_814_, 1, v_k_807_);
lean_ctor_set(v___x_814_, 0, v___x_926_);
v___x_930_ = v___x_814_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v___x_926_);
lean_ctor_set(v_reuseFailAlloc_931_, 1, v_k_807_);
lean_ctor_set(v_reuseFailAlloc_931_, 2, v_v_808_);
lean_ctor_set(v_reuseFailAlloc_931_, 3, v___x_928_);
lean_ctor_set(v_reuseFailAlloc_931_, 4, v_r_810_);
v___x_930_ = v_reuseFailAlloc_931_;
goto v_reusejp_929_;
}
v_reusejp_929_:
{
return v___x_930_;
}
}
}
else
{
lean_object* v_k_933_; lean_object* v_v_934_; lean_object* v___x_936_; 
v_k_933_ = lean_ctor_get(v___x_816_, 0);
lean_inc(v_k_933_);
v_v_934_ = lean_ctor_get(v___x_816_, 1);
lean_inc(v_v_934_);
lean_dec_ref(v___x_816_);
if (v_isShared_891_ == 0)
{
lean_ctor_set(v___x_890_, 3, v_r_810_);
v___x_936_ = v___x_890_;
goto v_reusejp_935_;
}
else
{
lean_object* v_reuseFailAlloc_941_; 
v_reuseFailAlloc_941_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_941_, 0, v_size_806_);
lean_ctor_set(v_reuseFailAlloc_941_, 1, v_k_807_);
lean_ctor_set(v_reuseFailAlloc_941_, 2, v_v_808_);
lean_ctor_set(v_reuseFailAlloc_941_, 3, v_r_810_);
lean_ctor_set(v_reuseFailAlloc_941_, 4, v_r_810_);
v___x_936_ = v_reuseFailAlloc_941_;
goto v_reusejp_935_;
}
v_reusejp_935_:
{
lean_object* v___x_937_; lean_object* v___x_939_; 
v___x_937_ = lean_unsigned_to_nat(2u);
if (v_isShared_815_ == 0)
{
lean_ctor_set(v___x_814_, 4, v___x_936_);
lean_ctor_set(v___x_814_, 3, v_r_810_);
lean_ctor_set(v___x_814_, 2, v_v_934_);
lean_ctor_set(v___x_814_, 1, v_k_933_);
lean_ctor_set(v___x_814_, 0, v___x_937_);
v___x_939_ = v___x_814_;
goto v_reusejp_938_;
}
else
{
lean_object* v_reuseFailAlloc_940_; 
v_reuseFailAlloc_940_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_940_, 0, v___x_937_);
lean_ctor_set(v_reuseFailAlloc_940_, 1, v_k_933_);
lean_ctor_set(v_reuseFailAlloc_940_, 2, v_v_934_);
lean_ctor_set(v_reuseFailAlloc_940_, 3, v_r_810_);
lean_ctor_set(v_reuseFailAlloc_940_, 4, v___x_936_);
v___x_939_ = v_reuseFailAlloc_940_;
goto v_reusejp_938_;
}
v_reusejp_938_:
{
return v___x_939_;
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
lean_object* v___x_955_; uint8_t v_isShared_956_; uint8_t v_isSharedCheck_1106_; 
lean_inc(v_r_810_);
lean_inc(v_v_808_);
lean_inc(v_k_807_);
v_isSharedCheck_1106_ = !lean_is_exclusive(v_r_622_);
if (v_isSharedCheck_1106_ == 0)
{
lean_object* v_unused_1107_; lean_object* v_unused_1108_; lean_object* v_unused_1109_; lean_object* v_unused_1110_; lean_object* v_unused_1111_; 
v_unused_1107_ = lean_ctor_get(v_r_622_, 4);
lean_dec(v_unused_1107_);
v_unused_1108_ = lean_ctor_get(v_r_622_, 3);
lean_dec(v_unused_1108_);
v_unused_1109_ = lean_ctor_get(v_r_622_, 2);
lean_dec(v_unused_1109_);
v_unused_1110_ = lean_ctor_get(v_r_622_, 1);
lean_dec(v_unused_1110_);
v_unused_1111_ = lean_ctor_get(v_r_622_, 0);
lean_dec(v_unused_1111_);
v___x_955_ = v_r_622_;
v_isShared_956_ = v_isSharedCheck_1106_;
goto v_resetjp_954_;
}
else
{
lean_dec(v_r_622_);
v___x_955_ = lean_box(0);
v_isShared_956_ = v_isSharedCheck_1106_;
goto v_resetjp_954_;
}
v_resetjp_954_:
{
lean_object* v___x_957_; lean_object* v_tree_958_; 
v___x_957_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_807_, v_v_808_, v_l_809_, v_r_810_);
v_tree_958_ = lean_ctor_get(v___x_957_, 2);
lean_inc(v_tree_958_);
if (lean_obj_tag(v_tree_958_) == 0)
{
lean_object* v_k_959_; lean_object* v_v_960_; lean_object* v_size_961_; lean_object* v___x_962_; lean_object* v___x_963_; uint8_t v___x_964_; 
v_k_959_ = lean_ctor_get(v___x_957_, 0);
lean_inc(v_k_959_);
v_v_960_ = lean_ctor_get(v___x_957_, 1);
lean_inc(v_v_960_);
lean_dec_ref(v___x_957_);
v_size_961_ = lean_ctor_get(v_tree_958_, 0);
v___x_962_ = lean_unsigned_to_nat(3u);
v___x_963_ = lean_nat_mul(v___x_962_, v_size_961_);
v___x_964_ = lean_nat_dec_lt(v___x_963_, v_size_801_);
lean_dec(v___x_963_);
if (v___x_964_ == 0)
{
lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_968_; 
lean_dec(v_r_805_);
v___x_965_ = lean_nat_add(v___x_811_, v_size_801_);
v___x_966_ = lean_nat_add(v___x_965_, v_size_961_);
lean_dec(v___x_965_);
if (v_isShared_956_ == 0)
{
lean_ctor_set(v___x_955_, 4, v_tree_958_);
lean_ctor_set(v___x_955_, 3, v_l_621_);
lean_ctor_set(v___x_955_, 2, v_v_960_);
lean_ctor_set(v___x_955_, 1, v_k_959_);
lean_ctor_set(v___x_955_, 0, v___x_966_);
v___x_968_ = v___x_955_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_969_; 
v_reuseFailAlloc_969_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_969_, 0, v___x_966_);
lean_ctor_set(v_reuseFailAlloc_969_, 1, v_k_959_);
lean_ctor_set(v_reuseFailAlloc_969_, 2, v_v_960_);
lean_ctor_set(v_reuseFailAlloc_969_, 3, v_l_621_);
lean_ctor_set(v_reuseFailAlloc_969_, 4, v_tree_958_);
v___x_968_ = v_reuseFailAlloc_969_;
goto v_reusejp_967_;
}
v_reusejp_967_:
{
return v___x_968_;
}
}
else
{
lean_object* v___x_971_; uint8_t v_isShared_972_; uint8_t v_isSharedCheck_1035_; 
lean_inc(v_l_804_);
lean_inc(v_v_803_);
lean_inc(v_k_802_);
lean_inc(v_size_801_);
v_isSharedCheck_1035_ = !lean_is_exclusive(v_l_621_);
if (v_isSharedCheck_1035_ == 0)
{
lean_object* v_unused_1036_; lean_object* v_unused_1037_; lean_object* v_unused_1038_; lean_object* v_unused_1039_; lean_object* v_unused_1040_; 
v_unused_1036_ = lean_ctor_get(v_l_621_, 4);
lean_dec(v_unused_1036_);
v_unused_1037_ = lean_ctor_get(v_l_621_, 3);
lean_dec(v_unused_1037_);
v_unused_1038_ = lean_ctor_get(v_l_621_, 2);
lean_dec(v_unused_1038_);
v_unused_1039_ = lean_ctor_get(v_l_621_, 1);
lean_dec(v_unused_1039_);
v_unused_1040_ = lean_ctor_get(v_l_621_, 0);
lean_dec(v_unused_1040_);
v___x_971_ = v_l_621_;
v_isShared_972_ = v_isSharedCheck_1035_;
goto v_resetjp_970_;
}
else
{
lean_dec(v_l_621_);
v___x_971_ = lean_box(0);
v_isShared_972_ = v_isSharedCheck_1035_;
goto v_resetjp_970_;
}
v_resetjp_970_:
{
lean_object* v_size_973_; lean_object* v_size_974_; lean_object* v_k_975_; lean_object* v_v_976_; lean_object* v_l_977_; lean_object* v_r_978_; lean_object* v___x_979_; lean_object* v___x_980_; uint8_t v___x_981_; 
v_size_973_ = lean_ctor_get(v_l_804_, 0);
v_size_974_ = lean_ctor_get(v_r_805_, 0);
v_k_975_ = lean_ctor_get(v_r_805_, 1);
v_v_976_ = lean_ctor_get(v_r_805_, 2);
v_l_977_ = lean_ctor_get(v_r_805_, 3);
v_r_978_ = lean_ctor_get(v_r_805_, 4);
v___x_979_ = lean_unsigned_to_nat(2u);
v___x_980_ = lean_nat_mul(v___x_979_, v_size_973_);
v___x_981_ = lean_nat_dec_lt(v_size_974_, v___x_980_);
lean_dec(v___x_980_);
if (v___x_981_ == 0)
{
lean_object* v___x_983_; uint8_t v_isShared_984_; uint8_t v_isSharedCheck_1019_; 
lean_inc(v_r_978_);
lean_inc(v_l_977_);
lean_inc(v_v_976_);
lean_inc(v_k_975_);
lean_del_object(v___x_971_);
v_isSharedCheck_1019_ = !lean_is_exclusive(v_r_805_);
if (v_isSharedCheck_1019_ == 0)
{
lean_object* v_unused_1020_; lean_object* v_unused_1021_; lean_object* v_unused_1022_; lean_object* v_unused_1023_; lean_object* v_unused_1024_; 
v_unused_1020_ = lean_ctor_get(v_r_805_, 4);
lean_dec(v_unused_1020_);
v_unused_1021_ = lean_ctor_get(v_r_805_, 3);
lean_dec(v_unused_1021_);
v_unused_1022_ = lean_ctor_get(v_r_805_, 2);
lean_dec(v_unused_1022_);
v_unused_1023_ = lean_ctor_get(v_r_805_, 1);
lean_dec(v_unused_1023_);
v_unused_1024_ = lean_ctor_get(v_r_805_, 0);
lean_dec(v_unused_1024_);
v___x_983_ = v_r_805_;
v_isShared_984_ = v_isSharedCheck_1019_;
goto v_resetjp_982_;
}
else
{
lean_dec(v_r_805_);
v___x_983_ = lean_box(0);
v_isShared_984_ = v_isSharedCheck_1019_;
goto v_resetjp_982_;
}
v_resetjp_982_:
{
lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___y_988_; lean_object* v___y_989_; lean_object* v___y_990_; lean_object* v___x_1007_; lean_object* v___y_1009_; 
v___x_985_ = lean_nat_add(v___x_811_, v_size_801_);
lean_dec(v_size_801_);
v___x_986_ = lean_nat_add(v___x_985_, v_size_961_);
lean_dec(v___x_985_);
v___x_1007_ = lean_nat_add(v___x_811_, v_size_973_);
if (lean_obj_tag(v_l_977_) == 0)
{
lean_object* v_size_1017_; 
v_size_1017_ = lean_ctor_get(v_l_977_, 0);
lean_inc(v_size_1017_);
v___y_1009_ = v_size_1017_;
goto v___jp_1008_;
}
else
{
lean_object* v___x_1018_; 
v___x_1018_ = lean_unsigned_to_nat(0u);
v___y_1009_ = v___x_1018_;
goto v___jp_1008_;
}
v___jp_987_:
{
lean_object* v___x_991_; lean_object* v___x_993_; 
v___x_991_ = lean_nat_add(v___y_988_, v___y_990_);
lean_dec(v___y_990_);
lean_dec(v___y_988_);
lean_inc_ref(v_tree_958_);
if (v_isShared_984_ == 0)
{
lean_ctor_set(v___x_983_, 4, v_tree_958_);
lean_ctor_set(v___x_983_, 3, v_r_978_);
lean_ctor_set(v___x_983_, 2, v_v_960_);
lean_ctor_set(v___x_983_, 1, v_k_959_);
lean_ctor_set(v___x_983_, 0, v___x_991_);
v___x_993_ = v___x_983_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_1006_; 
v_reuseFailAlloc_1006_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1006_, 0, v___x_991_);
lean_ctor_set(v_reuseFailAlloc_1006_, 1, v_k_959_);
lean_ctor_set(v_reuseFailAlloc_1006_, 2, v_v_960_);
lean_ctor_set(v_reuseFailAlloc_1006_, 3, v_r_978_);
lean_ctor_set(v_reuseFailAlloc_1006_, 4, v_tree_958_);
v___x_993_ = v_reuseFailAlloc_1006_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1000_; 
v_isSharedCheck_1000_ = !lean_is_exclusive(v_tree_958_);
if (v_isSharedCheck_1000_ == 0)
{
lean_object* v_unused_1001_; lean_object* v_unused_1002_; lean_object* v_unused_1003_; lean_object* v_unused_1004_; lean_object* v_unused_1005_; 
v_unused_1001_ = lean_ctor_get(v_tree_958_, 4);
lean_dec(v_unused_1001_);
v_unused_1002_ = lean_ctor_get(v_tree_958_, 3);
lean_dec(v_unused_1002_);
v_unused_1003_ = lean_ctor_get(v_tree_958_, 2);
lean_dec(v_unused_1003_);
v_unused_1004_ = lean_ctor_get(v_tree_958_, 1);
lean_dec(v_unused_1004_);
v_unused_1005_ = lean_ctor_get(v_tree_958_, 0);
lean_dec(v_unused_1005_);
v___x_995_ = v_tree_958_;
v_isShared_996_ = v_isSharedCheck_1000_;
goto v_resetjp_994_;
}
else
{
lean_dec(v_tree_958_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1000_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
lean_object* v___x_998_; 
if (v_isShared_996_ == 0)
{
lean_ctor_set(v___x_995_, 4, v___x_993_);
lean_ctor_set(v___x_995_, 3, v___y_989_);
lean_ctor_set(v___x_995_, 2, v_v_976_);
lean_ctor_set(v___x_995_, 1, v_k_975_);
lean_ctor_set(v___x_995_, 0, v___x_986_);
v___x_998_ = v___x_995_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v___x_986_);
lean_ctor_set(v_reuseFailAlloc_999_, 1, v_k_975_);
lean_ctor_set(v_reuseFailAlloc_999_, 2, v_v_976_);
lean_ctor_set(v_reuseFailAlloc_999_, 3, v___y_989_);
lean_ctor_set(v_reuseFailAlloc_999_, 4, v___x_993_);
v___x_998_ = v_reuseFailAlloc_999_;
goto v_reusejp_997_;
}
v_reusejp_997_:
{
return v___x_998_;
}
}
}
}
v___jp_1008_:
{
lean_object* v___x_1010_; lean_object* v___x_1012_; 
v___x_1010_ = lean_nat_add(v___x_1007_, v___y_1009_);
lean_dec(v___y_1009_);
lean_dec(v___x_1007_);
if (v_isShared_956_ == 0)
{
lean_ctor_set(v___x_955_, 4, v_l_977_);
lean_ctor_set(v___x_955_, 3, v_l_804_);
lean_ctor_set(v___x_955_, 2, v_v_803_);
lean_ctor_set(v___x_955_, 1, v_k_802_);
lean_ctor_set(v___x_955_, 0, v___x_1010_);
v___x_1012_ = v___x_955_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v___x_1010_);
lean_ctor_set(v_reuseFailAlloc_1016_, 1, v_k_802_);
lean_ctor_set(v_reuseFailAlloc_1016_, 2, v_v_803_);
lean_ctor_set(v_reuseFailAlloc_1016_, 3, v_l_804_);
lean_ctor_set(v_reuseFailAlloc_1016_, 4, v_l_977_);
v___x_1012_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
lean_object* v___x_1013_; 
v___x_1013_ = lean_nat_add(v___x_811_, v_size_961_);
if (lean_obj_tag(v_r_978_) == 0)
{
lean_object* v_size_1014_; 
v_size_1014_ = lean_ctor_get(v_r_978_, 0);
lean_inc(v_size_1014_);
v___y_988_ = v___x_1013_;
v___y_989_ = v___x_1012_;
v___y_990_ = v_size_1014_;
goto v___jp_987_;
}
else
{
lean_object* v___x_1015_; 
v___x_1015_ = lean_unsigned_to_nat(0u);
v___y_988_ = v___x_1013_;
v___y_989_ = v___x_1012_;
v___y_990_ = v___x_1015_;
goto v___jp_987_;
}
}
}
}
}
else
{
lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1030_; 
v___x_1025_ = lean_nat_add(v___x_811_, v_size_801_);
lean_dec(v_size_801_);
v___x_1026_ = lean_nat_add(v___x_1025_, v_size_961_);
lean_dec(v___x_1025_);
v___x_1027_ = lean_nat_add(v___x_811_, v_size_961_);
v___x_1028_ = lean_nat_add(v___x_1027_, v_size_974_);
lean_dec(v___x_1027_);
if (v_isShared_956_ == 0)
{
lean_ctor_set(v___x_955_, 4, v_tree_958_);
lean_ctor_set(v___x_955_, 3, v_r_805_);
lean_ctor_set(v___x_955_, 2, v_v_960_);
lean_ctor_set(v___x_955_, 1, v_k_959_);
lean_ctor_set(v___x_955_, 0, v___x_1028_);
v___x_1030_ = v___x_955_;
goto v_reusejp_1029_;
}
else
{
lean_object* v_reuseFailAlloc_1034_; 
v_reuseFailAlloc_1034_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1034_, 0, v___x_1028_);
lean_ctor_set(v_reuseFailAlloc_1034_, 1, v_k_959_);
lean_ctor_set(v_reuseFailAlloc_1034_, 2, v_v_960_);
lean_ctor_set(v_reuseFailAlloc_1034_, 3, v_r_805_);
lean_ctor_set(v_reuseFailAlloc_1034_, 4, v_tree_958_);
v___x_1030_ = v_reuseFailAlloc_1034_;
goto v_reusejp_1029_;
}
v_reusejp_1029_:
{
lean_object* v___x_1032_; 
if (v_isShared_972_ == 0)
{
lean_ctor_set(v___x_971_, 4, v___x_1030_);
lean_ctor_set(v___x_971_, 0, v___x_1026_);
v___x_1032_ = v___x_971_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v___x_1026_);
lean_ctor_set(v_reuseFailAlloc_1033_, 1, v_k_802_);
lean_ctor_set(v_reuseFailAlloc_1033_, 2, v_v_803_);
lean_ctor_set(v_reuseFailAlloc_1033_, 3, v_l_804_);
lean_ctor_set(v_reuseFailAlloc_1033_, 4, v___x_1030_);
v___x_1032_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
return v___x_1032_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_804_) == 0)
{
lean_object* v___x_1042_; uint8_t v_isShared_1043_; uint8_t v_isSharedCheck_1064_; 
lean_inc_ref(v_l_804_);
lean_inc(v_v_803_);
lean_inc(v_k_802_);
lean_inc(v_size_801_);
v_isSharedCheck_1064_ = !lean_is_exclusive(v_l_621_);
if (v_isSharedCheck_1064_ == 0)
{
lean_object* v_unused_1065_; lean_object* v_unused_1066_; lean_object* v_unused_1067_; lean_object* v_unused_1068_; lean_object* v_unused_1069_; 
v_unused_1065_ = lean_ctor_get(v_l_621_, 4);
lean_dec(v_unused_1065_);
v_unused_1066_ = lean_ctor_get(v_l_621_, 3);
lean_dec(v_unused_1066_);
v_unused_1067_ = lean_ctor_get(v_l_621_, 2);
lean_dec(v_unused_1067_);
v_unused_1068_ = lean_ctor_get(v_l_621_, 1);
lean_dec(v_unused_1068_);
v_unused_1069_ = lean_ctor_get(v_l_621_, 0);
lean_dec(v_unused_1069_);
v___x_1042_ = v_l_621_;
v_isShared_1043_ = v_isSharedCheck_1064_;
goto v_resetjp_1041_;
}
else
{
lean_dec(v_l_621_);
v___x_1042_ = lean_box(0);
v_isShared_1043_ = v_isSharedCheck_1064_;
goto v_resetjp_1041_;
}
v_resetjp_1041_:
{
if (lean_obj_tag(v_r_805_) == 0)
{
lean_object* v_k_1044_; lean_object* v_v_1045_; lean_object* v_size_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1050_; 
v_k_1044_ = lean_ctor_get(v___x_957_, 0);
lean_inc(v_k_1044_);
v_v_1045_ = lean_ctor_get(v___x_957_, 1);
lean_inc(v_v_1045_);
lean_dec_ref(v___x_957_);
v_size_1046_ = lean_ctor_get(v_r_805_, 0);
v___x_1047_ = lean_nat_add(v___x_811_, v_size_801_);
lean_dec(v_size_801_);
v___x_1048_ = lean_nat_add(v___x_811_, v_size_1046_);
if (v_isShared_956_ == 0)
{
lean_ctor_set(v___x_955_, 4, v_tree_958_);
lean_ctor_set(v___x_955_, 3, v_r_805_);
lean_ctor_set(v___x_955_, 2, v_v_1045_);
lean_ctor_set(v___x_955_, 1, v_k_1044_);
lean_ctor_set(v___x_955_, 0, v___x_1048_);
v___x_1050_ = v___x_955_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1054_; 
v_reuseFailAlloc_1054_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1054_, 0, v___x_1048_);
lean_ctor_set(v_reuseFailAlloc_1054_, 1, v_k_1044_);
lean_ctor_set(v_reuseFailAlloc_1054_, 2, v_v_1045_);
lean_ctor_set(v_reuseFailAlloc_1054_, 3, v_r_805_);
lean_ctor_set(v_reuseFailAlloc_1054_, 4, v_tree_958_);
v___x_1050_ = v_reuseFailAlloc_1054_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
lean_object* v___x_1052_; 
if (v_isShared_1043_ == 0)
{
lean_ctor_set(v___x_1042_, 4, v___x_1050_);
lean_ctor_set(v___x_1042_, 0, v___x_1047_);
v___x_1052_ = v___x_1042_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v___x_1047_);
lean_ctor_set(v_reuseFailAlloc_1053_, 1, v_k_802_);
lean_ctor_set(v_reuseFailAlloc_1053_, 2, v_v_803_);
lean_ctor_set(v_reuseFailAlloc_1053_, 3, v_l_804_);
lean_ctor_set(v_reuseFailAlloc_1053_, 4, v___x_1050_);
v___x_1052_ = v_reuseFailAlloc_1053_;
goto v_reusejp_1051_;
}
v_reusejp_1051_:
{
return v___x_1052_;
}
}
}
else
{
lean_object* v_k_1055_; lean_object* v_v_1056_; lean_object* v___x_1057_; lean_object* v___x_1059_; 
lean_dec(v_size_801_);
v_k_1055_ = lean_ctor_get(v___x_957_, 0);
lean_inc(v_k_1055_);
v_v_1056_ = lean_ctor_get(v___x_957_, 1);
lean_inc(v_v_1056_);
lean_dec_ref(v___x_957_);
v___x_1057_ = lean_unsigned_to_nat(3u);
if (v_isShared_956_ == 0)
{
lean_ctor_set(v___x_955_, 4, v_r_805_);
lean_ctor_set(v___x_955_, 3, v_r_805_);
lean_ctor_set(v___x_955_, 2, v_v_1056_);
lean_ctor_set(v___x_955_, 1, v_k_1055_);
lean_ctor_set(v___x_955_, 0, v___x_811_);
v___x_1059_ = v___x_955_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v___x_811_);
lean_ctor_set(v_reuseFailAlloc_1063_, 1, v_k_1055_);
lean_ctor_set(v_reuseFailAlloc_1063_, 2, v_v_1056_);
lean_ctor_set(v_reuseFailAlloc_1063_, 3, v_r_805_);
lean_ctor_set(v_reuseFailAlloc_1063_, 4, v_r_805_);
v___x_1059_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1058_;
}
v_reusejp_1058_:
{
lean_object* v___x_1061_; 
if (v_isShared_1043_ == 0)
{
lean_ctor_set(v___x_1042_, 4, v___x_1059_);
lean_ctor_set(v___x_1042_, 0, v___x_1057_);
v___x_1061_ = v___x_1042_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v___x_1057_);
lean_ctor_set(v_reuseFailAlloc_1062_, 1, v_k_802_);
lean_ctor_set(v_reuseFailAlloc_1062_, 2, v_v_803_);
lean_ctor_set(v_reuseFailAlloc_1062_, 3, v_l_804_);
lean_ctor_set(v_reuseFailAlloc_1062_, 4, v___x_1059_);
v___x_1061_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
return v___x_1061_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_805_) == 0)
{
lean_object* v___x_1071_; uint8_t v_isShared_1072_; uint8_t v_isSharedCheck_1094_; 
lean_inc(v_l_804_);
lean_inc(v_v_803_);
lean_inc(v_k_802_);
v_isSharedCheck_1094_ = !lean_is_exclusive(v_l_621_);
if (v_isSharedCheck_1094_ == 0)
{
lean_object* v_unused_1095_; lean_object* v_unused_1096_; lean_object* v_unused_1097_; lean_object* v_unused_1098_; lean_object* v_unused_1099_; 
v_unused_1095_ = lean_ctor_get(v_l_621_, 4);
lean_dec(v_unused_1095_);
v_unused_1096_ = lean_ctor_get(v_l_621_, 3);
lean_dec(v_unused_1096_);
v_unused_1097_ = lean_ctor_get(v_l_621_, 2);
lean_dec(v_unused_1097_);
v_unused_1098_ = lean_ctor_get(v_l_621_, 1);
lean_dec(v_unused_1098_);
v_unused_1099_ = lean_ctor_get(v_l_621_, 0);
lean_dec(v_unused_1099_);
v___x_1071_ = v_l_621_;
v_isShared_1072_ = v_isSharedCheck_1094_;
goto v_resetjp_1070_;
}
else
{
lean_dec(v_l_621_);
v___x_1071_ = lean_box(0);
v_isShared_1072_ = v_isSharedCheck_1094_;
goto v_resetjp_1070_;
}
v_resetjp_1070_:
{
lean_object* v_k_1073_; lean_object* v_v_1074_; lean_object* v_k_1075_; lean_object* v_v_1076_; lean_object* v___x_1078_; uint8_t v_isShared_1079_; uint8_t v_isSharedCheck_1090_; 
v_k_1073_ = lean_ctor_get(v___x_957_, 0);
lean_inc(v_k_1073_);
v_v_1074_ = lean_ctor_get(v___x_957_, 1);
lean_inc(v_v_1074_);
lean_dec_ref(v___x_957_);
v_k_1075_ = lean_ctor_get(v_r_805_, 1);
v_v_1076_ = lean_ctor_get(v_r_805_, 2);
v_isSharedCheck_1090_ = !lean_is_exclusive(v_r_805_);
if (v_isSharedCheck_1090_ == 0)
{
lean_object* v_unused_1091_; lean_object* v_unused_1092_; lean_object* v_unused_1093_; 
v_unused_1091_ = lean_ctor_get(v_r_805_, 4);
lean_dec(v_unused_1091_);
v_unused_1092_ = lean_ctor_get(v_r_805_, 3);
lean_dec(v_unused_1092_);
v_unused_1093_ = lean_ctor_get(v_r_805_, 0);
lean_dec(v_unused_1093_);
v___x_1078_ = v_r_805_;
v_isShared_1079_ = v_isSharedCheck_1090_;
goto v_resetjp_1077_;
}
else
{
lean_inc(v_v_1076_);
lean_inc(v_k_1075_);
lean_dec(v_r_805_);
v___x_1078_ = lean_box(0);
v_isShared_1079_ = v_isSharedCheck_1090_;
goto v_resetjp_1077_;
}
v_resetjp_1077_:
{
lean_object* v___x_1080_; lean_object* v___x_1082_; 
v___x_1080_ = lean_unsigned_to_nat(3u);
if (v_isShared_1079_ == 0)
{
lean_ctor_set(v___x_1078_, 4, v_l_804_);
lean_ctor_set(v___x_1078_, 3, v_l_804_);
lean_ctor_set(v___x_1078_, 2, v_v_803_);
lean_ctor_set(v___x_1078_, 1, v_k_802_);
lean_ctor_set(v___x_1078_, 0, v___x_811_);
v___x_1082_ = v___x_1078_;
goto v_reusejp_1081_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v___x_811_);
lean_ctor_set(v_reuseFailAlloc_1089_, 1, v_k_802_);
lean_ctor_set(v_reuseFailAlloc_1089_, 2, v_v_803_);
lean_ctor_set(v_reuseFailAlloc_1089_, 3, v_l_804_);
lean_ctor_set(v_reuseFailAlloc_1089_, 4, v_l_804_);
v___x_1082_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1081_;
}
v_reusejp_1081_:
{
lean_object* v___x_1084_; 
if (v_isShared_956_ == 0)
{
lean_ctor_set(v___x_955_, 4, v_l_804_);
lean_ctor_set(v___x_955_, 3, v_l_804_);
lean_ctor_set(v___x_955_, 2, v_v_1074_);
lean_ctor_set(v___x_955_, 1, v_k_1073_);
lean_ctor_set(v___x_955_, 0, v___x_811_);
v___x_1084_ = v___x_955_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v___x_811_);
lean_ctor_set(v_reuseFailAlloc_1088_, 1, v_k_1073_);
lean_ctor_set(v_reuseFailAlloc_1088_, 2, v_v_1074_);
lean_ctor_set(v_reuseFailAlloc_1088_, 3, v_l_804_);
lean_ctor_set(v_reuseFailAlloc_1088_, 4, v_l_804_);
v___x_1084_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
lean_object* v___x_1086_; 
if (v_isShared_1072_ == 0)
{
lean_ctor_set(v___x_1071_, 4, v___x_1084_);
lean_ctor_set(v___x_1071_, 3, v___x_1082_);
lean_ctor_set(v___x_1071_, 2, v_v_1076_);
lean_ctor_set(v___x_1071_, 1, v_k_1075_);
lean_ctor_set(v___x_1071_, 0, v___x_1080_);
v___x_1086_ = v___x_1071_;
goto v_reusejp_1085_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v___x_1080_);
lean_ctor_set(v_reuseFailAlloc_1087_, 1, v_k_1075_);
lean_ctor_set(v_reuseFailAlloc_1087_, 2, v_v_1076_);
lean_ctor_set(v_reuseFailAlloc_1087_, 3, v___x_1082_);
lean_ctor_set(v_reuseFailAlloc_1087_, 4, v___x_1084_);
v___x_1086_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1085_;
}
v_reusejp_1085_:
{
return v___x_1086_;
}
}
}
}
}
}
else
{
lean_object* v_k_1100_; lean_object* v_v_1101_; lean_object* v___x_1102_; lean_object* v___x_1104_; 
v_k_1100_ = lean_ctor_get(v___x_957_, 0);
lean_inc(v_k_1100_);
v_v_1101_ = lean_ctor_get(v___x_957_, 1);
lean_inc(v_v_1101_);
lean_dec_ref(v___x_957_);
v___x_1102_ = lean_unsigned_to_nat(2u);
if (v_isShared_956_ == 0)
{
lean_ctor_set(v___x_955_, 4, v_r_805_);
lean_ctor_set(v___x_955_, 3, v_l_621_);
lean_ctor_set(v___x_955_, 2, v_v_1101_);
lean_ctor_set(v___x_955_, 1, v_k_1100_);
lean_ctor_set(v___x_955_, 0, v___x_1102_);
v___x_1104_ = v___x_955_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v___x_1102_);
lean_ctor_set(v_reuseFailAlloc_1105_, 1, v_k_1100_);
lean_ctor_set(v_reuseFailAlloc_1105_, 2, v_v_1101_);
lean_ctor_set(v_reuseFailAlloc_1105_, 3, v_l_621_);
lean_ctor_set(v_reuseFailAlloc_1105_, 4, v_r_805_);
v___x_1104_ = v_reuseFailAlloc_1105_;
goto v_reusejp_1103_;
}
v_reusejp_1103_:
{
return v___x_1104_;
}
}
}
}
}
}
}
else
{
return v_l_621_;
}
}
else
{
return v_r_622_;
}
}
default: 
{
lean_object* v_impl_1112_; lean_object* v___x_1113_; 
v_impl_1112_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Compiler_LCNF_Check_Impure_makeScalar_spec__0___redArg(v_k_617_, v_r_622_);
v___x_1113_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_1112_) == 0)
{
if (lean_obj_tag(v_l_621_) == 0)
{
lean_object* v_size_1114_; lean_object* v_size_1115_; lean_object* v_k_1116_; lean_object* v_v_1117_; lean_object* v_l_1118_; lean_object* v_r_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; uint8_t v___x_1122_; 
v_size_1114_ = lean_ctor_get(v_impl_1112_, 0);
lean_inc(v_size_1114_);
v_size_1115_ = lean_ctor_get(v_l_621_, 0);
v_k_1116_ = lean_ctor_get(v_l_621_, 1);
v_v_1117_ = lean_ctor_get(v_l_621_, 2);
v_l_1118_ = lean_ctor_get(v_l_621_, 3);
v_r_1119_ = lean_ctor_get(v_l_621_, 4);
lean_inc(v_r_1119_);
v___x_1120_ = lean_unsigned_to_nat(3u);
v___x_1121_ = lean_nat_mul(v___x_1120_, v_size_1114_);
v___x_1122_ = lean_nat_dec_lt(v___x_1121_, v_size_1115_);
lean_dec(v___x_1121_);
if (v___x_1122_ == 0)
{
lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1126_; 
lean_dec(v_r_1119_);
v___x_1123_ = lean_nat_add(v___x_1113_, v_size_1115_);
v___x_1124_ = lean_nat_add(v___x_1123_, v_size_1114_);
lean_dec(v_size_1114_);
lean_dec(v___x_1123_);
if (v_isShared_625_ == 0)
{
lean_ctor_set(v___x_624_, 4, v_impl_1112_);
lean_ctor_set(v___x_624_, 0, v___x_1124_);
v___x_1126_ = v___x_624_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v___x_1124_);
lean_ctor_set(v_reuseFailAlloc_1127_, 1, v_k_619_);
lean_ctor_set(v_reuseFailAlloc_1127_, 2, v_v_620_);
lean_ctor_set(v_reuseFailAlloc_1127_, 3, v_l_621_);
lean_ctor_set(v_reuseFailAlloc_1127_, 4, v_impl_1112_);
v___x_1126_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1125_;
}
v_reusejp_1125_:
{
return v___x_1126_;
}
}
else
{
lean_object* v___x_1129_; uint8_t v_isShared_1130_; uint8_t v_isSharedCheck_1193_; 
lean_inc(v_l_1118_);
lean_inc(v_v_1117_);
lean_inc(v_k_1116_);
lean_inc(v_size_1115_);
v_isSharedCheck_1193_ = !lean_is_exclusive(v_l_621_);
if (v_isSharedCheck_1193_ == 0)
{
lean_object* v_unused_1194_; lean_object* v_unused_1195_; lean_object* v_unused_1196_; lean_object* v_unused_1197_; lean_object* v_unused_1198_; 
v_unused_1194_ = lean_ctor_get(v_l_621_, 4);
lean_dec(v_unused_1194_);
v_unused_1195_ = lean_ctor_get(v_l_621_, 3);
lean_dec(v_unused_1195_);
v_unused_1196_ = lean_ctor_get(v_l_621_, 2);
lean_dec(v_unused_1196_);
v_unused_1197_ = lean_ctor_get(v_l_621_, 1);
lean_dec(v_unused_1197_);
v_unused_1198_ = lean_ctor_get(v_l_621_, 0);
lean_dec(v_unused_1198_);
v___x_1129_ = v_l_621_;
v_isShared_1130_ = v_isSharedCheck_1193_;
goto v_resetjp_1128_;
}
else
{
lean_dec(v_l_621_);
v___x_1129_ = lean_box(0);
v_isShared_1130_ = v_isSharedCheck_1193_;
goto v_resetjp_1128_;
}
v_resetjp_1128_:
{
lean_object* v_size_1131_; lean_object* v_size_1132_; lean_object* v_k_1133_; lean_object* v_v_1134_; lean_object* v_l_1135_; lean_object* v_r_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; uint8_t v___x_1139_; 
v_size_1131_ = lean_ctor_get(v_l_1118_, 0);
v_size_1132_ = lean_ctor_get(v_r_1119_, 0);
v_k_1133_ = lean_ctor_get(v_r_1119_, 1);
v_v_1134_ = lean_ctor_get(v_r_1119_, 2);
v_l_1135_ = lean_ctor_get(v_r_1119_, 3);
v_r_1136_ = lean_ctor_get(v_r_1119_, 4);
v___x_1137_ = lean_unsigned_to_nat(2u);
v___x_1138_ = lean_nat_mul(v___x_1137_, v_size_1131_);
v___x_1139_ = lean_nat_dec_lt(v_size_1132_, v___x_1138_);
lean_dec(v___x_1138_);
if (v___x_1139_ == 0)
{
lean_object* v___x_1141_; uint8_t v_isShared_1142_; uint8_t v_isSharedCheck_1168_; 
lean_inc(v_r_1136_);
lean_inc(v_l_1135_);
lean_inc(v_v_1134_);
lean_inc(v_k_1133_);
v_isSharedCheck_1168_ = !lean_is_exclusive(v_r_1119_);
if (v_isSharedCheck_1168_ == 0)
{
lean_object* v_unused_1169_; lean_object* v_unused_1170_; lean_object* v_unused_1171_; lean_object* v_unused_1172_; lean_object* v_unused_1173_; 
v_unused_1169_ = lean_ctor_get(v_r_1119_, 4);
lean_dec(v_unused_1169_);
v_unused_1170_ = lean_ctor_get(v_r_1119_, 3);
lean_dec(v_unused_1170_);
v_unused_1171_ = lean_ctor_get(v_r_1119_, 2);
lean_dec(v_unused_1171_);
v_unused_1172_ = lean_ctor_get(v_r_1119_, 1);
lean_dec(v_unused_1172_);
v_unused_1173_ = lean_ctor_get(v_r_1119_, 0);
lean_dec(v_unused_1173_);
v___x_1141_ = v_r_1119_;
v_isShared_1142_ = v_isSharedCheck_1168_;
goto v_resetjp_1140_;
}
else
{
lean_dec(v_r_1119_);
v___x_1141_ = lean_box(0);
v_isShared_1142_ = v_isSharedCheck_1168_;
goto v_resetjp_1140_;
}
v_resetjp_1140_:
{
lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___y_1146_; lean_object* v___y_1147_; lean_object* v___y_1148_; lean_object* v___x_1156_; lean_object* v___y_1158_; 
v___x_1143_ = lean_nat_add(v___x_1113_, v_size_1115_);
lean_dec(v_size_1115_);
v___x_1144_ = lean_nat_add(v___x_1143_, v_size_1114_);
lean_dec(v___x_1143_);
v___x_1156_ = lean_nat_add(v___x_1113_, v_size_1131_);
if (lean_obj_tag(v_l_1135_) == 0)
{
lean_object* v_size_1166_; 
v_size_1166_ = lean_ctor_get(v_l_1135_, 0);
lean_inc(v_size_1166_);
v___y_1158_ = v_size_1166_;
goto v___jp_1157_;
}
else
{
lean_object* v___x_1167_; 
v___x_1167_ = lean_unsigned_to_nat(0u);
v___y_1158_ = v___x_1167_;
goto v___jp_1157_;
}
v___jp_1145_:
{
lean_object* v___x_1149_; lean_object* v___x_1151_; 
v___x_1149_ = lean_nat_add(v___y_1146_, v___y_1148_);
lean_dec(v___y_1148_);
lean_dec(v___y_1146_);
if (v_isShared_1142_ == 0)
{
lean_ctor_set(v___x_1141_, 4, v_impl_1112_);
lean_ctor_set(v___x_1141_, 3, v_r_1136_);
lean_ctor_set(v___x_1141_, 2, v_v_620_);
lean_ctor_set(v___x_1141_, 1, v_k_619_);
lean_ctor_set(v___x_1141_, 0, v___x_1149_);
v___x_1151_ = v___x_1141_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1155_; 
v_reuseFailAlloc_1155_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1155_, 0, v___x_1149_);
lean_ctor_set(v_reuseFailAlloc_1155_, 1, v_k_619_);
lean_ctor_set(v_reuseFailAlloc_1155_, 2, v_v_620_);
lean_ctor_set(v_reuseFailAlloc_1155_, 3, v_r_1136_);
lean_ctor_set(v_reuseFailAlloc_1155_, 4, v_impl_1112_);
v___x_1151_ = v_reuseFailAlloc_1155_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
lean_object* v___x_1153_; 
if (v_isShared_1130_ == 0)
{
lean_ctor_set(v___x_1129_, 4, v___x_1151_);
lean_ctor_set(v___x_1129_, 3, v___y_1147_);
lean_ctor_set(v___x_1129_, 2, v_v_1134_);
lean_ctor_set(v___x_1129_, 1, v_k_1133_);
lean_ctor_set(v___x_1129_, 0, v___x_1144_);
v___x_1153_ = v___x_1129_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1154_, 0, v___x_1144_);
lean_ctor_set(v_reuseFailAlloc_1154_, 1, v_k_1133_);
lean_ctor_set(v_reuseFailAlloc_1154_, 2, v_v_1134_);
lean_ctor_set(v_reuseFailAlloc_1154_, 3, v___y_1147_);
lean_ctor_set(v_reuseFailAlloc_1154_, 4, v___x_1151_);
v___x_1153_ = v_reuseFailAlloc_1154_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
return v___x_1153_;
}
}
}
v___jp_1157_:
{
lean_object* v___x_1159_; lean_object* v___x_1161_; 
v___x_1159_ = lean_nat_add(v___x_1156_, v___y_1158_);
lean_dec(v___y_1158_);
lean_dec(v___x_1156_);
if (v_isShared_625_ == 0)
{
lean_ctor_set(v___x_624_, 4, v_l_1135_);
lean_ctor_set(v___x_624_, 3, v_l_1118_);
lean_ctor_set(v___x_624_, 2, v_v_1117_);
lean_ctor_set(v___x_624_, 1, v_k_1116_);
lean_ctor_set(v___x_624_, 0, v___x_1159_);
v___x_1161_ = v___x_624_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1165_; 
v_reuseFailAlloc_1165_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1165_, 0, v___x_1159_);
lean_ctor_set(v_reuseFailAlloc_1165_, 1, v_k_1116_);
lean_ctor_set(v_reuseFailAlloc_1165_, 2, v_v_1117_);
lean_ctor_set(v_reuseFailAlloc_1165_, 3, v_l_1118_);
lean_ctor_set(v_reuseFailAlloc_1165_, 4, v_l_1135_);
v___x_1161_ = v_reuseFailAlloc_1165_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
lean_object* v___x_1162_; 
v___x_1162_ = lean_nat_add(v___x_1113_, v_size_1114_);
lean_dec(v_size_1114_);
if (lean_obj_tag(v_r_1136_) == 0)
{
lean_object* v_size_1163_; 
v_size_1163_ = lean_ctor_get(v_r_1136_, 0);
lean_inc(v_size_1163_);
v___y_1146_ = v___x_1162_;
v___y_1147_ = v___x_1161_;
v___y_1148_ = v_size_1163_;
goto v___jp_1145_;
}
else
{
lean_object* v___x_1164_; 
v___x_1164_ = lean_unsigned_to_nat(0u);
v___y_1146_ = v___x_1162_;
v___y_1147_ = v___x_1161_;
v___y_1148_ = v___x_1164_;
goto v___jp_1145_;
}
}
}
}
}
else
{
lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1179_; 
lean_del_object(v___x_624_);
v___x_1174_ = lean_nat_add(v___x_1113_, v_size_1115_);
lean_dec(v_size_1115_);
v___x_1175_ = lean_nat_add(v___x_1174_, v_size_1114_);
lean_dec(v___x_1174_);
v___x_1176_ = lean_nat_add(v___x_1113_, v_size_1114_);
lean_dec(v_size_1114_);
v___x_1177_ = lean_nat_add(v___x_1176_, v_size_1132_);
lean_dec(v___x_1176_);
lean_inc_ref(v_impl_1112_);
if (v_isShared_1130_ == 0)
{
lean_ctor_set(v___x_1129_, 4, v_impl_1112_);
lean_ctor_set(v___x_1129_, 3, v_r_1119_);
lean_ctor_set(v___x_1129_, 2, v_v_620_);
lean_ctor_set(v___x_1129_, 1, v_k_619_);
lean_ctor_set(v___x_1129_, 0, v___x_1177_);
v___x_1179_ = v___x_1129_;
goto v_reusejp_1178_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v___x_1177_);
lean_ctor_set(v_reuseFailAlloc_1192_, 1, v_k_619_);
lean_ctor_set(v_reuseFailAlloc_1192_, 2, v_v_620_);
lean_ctor_set(v_reuseFailAlloc_1192_, 3, v_r_1119_);
lean_ctor_set(v_reuseFailAlloc_1192_, 4, v_impl_1112_);
v___x_1179_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1178_;
}
v_reusejp_1178_:
{
lean_object* v___x_1181_; uint8_t v_isShared_1182_; uint8_t v_isSharedCheck_1186_; 
v_isSharedCheck_1186_ = !lean_is_exclusive(v_impl_1112_);
if (v_isSharedCheck_1186_ == 0)
{
lean_object* v_unused_1187_; lean_object* v_unused_1188_; lean_object* v_unused_1189_; lean_object* v_unused_1190_; lean_object* v_unused_1191_; 
v_unused_1187_ = lean_ctor_get(v_impl_1112_, 4);
lean_dec(v_unused_1187_);
v_unused_1188_ = lean_ctor_get(v_impl_1112_, 3);
lean_dec(v_unused_1188_);
v_unused_1189_ = lean_ctor_get(v_impl_1112_, 2);
lean_dec(v_unused_1189_);
v_unused_1190_ = lean_ctor_get(v_impl_1112_, 1);
lean_dec(v_unused_1190_);
v_unused_1191_ = lean_ctor_get(v_impl_1112_, 0);
lean_dec(v_unused_1191_);
v___x_1181_ = v_impl_1112_;
v_isShared_1182_ = v_isSharedCheck_1186_;
goto v_resetjp_1180_;
}
else
{
lean_dec(v_impl_1112_);
v___x_1181_ = lean_box(0);
v_isShared_1182_ = v_isSharedCheck_1186_;
goto v_resetjp_1180_;
}
v_resetjp_1180_:
{
lean_object* v___x_1184_; 
if (v_isShared_1182_ == 0)
{
lean_ctor_set(v___x_1181_, 4, v___x_1179_);
lean_ctor_set(v___x_1181_, 3, v_l_1118_);
lean_ctor_set(v___x_1181_, 2, v_v_1117_);
lean_ctor_set(v___x_1181_, 1, v_k_1116_);
lean_ctor_set(v___x_1181_, 0, v___x_1175_);
v___x_1184_ = v___x_1181_;
goto v_reusejp_1183_;
}
else
{
lean_object* v_reuseFailAlloc_1185_; 
v_reuseFailAlloc_1185_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1185_, 0, v___x_1175_);
lean_ctor_set(v_reuseFailAlloc_1185_, 1, v_k_1116_);
lean_ctor_set(v_reuseFailAlloc_1185_, 2, v_v_1117_);
lean_ctor_set(v_reuseFailAlloc_1185_, 3, v_l_1118_);
lean_ctor_set(v_reuseFailAlloc_1185_, 4, v___x_1179_);
v___x_1184_ = v_reuseFailAlloc_1185_;
goto v_reusejp_1183_;
}
v_reusejp_1183_:
{
return v___x_1184_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_1199_; lean_object* v___x_1200_; lean_object* v___x_1202_; 
v_size_1199_ = lean_ctor_get(v_impl_1112_, 0);
lean_inc(v_size_1199_);
v___x_1200_ = lean_nat_add(v___x_1113_, v_size_1199_);
lean_dec(v_size_1199_);
if (v_isShared_625_ == 0)
{
lean_ctor_set(v___x_624_, 4, v_impl_1112_);
lean_ctor_set(v___x_624_, 0, v___x_1200_);
v___x_1202_ = v___x_624_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v___x_1200_);
lean_ctor_set(v_reuseFailAlloc_1203_, 1, v_k_619_);
lean_ctor_set(v_reuseFailAlloc_1203_, 2, v_v_620_);
lean_ctor_set(v_reuseFailAlloc_1203_, 3, v_l_621_);
lean_ctor_set(v_reuseFailAlloc_1203_, 4, v_impl_1112_);
v___x_1202_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
return v___x_1202_;
}
}
}
else
{
if (lean_obj_tag(v_l_621_) == 0)
{
lean_object* v_l_1204_; 
v_l_1204_ = lean_ctor_get(v_l_621_, 3);
if (lean_obj_tag(v_l_1204_) == 0)
{
lean_object* v_r_1205_; 
lean_inc_ref(v_l_1204_);
v_r_1205_ = lean_ctor_get(v_l_621_, 4);
lean_inc(v_r_1205_);
if (lean_obj_tag(v_r_1205_) == 0)
{
lean_object* v_size_1206_; lean_object* v_k_1207_; lean_object* v_v_1208_; lean_object* v___x_1210_; uint8_t v_isShared_1211_; uint8_t v_isSharedCheck_1221_; 
v_size_1206_ = lean_ctor_get(v_l_621_, 0);
v_k_1207_ = lean_ctor_get(v_l_621_, 1);
v_v_1208_ = lean_ctor_get(v_l_621_, 2);
v_isSharedCheck_1221_ = !lean_is_exclusive(v_l_621_);
if (v_isSharedCheck_1221_ == 0)
{
lean_object* v_unused_1222_; lean_object* v_unused_1223_; 
v_unused_1222_ = lean_ctor_get(v_l_621_, 4);
lean_dec(v_unused_1222_);
v_unused_1223_ = lean_ctor_get(v_l_621_, 3);
lean_dec(v_unused_1223_);
v___x_1210_ = v_l_621_;
v_isShared_1211_ = v_isSharedCheck_1221_;
goto v_resetjp_1209_;
}
else
{
lean_inc(v_v_1208_);
lean_inc(v_k_1207_);
lean_inc(v_size_1206_);
lean_dec(v_l_621_);
v___x_1210_ = lean_box(0);
v_isShared_1211_ = v_isSharedCheck_1221_;
goto v_resetjp_1209_;
}
v_resetjp_1209_:
{
lean_object* v_size_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1216_; 
v_size_1212_ = lean_ctor_get(v_r_1205_, 0);
v___x_1213_ = lean_nat_add(v___x_1113_, v_size_1206_);
lean_dec(v_size_1206_);
v___x_1214_ = lean_nat_add(v___x_1113_, v_size_1212_);
if (v_isShared_1211_ == 0)
{
lean_ctor_set(v___x_1210_, 4, v_impl_1112_);
lean_ctor_set(v___x_1210_, 3, v_r_1205_);
lean_ctor_set(v___x_1210_, 2, v_v_620_);
lean_ctor_set(v___x_1210_, 1, v_k_619_);
lean_ctor_set(v___x_1210_, 0, v___x_1214_);
v___x_1216_ = v___x_1210_;
goto v_reusejp_1215_;
}
else
{
lean_object* v_reuseFailAlloc_1220_; 
v_reuseFailAlloc_1220_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1220_, 0, v___x_1214_);
lean_ctor_set(v_reuseFailAlloc_1220_, 1, v_k_619_);
lean_ctor_set(v_reuseFailAlloc_1220_, 2, v_v_620_);
lean_ctor_set(v_reuseFailAlloc_1220_, 3, v_r_1205_);
lean_ctor_set(v_reuseFailAlloc_1220_, 4, v_impl_1112_);
v___x_1216_ = v_reuseFailAlloc_1220_;
goto v_reusejp_1215_;
}
v_reusejp_1215_:
{
lean_object* v___x_1218_; 
if (v_isShared_625_ == 0)
{
lean_ctor_set(v___x_624_, 4, v___x_1216_);
lean_ctor_set(v___x_624_, 3, v_l_1204_);
lean_ctor_set(v___x_624_, 2, v_v_1208_);
lean_ctor_set(v___x_624_, 1, v_k_1207_);
lean_ctor_set(v___x_624_, 0, v___x_1213_);
v___x_1218_ = v___x_624_;
goto v_reusejp_1217_;
}
else
{
lean_object* v_reuseFailAlloc_1219_; 
v_reuseFailAlloc_1219_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1219_, 0, v___x_1213_);
lean_ctor_set(v_reuseFailAlloc_1219_, 1, v_k_1207_);
lean_ctor_set(v_reuseFailAlloc_1219_, 2, v_v_1208_);
lean_ctor_set(v_reuseFailAlloc_1219_, 3, v_l_1204_);
lean_ctor_set(v_reuseFailAlloc_1219_, 4, v___x_1216_);
v___x_1218_ = v_reuseFailAlloc_1219_;
goto v_reusejp_1217_;
}
v_reusejp_1217_:
{
return v___x_1218_;
}
}
}
}
else
{
lean_object* v_k_1224_; lean_object* v_v_1225_; lean_object* v___x_1227_; uint8_t v_isShared_1228_; uint8_t v_isSharedCheck_1236_; 
v_k_1224_ = lean_ctor_get(v_l_621_, 1);
v_v_1225_ = lean_ctor_get(v_l_621_, 2);
v_isSharedCheck_1236_ = !lean_is_exclusive(v_l_621_);
if (v_isSharedCheck_1236_ == 0)
{
lean_object* v_unused_1237_; lean_object* v_unused_1238_; lean_object* v_unused_1239_; 
v_unused_1237_ = lean_ctor_get(v_l_621_, 4);
lean_dec(v_unused_1237_);
v_unused_1238_ = lean_ctor_get(v_l_621_, 3);
lean_dec(v_unused_1238_);
v_unused_1239_ = lean_ctor_get(v_l_621_, 0);
lean_dec(v_unused_1239_);
v___x_1227_ = v_l_621_;
v_isShared_1228_ = v_isSharedCheck_1236_;
goto v_resetjp_1226_;
}
else
{
lean_inc(v_v_1225_);
lean_inc(v_k_1224_);
lean_dec(v_l_621_);
v___x_1227_ = lean_box(0);
v_isShared_1228_ = v_isSharedCheck_1236_;
goto v_resetjp_1226_;
}
v_resetjp_1226_:
{
lean_object* v___x_1229_; lean_object* v___x_1231_; 
v___x_1229_ = lean_unsigned_to_nat(3u);
if (v_isShared_1228_ == 0)
{
lean_ctor_set(v___x_1227_, 3, v_r_1205_);
lean_ctor_set(v___x_1227_, 2, v_v_620_);
lean_ctor_set(v___x_1227_, 1, v_k_619_);
lean_ctor_set(v___x_1227_, 0, v___x_1113_);
v___x_1231_ = v___x_1227_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1235_; 
v_reuseFailAlloc_1235_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1235_, 0, v___x_1113_);
lean_ctor_set(v_reuseFailAlloc_1235_, 1, v_k_619_);
lean_ctor_set(v_reuseFailAlloc_1235_, 2, v_v_620_);
lean_ctor_set(v_reuseFailAlloc_1235_, 3, v_r_1205_);
lean_ctor_set(v_reuseFailAlloc_1235_, 4, v_r_1205_);
v___x_1231_ = v_reuseFailAlloc_1235_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
lean_object* v___x_1233_; 
if (v_isShared_625_ == 0)
{
lean_ctor_set(v___x_624_, 4, v___x_1231_);
lean_ctor_set(v___x_624_, 3, v_l_1204_);
lean_ctor_set(v___x_624_, 2, v_v_1225_);
lean_ctor_set(v___x_624_, 1, v_k_1224_);
lean_ctor_set(v___x_624_, 0, v___x_1229_);
v___x_1233_ = v___x_624_;
goto v_reusejp_1232_;
}
else
{
lean_object* v_reuseFailAlloc_1234_; 
v_reuseFailAlloc_1234_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1234_, 0, v___x_1229_);
lean_ctor_set(v_reuseFailAlloc_1234_, 1, v_k_1224_);
lean_ctor_set(v_reuseFailAlloc_1234_, 2, v_v_1225_);
lean_ctor_set(v_reuseFailAlloc_1234_, 3, v_l_1204_);
lean_ctor_set(v_reuseFailAlloc_1234_, 4, v___x_1231_);
v___x_1233_ = v_reuseFailAlloc_1234_;
goto v_reusejp_1232_;
}
v_reusejp_1232_:
{
return v___x_1233_;
}
}
}
}
}
else
{
lean_object* v_r_1240_; 
v_r_1240_ = lean_ctor_get(v_l_621_, 4);
lean_inc(v_r_1240_);
if (lean_obj_tag(v_r_1240_) == 0)
{
lean_object* v_k_1241_; lean_object* v_v_1242_; lean_object* v___x_1244_; uint8_t v_isShared_1245_; uint8_t v_isSharedCheck_1265_; 
lean_inc(v_l_1204_);
v_k_1241_ = lean_ctor_get(v_l_621_, 1);
v_v_1242_ = lean_ctor_get(v_l_621_, 2);
v_isSharedCheck_1265_ = !lean_is_exclusive(v_l_621_);
if (v_isSharedCheck_1265_ == 0)
{
lean_object* v_unused_1266_; lean_object* v_unused_1267_; lean_object* v_unused_1268_; 
v_unused_1266_ = lean_ctor_get(v_l_621_, 4);
lean_dec(v_unused_1266_);
v_unused_1267_ = lean_ctor_get(v_l_621_, 3);
lean_dec(v_unused_1267_);
v_unused_1268_ = lean_ctor_get(v_l_621_, 0);
lean_dec(v_unused_1268_);
v___x_1244_ = v_l_621_;
v_isShared_1245_ = v_isSharedCheck_1265_;
goto v_resetjp_1243_;
}
else
{
lean_inc(v_v_1242_);
lean_inc(v_k_1241_);
lean_dec(v_l_621_);
v___x_1244_ = lean_box(0);
v_isShared_1245_ = v_isSharedCheck_1265_;
goto v_resetjp_1243_;
}
v_resetjp_1243_:
{
lean_object* v_k_1246_; lean_object* v_v_1247_; lean_object* v___x_1249_; uint8_t v_isShared_1250_; uint8_t v_isSharedCheck_1261_; 
v_k_1246_ = lean_ctor_get(v_r_1240_, 1);
v_v_1247_ = lean_ctor_get(v_r_1240_, 2);
v_isSharedCheck_1261_ = !lean_is_exclusive(v_r_1240_);
if (v_isSharedCheck_1261_ == 0)
{
lean_object* v_unused_1262_; lean_object* v_unused_1263_; lean_object* v_unused_1264_; 
v_unused_1262_ = lean_ctor_get(v_r_1240_, 4);
lean_dec(v_unused_1262_);
v_unused_1263_ = lean_ctor_get(v_r_1240_, 3);
lean_dec(v_unused_1263_);
v_unused_1264_ = lean_ctor_get(v_r_1240_, 0);
lean_dec(v_unused_1264_);
v___x_1249_ = v_r_1240_;
v_isShared_1250_ = v_isSharedCheck_1261_;
goto v_resetjp_1248_;
}
else
{
lean_inc(v_v_1247_);
lean_inc(v_k_1246_);
lean_dec(v_r_1240_);
v___x_1249_ = lean_box(0);
v_isShared_1250_ = v_isSharedCheck_1261_;
goto v_resetjp_1248_;
}
v_resetjp_1248_:
{
lean_object* v___x_1251_; lean_object* v___x_1253_; 
v___x_1251_ = lean_unsigned_to_nat(3u);
if (v_isShared_1250_ == 0)
{
lean_ctor_set(v___x_1249_, 4, v_l_1204_);
lean_ctor_set(v___x_1249_, 3, v_l_1204_);
lean_ctor_set(v___x_1249_, 2, v_v_1242_);
lean_ctor_set(v___x_1249_, 1, v_k_1241_);
lean_ctor_set(v___x_1249_, 0, v___x_1113_);
v___x_1253_ = v___x_1249_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1260_; 
v_reuseFailAlloc_1260_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v___x_1113_);
lean_ctor_set(v_reuseFailAlloc_1260_, 1, v_k_1241_);
lean_ctor_set(v_reuseFailAlloc_1260_, 2, v_v_1242_);
lean_ctor_set(v_reuseFailAlloc_1260_, 3, v_l_1204_);
lean_ctor_set(v_reuseFailAlloc_1260_, 4, v_l_1204_);
v___x_1253_ = v_reuseFailAlloc_1260_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
lean_object* v___x_1255_; 
if (v_isShared_1245_ == 0)
{
lean_ctor_set(v___x_1244_, 4, v_l_1204_);
lean_ctor_set(v___x_1244_, 2, v_v_620_);
lean_ctor_set(v___x_1244_, 1, v_k_619_);
lean_ctor_set(v___x_1244_, 0, v___x_1113_);
v___x_1255_ = v___x_1244_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1259_; 
v_reuseFailAlloc_1259_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1259_, 0, v___x_1113_);
lean_ctor_set(v_reuseFailAlloc_1259_, 1, v_k_619_);
lean_ctor_set(v_reuseFailAlloc_1259_, 2, v_v_620_);
lean_ctor_set(v_reuseFailAlloc_1259_, 3, v_l_1204_);
lean_ctor_set(v_reuseFailAlloc_1259_, 4, v_l_1204_);
v___x_1255_ = v_reuseFailAlloc_1259_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
lean_object* v___x_1257_; 
if (v_isShared_625_ == 0)
{
lean_ctor_set(v___x_624_, 4, v___x_1255_);
lean_ctor_set(v___x_624_, 3, v___x_1253_);
lean_ctor_set(v___x_624_, 2, v_v_1247_);
lean_ctor_set(v___x_624_, 1, v_k_1246_);
lean_ctor_set(v___x_624_, 0, v___x_1251_);
v___x_1257_ = v___x_624_;
goto v_reusejp_1256_;
}
else
{
lean_object* v_reuseFailAlloc_1258_; 
v_reuseFailAlloc_1258_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1258_, 0, v___x_1251_);
lean_ctor_set(v_reuseFailAlloc_1258_, 1, v_k_1246_);
lean_ctor_set(v_reuseFailAlloc_1258_, 2, v_v_1247_);
lean_ctor_set(v_reuseFailAlloc_1258_, 3, v___x_1253_);
lean_ctor_set(v_reuseFailAlloc_1258_, 4, v___x_1255_);
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
else
{
lean_object* v___x_1269_; lean_object* v___x_1271_; 
v___x_1269_ = lean_unsigned_to_nat(2u);
if (v_isShared_625_ == 0)
{
lean_ctor_set(v___x_624_, 4, v_r_1240_);
lean_ctor_set(v___x_624_, 0, v___x_1269_);
v___x_1271_ = v___x_624_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v___x_1269_);
lean_ctor_set(v_reuseFailAlloc_1272_, 1, v_k_619_);
lean_ctor_set(v_reuseFailAlloc_1272_, 2, v_v_620_);
lean_ctor_set(v_reuseFailAlloc_1272_, 3, v_l_621_);
lean_ctor_set(v_reuseFailAlloc_1272_, 4, v_r_1240_);
v___x_1271_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
return v___x_1271_;
}
}
}
}
else
{
lean_object* v___x_1274_; 
if (v_isShared_625_ == 0)
{
lean_ctor_set(v___x_624_, 4, v_l_621_);
lean_ctor_set(v___x_624_, 0, v___x_1113_);
v___x_1274_ = v___x_624_;
goto v_reusejp_1273_;
}
else
{
lean_object* v_reuseFailAlloc_1275_; 
v_reuseFailAlloc_1275_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1275_, 0, v___x_1113_);
lean_ctor_set(v_reuseFailAlloc_1275_, 1, v_k_619_);
lean_ctor_set(v_reuseFailAlloc_1275_, 2, v_v_620_);
lean_ctor_set(v_reuseFailAlloc_1275_, 3, v_l_621_);
lean_ctor_set(v_reuseFailAlloc_1275_, 4, v_l_621_);
v___x_1274_ = v_reuseFailAlloc_1275_;
goto v_reusejp_1273_;
}
v_reusejp_1273_:
{
return v___x_1274_;
}
}
}
}
}
}
}
else
{
return v_t_618_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Compiler_LCNF_Check_Impure_makeScalar_spec__0___redArg___boxed(lean_object* v_k_1278_, lean_object* v_t_1279_){
_start:
{
lean_object* v_res_1280_; 
v_res_1280_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Compiler_LCNF_Check_Impure_makeScalar_spec__0___redArg(v_k_1278_, v_t_1279_);
lean_dec(v_k_1278_);
return v_res_1280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Impure_makeScalar___redArg(lean_object* v_v_1281_, lean_object* v_a_1282_){
_start:
{
lean_object* v___x_1284_; lean_object* v_subst_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; 
v___x_1284_ = lean_st_ref_get(v_a_1282_);
v_subst_1285_ = lean_ctor_get(v___x_1284_, 1);
lean_inc_ref(v_subst_1285_);
lean_dec(v___x_1284_);
lean_inc(v_v_1281_);
v___x_1286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1286_, 0, v_v_1281_);
v___x_1287_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_Check_Impure_kill_spec__0___redArg(v_subst_1285_, v_v_1281_, v___x_1286_);
lean_dec_ref(v___x_1286_);
lean_dec(v_v_1281_);
lean_dec_ref(v_subst_1285_);
if (lean_obj_tag(v___x_1287_) == 1)
{
lean_object* v_fvarId_1288_; lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1308_; 
v_fvarId_1288_ = lean_ctor_get(v___x_1287_, 0);
v_isSharedCheck_1308_ = !lean_is_exclusive(v___x_1287_);
if (v_isSharedCheck_1308_ == 0)
{
v___x_1290_ = v___x_1287_;
v_isShared_1291_ = v_isSharedCheck_1308_;
goto v_resetjp_1289_;
}
else
{
lean_inc(v_fvarId_1288_);
lean_dec(v___x_1287_);
v___x_1290_ = lean_box(0);
v_isShared_1291_ = v_isSharedCheck_1308_;
goto v_resetjp_1289_;
}
v_resetjp_1289_:
{
lean_object* v___x_1292_; lean_object* v_rc_1293_; lean_object* v_subst_1294_; lean_object* v___x_1296_; uint8_t v_isShared_1297_; uint8_t v_isSharedCheck_1307_; 
v___x_1292_ = lean_st_ref_take(v_a_1282_);
v_rc_1293_ = lean_ctor_get(v___x_1292_, 0);
v_subst_1294_ = lean_ctor_get(v___x_1292_, 1);
v_isSharedCheck_1307_ = !lean_is_exclusive(v___x_1292_);
if (v_isSharedCheck_1307_ == 0)
{
v___x_1296_ = v___x_1292_;
v_isShared_1297_ = v_isSharedCheck_1307_;
goto v_resetjp_1295_;
}
else
{
lean_inc(v_subst_1294_);
lean_inc(v_rc_1293_);
lean_dec(v___x_1292_);
v___x_1296_ = lean_box(0);
v_isShared_1297_ = v_isSharedCheck_1307_;
goto v_resetjp_1295_;
}
v_resetjp_1295_:
{
lean_object* v___x_1298_; lean_object* v___x_1300_; 
v___x_1298_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Compiler_LCNF_Check_Impure_makeScalar_spec__0___redArg(v_fvarId_1288_, v_rc_1293_);
lean_dec(v_fvarId_1288_);
if (v_isShared_1297_ == 0)
{
lean_ctor_set(v___x_1296_, 0, v___x_1298_);
v___x_1300_ = v___x_1296_;
goto v_reusejp_1299_;
}
else
{
lean_object* v_reuseFailAlloc_1306_; 
v_reuseFailAlloc_1306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1306_, 0, v___x_1298_);
lean_ctor_set(v_reuseFailAlloc_1306_, 1, v_subst_1294_);
v___x_1300_ = v_reuseFailAlloc_1306_;
goto v_reusejp_1299_;
}
v_reusejp_1299_:
{
lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1304_; 
v___x_1301_ = lean_st_ref_set(v_a_1282_, v___x_1300_);
v___x_1302_ = lean_box(0);
if (v_isShared_1291_ == 0)
{
lean_ctor_set_tag(v___x_1290_, 0);
lean_ctor_set(v___x_1290_, 0, v___x_1302_);
v___x_1304_ = v___x_1290_;
goto v_reusejp_1303_;
}
else
{
lean_object* v_reuseFailAlloc_1305_; 
v_reuseFailAlloc_1305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1305_, 0, v___x_1302_);
v___x_1304_ = v_reuseFailAlloc_1305_;
goto v_reusejp_1303_;
}
v_reusejp_1303_:
{
return v___x_1304_;
}
}
}
}
}
else
{
lean_object* v___x_1309_; lean_object* v___x_1310_; 
lean_dec(v___x_1287_);
v___x_1309_ = lean_box(0);
v___x_1310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1310_, 0, v___x_1309_);
return v___x_1310_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Impure_makeScalar___redArg___boxed(lean_object* v_v_1311_, lean_object* v_a_1312_, lean_object* v_a_1313_){
_start:
{
lean_object* v_res_1314_; 
v_res_1314_ = l_Lean_Compiler_LCNF_Check_Impure_makeScalar___redArg(v_v_1311_, v_a_1312_);
lean_dec(v_a_1312_);
return v_res_1314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Impure_makeScalar(lean_object* v_v_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_, lean_object* v_a_1318_, lean_object* v_a_1319_, lean_object* v_a_1320_){
_start:
{
lean_object* v___x_1322_; 
v___x_1322_ = l_Lean_Compiler_LCNF_Check_Impure_makeScalar___redArg(v_v_1315_, v_a_1316_);
return v___x_1322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Impure_makeScalar___boxed(lean_object* v_v_1323_, lean_object* v_a_1324_, lean_object* v_a_1325_, lean_object* v_a_1326_, lean_object* v_a_1327_, lean_object* v_a_1328_, lean_object* v_a_1329_){
_start:
{
lean_object* v_res_1330_; 
v_res_1330_ = l_Lean_Compiler_LCNF_Check_Impure_makeScalar(v_v_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_);
lean_dec(v_a_1328_);
lean_dec_ref(v_a_1327_);
lean_dec(v_a_1326_);
lean_dec_ref(v_a_1325_);
lean_dec(v_a_1324_);
return v_res_1330_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Compiler_LCNF_Check_Impure_makeScalar_spec__0(lean_object* v_00_u03b2_1331_, lean_object* v_k_1332_, lean_object* v_t_1333_, lean_object* v_h_1334_){
_start:
{
lean_object* v___x_1335_; 
v___x_1335_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Compiler_LCNF_Check_Impure_makeScalar_spec__0___redArg(v_k_1332_, v_t_1333_);
return v___x_1335_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Compiler_LCNF_Check_Impure_makeScalar_spec__0___boxed(lean_object* v_00_u03b2_1336_, lean_object* v_k_1337_, lean_object* v_t_1338_, lean_object* v_h_1339_){
_start:
{
lean_object* v_res_1340_; 
v_res_1340_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Compiler_LCNF_Check_Impure_makeScalar_spec__0(v_00_u03b2_1336_, v_k_1337_, v_t_1338_, v_h_1339_);
lean_dec(v_k_1337_);
return v_res_1340_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Lean_Compiler_LCNF_Check_Impure_consume_spec__0(lean_object* v_n_1341_, lean_object* v_k_1342_, lean_object* v_t_1343_){
_start:
{
if (lean_obj_tag(v_t_1343_) == 0)
{
lean_object* v_size_1344_; lean_object* v_k_1345_; lean_object* v_v_1346_; lean_object* v_l_1347_; lean_object* v_r_1348_; lean_object* v___x_1350_; uint8_t v_isShared_1351_; uint8_t v_isSharedCheck_1376_; 
v_size_1344_ = lean_ctor_get(v_t_1343_, 0);
v_k_1345_ = lean_ctor_get(v_t_1343_, 1);
v_v_1346_ = lean_ctor_get(v_t_1343_, 2);
v_l_1347_ = lean_ctor_get(v_t_1343_, 3);
v_r_1348_ = lean_ctor_get(v_t_1343_, 4);
v_isSharedCheck_1376_ = !lean_is_exclusive(v_t_1343_);
if (v_isSharedCheck_1376_ == 0)
{
v___x_1350_ = v_t_1343_;
v_isShared_1351_ = v_isSharedCheck_1376_;
goto v_resetjp_1349_;
}
else
{
lean_inc(v_r_1348_);
lean_inc(v_l_1347_);
lean_inc(v_v_1346_);
lean_inc(v_k_1345_);
lean_inc(v_size_1344_);
lean_dec(v_t_1343_);
v___x_1350_ = lean_box(0);
v_isShared_1351_ = v_isSharedCheck_1376_;
goto v_resetjp_1349_;
}
v_resetjp_1349_:
{
uint8_t v___x_1352_; 
v___x_1352_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1342_, v_k_1345_);
switch(v___x_1352_)
{
case 0:
{
lean_object* v___x_1353_; lean_object* v___x_1355_; 
v___x_1353_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Lean_Compiler_LCNF_Check_Impure_consume_spec__0(v_n_1341_, v_k_1342_, v_l_1347_);
if (v_isShared_1351_ == 0)
{
lean_ctor_set(v___x_1350_, 3, v___x_1353_);
v___x_1355_ = v___x_1350_;
goto v_reusejp_1354_;
}
else
{
lean_object* v_reuseFailAlloc_1356_; 
v_reuseFailAlloc_1356_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v_size_1344_);
lean_ctor_set(v_reuseFailAlloc_1356_, 1, v_k_1345_);
lean_ctor_set(v_reuseFailAlloc_1356_, 2, v_v_1346_);
lean_ctor_set(v_reuseFailAlloc_1356_, 3, v___x_1353_);
lean_ctor_set(v_reuseFailAlloc_1356_, 4, v_r_1348_);
v___x_1355_ = v_reuseFailAlloc_1356_;
goto v_reusejp_1354_;
}
v_reusejp_1354_:
{
return v___x_1355_;
}
}
case 1:
{
lean_object* v_rc_1357_; uint8_t v_borrowed_1358_; lean_object* v_parents_1359_; lean_object* v_children_1360_; lean_object* v___x_1362_; uint8_t v_isShared_1363_; uint8_t v_isSharedCheck_1371_; 
lean_dec(v_k_1345_);
v_rc_1357_ = lean_ctor_get(v_v_1346_, 0);
v_borrowed_1358_ = lean_ctor_get_uint8(v_v_1346_, sizeof(void*)*3);
v_parents_1359_ = lean_ctor_get(v_v_1346_, 1);
v_children_1360_ = lean_ctor_get(v_v_1346_, 2);
v_isSharedCheck_1371_ = !lean_is_exclusive(v_v_1346_);
if (v_isSharedCheck_1371_ == 0)
{
v___x_1362_ = v_v_1346_;
v_isShared_1363_ = v_isSharedCheck_1371_;
goto v_resetjp_1361_;
}
else
{
lean_inc(v_children_1360_);
lean_inc(v_parents_1359_);
lean_inc(v_rc_1357_);
lean_dec(v_v_1346_);
v___x_1362_ = lean_box(0);
v_isShared_1363_ = v_isSharedCheck_1371_;
goto v_resetjp_1361_;
}
v_resetjp_1361_:
{
lean_object* v___x_1364_; lean_object* v___x_1366_; 
v___x_1364_ = lean_nat_sub(v_rc_1357_, v_n_1341_);
lean_dec(v_rc_1357_);
if (v_isShared_1363_ == 0)
{
lean_ctor_set(v___x_1362_, 0, v___x_1364_);
v___x_1366_ = v___x_1362_;
goto v_reusejp_1365_;
}
else
{
lean_object* v_reuseFailAlloc_1370_; 
v_reuseFailAlloc_1370_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1370_, 0, v___x_1364_);
lean_ctor_set(v_reuseFailAlloc_1370_, 1, v_parents_1359_);
lean_ctor_set(v_reuseFailAlloc_1370_, 2, v_children_1360_);
lean_ctor_set_uint8(v_reuseFailAlloc_1370_, sizeof(void*)*3, v_borrowed_1358_);
v___x_1366_ = v_reuseFailAlloc_1370_;
goto v_reusejp_1365_;
}
v_reusejp_1365_:
{
lean_object* v___x_1368_; 
if (v_isShared_1351_ == 0)
{
lean_ctor_set(v___x_1350_, 2, v___x_1366_);
lean_ctor_set(v___x_1350_, 1, v_k_1342_);
v___x_1368_ = v___x_1350_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v_size_1344_);
lean_ctor_set(v_reuseFailAlloc_1369_, 1, v_k_1342_);
lean_ctor_set(v_reuseFailAlloc_1369_, 2, v___x_1366_);
lean_ctor_set(v_reuseFailAlloc_1369_, 3, v_l_1347_);
lean_ctor_set(v_reuseFailAlloc_1369_, 4, v_r_1348_);
v___x_1368_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1367_;
}
v_reusejp_1367_:
{
return v___x_1368_;
}
}
}
}
default: 
{
lean_object* v___x_1372_; lean_object* v___x_1374_; 
v___x_1372_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Lean_Compiler_LCNF_Check_Impure_consume_spec__0(v_n_1341_, v_k_1342_, v_r_1348_);
if (v_isShared_1351_ == 0)
{
lean_ctor_set(v___x_1350_, 4, v___x_1372_);
v___x_1374_ = v___x_1350_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1375_; 
v_reuseFailAlloc_1375_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1375_, 0, v_size_1344_);
lean_ctor_set(v_reuseFailAlloc_1375_, 1, v_k_1345_);
lean_ctor_set(v_reuseFailAlloc_1375_, 2, v_v_1346_);
lean_ctor_set(v_reuseFailAlloc_1375_, 3, v_l_1347_);
lean_ctor_set(v_reuseFailAlloc_1375_, 4, v___x_1372_);
v___x_1374_ = v_reuseFailAlloc_1375_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
return v___x_1374_;
}
}
}
}
}
else
{
lean_dec(v_k_1342_);
return v_t_1343_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Lean_Compiler_LCNF_Check_Impure_consume_spec__0___boxed(lean_object* v_n_1377_, lean_object* v_k_1378_, lean_object* v_t_1379_){
_start:
{
lean_object* v_res_1380_; 
v_res_1380_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Lean_Compiler_LCNF_Check_Impure_consume_spec__0(v_n_1377_, v_k_1378_, v_t_1379_);
lean_dec(v_n_1377_);
return v_res_1380_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Check_Impure_consume___closed__1(void){
_start:
{
lean_object* v___x_1382_; lean_object* v___x_1383_; 
v___x_1382_ = ((lean_object*)(l_Lean_Compiler_LCNF_Check_Impure_consume___closed__0));
v___x_1383_ = l_Lean_stringToMessageData(v___x_1382_);
return v___x_1383_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Check_Impure_consume___closed__3(void){
_start:
{
lean_object* v___x_1385_; lean_object* v___x_1386_; 
v___x_1385_ = ((lean_object*)(l_Lean_Compiler_LCNF_Check_Impure_consume___closed__2));
v___x_1386_ = l_Lean_stringToMessageData(v___x_1385_);
return v___x_1386_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Check_Impure_consume___closed__5(void){
_start:
{
lean_object* v___x_1388_; lean_object* v___x_1389_; 
v___x_1388_ = ((lean_object*)(l_Lean_Compiler_LCNF_Check_Impure_consume___closed__4));
v___x_1389_ = l_Lean_stringToMessageData(v___x_1388_);
return v___x_1389_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Check_Impure_consume___closed__7(void){
_start:
{
lean_object* v___x_1391_; lean_object* v___x_1392_; 
v___x_1391_ = ((lean_object*)(l_Lean_Compiler_LCNF_Check_Impure_consume___closed__6));
v___x_1392_ = l_Lean_stringToMessageData(v___x_1391_);
return v___x_1392_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Check_Impure_consume___closed__9(void){
_start:
{
lean_object* v___x_1394_; lean_object* v___x_1395_; 
v___x_1394_ = ((lean_object*)(l_Lean_Compiler_LCNF_Check_Impure_consume___closed__8));
v___x_1395_ = l_Lean_stringToMessageData(v___x_1394_);
return v___x_1395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Impure_consume(lean_object* v_v_1396_, lean_object* v_n_1397_, lean_object* v_a_1398_, lean_object* v_a_1399_, lean_object* v_a_1400_, lean_object* v_a_1401_, lean_object* v_a_1402_){
_start:
{
lean_object* v___x_1404_; lean_object* v_subst_1405_; lean_object* v___x_1407_; uint8_t v_isShared_1408_; uint8_t v_isSharedCheck_1542_; 
v___x_1404_ = lean_st_ref_get(v_a_1398_);
v_subst_1405_ = lean_ctor_get(v___x_1404_, 1);
v_isSharedCheck_1542_ = !lean_is_exclusive(v___x_1404_);
if (v_isSharedCheck_1542_ == 0)
{
lean_object* v_unused_1543_; 
v_unused_1543_ = lean_ctor_get(v___x_1404_, 0);
lean_dec(v_unused_1543_);
v___x_1407_ = v___x_1404_;
v_isShared_1408_ = v_isSharedCheck_1542_;
goto v_resetjp_1406_;
}
else
{
lean_inc(v_subst_1405_);
lean_dec(v___x_1404_);
v___x_1407_ = lean_box(0);
v_isShared_1408_ = v_isSharedCheck_1542_;
goto v_resetjp_1406_;
}
v_resetjp_1406_:
{
lean_object* v___x_1409_; lean_object* v___x_1410_; 
lean_inc(v_v_1396_);
v___x_1409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1409_, 0, v_v_1396_);
v___x_1410_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_Check_Impure_kill_spec__0___redArg(v_subst_1405_, v_v_1396_, v___x_1409_);
lean_dec_ref(v___x_1409_);
lean_dec(v_v_1396_);
lean_dec_ref(v_subst_1405_);
if (lean_obj_tag(v___x_1410_) == 1)
{
lean_object* v_fvarId_1411_; lean_object* v___x_1413_; uint8_t v_isShared_1414_; uint8_t v_isSharedCheck_1539_; 
v_fvarId_1411_ = lean_ctor_get(v___x_1410_, 0);
v_isSharedCheck_1539_ = !lean_is_exclusive(v___x_1410_);
if (v_isSharedCheck_1539_ == 0)
{
v___x_1413_ = v___x_1410_;
v_isShared_1414_ = v_isSharedCheck_1539_;
goto v_resetjp_1412_;
}
else
{
lean_inc(v_fvarId_1411_);
lean_dec(v___x_1410_);
v___x_1413_ = lean_box(0);
v_isShared_1414_ = v_isSharedCheck_1539_;
goto v_resetjp_1412_;
}
v_resetjp_1412_:
{
lean_object* v___x_1415_; 
lean_inc(v_fvarId_1411_);
v___x_1415_ = l_Lean_Compiler_LCNF_getBinderName(v_fvarId_1411_, v_a_1399_, v_a_1400_, v_a_1401_, v_a_1402_);
if (lean_obj_tag(v___x_1415_) == 0)
{
lean_object* v_a_1416_; lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1530_; 
v_a_1416_ = lean_ctor_get(v___x_1415_, 0);
v_isSharedCheck_1530_ = !lean_is_exclusive(v___x_1415_);
if (v_isSharedCheck_1530_ == 0)
{
v___x_1418_ = v___x_1415_;
v_isShared_1419_ = v_isSharedCheck_1530_;
goto v_resetjp_1417_;
}
else
{
lean_inc(v_a_1416_);
lean_dec(v___x_1415_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1530_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
lean_object* v___x_1420_; lean_object* v_rc_1421_; lean_object* v___x_1423_; uint8_t v_isShared_1424_; uint8_t v_isSharedCheck_1528_; 
v___x_1420_ = lean_st_ref_get(v_a_1398_);
v_rc_1421_ = lean_ctor_get(v___x_1420_, 0);
v_isSharedCheck_1528_ = !lean_is_exclusive(v___x_1420_);
if (v_isSharedCheck_1528_ == 0)
{
lean_object* v_unused_1529_; 
v_unused_1529_ = lean_ctor_get(v___x_1420_, 1);
lean_dec(v_unused_1529_);
v___x_1423_ = v___x_1420_;
v_isShared_1424_ = v_isSharedCheck_1528_;
goto v_resetjp_1422_;
}
else
{
lean_inc(v_rc_1421_);
lean_dec(v___x_1420_);
v___x_1423_ = lean_box(0);
v_isShared_1424_ = v_isSharedCheck_1528_;
goto v_resetjp_1422_;
}
v_resetjp_1422_:
{
lean_object* v___x_1425_; 
v___x_1425_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_Check_Impure_isDead_spec__0___redArg(v_rc_1421_, v_fvarId_1411_);
lean_dec(v_rc_1421_);
if (lean_obj_tag(v___x_1425_) == 1)
{
lean_object* v_val_1426_; lean_object* v___x_1428_; uint8_t v_isShared_1429_; uint8_t v_isSharedCheck_1523_; 
v_val_1426_ = lean_ctor_get(v___x_1425_, 0);
v_isSharedCheck_1523_ = !lean_is_exclusive(v___x_1425_);
if (v_isSharedCheck_1523_ == 0)
{
v___x_1428_ = v___x_1425_;
v_isShared_1429_ = v_isSharedCheck_1523_;
goto v_resetjp_1427_;
}
else
{
lean_inc(v_val_1426_);
lean_dec(v___x_1425_);
v___x_1428_ = lean_box(0);
v_isShared_1429_ = v_isSharedCheck_1523_;
goto v_resetjp_1427_;
}
v_resetjp_1427_:
{
lean_object* v_rc_1430_; uint8_t v_borrowed_1431_; lean_object* v_children_1432_; lean_object* v___y_1434_; lean_object* v___y_1435_; lean_object* v___y_1436_; lean_object* v___y_1437_; lean_object* v___y_1438_; uint8_t v___y_1439_; lean_object* v___y_1469_; lean_object* v___y_1470_; lean_object* v___y_1471_; lean_object* v___y_1472_; lean_object* v___y_1473_; lean_object* v___y_1477_; lean_object* v___y_1478_; lean_object* v___y_1479_; lean_object* v___y_1480_; lean_object* v___y_1481_; uint8_t v___x_1508_; 
v_rc_1430_ = lean_ctor_get(v_val_1426_, 0);
lean_inc(v_rc_1430_);
v_borrowed_1431_ = lean_ctor_get_uint8(v_val_1426_, sizeof(void*)*3);
v_children_1432_ = lean_ctor_get(v_val_1426_, 2);
lean_inc_ref(v_children_1432_);
lean_dec(v_val_1426_);
v___x_1508_ = lean_nat_dec_lt(v_rc_1430_, v_n_1397_);
if (v___x_1508_ == 0)
{
lean_del_object(v___x_1428_);
lean_del_object(v___x_1423_);
lean_dec(v_a_1416_);
lean_del_object(v___x_1413_);
lean_del_object(v___x_1407_);
v___y_1469_ = v_a_1398_;
v___y_1470_ = v_a_1399_;
v___y_1471_ = v_a_1400_;
v___y_1472_ = v_a_1401_;
v___y_1473_ = v_a_1402_;
goto v___jp_1468_;
}
else
{
lean_dec_ref(v_children_1432_);
lean_del_object(v___x_1418_);
lean_dec(v_fvarId_1411_);
if (v_borrowed_1431_ == 0)
{
lean_object* v___x_1509_; uint8_t v___x_1510_; 
v___x_1509_ = lean_unsigned_to_nat(0u);
v___x_1510_ = lean_nat_dec_eq(v_rc_1430_, v___x_1509_);
if (v___x_1510_ == 0)
{
v___y_1477_ = v_a_1398_;
v___y_1478_ = v_a_1399_;
v___y_1479_ = v_a_1400_;
v___y_1480_ = v_a_1401_;
v___y_1481_ = v_a_1402_;
goto v___jp_1476_;
}
else
{
lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; 
lean_dec(v_rc_1430_);
lean_del_object(v___x_1428_);
lean_del_object(v___x_1423_);
lean_del_object(v___x_1413_);
lean_del_object(v___x_1407_);
v___x_1511_ = lean_obj_once(&l_Lean_Compiler_LCNF_Check_Impure_consume___closed__1, &l_Lean_Compiler_LCNF_Check_Impure_consume___closed__1_once, _init_l_Lean_Compiler_LCNF_Check_Impure_consume___closed__1);
v___x_1512_ = l_Lean_MessageData_ofName(v_a_1416_);
v___x_1513_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1513_, 0, v___x_1511_);
lean_ctor_set(v___x_1513_, 1, v___x_1512_);
v___x_1514_ = lean_obj_once(&l_Lean_Compiler_LCNF_Check_Impure_consume___closed__3, &l_Lean_Compiler_LCNF_Check_Impure_consume___closed__3_once, _init_l_Lean_Compiler_LCNF_Check_Impure_consume___closed__3);
v___x_1515_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1515_, 0, v___x_1513_);
lean_ctor_set(v___x_1515_, 1, v___x_1514_);
v___x_1516_ = l_Nat_reprFast(v_n_1397_);
v___x_1517_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1517_, 0, v___x_1516_);
v___x_1518_ = l_Lean_MessageData_ofFormat(v___x_1517_);
v___x_1519_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1519_, 0, v___x_1515_);
lean_ctor_set(v___x_1519_, 1, v___x_1518_);
v___x_1520_ = lean_obj_once(&l_Lean_Compiler_LCNF_Check_Impure_consume___closed__9, &l_Lean_Compiler_LCNF_Check_Impure_consume___closed__9_once, _init_l_Lean_Compiler_LCNF_Check_Impure_consume___closed__9);
v___x_1521_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1521_, 0, v___x_1519_);
lean_ctor_set(v___x_1521_, 1, v___x_1520_);
v___x_1522_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Impure_kill_spec__1___redArg(v___x_1521_, v_a_1399_, v_a_1400_, v_a_1401_, v_a_1402_);
return v___x_1522_;
}
}
else
{
v___y_1477_ = v_a_1398_;
v___y_1478_ = v_a_1399_;
v___y_1479_ = v_a_1400_;
v___y_1480_ = v_a_1401_;
v___y_1481_ = v_a_1402_;
goto v___jp_1476_;
}
}
v___jp_1433_:
{
lean_object* v___x_1440_; lean_object* v_rc_1441_; lean_object* v_subst_1442_; lean_object* v___x_1444_; uint8_t v_isShared_1445_; uint8_t v_isSharedCheck_1467_; 
v___x_1440_ = lean_st_ref_take(v___y_1436_);
v_rc_1441_ = lean_ctor_get(v___x_1440_, 0);
v_subst_1442_ = lean_ctor_get(v___x_1440_, 1);
v_isSharedCheck_1467_ = !lean_is_exclusive(v___x_1440_);
if (v_isSharedCheck_1467_ == 0)
{
v___x_1444_ = v___x_1440_;
v_isShared_1445_ = v_isSharedCheck_1467_;
goto v_resetjp_1443_;
}
else
{
lean_inc(v_subst_1442_);
lean_inc(v_rc_1441_);
lean_dec(v___x_1440_);
v___x_1444_ = lean_box(0);
v_isShared_1445_ = v_isSharedCheck_1467_;
goto v_resetjp_1443_;
}
v_resetjp_1443_:
{
lean_object* v___x_1446_; lean_object* v___x_1448_; 
v___x_1446_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Lean_Compiler_LCNF_Check_Impure_consume_spec__0(v_n_1397_, v_fvarId_1411_, v_rc_1441_);
lean_dec(v_n_1397_);
if (v_isShared_1445_ == 0)
{
lean_ctor_set(v___x_1444_, 0, v___x_1446_);
v___x_1448_ = v___x_1444_;
goto v_reusejp_1447_;
}
else
{
lean_object* v_reuseFailAlloc_1466_; 
v_reuseFailAlloc_1466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1466_, 0, v___x_1446_);
lean_ctor_set(v_reuseFailAlloc_1466_, 1, v_subst_1442_);
v___x_1448_ = v_reuseFailAlloc_1466_;
goto v_reusejp_1447_;
}
v_reusejp_1447_:
{
lean_object* v___x_1449_; 
v___x_1449_ = lean_st_ref_set(v___y_1436_, v___x_1448_);
if (v___y_1439_ == 0)
{
lean_object* v___x_1450_; lean_object* v___x_1452_; 
lean_dec_ref(v_children_1432_);
v___x_1450_ = lean_box(0);
if (v_isShared_1419_ == 0)
{
lean_ctor_set(v___x_1418_, 0, v___x_1450_);
v___x_1452_ = v___x_1418_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v___x_1450_);
v___x_1452_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
return v___x_1452_;
}
}
else
{
lean_object* v___x_1454_; size_t v_sz_1455_; size_t v___x_1456_; lean_object* v___x_1457_; 
lean_del_object(v___x_1418_);
v___x_1454_ = lean_box(0);
v_sz_1455_ = lean_array_size(v_children_1432_);
v___x_1456_ = ((size_t)0ULL);
v___x_1457_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Impure_maybeKill_spec__0(v_children_1432_, v_sz_1455_, v___x_1456_, v___x_1454_, v___y_1436_, v___y_1438_, v___y_1437_, v___y_1434_, v___y_1435_);
lean_dec_ref(v_children_1432_);
if (lean_obj_tag(v___x_1457_) == 0)
{
lean_object* v___x_1459_; uint8_t v_isShared_1460_; uint8_t v_isSharedCheck_1464_; 
v_isSharedCheck_1464_ = !lean_is_exclusive(v___x_1457_);
if (v_isSharedCheck_1464_ == 0)
{
lean_object* v_unused_1465_; 
v_unused_1465_ = lean_ctor_get(v___x_1457_, 0);
lean_dec(v_unused_1465_);
v___x_1459_ = v___x_1457_;
v_isShared_1460_ = v_isSharedCheck_1464_;
goto v_resetjp_1458_;
}
else
{
lean_dec(v___x_1457_);
v___x_1459_ = lean_box(0);
v_isShared_1460_ = v_isSharedCheck_1464_;
goto v_resetjp_1458_;
}
v_resetjp_1458_:
{
lean_object* v___x_1462_; 
if (v_isShared_1460_ == 0)
{
lean_ctor_set(v___x_1459_, 0, v___x_1454_);
v___x_1462_ = v___x_1459_;
goto v_reusejp_1461_;
}
else
{
lean_object* v_reuseFailAlloc_1463_; 
v_reuseFailAlloc_1463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1463_, 0, v___x_1454_);
v___x_1462_ = v_reuseFailAlloc_1463_;
goto v_reusejp_1461_;
}
v_reusejp_1461_:
{
return v___x_1462_;
}
}
}
else
{
return v___x_1457_;
}
}
}
}
}
v___jp_1468_:
{
uint8_t v___x_1474_; 
v___x_1474_ = lean_nat_dec_eq(v_rc_1430_, v_n_1397_);
lean_dec(v_rc_1430_);
if (v___x_1474_ == 0)
{
v___y_1434_ = v___y_1472_;
v___y_1435_ = v___y_1473_;
v___y_1436_ = v___y_1469_;
v___y_1437_ = v___y_1471_;
v___y_1438_ = v___y_1470_;
v___y_1439_ = v___x_1474_;
goto v___jp_1433_;
}
else
{
if (v_borrowed_1431_ == 0)
{
v___y_1434_ = v___y_1472_;
v___y_1435_ = v___y_1473_;
v___y_1436_ = v___y_1469_;
v___y_1437_ = v___y_1471_;
v___y_1438_ = v___y_1470_;
v___y_1439_ = v___x_1474_;
goto v___jp_1433_;
}
else
{
uint8_t v___x_1475_; 
v___x_1475_ = 0;
v___y_1434_ = v___y_1472_;
v___y_1435_ = v___y_1473_;
v___y_1436_ = v___y_1469_;
v___y_1437_ = v___y_1471_;
v___y_1438_ = v___y_1470_;
v___y_1439_ = v___x_1475_;
goto v___jp_1433_;
}
}
}
v___jp_1476_:
{
lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1485_; 
v___x_1482_ = lean_obj_once(&l_Lean_Compiler_LCNF_Check_Impure_consume___closed__1, &l_Lean_Compiler_LCNF_Check_Impure_consume___closed__1_once, _init_l_Lean_Compiler_LCNF_Check_Impure_consume___closed__1);
v___x_1483_ = l_Lean_MessageData_ofName(v_a_1416_);
if (v_isShared_1424_ == 0)
{
lean_ctor_set_tag(v___x_1423_, 7);
lean_ctor_set(v___x_1423_, 1, v___x_1483_);
lean_ctor_set(v___x_1423_, 0, v___x_1482_);
v___x_1485_ = v___x_1423_;
goto v_reusejp_1484_;
}
else
{
lean_object* v_reuseFailAlloc_1507_; 
v_reuseFailAlloc_1507_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1507_, 0, v___x_1482_);
lean_ctor_set(v_reuseFailAlloc_1507_, 1, v___x_1483_);
v___x_1485_ = v_reuseFailAlloc_1507_;
goto v_reusejp_1484_;
}
v_reusejp_1484_:
{
lean_object* v___x_1486_; lean_object* v___x_1488_; 
v___x_1486_ = lean_obj_once(&l_Lean_Compiler_LCNF_Check_Impure_consume___closed__3, &l_Lean_Compiler_LCNF_Check_Impure_consume___closed__3_once, _init_l_Lean_Compiler_LCNF_Check_Impure_consume___closed__3);
if (v_isShared_1408_ == 0)
{
lean_ctor_set_tag(v___x_1407_, 7);
lean_ctor_set(v___x_1407_, 1, v___x_1486_);
lean_ctor_set(v___x_1407_, 0, v___x_1485_);
v___x_1488_ = v___x_1407_;
goto v_reusejp_1487_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v___x_1485_);
lean_ctor_set(v_reuseFailAlloc_1506_, 1, v___x_1486_);
v___x_1488_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1487_;
}
v_reusejp_1487_:
{
lean_object* v___x_1489_; lean_object* v___x_1491_; 
v___x_1489_ = l_Nat_reprFast(v_n_1397_);
if (v_isShared_1429_ == 0)
{
lean_ctor_set_tag(v___x_1428_, 3);
lean_ctor_set(v___x_1428_, 0, v___x_1489_);
v___x_1491_ = v___x_1428_;
goto v_reusejp_1490_;
}
else
{
lean_object* v_reuseFailAlloc_1505_; 
v_reuseFailAlloc_1505_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1505_, 0, v___x_1489_);
v___x_1491_ = v_reuseFailAlloc_1505_;
goto v_reusejp_1490_;
}
v_reusejp_1490_:
{
lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1498_; 
v___x_1492_ = l_Lean_MessageData_ofFormat(v___x_1491_);
v___x_1493_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1493_, 0, v___x_1488_);
lean_ctor_set(v___x_1493_, 1, v___x_1492_);
v___x_1494_ = lean_obj_once(&l_Lean_Compiler_LCNF_Check_Impure_consume___closed__5, &l_Lean_Compiler_LCNF_Check_Impure_consume___closed__5_once, _init_l_Lean_Compiler_LCNF_Check_Impure_consume___closed__5);
v___x_1495_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1495_, 0, v___x_1493_);
lean_ctor_set(v___x_1495_, 1, v___x_1494_);
v___x_1496_ = l_Nat_reprFast(v_rc_1430_);
if (v_isShared_1414_ == 0)
{
lean_ctor_set_tag(v___x_1413_, 3);
lean_ctor_set(v___x_1413_, 0, v___x_1496_);
v___x_1498_ = v___x_1413_;
goto v_reusejp_1497_;
}
else
{
lean_object* v_reuseFailAlloc_1504_; 
v_reuseFailAlloc_1504_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1504_, 0, v___x_1496_);
v___x_1498_ = v_reuseFailAlloc_1504_;
goto v_reusejp_1497_;
}
v_reusejp_1497_:
{
lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; 
v___x_1499_ = l_Lean_MessageData_ofFormat(v___x_1498_);
v___x_1500_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1500_, 0, v___x_1495_);
lean_ctor_set(v___x_1500_, 1, v___x_1499_);
v___x_1501_ = lean_obj_once(&l_Lean_Compiler_LCNF_Check_Impure_consume___closed__7, &l_Lean_Compiler_LCNF_Check_Impure_consume___closed__7_once, _init_l_Lean_Compiler_LCNF_Check_Impure_consume___closed__7);
v___x_1502_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1502_, 0, v___x_1500_);
lean_ctor_set(v___x_1502_, 1, v___x_1501_);
v___x_1503_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Impure_kill_spec__1___redArg(v___x_1502_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_);
return v___x_1503_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1524_; lean_object* v___x_1526_; 
lean_dec(v___x_1425_);
lean_del_object(v___x_1423_);
lean_dec(v_a_1416_);
lean_del_object(v___x_1413_);
lean_dec(v_fvarId_1411_);
lean_del_object(v___x_1407_);
lean_dec(v_n_1397_);
v___x_1524_ = lean_box(0);
if (v_isShared_1419_ == 0)
{
lean_ctor_set(v___x_1418_, 0, v___x_1524_);
v___x_1526_ = v___x_1418_;
goto v_reusejp_1525_;
}
else
{
lean_object* v_reuseFailAlloc_1527_; 
v_reuseFailAlloc_1527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1527_, 0, v___x_1524_);
v___x_1526_ = v_reuseFailAlloc_1527_;
goto v_reusejp_1525_;
}
v_reusejp_1525_:
{
return v___x_1526_;
}
}
}
}
}
else
{
lean_object* v_a_1531_; lean_object* v___x_1533_; uint8_t v_isShared_1534_; uint8_t v_isSharedCheck_1538_; 
lean_del_object(v___x_1413_);
lean_dec(v_fvarId_1411_);
lean_del_object(v___x_1407_);
lean_dec(v_n_1397_);
v_a_1531_ = lean_ctor_get(v___x_1415_, 0);
v_isSharedCheck_1538_ = !lean_is_exclusive(v___x_1415_);
if (v_isSharedCheck_1538_ == 0)
{
v___x_1533_ = v___x_1415_;
v_isShared_1534_ = v_isSharedCheck_1538_;
goto v_resetjp_1532_;
}
else
{
lean_inc(v_a_1531_);
lean_dec(v___x_1415_);
v___x_1533_ = lean_box(0);
v_isShared_1534_ = v_isSharedCheck_1538_;
goto v_resetjp_1532_;
}
v_resetjp_1532_:
{
lean_object* v___x_1536_; 
if (v_isShared_1534_ == 0)
{
v___x_1536_ = v___x_1533_;
goto v_reusejp_1535_;
}
else
{
lean_object* v_reuseFailAlloc_1537_; 
v_reuseFailAlloc_1537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1537_, 0, v_a_1531_);
v___x_1536_ = v_reuseFailAlloc_1537_;
goto v_reusejp_1535_;
}
v_reusejp_1535_:
{
return v___x_1536_;
}
}
}
}
}
else
{
lean_object* v___x_1540_; lean_object* v___x_1541_; 
lean_dec(v___x_1410_);
lean_del_object(v___x_1407_);
lean_dec(v_n_1397_);
v___x_1540_ = lean_box(0);
v___x_1541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1541_, 0, v___x_1540_);
return v___x_1541_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Impure_consume___boxed(lean_object* v_v_1544_, lean_object* v_n_1545_, lean_object* v_a_1546_, lean_object* v_a_1547_, lean_object* v_a_1548_, lean_object* v_a_1549_, lean_object* v_a_1550_, lean_object* v_a_1551_){
_start:
{
lean_object* v_res_1552_; 
v_res_1552_ = l_Lean_Compiler_LCNF_Check_Impure_consume(v_v_1544_, v_n_1545_, v_a_1546_, v_a_1547_, v_a_1548_, v_a_1549_, v_a_1550_);
lean_dec(v_a_1550_);
lean_dec_ref(v_a_1549_);
lean_dec(v_a_1548_);
lean_dec_ref(v_a_1547_);
lean_dec(v_a_1546_);
return v_res_1552_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Check_Impure_useVar___closed__1(void){
_start:
{
lean_object* v___x_1554_; lean_object* v___x_1555_; 
v___x_1554_ = ((lean_object*)(l_Lean_Compiler_LCNF_Check_Impure_useVar___closed__0));
v___x_1555_ = l_Lean_stringToMessageData(v___x_1554_);
return v___x_1555_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Check_Impure_useVar___closed__3(void){
_start:
{
lean_object* v___x_1557_; lean_object* v___x_1558_; 
v___x_1557_ = ((lean_object*)(l_Lean_Compiler_LCNF_Check_Impure_useVar___closed__2));
v___x_1558_ = l_Lean_stringToMessageData(v___x_1557_);
return v___x_1558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Impure_useVar(lean_object* v_v_1559_, lean_object* v_a_1560_, lean_object* v_a_1561_, lean_object* v_a_1562_, lean_object* v_a_1563_, lean_object* v_a_1564_){
_start:
{
lean_object* v___x_1566_; lean_object* v_subst_1567_; lean_object* v___x_1569_; uint8_t v_isShared_1570_; uint8_t v_isSharedCheck_1605_; 
v___x_1566_ = lean_st_ref_get(v_a_1560_);
v_subst_1567_ = lean_ctor_get(v___x_1566_, 1);
v_isSharedCheck_1605_ = !lean_is_exclusive(v___x_1566_);
if (v_isSharedCheck_1605_ == 0)
{
lean_object* v_unused_1606_; 
v_unused_1606_ = lean_ctor_get(v___x_1566_, 0);
lean_dec(v_unused_1606_);
v___x_1569_ = v___x_1566_;
v_isShared_1570_ = v_isSharedCheck_1605_;
goto v_resetjp_1568_;
}
else
{
lean_inc(v_subst_1567_);
lean_dec(v___x_1566_);
v___x_1569_ = lean_box(0);
v_isShared_1570_ = v_isSharedCheck_1605_;
goto v_resetjp_1568_;
}
v_resetjp_1568_:
{
lean_object* v___x_1571_; lean_object* v___x_1572_; 
lean_inc(v_v_1559_);
v___x_1571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1571_, 0, v_v_1559_);
v___x_1572_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_Check_Impure_kill_spec__0___redArg(v_subst_1567_, v_v_1559_, v___x_1571_);
lean_dec_ref(v___x_1571_);
lean_dec(v_v_1559_);
lean_dec_ref(v_subst_1567_);
if (lean_obj_tag(v___x_1572_) == 1)
{
lean_object* v_fvarId_1573_; lean_object* v___x_1574_; 
v_fvarId_1573_ = lean_ctor_get(v___x_1572_, 0);
lean_inc(v_fvarId_1573_);
lean_dec_ref(v___x_1572_);
lean_inc(v_fvarId_1573_);
v___x_1574_ = l_Lean_Compiler_LCNF_getBinderName(v_fvarId_1573_, v_a_1561_, v_a_1562_, v_a_1563_, v_a_1564_);
if (lean_obj_tag(v___x_1574_) == 0)
{
lean_object* v_a_1575_; lean_object* v___x_1576_; lean_object* v_a_1577_; lean_object* v___x_1579_; uint8_t v_isShared_1580_; uint8_t v_isSharedCheck_1594_; 
v_a_1575_ = lean_ctor_get(v___x_1574_, 0);
lean_inc(v_a_1575_);
lean_dec_ref(v___x_1574_);
v___x_1576_ = l_Lean_Compiler_LCNF_Check_Impure_isDead___redArg(v_fvarId_1573_, v_a_1560_);
lean_dec(v_fvarId_1573_);
v_a_1577_ = lean_ctor_get(v___x_1576_, 0);
v_isSharedCheck_1594_ = !lean_is_exclusive(v___x_1576_);
if (v_isSharedCheck_1594_ == 0)
{
v___x_1579_ = v___x_1576_;
v_isShared_1580_ = v_isSharedCheck_1594_;
goto v_resetjp_1578_;
}
else
{
lean_inc(v_a_1577_);
lean_dec(v___x_1576_);
v___x_1579_ = lean_box(0);
v_isShared_1580_ = v_isSharedCheck_1594_;
goto v_resetjp_1578_;
}
v_resetjp_1578_:
{
uint8_t v___x_1581_; 
v___x_1581_ = lean_unbox(v_a_1577_);
lean_dec(v_a_1577_);
if (v___x_1581_ == 0)
{
lean_object* v___x_1582_; lean_object* v___x_1584_; 
lean_dec(v_a_1575_);
lean_del_object(v___x_1569_);
v___x_1582_ = lean_box(0);
if (v_isShared_1580_ == 0)
{
lean_ctor_set(v___x_1579_, 0, v___x_1582_);
v___x_1584_ = v___x_1579_;
goto v_reusejp_1583_;
}
else
{
lean_object* v_reuseFailAlloc_1585_; 
v_reuseFailAlloc_1585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1585_, 0, v___x_1582_);
v___x_1584_ = v_reuseFailAlloc_1585_;
goto v_reusejp_1583_;
}
v_reusejp_1583_:
{
return v___x_1584_;
}
}
else
{
lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1589_; 
lean_del_object(v___x_1579_);
v___x_1586_ = lean_obj_once(&l_Lean_Compiler_LCNF_Check_Impure_useVar___closed__1, &l_Lean_Compiler_LCNF_Check_Impure_useVar___closed__1_once, _init_l_Lean_Compiler_LCNF_Check_Impure_useVar___closed__1);
v___x_1587_ = l_Lean_MessageData_ofName(v_a_1575_);
if (v_isShared_1570_ == 0)
{
lean_ctor_set_tag(v___x_1569_, 7);
lean_ctor_set(v___x_1569_, 1, v___x_1587_);
lean_ctor_set(v___x_1569_, 0, v___x_1586_);
v___x_1589_ = v___x_1569_;
goto v_reusejp_1588_;
}
else
{
lean_object* v_reuseFailAlloc_1593_; 
v_reuseFailAlloc_1593_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1593_, 0, v___x_1586_);
lean_ctor_set(v_reuseFailAlloc_1593_, 1, v___x_1587_);
v___x_1589_ = v_reuseFailAlloc_1593_;
goto v_reusejp_1588_;
}
v_reusejp_1588_:
{
lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; 
v___x_1590_ = lean_obj_once(&l_Lean_Compiler_LCNF_Check_Impure_useVar___closed__3, &l_Lean_Compiler_LCNF_Check_Impure_useVar___closed__3_once, _init_l_Lean_Compiler_LCNF_Check_Impure_useVar___closed__3);
v___x_1591_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1591_, 0, v___x_1589_);
lean_ctor_set(v___x_1591_, 1, v___x_1590_);
v___x_1592_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Impure_kill_spec__1___redArg(v___x_1591_, v_a_1561_, v_a_1562_, v_a_1563_, v_a_1564_);
return v___x_1592_;
}
}
}
}
else
{
lean_object* v_a_1595_; lean_object* v___x_1597_; uint8_t v_isShared_1598_; uint8_t v_isSharedCheck_1602_; 
lean_dec(v_fvarId_1573_);
lean_del_object(v___x_1569_);
v_a_1595_ = lean_ctor_get(v___x_1574_, 0);
v_isSharedCheck_1602_ = !lean_is_exclusive(v___x_1574_);
if (v_isSharedCheck_1602_ == 0)
{
v___x_1597_ = v___x_1574_;
v_isShared_1598_ = v_isSharedCheck_1602_;
goto v_resetjp_1596_;
}
else
{
lean_inc(v_a_1595_);
lean_dec(v___x_1574_);
v___x_1597_ = lean_box(0);
v_isShared_1598_ = v_isSharedCheck_1602_;
goto v_resetjp_1596_;
}
v_resetjp_1596_:
{
lean_object* v___x_1600_; 
if (v_isShared_1598_ == 0)
{
v___x_1600_ = v___x_1597_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v_a_1595_);
v___x_1600_ = v_reuseFailAlloc_1601_;
goto v_reusejp_1599_;
}
v_reusejp_1599_:
{
return v___x_1600_;
}
}
}
}
else
{
lean_object* v___x_1603_; lean_object* v___x_1604_; 
lean_dec(v___x_1572_);
lean_del_object(v___x_1569_);
v___x_1603_ = lean_box(0);
v___x_1604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1604_, 0, v___x_1603_);
return v___x_1604_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Impure_useVar___boxed(lean_object* v_v_1607_, lean_object* v_a_1608_, lean_object* v_a_1609_, lean_object* v_a_1610_, lean_object* v_a_1611_, lean_object* v_a_1612_, lean_object* v_a_1613_){
_start:
{
lean_object* v_res_1614_; 
v_res_1614_ = l_Lean_Compiler_LCNF_Check_Impure_useVar(v_v_1607_, v_a_1608_, v_a_1609_, v_a_1610_, v_a_1611_, v_a_1612_);
lean_dec(v_a_1612_);
lean_dec_ref(v_a_1611_);
lean_dec(v_a_1610_);
lean_dec_ref(v_a_1609_);
lean_dec(v_a_1608_);
return v_res_1614_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Check_Impure_checkShared___closed__1(void){
_start:
{
lean_object* v___x_1616_; lean_object* v___x_1617_; 
v___x_1616_ = ((lean_object*)(l_Lean_Compiler_LCNF_Check_Impure_checkShared___closed__0));
v___x_1617_ = l_Lean_stringToMessageData(v___x_1616_);
return v___x_1617_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Check_Impure_checkShared___closed__3(void){
_start:
{
lean_object* v___x_1619_; lean_object* v___x_1620_; 
v___x_1619_ = ((lean_object*)(l_Lean_Compiler_LCNF_Check_Impure_checkShared___closed__2));
v___x_1620_ = l_Lean_stringToMessageData(v___x_1619_);
return v___x_1620_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Check_Impure_checkShared___closed__5(void){
_start:
{
lean_object* v___x_1622_; lean_object* v___x_1623_; 
v___x_1622_ = ((lean_object*)(l_Lean_Compiler_LCNF_Check_Impure_checkShared___closed__4));
v___x_1623_ = l_Lean_stringToMessageData(v___x_1622_);
return v___x_1623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Impure_checkShared(lean_object* v_v_1624_, lean_object* v_a_1625_, lean_object* v_a_1626_, lean_object* v_a_1627_, lean_object* v_a_1628_, lean_object* v_a_1629_){
_start:
{
lean_object* v___x_1631_; lean_object* v_subst_1632_; lean_object* v___x_1634_; uint8_t v_isShared_1635_; uint8_t v_isSharedCheck_1718_; 
v___x_1631_ = lean_st_ref_get(v_a_1625_);
v_subst_1632_ = lean_ctor_get(v___x_1631_, 1);
v_isSharedCheck_1718_ = !lean_is_exclusive(v___x_1631_);
if (v_isSharedCheck_1718_ == 0)
{
lean_object* v_unused_1719_; 
v_unused_1719_ = lean_ctor_get(v___x_1631_, 0);
lean_dec(v_unused_1719_);
v___x_1634_ = v___x_1631_;
v_isShared_1635_ = v_isSharedCheck_1718_;
goto v_resetjp_1633_;
}
else
{
lean_inc(v_subst_1632_);
lean_dec(v___x_1631_);
v___x_1634_ = lean_box(0);
v_isShared_1635_ = v_isSharedCheck_1718_;
goto v_resetjp_1633_;
}
v_resetjp_1633_:
{
lean_object* v___x_1636_; lean_object* v___x_1637_; 
lean_inc(v_v_1624_);
v___x_1636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1636_, 0, v_v_1624_);
v___x_1637_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_Check_Impure_kill_spec__0___redArg(v_subst_1632_, v_v_1624_, v___x_1636_);
lean_dec_ref(v___x_1636_);
lean_dec(v_v_1624_);
lean_dec_ref(v_subst_1632_);
if (lean_obj_tag(v___x_1637_) == 1)
{
lean_object* v_fvarId_1638_; lean_object* v___x_1639_; 
v_fvarId_1638_ = lean_ctor_get(v___x_1637_, 0);
lean_inc(v_fvarId_1638_);
lean_dec_ref(v___x_1637_);
lean_inc(v_fvarId_1638_);
v___x_1639_ = l_Lean_Compiler_LCNF_getBinderName(v_fvarId_1638_, v_a_1626_, v_a_1627_, v_a_1628_, v_a_1629_);
if (lean_obj_tag(v___x_1639_) == 0)
{
lean_object* v_a_1640_; lean_object* v___x_1642_; uint8_t v_isShared_1643_; uint8_t v_isSharedCheck_1707_; 
v_a_1640_ = lean_ctor_get(v___x_1639_, 0);
v_isSharedCheck_1707_ = !lean_is_exclusive(v___x_1639_);
if (v_isSharedCheck_1707_ == 0)
{
v___x_1642_ = v___x_1639_;
v_isShared_1643_ = v_isSharedCheck_1707_;
goto v_resetjp_1641_;
}
else
{
lean_inc(v_a_1640_);
lean_dec(v___x_1639_);
v___x_1642_ = lean_box(0);
v_isShared_1643_ = v_isSharedCheck_1707_;
goto v_resetjp_1641_;
}
v_resetjp_1641_:
{
lean_object* v___x_1644_; lean_object* v_rc_1645_; lean_object* v___x_1647_; uint8_t v_isShared_1648_; uint8_t v_isSharedCheck_1705_; 
v___x_1644_ = lean_st_ref_get(v_a_1625_);
v_rc_1645_ = lean_ctor_get(v___x_1644_, 0);
v_isSharedCheck_1705_ = !lean_is_exclusive(v___x_1644_);
if (v_isSharedCheck_1705_ == 0)
{
lean_object* v_unused_1706_; 
v_unused_1706_ = lean_ctor_get(v___x_1644_, 1);
lean_dec(v_unused_1706_);
v___x_1647_ = v___x_1644_;
v_isShared_1648_ = v_isSharedCheck_1705_;
goto v_resetjp_1646_;
}
else
{
lean_inc(v_rc_1645_);
lean_dec(v___x_1644_);
v___x_1647_ = lean_box(0);
v_isShared_1648_ = v_isSharedCheck_1705_;
goto v_resetjp_1646_;
}
v_resetjp_1646_:
{
lean_object* v___x_1649_; 
v___x_1649_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_Check_Impure_isDead_spec__0___redArg(v_rc_1645_, v_fvarId_1638_);
lean_dec(v_fvarId_1638_);
lean_dec(v_rc_1645_);
if (lean_obj_tag(v___x_1649_) == 1)
{
lean_object* v_val_1650_; lean_object* v___x_1652_; uint8_t v_isShared_1653_; uint8_t v_isSharedCheck_1700_; 
v_val_1650_ = lean_ctor_get(v___x_1649_, 0);
v_isSharedCheck_1700_ = !lean_is_exclusive(v___x_1649_);
if (v_isSharedCheck_1700_ == 0)
{
v___x_1652_ = v___x_1649_;
v_isShared_1653_ = v_isSharedCheck_1700_;
goto v_resetjp_1651_;
}
else
{
lean_inc(v_val_1650_);
lean_dec(v___x_1649_);
v___x_1652_ = lean_box(0);
v_isShared_1653_ = v_isSharedCheck_1700_;
goto v_resetjp_1651_;
}
v_resetjp_1651_:
{
lean_object* v_rc_1654_; uint8_t v_borrowed_1655_; lean_object* v___y_1657_; lean_object* v___y_1658_; lean_object* v___y_1659_; lean_object* v___y_1660_; lean_object* v___y_1684_; lean_object* v___y_1685_; lean_object* v___y_1686_; lean_object* v___y_1687_; 
v_rc_1654_ = lean_ctor_get(v_val_1650_, 0);
lean_inc(v_rc_1654_);
v_borrowed_1655_ = lean_ctor_get_uint8(v_val_1650_, sizeof(void*)*3);
lean_dec(v_val_1650_);
if (v_borrowed_1655_ == 0)
{
v___y_1684_ = v_a_1626_;
v___y_1685_ = v_a_1627_;
v___y_1686_ = v_a_1628_;
v___y_1687_ = v_a_1629_;
goto v___jp_1683_;
}
else
{
lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; 
lean_dec(v_rc_1654_);
lean_del_object(v___x_1652_);
lean_del_object(v___x_1647_);
lean_del_object(v___x_1642_);
lean_del_object(v___x_1634_);
v___x_1696_ = lean_obj_once(&l_Lean_Compiler_LCNF_Check_Impure_checkShared___closed__5, &l_Lean_Compiler_LCNF_Check_Impure_checkShared___closed__5_once, _init_l_Lean_Compiler_LCNF_Check_Impure_checkShared___closed__5);
v___x_1697_ = l_Lean_MessageData_ofName(v_a_1640_);
v___x_1698_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1698_, 0, v___x_1696_);
lean_ctor_set(v___x_1698_, 1, v___x_1697_);
v___x_1699_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Impure_kill_spec__1___redArg(v___x_1698_, v_a_1626_, v_a_1627_, v_a_1628_, v_a_1629_);
return v___x_1699_;
}
v___jp_1656_:
{
lean_object* v___x_1661_; uint8_t v___x_1662_; 
v___x_1661_ = lean_unsigned_to_nat(1u);
v___x_1662_ = lean_nat_dec_lt(v___x_1661_, v_rc_1654_);
if (v___x_1662_ == 0)
{
lean_object* v___x_1663_; lean_object* v___x_1665_; 
lean_dec(v_rc_1654_);
lean_del_object(v___x_1652_);
lean_del_object(v___x_1647_);
lean_dec(v_a_1640_);
lean_del_object(v___x_1634_);
v___x_1663_ = lean_box(0);
if (v_isShared_1643_ == 0)
{
lean_ctor_set(v___x_1642_, 0, v___x_1663_);
v___x_1665_ = v___x_1642_;
goto v_reusejp_1664_;
}
else
{
lean_object* v_reuseFailAlloc_1666_; 
v_reuseFailAlloc_1666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1666_, 0, v___x_1663_);
v___x_1665_ = v_reuseFailAlloc_1666_;
goto v_reusejp_1664_;
}
v_reusejp_1664_:
{
return v___x_1665_;
}
}
else
{
lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1670_; 
lean_del_object(v___x_1642_);
v___x_1667_ = lean_obj_once(&l_Lean_Compiler_LCNF_Check_Impure_checkShared___closed__1, &l_Lean_Compiler_LCNF_Check_Impure_checkShared___closed__1_once, _init_l_Lean_Compiler_LCNF_Check_Impure_checkShared___closed__1);
v___x_1668_ = l_Lean_MessageData_ofName(v_a_1640_);
if (v_isShared_1648_ == 0)
{
lean_ctor_set_tag(v___x_1647_, 7);
lean_ctor_set(v___x_1647_, 1, v___x_1668_);
lean_ctor_set(v___x_1647_, 0, v___x_1667_);
v___x_1670_ = v___x_1647_;
goto v_reusejp_1669_;
}
else
{
lean_object* v_reuseFailAlloc_1682_; 
v_reuseFailAlloc_1682_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1682_, 0, v___x_1667_);
lean_ctor_set(v_reuseFailAlloc_1682_, 1, v___x_1668_);
v___x_1670_ = v_reuseFailAlloc_1682_;
goto v_reusejp_1669_;
}
v_reusejp_1669_:
{
lean_object* v___x_1671_; lean_object* v___x_1673_; 
v___x_1671_ = lean_obj_once(&l_Lean_Compiler_LCNF_Check_Impure_checkShared___closed__3, &l_Lean_Compiler_LCNF_Check_Impure_checkShared___closed__3_once, _init_l_Lean_Compiler_LCNF_Check_Impure_checkShared___closed__3);
if (v_isShared_1635_ == 0)
{
lean_ctor_set_tag(v___x_1634_, 7);
lean_ctor_set(v___x_1634_, 1, v___x_1671_);
lean_ctor_set(v___x_1634_, 0, v___x_1670_);
v___x_1673_ = v___x_1634_;
goto v_reusejp_1672_;
}
else
{
lean_object* v_reuseFailAlloc_1681_; 
v_reuseFailAlloc_1681_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1681_, 0, v___x_1670_);
lean_ctor_set(v_reuseFailAlloc_1681_, 1, v___x_1671_);
v___x_1673_ = v_reuseFailAlloc_1681_;
goto v_reusejp_1672_;
}
v_reusejp_1672_:
{
lean_object* v___x_1674_; lean_object* v___x_1676_; 
v___x_1674_ = l_Nat_reprFast(v_rc_1654_);
if (v_isShared_1653_ == 0)
{
lean_ctor_set_tag(v___x_1652_, 3);
lean_ctor_set(v___x_1652_, 0, v___x_1674_);
v___x_1676_ = v___x_1652_;
goto v_reusejp_1675_;
}
else
{
lean_object* v_reuseFailAlloc_1680_; 
v_reuseFailAlloc_1680_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1680_, 0, v___x_1674_);
v___x_1676_ = v_reuseFailAlloc_1680_;
goto v_reusejp_1675_;
}
v_reusejp_1675_:
{
lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; 
v___x_1677_ = l_Lean_MessageData_ofFormat(v___x_1676_);
v___x_1678_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1678_, 0, v___x_1673_);
lean_ctor_set(v___x_1678_, 1, v___x_1677_);
v___x_1679_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Impure_kill_spec__1___redArg(v___x_1678_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_);
return v___x_1679_;
}
}
}
}
}
v___jp_1683_:
{
lean_object* v___x_1688_; uint8_t v___x_1689_; 
v___x_1688_ = lean_unsigned_to_nat(0u);
v___x_1689_ = lean_nat_dec_eq(v_rc_1654_, v___x_1688_);
if (v___x_1689_ == 0)
{
v___y_1657_ = v___y_1684_;
v___y_1658_ = v___y_1685_;
v___y_1659_ = v___y_1686_;
v___y_1660_ = v___y_1687_;
goto v___jp_1656_;
}
else
{
lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; 
lean_dec(v_rc_1654_);
lean_del_object(v___x_1652_);
lean_del_object(v___x_1647_);
lean_del_object(v___x_1642_);
lean_del_object(v___x_1634_);
v___x_1690_ = lean_obj_once(&l_Lean_Compiler_LCNF_Check_Impure_checkShared___closed__1, &l_Lean_Compiler_LCNF_Check_Impure_checkShared___closed__1_once, _init_l_Lean_Compiler_LCNF_Check_Impure_checkShared___closed__1);
v___x_1691_ = l_Lean_MessageData_ofName(v_a_1640_);
v___x_1692_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1692_, 0, v___x_1690_);
lean_ctor_set(v___x_1692_, 1, v___x_1691_);
v___x_1693_ = lean_obj_once(&l_Lean_Compiler_LCNF_Check_Impure_useVar___closed__3, &l_Lean_Compiler_LCNF_Check_Impure_useVar___closed__3_once, _init_l_Lean_Compiler_LCNF_Check_Impure_useVar___closed__3);
v___x_1694_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1694_, 0, v___x_1692_);
lean_ctor_set(v___x_1694_, 1, v___x_1693_);
v___x_1695_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Impure_kill_spec__1___redArg(v___x_1694_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_);
return v___x_1695_;
}
}
}
}
else
{
lean_object* v___x_1701_; lean_object* v___x_1703_; 
lean_dec(v___x_1649_);
lean_del_object(v___x_1647_);
lean_dec(v_a_1640_);
lean_del_object(v___x_1634_);
v___x_1701_ = lean_box(0);
if (v_isShared_1643_ == 0)
{
lean_ctor_set(v___x_1642_, 0, v___x_1701_);
v___x_1703_ = v___x_1642_;
goto v_reusejp_1702_;
}
else
{
lean_object* v_reuseFailAlloc_1704_; 
v_reuseFailAlloc_1704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1704_, 0, v___x_1701_);
v___x_1703_ = v_reuseFailAlloc_1704_;
goto v_reusejp_1702_;
}
v_reusejp_1702_:
{
return v___x_1703_;
}
}
}
}
}
else
{
lean_object* v_a_1708_; lean_object* v___x_1710_; uint8_t v_isShared_1711_; uint8_t v_isSharedCheck_1715_; 
lean_dec(v_fvarId_1638_);
lean_del_object(v___x_1634_);
v_a_1708_ = lean_ctor_get(v___x_1639_, 0);
v_isSharedCheck_1715_ = !lean_is_exclusive(v___x_1639_);
if (v_isSharedCheck_1715_ == 0)
{
v___x_1710_ = v___x_1639_;
v_isShared_1711_ = v_isSharedCheck_1715_;
goto v_resetjp_1709_;
}
else
{
lean_inc(v_a_1708_);
lean_dec(v___x_1639_);
v___x_1710_ = lean_box(0);
v_isShared_1711_ = v_isSharedCheck_1715_;
goto v_resetjp_1709_;
}
v_resetjp_1709_:
{
lean_object* v___x_1713_; 
if (v_isShared_1711_ == 0)
{
v___x_1713_ = v___x_1710_;
goto v_reusejp_1712_;
}
else
{
lean_object* v_reuseFailAlloc_1714_; 
v_reuseFailAlloc_1714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1714_, 0, v_a_1708_);
v___x_1713_ = v_reuseFailAlloc_1714_;
goto v_reusejp_1712_;
}
v_reusejp_1712_:
{
return v___x_1713_;
}
}
}
}
else
{
lean_object* v___x_1716_; lean_object* v___x_1717_; 
lean_dec(v___x_1637_);
lean_del_object(v___x_1634_);
v___x_1716_ = lean_box(0);
v___x_1717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1717_, 0, v___x_1716_);
return v___x_1717_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Impure_checkShared___boxed(lean_object* v_v_1720_, lean_object* v_a_1721_, lean_object* v_a_1722_, lean_object* v_a_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_, lean_object* v_a_1726_){
_start:
{
lean_object* v_res_1727_; 
v_res_1727_ = l_Lean_Compiler_LCNF_Check_Impure_checkShared(v_v_1720_, v_a_1721_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_);
lean_dec(v_a_1725_);
lean_dec_ref(v_a_1724_);
lean_dec(v_a_1723_);
lean_dec_ref(v_a_1722_);
lean_dec(v_a_1721_);
return v_res_1727_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Lean_Compiler_LCNF_Check_Impure_inc_spec__0(lean_object* v_n_1728_, lean_object* v_k_1729_, lean_object* v_t_1730_){
_start:
{
if (lean_obj_tag(v_t_1730_) == 0)
{
lean_object* v_size_1731_; lean_object* v_k_1732_; lean_object* v_v_1733_; lean_object* v_l_1734_; lean_object* v_r_1735_; lean_object* v___x_1737_; uint8_t v_isShared_1738_; uint8_t v_isSharedCheck_1763_; 
v_size_1731_ = lean_ctor_get(v_t_1730_, 0);
v_k_1732_ = lean_ctor_get(v_t_1730_, 1);
v_v_1733_ = lean_ctor_get(v_t_1730_, 2);
v_l_1734_ = lean_ctor_get(v_t_1730_, 3);
v_r_1735_ = lean_ctor_get(v_t_1730_, 4);
v_isSharedCheck_1763_ = !lean_is_exclusive(v_t_1730_);
if (v_isSharedCheck_1763_ == 0)
{
v___x_1737_ = v_t_1730_;
v_isShared_1738_ = v_isSharedCheck_1763_;
goto v_resetjp_1736_;
}
else
{
lean_inc(v_r_1735_);
lean_inc(v_l_1734_);
lean_inc(v_v_1733_);
lean_inc(v_k_1732_);
lean_inc(v_size_1731_);
lean_dec(v_t_1730_);
v___x_1737_ = lean_box(0);
v_isShared_1738_ = v_isSharedCheck_1763_;
goto v_resetjp_1736_;
}
v_resetjp_1736_:
{
uint8_t v___x_1739_; 
v___x_1739_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1729_, v_k_1732_);
switch(v___x_1739_)
{
case 0:
{
lean_object* v___x_1740_; lean_object* v___x_1742_; 
v___x_1740_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Lean_Compiler_LCNF_Check_Impure_inc_spec__0(v_n_1728_, v_k_1729_, v_l_1734_);
if (v_isShared_1738_ == 0)
{
lean_ctor_set(v___x_1737_, 3, v___x_1740_);
v___x_1742_ = v___x_1737_;
goto v_reusejp_1741_;
}
else
{
lean_object* v_reuseFailAlloc_1743_; 
v_reuseFailAlloc_1743_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1743_, 0, v_size_1731_);
lean_ctor_set(v_reuseFailAlloc_1743_, 1, v_k_1732_);
lean_ctor_set(v_reuseFailAlloc_1743_, 2, v_v_1733_);
lean_ctor_set(v_reuseFailAlloc_1743_, 3, v___x_1740_);
lean_ctor_set(v_reuseFailAlloc_1743_, 4, v_r_1735_);
v___x_1742_ = v_reuseFailAlloc_1743_;
goto v_reusejp_1741_;
}
v_reusejp_1741_:
{
return v___x_1742_;
}
}
case 1:
{
lean_object* v_rc_1744_; uint8_t v_borrowed_1745_; lean_object* v_parents_1746_; lean_object* v_children_1747_; lean_object* v___x_1749_; uint8_t v_isShared_1750_; uint8_t v_isSharedCheck_1758_; 
lean_dec(v_k_1732_);
v_rc_1744_ = lean_ctor_get(v_v_1733_, 0);
v_borrowed_1745_ = lean_ctor_get_uint8(v_v_1733_, sizeof(void*)*3);
v_parents_1746_ = lean_ctor_get(v_v_1733_, 1);
v_children_1747_ = lean_ctor_get(v_v_1733_, 2);
v_isSharedCheck_1758_ = !lean_is_exclusive(v_v_1733_);
if (v_isSharedCheck_1758_ == 0)
{
v___x_1749_ = v_v_1733_;
v_isShared_1750_ = v_isSharedCheck_1758_;
goto v_resetjp_1748_;
}
else
{
lean_inc(v_children_1747_);
lean_inc(v_parents_1746_);
lean_inc(v_rc_1744_);
lean_dec(v_v_1733_);
v___x_1749_ = lean_box(0);
v_isShared_1750_ = v_isSharedCheck_1758_;
goto v_resetjp_1748_;
}
v_resetjp_1748_:
{
lean_object* v___x_1751_; lean_object* v___x_1753_; 
v___x_1751_ = lean_nat_add(v_rc_1744_, v_n_1728_);
lean_dec(v_rc_1744_);
if (v_isShared_1750_ == 0)
{
lean_ctor_set(v___x_1749_, 0, v___x_1751_);
v___x_1753_ = v___x_1749_;
goto v_reusejp_1752_;
}
else
{
lean_object* v_reuseFailAlloc_1757_; 
v_reuseFailAlloc_1757_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1757_, 0, v___x_1751_);
lean_ctor_set(v_reuseFailAlloc_1757_, 1, v_parents_1746_);
lean_ctor_set(v_reuseFailAlloc_1757_, 2, v_children_1747_);
lean_ctor_set_uint8(v_reuseFailAlloc_1757_, sizeof(void*)*3, v_borrowed_1745_);
v___x_1753_ = v_reuseFailAlloc_1757_;
goto v_reusejp_1752_;
}
v_reusejp_1752_:
{
lean_object* v___x_1755_; 
if (v_isShared_1738_ == 0)
{
lean_ctor_set(v___x_1737_, 2, v___x_1753_);
lean_ctor_set(v___x_1737_, 1, v_k_1729_);
v___x_1755_ = v___x_1737_;
goto v_reusejp_1754_;
}
else
{
lean_object* v_reuseFailAlloc_1756_; 
v_reuseFailAlloc_1756_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1756_, 0, v_size_1731_);
lean_ctor_set(v_reuseFailAlloc_1756_, 1, v_k_1729_);
lean_ctor_set(v_reuseFailAlloc_1756_, 2, v___x_1753_);
lean_ctor_set(v_reuseFailAlloc_1756_, 3, v_l_1734_);
lean_ctor_set(v_reuseFailAlloc_1756_, 4, v_r_1735_);
v___x_1755_ = v_reuseFailAlloc_1756_;
goto v_reusejp_1754_;
}
v_reusejp_1754_:
{
return v___x_1755_;
}
}
}
}
default: 
{
lean_object* v___x_1759_; lean_object* v___x_1761_; 
v___x_1759_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Lean_Compiler_LCNF_Check_Impure_inc_spec__0(v_n_1728_, v_k_1729_, v_r_1735_);
if (v_isShared_1738_ == 0)
{
lean_ctor_set(v___x_1737_, 4, v___x_1759_);
v___x_1761_ = v___x_1737_;
goto v_reusejp_1760_;
}
else
{
lean_object* v_reuseFailAlloc_1762_; 
v_reuseFailAlloc_1762_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1762_, 0, v_size_1731_);
lean_ctor_set(v_reuseFailAlloc_1762_, 1, v_k_1732_);
lean_ctor_set(v_reuseFailAlloc_1762_, 2, v_v_1733_);
lean_ctor_set(v_reuseFailAlloc_1762_, 3, v_l_1734_);
lean_ctor_set(v_reuseFailAlloc_1762_, 4, v___x_1759_);
v___x_1761_ = v_reuseFailAlloc_1762_;
goto v_reusejp_1760_;
}
v_reusejp_1760_:
{
return v___x_1761_;
}
}
}
}
}
else
{
lean_dec(v_k_1729_);
return v_t_1730_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Lean_Compiler_LCNF_Check_Impure_inc_spec__0___boxed(lean_object* v_n_1764_, lean_object* v_k_1765_, lean_object* v_t_1766_){
_start:
{
lean_object* v_res_1767_; 
v_res_1767_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Lean_Compiler_LCNF_Check_Impure_inc_spec__0(v_n_1764_, v_k_1765_, v_t_1766_);
lean_dec(v_n_1764_);
return v_res_1767_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Check_Impure_inc___closed__1(void){
_start:
{
lean_object* v___x_1769_; lean_object* v___x_1770_; 
v___x_1769_ = ((lean_object*)(l_Lean_Compiler_LCNF_Check_Impure_inc___closed__0));
v___x_1770_ = l_Lean_stringToMessageData(v___x_1769_);
return v___x_1770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Impure_inc(lean_object* v_v_1771_, lean_object* v_n_1772_, lean_object* v_a_1773_, lean_object* v_a_1774_, lean_object* v_a_1775_, lean_object* v_a_1776_, lean_object* v_a_1777_){
_start:
{
lean_object* v___x_1779_; lean_object* v_subst_1780_; lean_object* v___x_1782_; uint8_t v_isShared_1783_; uint8_t v_isSharedCheck_1852_; 
v___x_1779_ = lean_st_ref_get(v_a_1773_);
v_subst_1780_ = lean_ctor_get(v___x_1779_, 1);
v_isSharedCheck_1852_ = !lean_is_exclusive(v___x_1779_);
if (v_isSharedCheck_1852_ == 0)
{
lean_object* v_unused_1853_; 
v_unused_1853_ = lean_ctor_get(v___x_1779_, 0);
lean_dec(v_unused_1853_);
v___x_1782_ = v___x_1779_;
v_isShared_1783_ = v_isSharedCheck_1852_;
goto v_resetjp_1781_;
}
else
{
lean_inc(v_subst_1780_);
lean_dec(v___x_1779_);
v___x_1782_ = lean_box(0);
v_isShared_1783_ = v_isSharedCheck_1852_;
goto v_resetjp_1781_;
}
v_resetjp_1781_:
{
lean_object* v___x_1784_; lean_object* v___x_1785_; 
lean_inc(v_v_1771_);
v___x_1784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1784_, 0, v_v_1771_);
v___x_1785_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_Check_Impure_kill_spec__0___redArg(v_subst_1780_, v_v_1771_, v___x_1784_);
lean_dec_ref(v___x_1784_);
lean_dec(v_v_1771_);
lean_dec_ref(v_subst_1780_);
if (lean_obj_tag(v___x_1785_) == 1)
{
lean_object* v_fvarId_1786_; lean_object* v___x_1788_; uint8_t v_isShared_1789_; uint8_t v_isSharedCheck_1849_; 
v_fvarId_1786_ = lean_ctor_get(v___x_1785_, 0);
v_isSharedCheck_1849_ = !lean_is_exclusive(v___x_1785_);
if (v_isSharedCheck_1849_ == 0)
{
v___x_1788_ = v___x_1785_;
v_isShared_1789_ = v_isSharedCheck_1849_;
goto v_resetjp_1787_;
}
else
{
lean_inc(v_fvarId_1786_);
lean_dec(v___x_1785_);
v___x_1788_ = lean_box(0);
v_isShared_1789_ = v_isSharedCheck_1849_;
goto v_resetjp_1787_;
}
v_resetjp_1787_:
{
lean_object* v___y_1791_; lean_object* v___x_1808_; 
lean_inc(v_fvarId_1786_);
v___x_1808_ = l_Lean_Compiler_LCNF_getBinderName(v_fvarId_1786_, v_a_1774_, v_a_1775_, v_a_1776_, v_a_1777_);
if (lean_obj_tag(v___x_1808_) == 0)
{
lean_object* v_a_1809_; lean_object* v___x_1811_; uint8_t v_isShared_1812_; uint8_t v_isSharedCheck_1840_; 
v_a_1809_ = lean_ctor_get(v___x_1808_, 0);
v_isSharedCheck_1840_ = !lean_is_exclusive(v___x_1808_);
if (v_isSharedCheck_1840_ == 0)
{
v___x_1811_ = v___x_1808_;
v_isShared_1812_ = v_isSharedCheck_1840_;
goto v_resetjp_1810_;
}
else
{
lean_inc(v_a_1809_);
lean_dec(v___x_1808_);
v___x_1811_ = lean_box(0);
v_isShared_1812_ = v_isSharedCheck_1840_;
goto v_resetjp_1810_;
}
v_resetjp_1810_:
{
lean_object* v___x_1813_; lean_object* v_rc_1814_; lean_object* v___x_1816_; uint8_t v_isShared_1817_; uint8_t v_isSharedCheck_1838_; 
v___x_1813_ = lean_st_ref_get(v_a_1773_);
v_rc_1814_ = lean_ctor_get(v___x_1813_, 0);
v_isSharedCheck_1838_ = !lean_is_exclusive(v___x_1813_);
if (v_isSharedCheck_1838_ == 0)
{
lean_object* v_unused_1839_; 
v_unused_1839_ = lean_ctor_get(v___x_1813_, 1);
lean_dec(v_unused_1839_);
v___x_1816_ = v___x_1813_;
v_isShared_1817_ = v_isSharedCheck_1838_;
goto v_resetjp_1815_;
}
else
{
lean_inc(v_rc_1814_);
lean_dec(v___x_1813_);
v___x_1816_ = lean_box(0);
v_isShared_1817_ = v_isSharedCheck_1838_;
goto v_resetjp_1815_;
}
v_resetjp_1815_:
{
lean_object* v___x_1818_; 
v___x_1818_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_Check_Impure_isDead_spec__0___redArg(v_rc_1814_, v_fvarId_1786_);
lean_dec(v_rc_1814_);
if (lean_obj_tag(v___x_1818_) == 1)
{
lean_object* v_val_1819_; uint8_t v_borrowed_1820_; 
lean_del_object(v___x_1811_);
v_val_1819_ = lean_ctor_get(v___x_1818_, 0);
lean_inc(v_val_1819_);
lean_dec_ref(v___x_1818_);
v_borrowed_1820_ = lean_ctor_get_uint8(v_val_1819_, sizeof(void*)*3);
if (v_borrowed_1820_ == 0)
{
lean_object* v_rc_1821_; lean_object* v___x_1822_; uint8_t v___x_1823_; 
v_rc_1821_ = lean_ctor_get(v_val_1819_, 0);
lean_inc(v_rc_1821_);
lean_dec(v_val_1819_);
v___x_1822_ = lean_unsigned_to_nat(0u);
v___x_1823_ = lean_nat_dec_eq(v_rc_1821_, v___x_1822_);
lean_dec(v_rc_1821_);
if (v___x_1823_ == 0)
{
lean_del_object(v___x_1816_);
lean_dec(v_a_1809_);
lean_del_object(v___x_1782_);
v___y_1791_ = v_a_1773_;
goto v___jp_1790_;
}
else
{
lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1827_; 
lean_del_object(v___x_1788_);
lean_dec(v_fvarId_1786_);
v___x_1824_ = lean_obj_once(&l_Lean_Compiler_LCNF_Check_Impure_inc___closed__1, &l_Lean_Compiler_LCNF_Check_Impure_inc___closed__1_once, _init_l_Lean_Compiler_LCNF_Check_Impure_inc___closed__1);
v___x_1825_ = l_Lean_MessageData_ofName(v_a_1809_);
if (v_isShared_1817_ == 0)
{
lean_ctor_set_tag(v___x_1816_, 7);
lean_ctor_set(v___x_1816_, 1, v___x_1825_);
lean_ctor_set(v___x_1816_, 0, v___x_1824_);
v___x_1827_ = v___x_1816_;
goto v_reusejp_1826_;
}
else
{
lean_object* v_reuseFailAlloc_1833_; 
v_reuseFailAlloc_1833_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1833_, 0, v___x_1824_);
lean_ctor_set(v_reuseFailAlloc_1833_, 1, v___x_1825_);
v___x_1827_ = v_reuseFailAlloc_1833_;
goto v_reusejp_1826_;
}
v_reusejp_1826_:
{
lean_object* v___x_1828_; lean_object* v___x_1830_; 
v___x_1828_ = lean_obj_once(&l_Lean_Compiler_LCNF_Check_Impure_useVar___closed__3, &l_Lean_Compiler_LCNF_Check_Impure_useVar___closed__3_once, _init_l_Lean_Compiler_LCNF_Check_Impure_useVar___closed__3);
if (v_isShared_1783_ == 0)
{
lean_ctor_set_tag(v___x_1782_, 7);
lean_ctor_set(v___x_1782_, 1, v___x_1828_);
lean_ctor_set(v___x_1782_, 0, v___x_1827_);
v___x_1830_ = v___x_1782_;
goto v_reusejp_1829_;
}
else
{
lean_object* v_reuseFailAlloc_1832_; 
v_reuseFailAlloc_1832_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1832_, 0, v___x_1827_);
lean_ctor_set(v_reuseFailAlloc_1832_, 1, v___x_1828_);
v___x_1830_ = v_reuseFailAlloc_1832_;
goto v_reusejp_1829_;
}
v_reusejp_1829_:
{
lean_object* v___x_1831_; 
v___x_1831_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Impure_kill_spec__1___redArg(v___x_1830_, v_a_1774_, v_a_1775_, v_a_1776_, v_a_1777_);
return v___x_1831_;
}
}
}
}
else
{
lean_dec(v_val_1819_);
lean_del_object(v___x_1816_);
lean_dec(v_a_1809_);
lean_del_object(v___x_1782_);
v___y_1791_ = v_a_1773_;
goto v___jp_1790_;
}
}
else
{
lean_object* v___x_1834_; lean_object* v___x_1836_; 
lean_dec(v___x_1818_);
lean_del_object(v___x_1816_);
lean_dec(v_a_1809_);
lean_del_object(v___x_1788_);
lean_dec(v_fvarId_1786_);
lean_del_object(v___x_1782_);
v___x_1834_ = lean_box(0);
if (v_isShared_1812_ == 0)
{
lean_ctor_set(v___x_1811_, 0, v___x_1834_);
v___x_1836_ = v___x_1811_;
goto v_reusejp_1835_;
}
else
{
lean_object* v_reuseFailAlloc_1837_; 
v_reuseFailAlloc_1837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1837_, 0, v___x_1834_);
v___x_1836_ = v_reuseFailAlloc_1837_;
goto v_reusejp_1835_;
}
v_reusejp_1835_:
{
return v___x_1836_;
}
}
}
}
}
else
{
lean_object* v_a_1841_; lean_object* v___x_1843_; uint8_t v_isShared_1844_; uint8_t v_isSharedCheck_1848_; 
lean_del_object(v___x_1788_);
lean_dec(v_fvarId_1786_);
lean_del_object(v___x_1782_);
v_a_1841_ = lean_ctor_get(v___x_1808_, 0);
v_isSharedCheck_1848_ = !lean_is_exclusive(v___x_1808_);
if (v_isSharedCheck_1848_ == 0)
{
v___x_1843_ = v___x_1808_;
v_isShared_1844_ = v_isSharedCheck_1848_;
goto v_resetjp_1842_;
}
else
{
lean_inc(v_a_1841_);
lean_dec(v___x_1808_);
v___x_1843_ = lean_box(0);
v_isShared_1844_ = v_isSharedCheck_1848_;
goto v_resetjp_1842_;
}
v_resetjp_1842_:
{
lean_object* v___x_1846_; 
if (v_isShared_1844_ == 0)
{
v___x_1846_ = v___x_1843_;
goto v_reusejp_1845_;
}
else
{
lean_object* v_reuseFailAlloc_1847_; 
v_reuseFailAlloc_1847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1847_, 0, v_a_1841_);
v___x_1846_ = v_reuseFailAlloc_1847_;
goto v_reusejp_1845_;
}
v_reusejp_1845_:
{
return v___x_1846_;
}
}
}
v___jp_1790_:
{
lean_object* v___x_1792_; lean_object* v_rc_1793_; lean_object* v_subst_1794_; lean_object* v___x_1796_; uint8_t v_isShared_1797_; uint8_t v_isSharedCheck_1807_; 
v___x_1792_ = lean_st_ref_take(v___y_1791_);
v_rc_1793_ = lean_ctor_get(v___x_1792_, 0);
v_subst_1794_ = lean_ctor_get(v___x_1792_, 1);
v_isSharedCheck_1807_ = !lean_is_exclusive(v___x_1792_);
if (v_isSharedCheck_1807_ == 0)
{
v___x_1796_ = v___x_1792_;
v_isShared_1797_ = v_isSharedCheck_1807_;
goto v_resetjp_1795_;
}
else
{
lean_inc(v_subst_1794_);
lean_inc(v_rc_1793_);
lean_dec(v___x_1792_);
v___x_1796_ = lean_box(0);
v_isShared_1797_ = v_isSharedCheck_1807_;
goto v_resetjp_1795_;
}
v_resetjp_1795_:
{
lean_object* v___x_1798_; lean_object* v___x_1800_; 
v___x_1798_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Lean_Compiler_LCNF_Check_Impure_inc_spec__0(v_n_1772_, v_fvarId_1786_, v_rc_1793_);
if (v_isShared_1797_ == 0)
{
lean_ctor_set(v___x_1796_, 0, v___x_1798_);
v___x_1800_ = v___x_1796_;
goto v_reusejp_1799_;
}
else
{
lean_object* v_reuseFailAlloc_1806_; 
v_reuseFailAlloc_1806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1806_, 0, v___x_1798_);
lean_ctor_set(v_reuseFailAlloc_1806_, 1, v_subst_1794_);
v___x_1800_ = v_reuseFailAlloc_1806_;
goto v_reusejp_1799_;
}
v_reusejp_1799_:
{
lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1804_; 
v___x_1801_ = lean_st_ref_set(v___y_1791_, v___x_1800_);
v___x_1802_ = lean_box(0);
if (v_isShared_1789_ == 0)
{
lean_ctor_set_tag(v___x_1788_, 0);
lean_ctor_set(v___x_1788_, 0, v___x_1802_);
v___x_1804_ = v___x_1788_;
goto v_reusejp_1803_;
}
else
{
lean_object* v_reuseFailAlloc_1805_; 
v_reuseFailAlloc_1805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1805_, 0, v___x_1802_);
v___x_1804_ = v_reuseFailAlloc_1805_;
goto v_reusejp_1803_;
}
v_reusejp_1803_:
{
return v___x_1804_;
}
}
}
}
}
}
else
{
lean_object* v___x_1850_; lean_object* v___x_1851_; 
lean_dec(v___x_1785_);
lean_del_object(v___x_1782_);
v___x_1850_ = lean_box(0);
v___x_1851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1851_, 0, v___x_1850_);
return v___x_1851_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Impure_inc___boxed(lean_object* v_v_1854_, lean_object* v_n_1855_, lean_object* v_a_1856_, lean_object* v_a_1857_, lean_object* v_a_1858_, lean_object* v_a_1859_, lean_object* v_a_1860_, lean_object* v_a_1861_){
_start:
{
lean_object* v_res_1862_; 
v_res_1862_ = l_Lean_Compiler_LCNF_Check_Impure_inc(v_v_1854_, v_n_1855_, v_a_1856_, v_a_1857_, v_a_1858_, v_a_1859_, v_a_1860_);
lean_dec(v_a_1860_);
lean_dec_ref(v_a_1859_);
lean_dec(v_a_1858_);
lean_dec_ref(v_a_1857_);
lean_dec(v_a_1856_);
lean_dec(v_n_1855_);
return v_res_1862_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Impure_consumeArg(lean_object* v_v_1863_, lean_object* v_a_1864_, lean_object* v_a_1865_, lean_object* v_a_1866_, lean_object* v_a_1867_, lean_object* v_a_1868_){
_start:
{
if (lean_obj_tag(v_v_1863_) == 0)
{
lean_object* v___x_1870_; lean_object* v___x_1871_; 
v___x_1870_ = lean_box(0);
v___x_1871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1871_, 0, v___x_1870_);
return v___x_1871_;
}
else
{
lean_object* v_fvarId_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; 
v_fvarId_1872_ = lean_ctor_get(v_v_1863_, 0);
lean_inc(v_fvarId_1872_);
lean_dec_ref(v_v_1863_);
v___x_1873_ = lean_unsigned_to_nat(1u);
v___x_1874_ = l_Lean_Compiler_LCNF_Check_Impure_consume(v_fvarId_1872_, v___x_1873_, v_a_1864_, v_a_1865_, v_a_1866_, v_a_1867_, v_a_1868_);
return v___x_1874_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Impure_consumeArg___boxed(lean_object* v_v_1875_, lean_object* v_a_1876_, lean_object* v_a_1877_, lean_object* v_a_1878_, lean_object* v_a_1879_, lean_object* v_a_1880_, lean_object* v_a_1881_){
_start:
{
lean_object* v_res_1882_; 
v_res_1882_ = l_Lean_Compiler_LCNF_Check_Impure_consumeArg(v_v_1875_, v_a_1876_, v_a_1877_, v_a_1878_, v_a_1879_, v_a_1880_);
lean_dec(v_a_1880_);
lean_dec_ref(v_a_1879_);
lean_dec(v_a_1878_);
lean_dec_ref(v_a_1877_);
lean_dec(v_a_1876_);
return v_res_1882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Impure_useArg(lean_object* v_v_1883_, lean_object* v_a_1884_, lean_object* v_a_1885_, lean_object* v_a_1886_, lean_object* v_a_1887_, lean_object* v_a_1888_){
_start:
{
if (lean_obj_tag(v_v_1883_) == 0)
{
lean_object* v___x_1890_; lean_object* v___x_1891_; 
v___x_1890_ = lean_box(0);
v___x_1891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1891_, 0, v___x_1890_);
return v___x_1891_;
}
else
{
lean_object* v_fvarId_1892_; lean_object* v___x_1893_; 
v_fvarId_1892_ = lean_ctor_get(v_v_1883_, 0);
lean_inc(v_fvarId_1892_);
lean_dec_ref(v_v_1883_);
v___x_1893_ = l_Lean_Compiler_LCNF_Check_Impure_useVar(v_fvarId_1892_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_);
return v___x_1893_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Impure_useArg___boxed(lean_object* v_v_1894_, lean_object* v_a_1895_, lean_object* v_a_1896_, lean_object* v_a_1897_, lean_object* v_a_1898_, lean_object* v_a_1899_, lean_object* v_a_1900_){
_start:
{
lean_object* v_res_1901_; 
v_res_1901_ = l_Lean_Compiler_LCNF_Check_Impure_useArg(v_v_1894_, v_a_1895_, v_a_1896_, v_a_1897_, v_a_1898_, v_a_1899_);
lean_dec(v_a_1899_);
lean_dec_ref(v_a_1898_);
lean_dec(v_a_1897_);
lean_dec_ref(v_a_1896_);
lean_dec(v_a_1895_);
return v_res_1901_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Check_Impure_checkLeaks_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_1903_; lean_object* v___x_1904_; 
v___x_1903_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Check_Impure_checkLeaks_spec__0___redArg___closed__0));
v___x_1904_ = l_Lean_stringToMessageData(v___x_1903_);
return v___x_1904_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Check_Impure_checkLeaks_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_1906_; lean_object* v___x_1907_; 
v___x_1906_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Check_Impure_checkLeaks_spec__0___redArg___closed__2));
v___x_1907_ = l_Lean_stringToMessageData(v___x_1906_);
return v___x_1907_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Check_Impure_checkLeaks_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_1909_; lean_object* v___x_1910_; 
v___x_1909_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Check_Impure_checkLeaks_spec__0___redArg___closed__4));
v___x_1910_ = l_Lean_stringToMessageData(v___x_1909_);
return v___x_1910_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Check_Impure_checkLeaks_spec__0___redArg(lean_object* v_init_1911_, lean_object* v_x_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_){
_start:
{
if (lean_obj_tag(v_x_1912_) == 0)
{
lean_object* v_k_1918_; lean_object* v_v_1919_; lean_object* v_l_1920_; lean_object* v_r_1921_; lean_object* v___x_1922_; 
v_k_1918_ = lean_ctor_get(v_x_1912_, 1);
lean_inc(v_k_1918_);
v_v_1919_ = lean_ctor_get(v_x_1912_, 2);
lean_inc(v_v_1919_);
v_l_1920_ = lean_ctor_get(v_x_1912_, 3);
lean_inc(v_l_1920_);
v_r_1921_ = lean_ctor_get(v_x_1912_, 4);
lean_inc(v_r_1921_);
lean_dec_ref(v_x_1912_);
v___x_1922_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Check_Impure_checkLeaks_spec__0___redArg(v_init_1911_, v_l_1920_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_);
if (lean_obj_tag(v___x_1922_) == 0)
{
lean_object* v_a_1923_; lean_object* v___x_1925_; uint8_t v_isShared_1926_; uint8_t v_isSharedCheck_1964_; 
v_a_1923_ = lean_ctor_get(v___x_1922_, 0);
lean_inc(v_a_1923_);
lean_dec_ref(v___x_1922_);
v_isSharedCheck_1964_ = !lean_is_exclusive(v_a_1923_);
if (v_isSharedCheck_1964_ == 0)
{
lean_object* v_unused_1965_; 
v_unused_1965_ = lean_ctor_get(v_a_1923_, 0);
lean_dec(v_unused_1965_);
v___x_1925_ = v_a_1923_;
v_isShared_1926_ = v_isSharedCheck_1964_;
goto v_resetjp_1924_;
}
else
{
lean_dec(v_a_1923_);
v___x_1925_ = lean_box(0);
v_isShared_1926_ = v_isSharedCheck_1964_;
goto v_resetjp_1924_;
}
v_resetjp_1924_:
{
lean_object* v_rc_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; uint8_t v___x_1930_; 
v_rc_1927_ = lean_ctor_get(v_v_1919_, 0);
lean_inc(v_rc_1927_);
lean_dec(v_v_1919_);
v___x_1928_ = lean_box(0);
v___x_1929_ = lean_unsigned_to_nat(0u);
v___x_1930_ = lean_nat_dec_lt(v___x_1929_, v_rc_1927_);
if (v___x_1930_ == 0)
{
lean_dec(v_rc_1927_);
lean_del_object(v___x_1925_);
lean_dec(v_k_1918_);
v_init_1911_ = v___x_1928_;
v_x_1912_ = v_r_1921_;
goto _start;
}
else
{
lean_object* v___x_1932_; 
lean_dec(v_r_1921_);
v___x_1932_ = l_Lean_Compiler_LCNF_getBinderName(v_k_1918_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_);
if (lean_obj_tag(v___x_1932_) == 0)
{
lean_object* v_a_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1941_; 
v_a_1933_ = lean_ctor_get(v___x_1932_, 0);
lean_inc(v_a_1933_);
lean_dec_ref(v___x_1932_);
v___x_1934_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Check_Impure_checkLeaks_spec__0___redArg___closed__1, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Check_Impure_checkLeaks_spec__0___redArg___closed__1_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Check_Impure_checkLeaks_spec__0___redArg___closed__1);
v___x_1935_ = l_Lean_MessageData_ofName(v_a_1933_);
v___x_1936_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1936_, 0, v___x_1934_);
lean_ctor_set(v___x_1936_, 1, v___x_1935_);
v___x_1937_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Check_Impure_checkLeaks_spec__0___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Check_Impure_checkLeaks_spec__0___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Check_Impure_checkLeaks_spec__0___redArg___closed__3);
v___x_1938_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1938_, 0, v___x_1936_);
lean_ctor_set(v___x_1938_, 1, v___x_1937_);
v___x_1939_ = l_Nat_reprFast(v_rc_1927_);
if (v_isShared_1926_ == 0)
{
lean_ctor_set_tag(v___x_1925_, 3);
lean_ctor_set(v___x_1925_, 0, v___x_1939_);
v___x_1941_ = v___x_1925_;
goto v_reusejp_1940_;
}
else
{
lean_object* v_reuseFailAlloc_1955_; 
v_reuseFailAlloc_1955_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1955_, 0, v___x_1939_);
v___x_1941_ = v_reuseFailAlloc_1955_;
goto v_reusejp_1940_;
}
v_reusejp_1940_:
{
lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v_a_1947_; lean_object* v___x_1949_; uint8_t v_isShared_1950_; uint8_t v_isSharedCheck_1954_; 
v___x_1942_ = l_Lean_MessageData_ofFormat(v___x_1941_);
v___x_1943_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1943_, 0, v___x_1938_);
lean_ctor_set(v___x_1943_, 1, v___x_1942_);
v___x_1944_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Check_Impure_checkLeaks_spec__0___redArg___closed__5, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Check_Impure_checkLeaks_spec__0___redArg___closed__5_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Check_Impure_checkLeaks_spec__0___redArg___closed__5);
v___x_1945_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1945_, 0, v___x_1943_);
lean_ctor_set(v___x_1945_, 1, v___x_1944_);
v___x_1946_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Impure_kill_spec__1___redArg(v___x_1945_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_);
v_a_1947_ = lean_ctor_get(v___x_1946_, 0);
v_isSharedCheck_1954_ = !lean_is_exclusive(v___x_1946_);
if (v_isSharedCheck_1954_ == 0)
{
v___x_1949_ = v___x_1946_;
v_isShared_1950_ = v_isSharedCheck_1954_;
goto v_resetjp_1948_;
}
else
{
lean_inc(v_a_1947_);
lean_dec(v___x_1946_);
v___x_1949_ = lean_box(0);
v_isShared_1950_ = v_isSharedCheck_1954_;
goto v_resetjp_1948_;
}
v_resetjp_1948_:
{
lean_object* v___x_1952_; 
if (v_isShared_1950_ == 0)
{
v___x_1952_ = v___x_1949_;
goto v_reusejp_1951_;
}
else
{
lean_object* v_reuseFailAlloc_1953_; 
v_reuseFailAlloc_1953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1953_, 0, v_a_1947_);
v___x_1952_ = v_reuseFailAlloc_1953_;
goto v_reusejp_1951_;
}
v_reusejp_1951_:
{
return v___x_1952_;
}
}
}
}
else
{
lean_object* v_a_1956_; lean_object* v___x_1958_; uint8_t v_isShared_1959_; uint8_t v_isSharedCheck_1963_; 
lean_dec(v_rc_1927_);
lean_del_object(v___x_1925_);
v_a_1956_ = lean_ctor_get(v___x_1932_, 0);
v_isSharedCheck_1963_ = !lean_is_exclusive(v___x_1932_);
if (v_isSharedCheck_1963_ == 0)
{
v___x_1958_ = v___x_1932_;
v_isShared_1959_ = v_isSharedCheck_1963_;
goto v_resetjp_1957_;
}
else
{
lean_inc(v_a_1956_);
lean_dec(v___x_1932_);
v___x_1958_ = lean_box(0);
v_isShared_1959_ = v_isSharedCheck_1963_;
goto v_resetjp_1957_;
}
v_resetjp_1957_:
{
lean_object* v___x_1961_; 
if (v_isShared_1959_ == 0)
{
v___x_1961_ = v___x_1958_;
goto v_reusejp_1960_;
}
else
{
lean_object* v_reuseFailAlloc_1962_; 
v_reuseFailAlloc_1962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1962_, 0, v_a_1956_);
v___x_1961_ = v_reuseFailAlloc_1962_;
goto v_reusejp_1960_;
}
v_reusejp_1960_:
{
return v___x_1961_;
}
}
}
}
}
}
else
{
lean_dec(v_r_1921_);
lean_dec(v_v_1919_);
lean_dec(v_k_1918_);
return v___x_1922_;
}
}
else
{
lean_object* v___x_1966_; lean_object* v___x_1967_; 
v___x_1966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1966_, 0, v_init_1911_);
v___x_1967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1967_, 0, v___x_1966_);
return v___x_1967_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Check_Impure_checkLeaks_spec__0___redArg___boxed(lean_object* v_init_1968_, lean_object* v_x_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_){
_start:
{
lean_object* v_res_1975_; 
v_res_1975_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Check_Impure_checkLeaks_spec__0___redArg(v_init_1968_, v_x_1969_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_);
lean_dec(v___y_1973_);
lean_dec_ref(v___y_1972_);
lean_dec(v___y_1971_);
lean_dec_ref(v___y_1970_);
return v_res_1975_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Impure_checkLeaks(lean_object* v_a_1976_, lean_object* v_a_1977_, lean_object* v_a_1978_, lean_object* v_a_1979_, lean_object* v_a_1980_){
_start:
{
lean_object* v___x_1982_; lean_object* v_rc_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; 
v___x_1982_ = lean_st_ref_get(v_a_1976_);
v_rc_1983_ = lean_ctor_get(v___x_1982_, 0);
lean_inc(v_rc_1983_);
lean_dec(v___x_1982_);
v___x_1984_ = lean_box(0);
v___x_1985_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Check_Impure_checkLeaks_spec__0___redArg(v___x_1984_, v_rc_1983_, v_a_1977_, v_a_1978_, v_a_1979_, v_a_1980_);
if (lean_obj_tag(v___x_1985_) == 0)
{
lean_object* v___x_1987_; uint8_t v_isShared_1988_; uint8_t v_isSharedCheck_1992_; 
v_isSharedCheck_1992_ = !lean_is_exclusive(v___x_1985_);
if (v_isSharedCheck_1992_ == 0)
{
lean_object* v_unused_1993_; 
v_unused_1993_ = lean_ctor_get(v___x_1985_, 0);
lean_dec(v_unused_1993_);
v___x_1987_ = v___x_1985_;
v_isShared_1988_ = v_isSharedCheck_1992_;
goto v_resetjp_1986_;
}
else
{
lean_dec(v___x_1985_);
v___x_1987_ = lean_box(0);
v_isShared_1988_ = v_isSharedCheck_1992_;
goto v_resetjp_1986_;
}
v_resetjp_1986_:
{
lean_object* v___x_1990_; 
if (v_isShared_1988_ == 0)
{
lean_ctor_set(v___x_1987_, 0, v___x_1984_);
v___x_1990_ = v___x_1987_;
goto v_reusejp_1989_;
}
else
{
lean_object* v_reuseFailAlloc_1991_; 
v_reuseFailAlloc_1991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1991_, 0, v___x_1984_);
v___x_1990_ = v_reuseFailAlloc_1991_;
goto v_reusejp_1989_;
}
v_reusejp_1989_:
{
return v___x_1990_;
}
}
}
else
{
lean_object* v_a_1994_; lean_object* v___x_1996_; uint8_t v_isShared_1997_; uint8_t v_isSharedCheck_2001_; 
v_a_1994_ = lean_ctor_get(v___x_1985_, 0);
v_isSharedCheck_2001_ = !lean_is_exclusive(v___x_1985_);
if (v_isSharedCheck_2001_ == 0)
{
v___x_1996_ = v___x_1985_;
v_isShared_1997_ = v_isSharedCheck_2001_;
goto v_resetjp_1995_;
}
else
{
lean_inc(v_a_1994_);
lean_dec(v___x_1985_);
v___x_1996_ = lean_box(0);
v_isShared_1997_ = v_isSharedCheck_2001_;
goto v_resetjp_1995_;
}
v_resetjp_1995_:
{
lean_object* v___x_1999_; 
if (v_isShared_1997_ == 0)
{
v___x_1999_ = v___x_1996_;
goto v_reusejp_1998_;
}
else
{
lean_object* v_reuseFailAlloc_2000_; 
v_reuseFailAlloc_2000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2000_, 0, v_a_1994_);
v___x_1999_ = v_reuseFailAlloc_2000_;
goto v_reusejp_1998_;
}
v_reusejp_1998_:
{
return v___x_1999_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Impure_checkLeaks___boxed(lean_object* v_a_2002_, lean_object* v_a_2003_, lean_object* v_a_2004_, lean_object* v_a_2005_, lean_object* v_a_2006_, lean_object* v_a_2007_){
_start:
{
lean_object* v_res_2008_; 
v_res_2008_ = l_Lean_Compiler_LCNF_Check_Impure_checkLeaks(v_a_2002_, v_a_2003_, v_a_2004_, v_a_2005_, v_a_2006_);
lean_dec(v_a_2006_);
lean_dec_ref(v_a_2005_);
lean_dec(v_a_2004_);
lean_dec_ref(v_a_2003_);
lean_dec(v_a_2002_);
return v_res_2008_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Check_Impure_checkLeaks_spec__0(lean_object* v_init_2009_, lean_object* v_x_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_){
_start:
{
lean_object* v___x_2017_; 
v___x_2017_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Check_Impure_checkLeaks_spec__0___redArg(v_init_2009_, v_x_2010_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_);
return v___x_2017_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Check_Impure_checkLeaks_spec__0___boxed(lean_object* v_init_2018_, lean_object* v_x_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_){
_start:
{
lean_object* v_res_2026_; 
v_res_2026_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Check_Impure_checkLeaks_spec__0(v_init_2018_, v_x_2019_, v___y_2020_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_);
lean_dec(v___y_2024_);
lean_dec_ref(v___y_2023_);
lean_dec(v___y_2022_);
lean_dec_ref(v___y_2021_);
lean_dec(v___y_2020_);
return v_res_2026_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Check_Impure_addOwned___redArg___closed__0(void){
_start:
{
lean_object* v___x_2027_; uint8_t v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; 
v___x_2027_ = ((lean_object*)(l_Lean_Compiler_LCNF_Check_Impure_deadInfo___closed__0));
v___x_2028_ = 0;
v___x_2029_ = lean_unsigned_to_nat(1u);
v___x_2030_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2030_, 0, v___x_2029_);
lean_ctor_set(v___x_2030_, 1, v___x_2027_);
lean_ctor_set(v___x_2030_, 2, v___x_2027_);
lean_ctor_set_uint8(v___x_2030_, sizeof(void*)*3, v___x_2028_);
return v___x_2030_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Impure_addOwned___redArg(lean_object* v_v_2031_, lean_object* v_a_2032_){
_start:
{
lean_object* v___x_2034_; lean_object* v_rc_2035_; lean_object* v_subst_2036_; lean_object* v___x_2038_; uint8_t v_isShared_2039_; uint8_t v_isSharedCheck_2048_; 
v___x_2034_ = lean_st_ref_take(v_a_2032_);
v_rc_2035_ = lean_ctor_get(v___x_2034_, 0);
v_subst_2036_ = lean_ctor_get(v___x_2034_, 1);
v_isSharedCheck_2048_ = !lean_is_exclusive(v___x_2034_);
if (v_isSharedCheck_2048_ == 0)
{
v___x_2038_ = v___x_2034_;
v_isShared_2039_ = v_isSharedCheck_2048_;
goto v_resetjp_2037_;
}
else
{
lean_inc(v_subst_2036_);
lean_inc(v_rc_2035_);
lean_dec(v___x_2034_);
v___x_2038_ = lean_box(0);
v_isShared_2039_ = v_isSharedCheck_2048_;
goto v_resetjp_2037_;
}
v_resetjp_2037_:
{
lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2043_; 
v___x_2040_ = lean_obj_once(&l_Lean_Compiler_LCNF_Check_Impure_addOwned___redArg___closed__0, &l_Lean_Compiler_LCNF_Check_Impure_addOwned___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_Check_Impure_addOwned___redArg___closed__0);
v___x_2041_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_v_2031_, v___x_2040_, v_rc_2035_);
if (v_isShared_2039_ == 0)
{
lean_ctor_set(v___x_2038_, 0, v___x_2041_);
v___x_2043_ = v___x_2038_;
goto v_reusejp_2042_;
}
else
{
lean_object* v_reuseFailAlloc_2047_; 
v_reuseFailAlloc_2047_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2047_, 0, v___x_2041_);
lean_ctor_set(v_reuseFailAlloc_2047_, 1, v_subst_2036_);
v___x_2043_ = v_reuseFailAlloc_2047_;
goto v_reusejp_2042_;
}
v_reusejp_2042_:
{
lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; 
v___x_2044_ = lean_st_ref_set(v_a_2032_, v___x_2043_);
v___x_2045_ = lean_box(0);
v___x_2046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2046_, 0, v___x_2045_);
return v___x_2046_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Impure_addOwned___redArg___boxed(lean_object* v_v_2049_, lean_object* v_a_2050_, lean_object* v_a_2051_){
_start:
{
lean_object* v_res_2052_; 
v_res_2052_ = l_Lean_Compiler_LCNF_Check_Impure_addOwned___redArg(v_v_2049_, v_a_2050_);
lean_dec(v_a_2050_);
return v_res_2052_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Impure_addOwned(lean_object* v_v_2053_, lean_object* v_a_2054_, lean_object* v_a_2055_, lean_object* v_a_2056_, lean_object* v_a_2057_, lean_object* v_a_2058_){
_start:
{
lean_object* v___x_2060_; 
v___x_2060_ = l_Lean_Compiler_LCNF_Check_Impure_addOwned___redArg(v_v_2053_, v_a_2054_);
return v___x_2060_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Impure_addOwned___boxed(lean_object* v_v_2061_, lean_object* v_a_2062_, lean_object* v_a_2063_, lean_object* v_a_2064_, lean_object* v_a_2065_, lean_object* v_a_2066_, lean_object* v_a_2067_){
_start:
{
lean_object* v_res_2068_; 
v_res_2068_ = l_Lean_Compiler_LCNF_Check_Impure_addOwned(v_v_2061_, v_a_2062_, v_a_2063_, v_a_2064_, v_a_2065_, v_a_2066_);
lean_dec(v_a_2066_);
lean_dec_ref(v_a_2065_);
lean_dec(v_a_2064_);
lean_dec_ref(v_a_2063_);
lean_dec(v_a_2062_);
return v_res_2068_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Lean_Compiler_LCNF_Check_Impure_addChild_spec__0(lean_object* v_child_2069_, lean_object* v_k_2070_, lean_object* v_t_2071_){
_start:
{
if (lean_obj_tag(v_t_2071_) == 0)
{
lean_object* v_size_2072_; lean_object* v_k_2073_; lean_object* v_v_2074_; lean_object* v_l_2075_; lean_object* v_r_2076_; lean_object* v___x_2078_; uint8_t v_isShared_2079_; uint8_t v_isSharedCheck_2104_; 
v_size_2072_ = lean_ctor_get(v_t_2071_, 0);
v_k_2073_ = lean_ctor_get(v_t_2071_, 1);
v_v_2074_ = lean_ctor_get(v_t_2071_, 2);
v_l_2075_ = lean_ctor_get(v_t_2071_, 3);
v_r_2076_ = lean_ctor_get(v_t_2071_, 4);
v_isSharedCheck_2104_ = !lean_is_exclusive(v_t_2071_);
if (v_isSharedCheck_2104_ == 0)
{
v___x_2078_ = v_t_2071_;
v_isShared_2079_ = v_isSharedCheck_2104_;
goto v_resetjp_2077_;
}
else
{
lean_inc(v_r_2076_);
lean_inc(v_l_2075_);
lean_inc(v_v_2074_);
lean_inc(v_k_2073_);
lean_inc(v_size_2072_);
lean_dec(v_t_2071_);
v___x_2078_ = lean_box(0);
v_isShared_2079_ = v_isSharedCheck_2104_;
goto v_resetjp_2077_;
}
v_resetjp_2077_:
{
uint8_t v___x_2080_; 
v___x_2080_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2070_, v_k_2073_);
switch(v___x_2080_)
{
case 0:
{
lean_object* v___x_2081_; lean_object* v___x_2083_; 
v___x_2081_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Lean_Compiler_LCNF_Check_Impure_addChild_spec__0(v_child_2069_, v_k_2070_, v_l_2075_);
if (v_isShared_2079_ == 0)
{
lean_ctor_set(v___x_2078_, 3, v___x_2081_);
v___x_2083_ = v___x_2078_;
goto v_reusejp_2082_;
}
else
{
lean_object* v_reuseFailAlloc_2084_; 
v_reuseFailAlloc_2084_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2084_, 0, v_size_2072_);
lean_ctor_set(v_reuseFailAlloc_2084_, 1, v_k_2073_);
lean_ctor_set(v_reuseFailAlloc_2084_, 2, v_v_2074_);
lean_ctor_set(v_reuseFailAlloc_2084_, 3, v___x_2081_);
lean_ctor_set(v_reuseFailAlloc_2084_, 4, v_r_2076_);
v___x_2083_ = v_reuseFailAlloc_2084_;
goto v_reusejp_2082_;
}
v_reusejp_2082_:
{
return v___x_2083_;
}
}
case 1:
{
lean_object* v_rc_2085_; uint8_t v_borrowed_2086_; lean_object* v_parents_2087_; lean_object* v_children_2088_; lean_object* v___x_2090_; uint8_t v_isShared_2091_; uint8_t v_isSharedCheck_2099_; 
lean_dec(v_k_2073_);
v_rc_2085_ = lean_ctor_get(v_v_2074_, 0);
v_borrowed_2086_ = lean_ctor_get_uint8(v_v_2074_, sizeof(void*)*3);
v_parents_2087_ = lean_ctor_get(v_v_2074_, 1);
v_children_2088_ = lean_ctor_get(v_v_2074_, 2);
v_isSharedCheck_2099_ = !lean_is_exclusive(v_v_2074_);
if (v_isSharedCheck_2099_ == 0)
{
v___x_2090_ = v_v_2074_;
v_isShared_2091_ = v_isSharedCheck_2099_;
goto v_resetjp_2089_;
}
else
{
lean_inc(v_children_2088_);
lean_inc(v_parents_2087_);
lean_inc(v_rc_2085_);
lean_dec(v_v_2074_);
v___x_2090_ = lean_box(0);
v_isShared_2091_ = v_isSharedCheck_2099_;
goto v_resetjp_2089_;
}
v_resetjp_2089_:
{
lean_object* v___x_2092_; lean_object* v___x_2094_; 
v___x_2092_ = lean_array_push(v_children_2088_, v_child_2069_);
if (v_isShared_2091_ == 0)
{
lean_ctor_set(v___x_2090_, 2, v___x_2092_);
v___x_2094_ = v___x_2090_;
goto v_reusejp_2093_;
}
else
{
lean_object* v_reuseFailAlloc_2098_; 
v_reuseFailAlloc_2098_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2098_, 0, v_rc_2085_);
lean_ctor_set(v_reuseFailAlloc_2098_, 1, v_parents_2087_);
lean_ctor_set(v_reuseFailAlloc_2098_, 2, v___x_2092_);
lean_ctor_set_uint8(v_reuseFailAlloc_2098_, sizeof(void*)*3, v_borrowed_2086_);
v___x_2094_ = v_reuseFailAlloc_2098_;
goto v_reusejp_2093_;
}
v_reusejp_2093_:
{
lean_object* v___x_2096_; 
if (v_isShared_2079_ == 0)
{
lean_ctor_set(v___x_2078_, 2, v___x_2094_);
lean_ctor_set(v___x_2078_, 1, v_k_2070_);
v___x_2096_ = v___x_2078_;
goto v_reusejp_2095_;
}
else
{
lean_object* v_reuseFailAlloc_2097_; 
v_reuseFailAlloc_2097_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2097_, 0, v_size_2072_);
lean_ctor_set(v_reuseFailAlloc_2097_, 1, v_k_2070_);
lean_ctor_set(v_reuseFailAlloc_2097_, 2, v___x_2094_);
lean_ctor_set(v_reuseFailAlloc_2097_, 3, v_l_2075_);
lean_ctor_set(v_reuseFailAlloc_2097_, 4, v_r_2076_);
v___x_2096_ = v_reuseFailAlloc_2097_;
goto v_reusejp_2095_;
}
v_reusejp_2095_:
{
return v___x_2096_;
}
}
}
}
default: 
{
lean_object* v___x_2100_; lean_object* v___x_2102_; 
v___x_2100_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Lean_Compiler_LCNF_Check_Impure_addChild_spec__0(v_child_2069_, v_k_2070_, v_r_2076_);
if (v_isShared_2079_ == 0)
{
lean_ctor_set(v___x_2078_, 4, v___x_2100_);
v___x_2102_ = v___x_2078_;
goto v_reusejp_2101_;
}
else
{
lean_object* v_reuseFailAlloc_2103_; 
v_reuseFailAlloc_2103_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2103_, 0, v_size_2072_);
lean_ctor_set(v_reuseFailAlloc_2103_, 1, v_k_2073_);
lean_ctor_set(v_reuseFailAlloc_2103_, 2, v_v_2074_);
lean_ctor_set(v_reuseFailAlloc_2103_, 3, v_l_2075_);
lean_ctor_set(v_reuseFailAlloc_2103_, 4, v___x_2100_);
v___x_2102_ = v_reuseFailAlloc_2103_;
goto v_reusejp_2101_;
}
v_reusejp_2101_:
{
return v___x_2102_;
}
}
}
}
}
else
{
lean_dec(v_k_2070_);
lean_dec(v_child_2069_);
return v_t_2071_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Impure_addChild___redArg(lean_object* v_parent_2105_, lean_object* v_child_2106_, lean_object* v_a_2107_){
_start:
{
lean_object* v___x_2109_; lean_object* v_rc_2110_; lean_object* v_subst_2111_; lean_object* v___x_2113_; uint8_t v_isShared_2114_; uint8_t v_isSharedCheck_2122_; 
v___x_2109_ = lean_st_ref_take(v_a_2107_);
v_rc_2110_ = lean_ctor_get(v___x_2109_, 0);
v_subst_2111_ = lean_ctor_get(v___x_2109_, 1);
v_isSharedCheck_2122_ = !lean_is_exclusive(v___x_2109_);
if (v_isSharedCheck_2122_ == 0)
{
v___x_2113_ = v___x_2109_;
v_isShared_2114_ = v_isSharedCheck_2122_;
goto v_resetjp_2112_;
}
else
{
lean_inc(v_subst_2111_);
lean_inc(v_rc_2110_);
lean_dec(v___x_2109_);
v___x_2113_ = lean_box(0);
v_isShared_2114_ = v_isSharedCheck_2122_;
goto v_resetjp_2112_;
}
v_resetjp_2112_:
{
lean_object* v___x_2115_; lean_object* v___x_2117_; 
v___x_2115_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Lean_Compiler_LCNF_Check_Impure_addChild_spec__0(v_child_2106_, v_parent_2105_, v_rc_2110_);
if (v_isShared_2114_ == 0)
{
lean_ctor_set(v___x_2113_, 0, v___x_2115_);
v___x_2117_ = v___x_2113_;
goto v_reusejp_2116_;
}
else
{
lean_object* v_reuseFailAlloc_2121_; 
v_reuseFailAlloc_2121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2121_, 0, v___x_2115_);
lean_ctor_set(v_reuseFailAlloc_2121_, 1, v_subst_2111_);
v___x_2117_ = v_reuseFailAlloc_2121_;
goto v_reusejp_2116_;
}
v_reusejp_2116_:
{
lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; 
v___x_2118_ = lean_st_ref_set(v_a_2107_, v___x_2117_);
v___x_2119_ = lean_box(0);
v___x_2120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2120_, 0, v___x_2119_);
return v___x_2120_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Impure_addChild___redArg___boxed(lean_object* v_parent_2123_, lean_object* v_child_2124_, lean_object* v_a_2125_, lean_object* v_a_2126_){
_start:
{
lean_object* v_res_2127_; 
v_res_2127_ = l_Lean_Compiler_LCNF_Check_Impure_addChild___redArg(v_parent_2123_, v_child_2124_, v_a_2125_);
lean_dec(v_a_2125_);
return v_res_2127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Impure_addChild(lean_object* v_parent_2128_, lean_object* v_child_2129_, lean_object* v_a_2130_, lean_object* v_a_2131_, lean_object* v_a_2132_, lean_object* v_a_2133_, lean_object* v_a_2134_){
_start:
{
lean_object* v___x_2136_; 
v___x_2136_ = l_Lean_Compiler_LCNF_Check_Impure_addChild___redArg(v_parent_2128_, v_child_2129_, v_a_2130_);
return v___x_2136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Impure_addChild___boxed(lean_object* v_parent_2137_, lean_object* v_child_2138_, lean_object* v_a_2139_, lean_object* v_a_2140_, lean_object* v_a_2141_, lean_object* v_a_2142_, lean_object* v_a_2143_, lean_object* v_a_2144_){
_start:
{
lean_object* v_res_2145_; 
v_res_2145_ = l_Lean_Compiler_LCNF_Check_Impure_addChild(v_parent_2137_, v_child_2138_, v_a_2139_, v_a_2140_, v_a_2141_, v_a_2142_, v_a_2143_);
lean_dec(v_a_2143_);
lean_dec_ref(v_a_2142_);
lean_dec(v_a_2141_);
lean_dec_ref(v_a_2140_);
lean_dec(v_a_2139_);
return v_res_2145_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_Check_Impure_addBorrowed_spec__0_spec__0(lean_object* v_as_2146_, size_t v_i_2147_, size_t v_stop_2148_, lean_object* v_b_2149_){
_start:
{
lean_object* v___y_2151_; uint8_t v___x_2155_; 
v___x_2155_ = lean_usize_dec_eq(v_i_2147_, v_stop_2148_);
if (v___x_2155_ == 0)
{
lean_object* v___x_2156_; 
v___x_2156_ = lean_array_uget_borrowed(v_as_2146_, v_i_2147_);
if (lean_obj_tag(v___x_2156_) == 0)
{
v___y_2151_ = v_b_2149_;
goto v___jp_2150_;
}
else
{
lean_object* v_fvarId_2157_; lean_object* v___x_2158_; 
v_fvarId_2157_ = lean_ctor_get(v___x_2156_, 0);
lean_inc(v_fvarId_2157_);
v___x_2158_ = lean_array_push(v_b_2149_, v_fvarId_2157_);
v___y_2151_ = v___x_2158_;
goto v___jp_2150_;
}
}
else
{
return v_b_2149_;
}
v___jp_2150_:
{
size_t v___x_2152_; size_t v___x_2153_; 
v___x_2152_ = ((size_t)1ULL);
v___x_2153_ = lean_usize_add(v_i_2147_, v___x_2152_);
v_i_2147_ = v___x_2153_;
v_b_2149_ = v___y_2151_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_Check_Impure_addBorrowed_spec__0_spec__0___boxed(lean_object* v_as_2159_, lean_object* v_i_2160_, lean_object* v_stop_2161_, lean_object* v_b_2162_){
_start:
{
size_t v_i_boxed_2163_; size_t v_stop_boxed_2164_; lean_object* v_res_2165_; 
v_i_boxed_2163_ = lean_unbox_usize(v_i_2160_);
lean_dec(v_i_2160_);
v_stop_boxed_2164_ = lean_unbox_usize(v_stop_2161_);
lean_dec(v_stop_2161_);
v_res_2165_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_Check_Impure_addBorrowed_spec__0_spec__0(v_as_2159_, v_i_boxed_2163_, v_stop_boxed_2164_, v_b_2162_);
lean_dec_ref(v_as_2159_);
return v_res_2165_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Compiler_LCNF_Check_Impure_addBorrowed_spec__0(lean_object* v_as_2166_, lean_object* v_start_2167_, lean_object* v_stop_2168_){
_start:
{
lean_object* v___x_2169_; uint8_t v___x_2170_; 
v___x_2169_ = ((lean_object*)(l_Lean_Compiler_LCNF_Check_Impure_deadInfo___closed__0));
v___x_2170_ = lean_nat_dec_lt(v_start_2167_, v_stop_2168_);
if (v___x_2170_ == 0)
{
return v___x_2169_;
}
else
{
lean_object* v___x_2171_; uint8_t v___x_2172_; 
v___x_2171_ = lean_array_get_size(v_as_2166_);
v___x_2172_ = lean_nat_dec_le(v_stop_2168_, v___x_2171_);
if (v___x_2172_ == 0)
{
uint8_t v___x_2173_; 
v___x_2173_ = lean_nat_dec_lt(v_start_2167_, v___x_2171_);
if (v___x_2173_ == 0)
{
return v___x_2169_;
}
else
{
size_t v___x_2174_; size_t v___x_2175_; lean_object* v___x_2176_; 
v___x_2174_ = lean_usize_of_nat(v_start_2167_);
v___x_2175_ = lean_usize_of_nat(v___x_2171_);
v___x_2176_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_Check_Impure_addBorrowed_spec__0_spec__0(v_as_2166_, v___x_2174_, v___x_2175_, v___x_2169_);
return v___x_2176_;
}
}
else
{
size_t v___x_2177_; size_t v___x_2178_; lean_object* v___x_2179_; 
v___x_2177_ = lean_usize_of_nat(v_start_2167_);
v___x_2178_ = lean_usize_of_nat(v_stop_2168_);
v___x_2179_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_Check_Impure_addBorrowed_spec__0_spec__0(v_as_2166_, v___x_2177_, v___x_2178_, v___x_2169_);
return v___x_2179_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Compiler_LCNF_Check_Impure_addBorrowed_spec__0___boxed(lean_object* v_as_2180_, lean_object* v_start_2181_, lean_object* v_stop_2182_){
_start:
{
lean_object* v_res_2183_; 
v_res_2183_ = l_Array_filterMapM___at___00Lean_Compiler_LCNF_Check_Impure_addBorrowed_spec__0(v_as_2180_, v_start_2181_, v_stop_2182_);
lean_dec(v_stop_2182_);
lean_dec(v_start_2181_);
lean_dec_ref(v_as_2180_);
return v_res_2183_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Impure_addBorrowed_spec__1___redArg(lean_object* v_v_2184_, lean_object* v_as_2185_, size_t v_sz_2186_, size_t v_i_2187_, lean_object* v_b_2188_, lean_object* v___y_2189_){
_start:
{
uint8_t v___x_2191_; 
v___x_2191_ = lean_usize_dec_lt(v_i_2187_, v_sz_2186_);
if (v___x_2191_ == 0)
{
lean_object* v___x_2192_; 
lean_dec(v_v_2184_);
v___x_2192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2192_, 0, v_b_2188_);
return v___x_2192_;
}
else
{
lean_object* v_a_2193_; lean_object* v___x_2194_; 
v_a_2193_ = lean_array_uget_borrowed(v_as_2185_, v_i_2187_);
lean_inc(v_v_2184_);
lean_inc(v_a_2193_);
v___x_2194_ = l_Lean_Compiler_LCNF_Check_Impure_addChild___redArg(v_a_2193_, v_v_2184_, v___y_2189_);
if (lean_obj_tag(v___x_2194_) == 0)
{
lean_object* v___x_2195_; size_t v___x_2196_; size_t v___x_2197_; 
lean_dec_ref(v___x_2194_);
v___x_2195_ = lean_box(0);
v___x_2196_ = ((size_t)1ULL);
v___x_2197_ = lean_usize_add(v_i_2187_, v___x_2196_);
v_i_2187_ = v___x_2197_;
v_b_2188_ = v___x_2195_;
goto _start;
}
else
{
lean_dec(v_v_2184_);
return v___x_2194_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Impure_addBorrowed_spec__1___redArg___boxed(lean_object* v_v_2199_, lean_object* v_as_2200_, lean_object* v_sz_2201_, lean_object* v_i_2202_, lean_object* v_b_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_){
_start:
{
size_t v_sz_boxed_2206_; size_t v_i_boxed_2207_; lean_object* v_res_2208_; 
v_sz_boxed_2206_ = lean_unbox_usize(v_sz_2201_);
lean_dec(v_sz_2201_);
v_i_boxed_2207_ = lean_unbox_usize(v_i_2202_);
lean_dec(v_i_2202_);
v_res_2208_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Impure_addBorrowed_spec__1___redArg(v_v_2199_, v_as_2200_, v_sz_boxed_2206_, v_i_boxed_2207_, v_b_2203_, v___y_2204_);
lean_dec(v___y_2204_);
lean_dec_ref(v_as_2200_);
return v_res_2208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Impure_addBorrowed(lean_object* v_v_2209_, lean_object* v_parents_2210_, lean_object* v_a_2211_, lean_object* v_a_2212_, lean_object* v_a_2213_, lean_object* v_a_2214_, lean_object* v_a_2215_){
_start:
{
lean_object* v___x_2217_; lean_object* v_rc_2218_; lean_object* v_subst_2219_; lean_object* v___x_2221_; uint8_t v_isShared_2222_; uint8_t v_isSharedCheck_2246_; 
v___x_2217_ = lean_st_ref_take(v_a_2211_);
v_rc_2218_ = lean_ctor_get(v___x_2217_, 0);
v_subst_2219_ = lean_ctor_get(v___x_2217_, 1);
v_isSharedCheck_2246_ = !lean_is_exclusive(v___x_2217_);
if (v_isSharedCheck_2246_ == 0)
{
v___x_2221_ = v___x_2217_;
v_isShared_2222_ = v_isSharedCheck_2246_;
goto v_resetjp_2220_;
}
else
{
lean_inc(v_subst_2219_);
lean_inc(v_rc_2218_);
lean_dec(v___x_2217_);
v___x_2221_ = lean_box(0);
v_isShared_2222_ = v_isSharedCheck_2246_;
goto v_resetjp_2220_;
}
v_resetjp_2220_:
{
lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v_parents_2225_; uint8_t v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2231_; 
v___x_2223_ = lean_array_get_size(v_parents_2210_);
v___x_2224_ = lean_unsigned_to_nat(0u);
v_parents_2225_ = l_Array_filterMapM___at___00Lean_Compiler_LCNF_Check_Impure_addBorrowed_spec__0(v_parents_2210_, v___x_2224_, v___x_2223_);
v___x_2226_ = 1;
v___x_2227_ = ((lean_object*)(l_Lean_Compiler_LCNF_Check_Impure_deadInfo___closed__0));
lean_inc_ref(v_parents_2225_);
v___x_2228_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2228_, 0, v___x_2224_);
lean_ctor_set(v___x_2228_, 1, v_parents_2225_);
lean_ctor_set(v___x_2228_, 2, v___x_2227_);
lean_ctor_set_uint8(v___x_2228_, sizeof(void*)*3, v___x_2226_);
lean_inc(v_v_2209_);
v___x_2229_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_v_2209_, v___x_2228_, v_rc_2218_);
if (v_isShared_2222_ == 0)
{
lean_ctor_set(v___x_2221_, 0, v___x_2229_);
v___x_2231_ = v___x_2221_;
goto v_reusejp_2230_;
}
else
{
lean_object* v_reuseFailAlloc_2245_; 
v_reuseFailAlloc_2245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2245_, 0, v___x_2229_);
lean_ctor_set(v_reuseFailAlloc_2245_, 1, v_subst_2219_);
v___x_2231_ = v_reuseFailAlloc_2245_;
goto v_reusejp_2230_;
}
v_reusejp_2230_:
{
lean_object* v___x_2232_; lean_object* v___x_2233_; size_t v_sz_2234_; size_t v___x_2235_; lean_object* v___x_2236_; 
v___x_2232_ = lean_st_ref_set(v_a_2211_, v___x_2231_);
v___x_2233_ = lean_box(0);
v_sz_2234_ = lean_array_size(v_parents_2225_);
v___x_2235_ = ((size_t)0ULL);
v___x_2236_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Impure_addBorrowed_spec__1___redArg(v_v_2209_, v_parents_2225_, v_sz_2234_, v___x_2235_, v___x_2233_, v_a_2211_);
lean_dec_ref(v_parents_2225_);
if (lean_obj_tag(v___x_2236_) == 0)
{
lean_object* v___x_2238_; uint8_t v_isShared_2239_; uint8_t v_isSharedCheck_2243_; 
v_isSharedCheck_2243_ = !lean_is_exclusive(v___x_2236_);
if (v_isSharedCheck_2243_ == 0)
{
lean_object* v_unused_2244_; 
v_unused_2244_ = lean_ctor_get(v___x_2236_, 0);
lean_dec(v_unused_2244_);
v___x_2238_ = v___x_2236_;
v_isShared_2239_ = v_isSharedCheck_2243_;
goto v_resetjp_2237_;
}
else
{
lean_dec(v___x_2236_);
v___x_2238_ = lean_box(0);
v_isShared_2239_ = v_isSharedCheck_2243_;
goto v_resetjp_2237_;
}
v_resetjp_2237_:
{
lean_object* v___x_2241_; 
if (v_isShared_2239_ == 0)
{
lean_ctor_set(v___x_2238_, 0, v___x_2233_);
v___x_2241_ = v___x_2238_;
goto v_reusejp_2240_;
}
else
{
lean_object* v_reuseFailAlloc_2242_; 
v_reuseFailAlloc_2242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2242_, 0, v___x_2233_);
v___x_2241_ = v_reuseFailAlloc_2242_;
goto v_reusejp_2240_;
}
v_reusejp_2240_:
{
return v___x_2241_;
}
}
}
else
{
return v___x_2236_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Impure_addBorrowed___boxed(lean_object* v_v_2247_, lean_object* v_parents_2248_, lean_object* v_a_2249_, lean_object* v_a_2250_, lean_object* v_a_2251_, lean_object* v_a_2252_, lean_object* v_a_2253_, lean_object* v_a_2254_){
_start:
{
lean_object* v_res_2255_; 
v_res_2255_ = l_Lean_Compiler_LCNF_Check_Impure_addBorrowed(v_v_2247_, v_parents_2248_, v_a_2249_, v_a_2250_, v_a_2251_, v_a_2252_, v_a_2253_);
lean_dec(v_a_2253_);
lean_dec_ref(v_a_2252_);
lean_dec(v_a_2251_);
lean_dec_ref(v_a_2250_);
lean_dec(v_a_2249_);
lean_dec_ref(v_parents_2248_);
return v_res_2255_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Impure_addBorrowed_spec__1(lean_object* v_v_2256_, lean_object* v_as_2257_, size_t v_sz_2258_, size_t v_i_2259_, lean_object* v_b_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_){
_start:
{
lean_object* v___x_2267_; 
v___x_2267_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Impure_addBorrowed_spec__1___redArg(v_v_2256_, v_as_2257_, v_sz_2258_, v_i_2259_, v_b_2260_, v___y_2261_);
return v___x_2267_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Impure_addBorrowed_spec__1___boxed(lean_object* v_v_2268_, lean_object* v_as_2269_, lean_object* v_sz_2270_, lean_object* v_i_2271_, lean_object* v_b_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_){
_start:
{
size_t v_sz_boxed_2279_; size_t v_i_boxed_2280_; lean_object* v_res_2281_; 
v_sz_boxed_2279_ = lean_unbox_usize(v_sz_2270_);
lean_dec(v_sz_2270_);
v_i_boxed_2280_ = lean_unbox_usize(v_i_2271_);
lean_dec(v_i_2271_);
v_res_2281_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Impure_addBorrowed_spec__1(v_v_2268_, v_as_2269_, v_sz_boxed_2279_, v_i_boxed_2280_, v_b_2272_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_);
lean_dec(v___y_2277_);
lean_dec_ref(v___y_2276_);
lean_dec(v___y_2275_);
lean_dec_ref(v___y_2274_);
lean_dec(v___y_2273_);
lean_dec_ref(v_as_2269_);
return v_res_2281_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Impure_checkLetDecl_spec__1(lean_object* v_as_2282_, size_t v_sz_2283_, size_t v_i_2284_, lean_object* v_b_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_){
_start:
{
lean_object* v_a_2293_; uint8_t v___x_2297_; 
v___x_2297_ = lean_usize_dec_lt(v_i_2284_, v_sz_2283_);
if (v___x_2297_ == 0)
{
lean_object* v___x_2298_; 
v___x_2298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2298_, 0, v_b_2285_);
return v___x_2298_;
}
else
{
lean_object* v_array_2299_; lean_object* v_start_2300_; lean_object* v_stop_2301_; uint8_t v___x_2302_; 
v_array_2299_ = lean_ctor_get(v_b_2285_, 0);
v_start_2300_ = lean_ctor_get(v_b_2285_, 1);
v_stop_2301_ = lean_ctor_get(v_b_2285_, 2);
v___x_2302_ = lean_nat_dec_lt(v_start_2300_, v_stop_2301_);
if (v___x_2302_ == 0)
{
lean_object* v___x_2303_; 
v___x_2303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2303_, 0, v_b_2285_);
return v___x_2303_;
}
else
{
lean_object* v___x_2305_; uint8_t v_isShared_2306_; uint8_t v_isSharedCheck_2324_; 
lean_inc(v_stop_2301_);
lean_inc(v_start_2300_);
lean_inc_ref(v_array_2299_);
v_isSharedCheck_2324_ = !lean_is_exclusive(v_b_2285_);
if (v_isSharedCheck_2324_ == 0)
{
lean_object* v_unused_2325_; lean_object* v_unused_2326_; lean_object* v_unused_2327_; 
v_unused_2325_ = lean_ctor_get(v_b_2285_, 2);
lean_dec(v_unused_2325_);
v_unused_2326_ = lean_ctor_get(v_b_2285_, 1);
lean_dec(v_unused_2326_);
v_unused_2327_ = lean_ctor_get(v_b_2285_, 0);
lean_dec(v_unused_2327_);
v___x_2305_ = v_b_2285_;
v_isShared_2306_ = v_isSharedCheck_2324_;
goto v_resetjp_2304_;
}
else
{
lean_dec(v_b_2285_);
v___x_2305_ = lean_box(0);
v_isShared_2306_ = v_isSharedCheck_2324_;
goto v_resetjp_2304_;
}
v_resetjp_2304_:
{
lean_object* v_a_2307_; uint8_t v_borrow_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2313_; 
v_a_2307_ = lean_array_uget_borrowed(v_as_2282_, v_i_2284_);
v_borrow_2308_ = lean_ctor_get_uint8(v_a_2307_, sizeof(void*)*3);
v___x_2309_ = lean_array_fget(v_array_2299_, v_start_2300_);
v___x_2310_ = lean_unsigned_to_nat(1u);
v___x_2311_ = lean_nat_add(v_start_2300_, v___x_2310_);
lean_dec(v_start_2300_);
if (v_isShared_2306_ == 0)
{
lean_ctor_set(v___x_2305_, 1, v___x_2311_);
v___x_2313_ = v___x_2305_;
goto v_reusejp_2312_;
}
else
{
lean_object* v_reuseFailAlloc_2323_; 
v_reuseFailAlloc_2323_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2323_, 0, v_array_2299_);
lean_ctor_set(v_reuseFailAlloc_2323_, 1, v___x_2311_);
lean_ctor_set(v_reuseFailAlloc_2323_, 2, v_stop_2301_);
v___x_2313_ = v_reuseFailAlloc_2323_;
goto v_reusejp_2312_;
}
v_reusejp_2312_:
{
if (v_borrow_2308_ == 0)
{
lean_object* v___x_2314_; 
v___x_2314_ = l_Lean_Compiler_LCNF_Check_Impure_consumeArg(v___x_2309_, v___y_2286_, v___y_2287_, v___y_2288_, v___y_2289_, v___y_2290_);
if (lean_obj_tag(v___x_2314_) == 0)
{
lean_dec_ref(v___x_2314_);
v_a_2293_ = v___x_2313_;
goto v___jp_2292_;
}
else
{
lean_object* v_a_2315_; lean_object* v___x_2317_; uint8_t v_isShared_2318_; uint8_t v_isSharedCheck_2322_; 
lean_dec_ref(v___x_2313_);
v_a_2315_ = lean_ctor_get(v___x_2314_, 0);
v_isSharedCheck_2322_ = !lean_is_exclusive(v___x_2314_);
if (v_isSharedCheck_2322_ == 0)
{
v___x_2317_ = v___x_2314_;
v_isShared_2318_ = v_isSharedCheck_2322_;
goto v_resetjp_2316_;
}
else
{
lean_inc(v_a_2315_);
lean_dec(v___x_2314_);
v___x_2317_ = lean_box(0);
v_isShared_2318_ = v_isSharedCheck_2322_;
goto v_resetjp_2316_;
}
v_resetjp_2316_:
{
lean_object* v___x_2320_; 
if (v_isShared_2318_ == 0)
{
v___x_2320_ = v___x_2317_;
goto v_reusejp_2319_;
}
else
{
lean_object* v_reuseFailAlloc_2321_; 
v_reuseFailAlloc_2321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2321_, 0, v_a_2315_);
v___x_2320_ = v_reuseFailAlloc_2321_;
goto v_reusejp_2319_;
}
v_reusejp_2319_:
{
return v___x_2320_;
}
}
}
}
else
{
lean_dec(v___x_2309_);
v_a_2293_ = v___x_2313_;
goto v___jp_2292_;
}
}
}
}
}
v___jp_2292_:
{
size_t v___x_2294_; size_t v___x_2295_; 
v___x_2294_ = ((size_t)1ULL);
v___x_2295_ = lean_usize_add(v_i_2284_, v___x_2294_);
v_i_2284_ = v___x_2295_;
v_b_2285_ = v_a_2293_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Impure_checkLetDecl_spec__1___boxed(lean_object* v_as_2328_, lean_object* v_sz_2329_, lean_object* v_i_2330_, lean_object* v_b_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_){
_start:
{
size_t v_sz_boxed_2338_; size_t v_i_boxed_2339_; lean_object* v_res_2340_; 
v_sz_boxed_2338_ = lean_unbox_usize(v_sz_2329_);
lean_dec(v_sz_2329_);
v_i_boxed_2339_ = lean_unbox_usize(v_i_2330_);
lean_dec(v_i_2330_);
v_res_2340_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Impure_checkLetDecl_spec__1(v_as_2328_, v_sz_boxed_2338_, v_i_boxed_2339_, v_b_2331_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_, v___y_2336_);
lean_dec(v___y_2336_);
lean_dec_ref(v___y_2335_);
lean_dec(v___y_2334_);
lean_dec_ref(v___y_2333_);
lean_dec(v___y_2332_);
lean_dec_ref(v_as_2328_);
return v_res_2340_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Impure_checkLetDecl_spec__0(lean_object* v_as_2341_, size_t v_i_2342_, size_t v_stop_2343_, lean_object* v_b_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_){
_start:
{
uint8_t v___x_2351_; 
v___x_2351_ = lean_usize_dec_eq(v_i_2342_, v_stop_2343_);
if (v___x_2351_ == 0)
{
lean_object* v___x_2352_; lean_object* v___x_2353_; 
v___x_2352_ = lean_array_uget_borrowed(v_as_2341_, v_i_2342_);
lean_inc(v___x_2352_);
v___x_2353_ = l_Lean_Compiler_LCNF_Check_Impure_consumeArg(v___x_2352_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_);
if (lean_obj_tag(v___x_2353_) == 0)
{
lean_object* v_a_2354_; size_t v___x_2355_; size_t v___x_2356_; 
v_a_2354_ = lean_ctor_get(v___x_2353_, 0);
lean_inc(v_a_2354_);
lean_dec_ref(v___x_2353_);
v___x_2355_ = ((size_t)1ULL);
v___x_2356_ = lean_usize_add(v_i_2342_, v___x_2355_);
v_i_2342_ = v___x_2356_;
v_b_2344_ = v_a_2354_;
goto _start;
}
else
{
return v___x_2353_;
}
}
else
{
lean_object* v___x_2358_; 
v___x_2358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2358_, 0, v_b_2344_);
return v___x_2358_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Impure_checkLetDecl_spec__0___boxed(lean_object* v_as_2359_, lean_object* v_i_2360_, lean_object* v_stop_2361_, lean_object* v_b_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_){
_start:
{
size_t v_i_boxed_2369_; size_t v_stop_boxed_2370_; lean_object* v_res_2371_; 
v_i_boxed_2369_ = lean_unbox_usize(v_i_2360_);
lean_dec(v_i_2360_);
v_stop_boxed_2370_ = lean_unbox_usize(v_stop_2361_);
lean_dec(v_stop_2361_);
v_res_2371_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Impure_checkLetDecl_spec__0(v_as_2359_, v_i_boxed_2369_, v_stop_boxed_2370_, v_b_2362_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_);
lean_dec(v___y_2367_);
lean_dec_ref(v___y_2366_);
lean_dec(v___y_2365_);
lean_dec_ref(v___y_2364_);
lean_dec(v___y_2363_);
lean_dec_ref(v_as_2359_);
return v_res_2371_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Impure_checkLetDecl_spec__2(lean_object* v_as_2372_, size_t v_sz_2373_, size_t v_i_2374_, lean_object* v_b_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_){
_start:
{
lean_object* v_a_2383_; uint8_t v___x_2387_; 
v___x_2387_ = lean_usize_dec_lt(v_i_2374_, v_sz_2373_);
if (v___x_2387_ == 0)
{
lean_object* v___x_2388_; 
v___x_2388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2388_, 0, v_b_2375_);
return v___x_2388_;
}
else
{
lean_object* v_array_2389_; lean_object* v_start_2390_; lean_object* v_stop_2391_; uint8_t v___x_2392_; 
v_array_2389_ = lean_ctor_get(v_b_2375_, 0);
v_start_2390_ = lean_ctor_get(v_b_2375_, 1);
v_stop_2391_ = lean_ctor_get(v_b_2375_, 2);
v___x_2392_ = lean_nat_dec_lt(v_start_2390_, v_stop_2391_);
if (v___x_2392_ == 0)
{
lean_object* v___x_2393_; 
v___x_2393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2393_, 0, v_b_2375_);
return v___x_2393_;
}
else
{
lean_object* v___x_2395_; uint8_t v_isShared_2396_; uint8_t v_isSharedCheck_2414_; 
lean_inc(v_stop_2391_);
lean_inc(v_start_2390_);
lean_inc_ref(v_array_2389_);
v_isSharedCheck_2414_ = !lean_is_exclusive(v_b_2375_);
if (v_isSharedCheck_2414_ == 0)
{
lean_object* v_unused_2415_; lean_object* v_unused_2416_; lean_object* v_unused_2417_; 
v_unused_2415_ = lean_ctor_get(v_b_2375_, 2);
lean_dec(v_unused_2415_);
v_unused_2416_ = lean_ctor_get(v_b_2375_, 1);
lean_dec(v_unused_2416_);
v_unused_2417_ = lean_ctor_get(v_b_2375_, 0);
lean_dec(v_unused_2417_);
v___x_2395_ = v_b_2375_;
v_isShared_2396_ = v_isSharedCheck_2414_;
goto v_resetjp_2394_;
}
else
{
lean_dec(v_b_2375_);
v___x_2395_ = lean_box(0);
v_isShared_2396_ = v_isSharedCheck_2414_;
goto v_resetjp_2394_;
}
v_resetjp_2394_:
{
lean_object* v_a_2397_; uint8_t v_borrow_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2403_; 
v_a_2397_ = lean_array_uget_borrowed(v_as_2372_, v_i_2374_);
v_borrow_2398_ = lean_ctor_get_uint8(v_a_2397_, sizeof(void*)*3);
v___x_2399_ = lean_array_fget(v_array_2389_, v_start_2390_);
v___x_2400_ = lean_unsigned_to_nat(1u);
v___x_2401_ = lean_nat_add(v_start_2390_, v___x_2400_);
lean_dec(v_start_2390_);
if (v_isShared_2396_ == 0)
{
lean_ctor_set(v___x_2395_, 1, v___x_2401_);
v___x_2403_ = v___x_2395_;
goto v_reusejp_2402_;
}
else
{
lean_object* v_reuseFailAlloc_2413_; 
v_reuseFailAlloc_2413_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2413_, 0, v_array_2389_);
lean_ctor_set(v_reuseFailAlloc_2413_, 1, v___x_2401_);
lean_ctor_set(v_reuseFailAlloc_2413_, 2, v_stop_2391_);
v___x_2403_ = v_reuseFailAlloc_2413_;
goto v_reusejp_2402_;
}
v_reusejp_2402_:
{
if (v_borrow_2398_ == 0)
{
lean_dec(v___x_2399_);
v_a_2383_ = v___x_2403_;
goto v___jp_2382_;
}
else
{
lean_object* v___x_2404_; 
v___x_2404_ = l_Lean_Compiler_LCNF_Check_Impure_useArg(v___x_2399_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_);
if (lean_obj_tag(v___x_2404_) == 0)
{
lean_dec_ref(v___x_2404_);
v_a_2383_ = v___x_2403_;
goto v___jp_2382_;
}
else
{
lean_object* v_a_2405_; lean_object* v___x_2407_; uint8_t v_isShared_2408_; uint8_t v_isSharedCheck_2412_; 
lean_dec_ref(v___x_2403_);
v_a_2405_ = lean_ctor_get(v___x_2404_, 0);
v_isSharedCheck_2412_ = !lean_is_exclusive(v___x_2404_);
if (v_isSharedCheck_2412_ == 0)
{
v___x_2407_ = v___x_2404_;
v_isShared_2408_ = v_isSharedCheck_2412_;
goto v_resetjp_2406_;
}
else
{
lean_inc(v_a_2405_);
lean_dec(v___x_2404_);
v___x_2407_ = lean_box(0);
v_isShared_2408_ = v_isSharedCheck_2412_;
goto v_resetjp_2406_;
}
v_resetjp_2406_:
{
lean_object* v___x_2410_; 
if (v_isShared_2408_ == 0)
{
v___x_2410_ = v___x_2407_;
goto v_reusejp_2409_;
}
else
{
lean_object* v_reuseFailAlloc_2411_; 
v_reuseFailAlloc_2411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2411_, 0, v_a_2405_);
v___x_2410_ = v_reuseFailAlloc_2411_;
goto v_reusejp_2409_;
}
v_reusejp_2409_:
{
return v___x_2410_;
}
}
}
}
}
}
}
}
v___jp_2382_:
{
size_t v___x_2384_; size_t v___x_2385_; 
v___x_2384_ = ((size_t)1ULL);
v___x_2385_ = lean_usize_add(v_i_2374_, v___x_2384_);
v_i_2374_ = v___x_2385_;
v_b_2375_ = v_a_2383_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Impure_checkLetDecl_spec__2___boxed(lean_object* v_as_2418_, lean_object* v_sz_2419_, lean_object* v_i_2420_, lean_object* v_b_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_){
_start:
{
size_t v_sz_boxed_2428_; size_t v_i_boxed_2429_; lean_object* v_res_2430_; 
v_sz_boxed_2428_ = lean_unbox_usize(v_sz_2419_);
lean_dec(v_sz_2419_);
v_i_boxed_2429_ = lean_unbox_usize(v_i_2420_);
lean_dec(v_i_2420_);
v_res_2430_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Impure_checkLetDecl_spec__2(v_as_2418_, v_sz_boxed_2428_, v_i_boxed_2429_, v_b_2421_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_);
lean_dec(v___y_2426_);
lean_dec_ref(v___y_2425_);
lean_dec(v___y_2424_);
lean_dec_ref(v___y_2423_);
lean_dec(v___y_2422_);
lean_dec_ref(v_as_2418_);
return v_res_2430_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Check_Impure_checkLetDecl___closed__8(void){
_start:
{
lean_object* v___x_2445_; lean_object* v___x_2446_; 
v___x_2445_ = ((lean_object*)(l_Lean_Compiler_LCNF_Check_Impure_checkLetDecl___closed__7));
v___x_2446_ = l_Lean_stringToMessageData(v___x_2445_);
return v___x_2446_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Check_Impure_checkLetDecl___closed__10(void){
_start:
{
lean_object* v___x_2448_; lean_object* v___x_2449_; 
v___x_2448_ = ((lean_object*)(l_Lean_Compiler_LCNF_Check_Impure_checkLetDecl___closed__9));
v___x_2449_ = l_Lean_stringToMessageData(v___x_2448_);
return v___x_2449_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Check_Impure_checkLetDecl___closed__12(void){
_start:
{
lean_object* v___x_2451_; lean_object* v___x_2452_; 
v___x_2451_ = ((lean_object*)(l_Lean_Compiler_LCNF_Check_Impure_checkLetDecl___closed__11));
v___x_2452_ = l_Lean_stringToMessageData(v___x_2451_);
return v___x_2452_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Check_Impure_checkLetDecl___closed__14(void){
_start:
{
lean_object* v___x_2454_; lean_object* v___x_2455_; 
v___x_2454_ = ((lean_object*)(l_Lean_Compiler_LCNF_Check_Impure_checkLetDecl___closed__13));
v___x_2455_ = l_Lean_stringToMessageData(v___x_2454_);
return v___x_2455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Impure_checkLetDecl(lean_object* v_decl_2456_, lean_object* v_a_2457_, lean_object* v_a_2458_, lean_object* v_a_2459_, lean_object* v_a_2460_, lean_object* v_a_2461_){
_start:
{
lean_object* v_fvarId_2463_; lean_object* v_type_2464_; lean_object* v_value_2465_; lean_object* v___y_2467_; lean_object* v___y_2470_; lean_object* v___y_2473_; 
v_fvarId_2463_ = lean_ctor_get(v_decl_2456_, 0);
lean_inc(v_fvarId_2463_);
v_type_2464_ = lean_ctor_get(v_decl_2456_, 2);
lean_inc_ref(v_type_2464_);
v_value_2465_ = lean_ctor_get(v_decl_2456_, 3);
lean_inc(v_value_2465_);
lean_dec_ref(v_decl_2456_);
switch(lean_obj_tag(v_value_2465_))
{
case 0:
{
lean_object* v___x_2476_; uint8_t v_isShared_2477_; uint8_t v_isSharedCheck_2484_; 
v_isSharedCheck_2484_ = !lean_is_exclusive(v_value_2465_);
if (v_isSharedCheck_2484_ == 0)
{
lean_object* v_unused_2485_; 
v_unused_2485_ = lean_ctor_get(v_value_2465_, 0);
lean_dec(v_unused_2485_);
v___x_2476_ = v_value_2465_;
v_isShared_2477_ = v_isSharedCheck_2484_;
goto v_resetjp_2475_;
}
else
{
lean_dec(v_value_2465_);
v___x_2476_ = lean_box(0);
v_isShared_2477_ = v_isSharedCheck_2484_;
goto v_resetjp_2475_;
}
v_resetjp_2475_:
{
uint8_t v___x_2478_; 
v___x_2478_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isPossibleRef(v_type_2464_);
lean_dec_ref(v_type_2464_);
if (v___x_2478_ == 0)
{
lean_object* v___x_2479_; lean_object* v___x_2481_; 
lean_dec(v_fvarId_2463_);
v___x_2479_ = lean_box(0);
if (v_isShared_2477_ == 0)
{
lean_ctor_set(v___x_2476_, 0, v___x_2479_);
v___x_2481_ = v___x_2476_;
goto v_reusejp_2480_;
}
else
{
lean_object* v_reuseFailAlloc_2482_; 
v_reuseFailAlloc_2482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2482_, 0, v___x_2479_);
v___x_2481_ = v_reuseFailAlloc_2482_;
goto v_reusejp_2480_;
}
v_reusejp_2480_:
{
return v___x_2481_;
}
}
else
{
lean_object* v___x_2483_; 
lean_del_object(v___x_2476_);
v___x_2483_ = l_Lean_Compiler_LCNF_Check_Impure_addOwned___redArg(v_fvarId_2463_, v_a_2457_);
return v___x_2483_;
}
}
}
case 1:
{
lean_object* v___x_2486_; lean_object* v___x_2487_; 
lean_dec_ref(v_type_2464_);
lean_dec(v_fvarId_2463_);
v___x_2486_ = lean_box(0);
v___x_2487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2487_, 0, v___x_2486_);
return v___x_2487_;
}
case 4:
{
lean_object* v_fvarId_2488_; lean_object* v_args_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; 
lean_dec_ref(v_type_2464_);
v_fvarId_2488_ = lean_ctor_get(v_value_2465_, 0);
lean_inc(v_fvarId_2488_);
v_args_2489_ = lean_ctor_get(v_value_2465_, 1);
lean_inc_ref(v_args_2489_);
lean_dec_ref(v_value_2465_);
v___x_2490_ = lean_unsigned_to_nat(1u);
v___x_2491_ = l_Lean_Compiler_LCNF_Check_Impure_consume(v_fvarId_2488_, v___x_2490_, v_a_2457_, v_a_2458_, v_a_2459_, v_a_2460_, v_a_2461_);
if (lean_obj_tag(v___x_2491_) == 0)
{
lean_object* v___x_2492_; lean_object* v___x_2493_; uint8_t v___x_2494_; 
lean_dec_ref(v___x_2491_);
v___x_2492_ = lean_unsigned_to_nat(0u);
v___x_2493_ = lean_array_get_size(v_args_2489_);
v___x_2494_ = lean_nat_dec_lt(v___x_2492_, v___x_2493_);
if (v___x_2494_ == 0)
{
lean_object* v___x_2495_; 
lean_dec_ref(v_args_2489_);
v___x_2495_ = l_Lean_Compiler_LCNF_Check_Impure_addOwned___redArg(v_fvarId_2463_, v_a_2457_);
return v___x_2495_;
}
else
{
lean_object* v___x_2496_; uint8_t v___x_2497_; 
v___x_2496_ = lean_box(0);
v___x_2497_ = lean_nat_dec_le(v___x_2493_, v___x_2493_);
if (v___x_2497_ == 0)
{
if (v___x_2494_ == 0)
{
lean_object* v___x_2498_; 
lean_dec_ref(v_args_2489_);
v___x_2498_ = l_Lean_Compiler_LCNF_Check_Impure_addOwned___redArg(v_fvarId_2463_, v_a_2457_);
return v___x_2498_;
}
else
{
size_t v___x_2499_; size_t v___x_2500_; lean_object* v___x_2501_; 
v___x_2499_ = ((size_t)0ULL);
v___x_2500_ = lean_usize_of_nat(v___x_2493_);
v___x_2501_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Impure_checkLetDecl_spec__0(v_args_2489_, v___x_2499_, v___x_2500_, v___x_2496_, v_a_2457_, v_a_2458_, v_a_2459_, v_a_2460_, v_a_2461_);
lean_dec_ref(v_args_2489_);
v___y_2473_ = v___x_2501_;
goto v___jp_2472_;
}
}
else
{
size_t v___x_2502_; size_t v___x_2503_; lean_object* v___x_2504_; 
v___x_2502_ = ((size_t)0ULL);
v___x_2503_ = lean_usize_of_nat(v___x_2493_);
v___x_2504_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Impure_checkLetDecl_spec__0(v_args_2489_, v___x_2502_, v___x_2503_, v___x_2496_, v_a_2457_, v_a_2458_, v_a_2459_, v_a_2460_, v_a_2461_);
lean_dec_ref(v_args_2489_);
v___y_2473_ = v___x_2504_;
goto v___jp_2472_;
}
}
}
else
{
lean_dec_ref(v_args_2489_);
lean_dec(v_fvarId_2463_);
return v___x_2491_;
}
}
case 5:
{
lean_object* v_i_2505_; lean_object* v_args_2506_; lean_object* v___y_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; uint8_t v___x_2516_; 
lean_dec_ref(v_type_2464_);
v_i_2505_ = lean_ctor_get(v_value_2465_, 0);
lean_inc_ref(v_i_2505_);
v_args_2506_ = lean_ctor_get(v_value_2465_, 1);
lean_inc_ref(v_args_2506_);
lean_dec_ref(v_value_2465_);
v___x_2514_ = lean_unsigned_to_nat(0u);
v___x_2515_ = lean_array_get_size(v_args_2506_);
v___x_2516_ = lean_nat_dec_lt(v___x_2514_, v___x_2515_);
if (v___x_2516_ == 0)
{
lean_dec_ref(v_args_2506_);
goto v___jp_2507_;
}
else
{
lean_object* v___x_2517_; uint8_t v___x_2518_; 
v___x_2517_ = lean_box(0);
v___x_2518_ = lean_nat_dec_le(v___x_2515_, v___x_2515_);
if (v___x_2518_ == 0)
{
if (v___x_2516_ == 0)
{
lean_dec_ref(v_args_2506_);
goto v___jp_2507_;
}
else
{
size_t v___x_2519_; size_t v___x_2520_; lean_object* v___x_2521_; 
v___x_2519_ = ((size_t)0ULL);
v___x_2520_ = lean_usize_of_nat(v___x_2515_);
v___x_2521_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Impure_checkLetDecl_spec__0(v_args_2506_, v___x_2519_, v___x_2520_, v___x_2517_, v_a_2457_, v_a_2458_, v_a_2459_, v_a_2460_, v_a_2461_);
lean_dec_ref(v_args_2506_);
v___y_2513_ = v___x_2521_;
goto v___jp_2512_;
}
}
else
{
size_t v___x_2522_; size_t v___x_2523_; lean_object* v___x_2524_; 
v___x_2522_ = ((size_t)0ULL);
v___x_2523_ = lean_usize_of_nat(v___x_2515_);
v___x_2524_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Impure_checkLetDecl_spec__0(v_args_2506_, v___x_2522_, v___x_2523_, v___x_2517_, v_a_2457_, v_a_2458_, v_a_2459_, v_a_2460_, v_a_2461_);
lean_dec_ref(v_args_2506_);
v___y_2513_ = v___x_2524_;
goto v___jp_2512_;
}
}
v___jp_2507_:
{
uint8_t v___x_2508_; 
v___x_2508_ = l_Lean_Compiler_LCNF_CtorInfo_isRef(v_i_2505_);
lean_dec_ref(v_i_2505_);
if (v___x_2508_ == 0)
{
lean_object* v___x_2509_; lean_object* v___x_2510_; 
lean_dec(v_fvarId_2463_);
v___x_2509_ = lean_box(0);
v___x_2510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2510_, 0, v___x_2509_);
return v___x_2510_;
}
else
{
lean_object* v___x_2511_; 
v___x_2511_ = l_Lean_Compiler_LCNF_Check_Impure_addOwned___redArg(v_fvarId_2463_, v_a_2457_);
return v___x_2511_;
}
}
v___jp_2512_:
{
if (lean_obj_tag(v___y_2513_) == 0)
{
lean_dec_ref(v___y_2513_);
goto v___jp_2507_;
}
else
{
lean_dec_ref(v_i_2505_);
lean_dec(v_fvarId_2463_);
return v___y_2513_;
}
}
}
case 6:
{
lean_object* v_var_2525_; lean_object* v___x_2526_; 
lean_dec_ref(v_type_2464_);
v_var_2525_ = lean_ctor_get(v_value_2465_, 1);
lean_inc(v_var_2525_);
lean_dec_ref(v_value_2465_);
lean_inc(v_var_2525_);
v___x_2526_ = l_Lean_Compiler_LCNF_Check_Impure_useVar(v_var_2525_, v_a_2457_, v_a_2458_, v_a_2459_, v_a_2460_, v_a_2461_);
if (lean_obj_tag(v___x_2526_) == 0)
{
lean_object* v___x_2528_; uint8_t v_isShared_2529_; uint8_t v_isSharedCheck_2537_; 
v_isSharedCheck_2537_ = !lean_is_exclusive(v___x_2526_);
if (v_isSharedCheck_2537_ == 0)
{
lean_object* v_unused_2538_; 
v_unused_2538_ = lean_ctor_get(v___x_2526_, 0);
lean_dec(v_unused_2538_);
v___x_2528_ = v___x_2526_;
v_isShared_2529_ = v_isSharedCheck_2537_;
goto v_resetjp_2527_;
}
else
{
lean_dec(v___x_2526_);
v___x_2528_ = lean_box(0);
v_isShared_2529_ = v_isSharedCheck_2537_;
goto v_resetjp_2527_;
}
v_resetjp_2527_:
{
lean_object* v___x_2531_; 
if (v_isShared_2529_ == 0)
{
lean_ctor_set_tag(v___x_2528_, 1);
lean_ctor_set(v___x_2528_, 0, v_var_2525_);
v___x_2531_ = v___x_2528_;
goto v_reusejp_2530_;
}
else
{
lean_object* v_reuseFailAlloc_2536_; 
v_reuseFailAlloc_2536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2536_, 0, v_var_2525_);
v___x_2531_ = v_reuseFailAlloc_2536_;
goto v_reusejp_2530_;
}
v_reusejp_2530_:
{
lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; 
v___x_2532_ = lean_unsigned_to_nat(1u);
v___x_2533_ = lean_mk_empty_array_with_capacity(v___x_2532_);
v___x_2534_ = lean_array_push(v___x_2533_, v___x_2531_);
v___x_2535_ = l_Lean_Compiler_LCNF_Check_Impure_addBorrowed(v_fvarId_2463_, v___x_2534_, v_a_2457_, v_a_2458_, v_a_2459_, v_a_2460_, v_a_2461_);
lean_dec_ref(v___x_2534_);
return v___x_2535_;
}
}
}
else
{
lean_dec(v_var_2525_);
lean_dec(v_fvarId_2463_);
return v___x_2526_;
}
}
case 7:
{
lean_object* v_var_2539_; lean_object* v___x_2540_; 
lean_dec_ref(v_type_2464_);
lean_dec(v_fvarId_2463_);
v_var_2539_ = lean_ctor_get(v_value_2465_, 1);
lean_inc(v_var_2539_);
lean_dec_ref(v_value_2465_);
v___x_2540_ = l_Lean_Compiler_LCNF_Check_Impure_useVar(v_var_2539_, v_a_2457_, v_a_2458_, v_a_2459_, v_a_2460_, v_a_2461_);
return v___x_2540_;
}
case 8:
{
lean_object* v_var_2541_; lean_object* v___x_2542_; 
lean_dec_ref(v_type_2464_);
lean_dec(v_fvarId_2463_);
v_var_2541_ = lean_ctor_get(v_value_2465_, 2);
lean_inc(v_var_2541_);
lean_dec_ref(v_value_2465_);
v___x_2542_ = l_Lean_Compiler_LCNF_Check_Impure_useVar(v_var_2541_, v_a_2457_, v_a_2458_, v_a_2459_, v_a_2460_, v_a_2461_);
return v___x_2542_;
}
case 9:
{
lean_object* v_fn_2543_; lean_object* v_args_2544_; lean_object* v___x_2546_; uint8_t v_isShared_2547_; uint8_t v_isSharedCheck_2660_; 
v_fn_2543_ = lean_ctor_get(v_value_2465_, 0);
v_args_2544_ = lean_ctor_get(v_value_2465_, 1);
v_isSharedCheck_2660_ = !lean_is_exclusive(v_value_2465_);
if (v_isSharedCheck_2660_ == 0)
{
v___x_2546_ = v_value_2465_;
v_isShared_2547_ = v_isSharedCheck_2660_;
goto v_resetjp_2545_;
}
else
{
lean_inc(v_args_2544_);
lean_inc(v_fn_2543_);
lean_dec(v_value_2465_);
v___x_2546_ = lean_box(0);
v_isShared_2547_ = v_isSharedCheck_2660_;
goto v_resetjp_2545_;
}
v_resetjp_2545_:
{
lean_object* v___x_2548_; 
lean_inc(v_fn_2543_);
v___x_2548_ = l_Lean_Compiler_LCNF_getImpureSignature_x3f___redArg(v_fn_2543_, v_a_2461_);
if (lean_obj_tag(v___x_2548_) == 0)
{
lean_object* v_a_2549_; 
v_a_2549_ = lean_ctor_get(v___x_2548_, 0);
lean_inc(v_a_2549_);
lean_dec_ref(v___x_2548_);
if (lean_obj_tag(v_a_2549_) == 1)
{
lean_object* v_val_2550_; lean_object* v___x_2552_; uint8_t v_isShared_2553_; uint8_t v_isSharedCheck_2645_; 
v_val_2550_ = lean_ctor_get(v_a_2549_, 0);
v_isSharedCheck_2645_ = !lean_is_exclusive(v_a_2549_);
if (v_isSharedCheck_2645_ == 0)
{
v___x_2552_ = v_a_2549_;
v_isShared_2553_ = v_isSharedCheck_2645_;
goto v_resetjp_2551_;
}
else
{
lean_inc(v_val_2550_);
lean_dec(v_a_2549_);
v___x_2552_ = lean_box(0);
v_isShared_2553_ = v_isSharedCheck_2645_;
goto v_resetjp_2551_;
}
v_resetjp_2551_:
{
lean_object* v_params_2554_; lean_object* v___y_2556_; lean_object* v___y_2557_; lean_object* v___y_2558_; lean_object* v___y_2559_; lean_object* v___y_2560_; lean_object* v___x_2622_; lean_object* v___x_2623_; uint8_t v___x_2624_; 
v_params_2554_ = lean_ctor_get(v_val_2550_, 3);
lean_inc_ref(v_params_2554_);
lean_dec(v_val_2550_);
v___x_2622_ = lean_array_get_size(v_args_2544_);
v___x_2623_ = lean_array_get_size(v_params_2554_);
v___x_2624_ = lean_nat_dec_eq(v___x_2622_, v___x_2623_);
if (v___x_2624_ == 0)
{
lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2628_; 
lean_dec_ref(v_params_2554_);
lean_dec_ref(v_args_2544_);
lean_dec_ref(v_type_2464_);
lean_dec(v_fvarId_2463_);
v___x_2625_ = lean_obj_once(&l_Lean_Compiler_LCNF_Check_Impure_checkLetDecl___closed__8, &l_Lean_Compiler_LCNF_Check_Impure_checkLetDecl___closed__8_once, _init_l_Lean_Compiler_LCNF_Check_Impure_checkLetDecl___closed__8);
v___x_2626_ = l_Lean_MessageData_ofName(v_fn_2543_);
if (v_isShared_2547_ == 0)
{
lean_ctor_set_tag(v___x_2546_, 7);
lean_ctor_set(v___x_2546_, 1, v___x_2626_);
lean_ctor_set(v___x_2546_, 0, v___x_2625_);
v___x_2628_ = v___x_2546_;
goto v_reusejp_2627_;
}
else
{
lean_object* v_reuseFailAlloc_2644_; 
v_reuseFailAlloc_2644_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2644_, 0, v___x_2625_);
lean_ctor_set(v_reuseFailAlloc_2644_, 1, v___x_2626_);
v___x_2628_ = v_reuseFailAlloc_2644_;
goto v_reusejp_2627_;
}
v_reusejp_2627_:
{
lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2633_; 
v___x_2629_ = lean_obj_once(&l_Lean_Compiler_LCNF_Check_Impure_checkLetDecl___closed__10, &l_Lean_Compiler_LCNF_Check_Impure_checkLetDecl___closed__10_once, _init_l_Lean_Compiler_LCNF_Check_Impure_checkLetDecl___closed__10);
v___x_2630_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2630_, 0, v___x_2628_);
lean_ctor_set(v___x_2630_, 1, v___x_2629_);
v___x_2631_ = l_Nat_reprFast(v___x_2623_);
if (v_isShared_2553_ == 0)
{
lean_ctor_set_tag(v___x_2552_, 3);
lean_ctor_set(v___x_2552_, 0, v___x_2631_);
v___x_2633_ = v___x_2552_;
goto v_reusejp_2632_;
}
else
{
lean_object* v_reuseFailAlloc_2643_; 
v_reuseFailAlloc_2643_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2643_, 0, v___x_2631_);
v___x_2633_ = v_reuseFailAlloc_2643_;
goto v_reusejp_2632_;
}
v_reusejp_2632_:
{
lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; 
v___x_2634_ = l_Lean_MessageData_ofFormat(v___x_2633_);
v___x_2635_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2635_, 0, v___x_2630_);
lean_ctor_set(v___x_2635_, 1, v___x_2634_);
v___x_2636_ = lean_obj_once(&l_Lean_Compiler_LCNF_Check_Impure_checkLetDecl___closed__12, &l_Lean_Compiler_LCNF_Check_Impure_checkLetDecl___closed__12_once, _init_l_Lean_Compiler_LCNF_Check_Impure_checkLetDecl___closed__12);
v___x_2637_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2637_, 0, v___x_2635_);
lean_ctor_set(v___x_2637_, 1, v___x_2636_);
v___x_2638_ = l_Nat_reprFast(v___x_2622_);
v___x_2639_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2639_, 0, v___x_2638_);
v___x_2640_ = l_Lean_MessageData_ofFormat(v___x_2639_);
v___x_2641_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2641_, 0, v___x_2637_);
lean_ctor_set(v___x_2641_, 1, v___x_2640_);
v___x_2642_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Impure_kill_spec__1___redArg(v___x_2641_, v_a_2458_, v_a_2459_, v_a_2460_, v_a_2461_);
return v___x_2642_;
}
}
}
else
{
lean_del_object(v___x_2552_);
lean_del_object(v___x_2546_);
v___y_2556_ = v_a_2457_;
v___y_2557_ = v_a_2458_;
v___y_2558_ = v_a_2459_;
v___y_2559_ = v_a_2460_;
v___y_2560_ = v_a_2461_;
goto v___jp_2555_;
}
v___jp_2555_:
{
lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; size_t v_sz_2564_; size_t v___x_2565_; lean_object* v___x_2566_; 
v___x_2561_ = lean_array_get_size(v_args_2544_);
v___x_2562_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_args_2544_);
v___x_2563_ = l_Array_toSubarray___redArg(v_args_2544_, v___x_2562_, v___x_2561_);
v_sz_2564_ = lean_array_size(v_params_2554_);
v___x_2565_ = ((size_t)0ULL);
lean_inc_ref(v___x_2563_);
v___x_2566_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Impure_checkLetDecl_spec__1(v_params_2554_, v_sz_2564_, v___x_2565_, v___x_2563_, v___y_2556_, v___y_2557_, v___y_2558_, v___y_2559_, v___y_2560_);
if (lean_obj_tag(v___x_2566_) == 0)
{
lean_object* v___x_2567_; 
lean_dec_ref(v___x_2566_);
v___x_2567_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Impure_checkLetDecl_spec__2(v_params_2554_, v_sz_2564_, v___x_2565_, v___x_2563_, v___y_2556_, v___y_2557_, v___y_2558_, v___y_2559_, v___y_2560_);
lean_dec_ref(v_params_2554_);
if (lean_obj_tag(v___x_2567_) == 0)
{
lean_object* v___x_2569_; uint8_t v_isShared_2570_; uint8_t v_isSharedCheck_2604_; 
v_isSharedCheck_2604_ = !lean_is_exclusive(v___x_2567_);
if (v_isSharedCheck_2604_ == 0)
{
lean_object* v_unused_2605_; 
v_unused_2605_ = lean_ctor_get(v___x_2567_, 0);
lean_dec(v_unused_2605_);
v___x_2569_ = v___x_2567_;
v_isShared_2570_ = v_isSharedCheck_2604_;
goto v_resetjp_2568_;
}
else
{
lean_dec(v___x_2567_);
v___x_2569_ = lean_box(0);
v_isShared_2570_ = v_isSharedCheck_2604_;
goto v_resetjp_2568_;
}
v_resetjp_2568_:
{
lean_object* v___x_2571_; uint8_t v___x_2572_; 
v___x_2571_ = ((lean_object*)(l_Lean_Compiler_LCNF_Check_Impure_checkLetDecl___closed__2));
v___x_2572_ = lean_name_eq(v_fn_2543_, v___x_2571_);
if (v___x_2572_ == 0)
{
lean_object* v___x_2573_; uint8_t v___x_2574_; 
v___x_2573_ = ((lean_object*)(l_Lean_Compiler_LCNF_Check_Impure_checkLetDecl___closed__4));
v___x_2574_ = lean_name_eq(v_fn_2543_, v___x_2573_);
if (v___x_2574_ == 0)
{
lean_object* v___x_2575_; uint8_t v___x_2576_; 
v___x_2575_ = ((lean_object*)(l_Lean_Compiler_LCNF_Check_Impure_checkLetDecl___closed__6));
v___x_2576_ = lean_name_eq(v_fn_2543_, v___x_2575_);
lean_dec(v_fn_2543_);
if (v___x_2576_ == 0)
{
uint8_t v___x_2577_; 
lean_dec_ref(v_args_2544_);
v___x_2577_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isPossibleRef(v_type_2464_);
lean_dec_ref(v_type_2464_);
if (v___x_2577_ == 0)
{
lean_object* v___x_2578_; lean_object* v___x_2580_; 
lean_dec(v_fvarId_2463_);
v___x_2578_ = lean_box(0);
if (v_isShared_2570_ == 0)
{
lean_ctor_set(v___x_2569_, 0, v___x_2578_);
v___x_2580_ = v___x_2569_;
goto v_reusejp_2579_;
}
else
{
lean_object* v_reuseFailAlloc_2581_; 
v_reuseFailAlloc_2581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2581_, 0, v___x_2578_);
v___x_2580_ = v_reuseFailAlloc_2581_;
goto v_reusejp_2579_;
}
v_reusejp_2579_:
{
return v___x_2580_;
}
}
else
{
lean_object* v___x_2582_; 
lean_del_object(v___x_2569_);
v___x_2582_ = l_Lean_Compiler_LCNF_Check_Impure_addOwned___redArg(v_fvarId_2463_, v___y_2556_);
return v___x_2582_;
}
}
else
{
lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; 
lean_del_object(v___x_2569_);
lean_dec_ref(v_type_2464_);
v___x_2583_ = lean_box(0);
v___x_2584_ = lean_unsigned_to_nat(1u);
v___x_2585_ = lean_array_get(v___x_2583_, v_args_2544_, v___x_2584_);
lean_dec_ref(v_args_2544_);
v___x_2586_ = lean_mk_empty_array_with_capacity(v___x_2584_);
v___x_2587_ = lean_array_push(v___x_2586_, v___x_2585_);
v___x_2588_ = l_Lean_Compiler_LCNF_Check_Impure_addBorrowed(v_fvarId_2463_, v___x_2587_, v___y_2556_, v___y_2557_, v___y_2558_, v___y_2559_, v___y_2560_);
lean_dec_ref(v___x_2587_);
return v___x_2588_;
}
}
else
{
lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; 
lean_del_object(v___x_2569_);
lean_dec(v_fn_2543_);
lean_dec_ref(v_type_2464_);
v___x_2589_ = lean_box(0);
v___x_2590_ = lean_unsigned_to_nat(1u);
v___x_2591_ = lean_array_get(v___x_2589_, v_args_2544_, v___x_2590_);
v___x_2592_ = lean_unsigned_to_nat(2u);
v___x_2593_ = lean_array_get(v___x_2589_, v_args_2544_, v___x_2592_);
lean_dec_ref(v_args_2544_);
v___x_2594_ = lean_mk_empty_array_with_capacity(v___x_2592_);
v___x_2595_ = lean_array_push(v___x_2594_, v___x_2591_);
v___x_2596_ = lean_array_push(v___x_2595_, v___x_2593_);
v___x_2597_ = l_Lean_Compiler_LCNF_Check_Impure_addBorrowed(v_fvarId_2463_, v___x_2596_, v___y_2556_, v___y_2557_, v___y_2558_, v___y_2559_, v___y_2560_);
lean_dec_ref(v___x_2596_);
return v___x_2597_;
}
}
else
{
lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; 
lean_del_object(v___x_2569_);
lean_dec(v_fn_2543_);
lean_dec_ref(v_type_2464_);
v___x_2598_ = lean_box(0);
v___x_2599_ = lean_unsigned_to_nat(1u);
v___x_2600_ = lean_array_get(v___x_2598_, v_args_2544_, v___x_2599_);
lean_dec_ref(v_args_2544_);
v___x_2601_ = lean_mk_empty_array_with_capacity(v___x_2599_);
v___x_2602_ = lean_array_push(v___x_2601_, v___x_2600_);
v___x_2603_ = l_Lean_Compiler_LCNF_Check_Impure_addBorrowed(v_fvarId_2463_, v___x_2602_, v___y_2556_, v___y_2557_, v___y_2558_, v___y_2559_, v___y_2560_);
lean_dec_ref(v___x_2602_);
return v___x_2603_;
}
}
}
else
{
lean_object* v_a_2606_; lean_object* v___x_2608_; uint8_t v_isShared_2609_; uint8_t v_isSharedCheck_2613_; 
lean_dec_ref(v_args_2544_);
lean_dec(v_fn_2543_);
lean_dec_ref(v_type_2464_);
lean_dec(v_fvarId_2463_);
v_a_2606_ = lean_ctor_get(v___x_2567_, 0);
v_isSharedCheck_2613_ = !lean_is_exclusive(v___x_2567_);
if (v_isSharedCheck_2613_ == 0)
{
v___x_2608_ = v___x_2567_;
v_isShared_2609_ = v_isSharedCheck_2613_;
goto v_resetjp_2607_;
}
else
{
lean_inc(v_a_2606_);
lean_dec(v___x_2567_);
v___x_2608_ = lean_box(0);
v_isShared_2609_ = v_isSharedCheck_2613_;
goto v_resetjp_2607_;
}
v_resetjp_2607_:
{
lean_object* v___x_2611_; 
if (v_isShared_2609_ == 0)
{
v___x_2611_ = v___x_2608_;
goto v_reusejp_2610_;
}
else
{
lean_object* v_reuseFailAlloc_2612_; 
v_reuseFailAlloc_2612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2612_, 0, v_a_2606_);
v___x_2611_ = v_reuseFailAlloc_2612_;
goto v_reusejp_2610_;
}
v_reusejp_2610_:
{
return v___x_2611_;
}
}
}
}
else
{
lean_object* v_a_2614_; lean_object* v___x_2616_; uint8_t v_isShared_2617_; uint8_t v_isSharedCheck_2621_; 
lean_dec_ref(v___x_2563_);
lean_dec_ref(v_params_2554_);
lean_dec_ref(v_args_2544_);
lean_dec(v_fn_2543_);
lean_dec_ref(v_type_2464_);
lean_dec(v_fvarId_2463_);
v_a_2614_ = lean_ctor_get(v___x_2566_, 0);
v_isSharedCheck_2621_ = !lean_is_exclusive(v___x_2566_);
if (v_isSharedCheck_2621_ == 0)
{
v___x_2616_ = v___x_2566_;
v_isShared_2617_ = v_isSharedCheck_2621_;
goto v_resetjp_2615_;
}
else
{
lean_inc(v_a_2614_);
lean_dec(v___x_2566_);
v___x_2616_ = lean_box(0);
v_isShared_2617_ = v_isSharedCheck_2621_;
goto v_resetjp_2615_;
}
v_resetjp_2615_:
{
lean_object* v___x_2619_; 
if (v_isShared_2617_ == 0)
{
v___x_2619_ = v___x_2616_;
goto v_reusejp_2618_;
}
else
{
lean_object* v_reuseFailAlloc_2620_; 
v_reuseFailAlloc_2620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2620_, 0, v_a_2614_);
v___x_2619_ = v_reuseFailAlloc_2620_;
goto v_reusejp_2618_;
}
v_reusejp_2618_:
{
return v___x_2619_;
}
}
}
}
}
}
else
{
lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2649_; 
lean_dec(v_a_2549_);
lean_dec_ref(v_args_2544_);
lean_dec_ref(v_type_2464_);
lean_dec(v_fvarId_2463_);
v___x_2646_ = lean_obj_once(&l_Lean_Compiler_LCNF_Check_Impure_checkLetDecl___closed__14, &l_Lean_Compiler_LCNF_Check_Impure_checkLetDecl___closed__14_once, _init_l_Lean_Compiler_LCNF_Check_Impure_checkLetDecl___closed__14);
v___x_2647_ = l_Lean_MessageData_ofName(v_fn_2543_);
if (v_isShared_2547_ == 0)
{
lean_ctor_set_tag(v___x_2546_, 7);
lean_ctor_set(v___x_2546_, 1, v___x_2647_);
lean_ctor_set(v___x_2546_, 0, v___x_2646_);
v___x_2649_ = v___x_2546_;
goto v_reusejp_2648_;
}
else
{
lean_object* v_reuseFailAlloc_2651_; 
v_reuseFailAlloc_2651_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2651_, 0, v___x_2646_);
lean_ctor_set(v_reuseFailAlloc_2651_, 1, v___x_2647_);
v___x_2649_ = v_reuseFailAlloc_2651_;
goto v_reusejp_2648_;
}
v_reusejp_2648_:
{
lean_object* v___x_2650_; 
v___x_2650_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Impure_kill_spec__1___redArg(v___x_2649_, v_a_2458_, v_a_2459_, v_a_2460_, v_a_2461_);
return v___x_2650_;
}
}
}
else
{
lean_object* v_a_2652_; lean_object* v___x_2654_; uint8_t v_isShared_2655_; uint8_t v_isSharedCheck_2659_; 
lean_del_object(v___x_2546_);
lean_dec_ref(v_args_2544_);
lean_dec(v_fn_2543_);
lean_dec_ref(v_type_2464_);
lean_dec(v_fvarId_2463_);
v_a_2652_ = lean_ctor_get(v___x_2548_, 0);
v_isSharedCheck_2659_ = !lean_is_exclusive(v___x_2548_);
if (v_isSharedCheck_2659_ == 0)
{
v___x_2654_ = v___x_2548_;
v_isShared_2655_ = v_isSharedCheck_2659_;
goto v_resetjp_2653_;
}
else
{
lean_inc(v_a_2652_);
lean_dec(v___x_2548_);
v___x_2654_ = lean_box(0);
v_isShared_2655_ = v_isSharedCheck_2659_;
goto v_resetjp_2653_;
}
v_resetjp_2653_:
{
lean_object* v___x_2657_; 
if (v_isShared_2655_ == 0)
{
v___x_2657_ = v___x_2654_;
goto v_reusejp_2656_;
}
else
{
lean_object* v_reuseFailAlloc_2658_; 
v_reuseFailAlloc_2658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2658_, 0, v_a_2652_);
v___x_2657_ = v_reuseFailAlloc_2658_;
goto v_reusejp_2656_;
}
v_reusejp_2656_:
{
return v___x_2657_;
}
}
}
}
}
case 10:
{
lean_object* v_args_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; uint8_t v___x_2664_; 
lean_dec_ref(v_type_2464_);
v_args_2661_ = lean_ctor_get(v_value_2465_, 1);
lean_inc_ref(v_args_2661_);
lean_dec_ref(v_value_2465_);
v___x_2662_ = lean_unsigned_to_nat(0u);
v___x_2663_ = lean_array_get_size(v_args_2661_);
v___x_2664_ = lean_nat_dec_lt(v___x_2662_, v___x_2663_);
if (v___x_2664_ == 0)
{
lean_object* v___x_2665_; 
lean_dec_ref(v_args_2661_);
v___x_2665_ = l_Lean_Compiler_LCNF_Check_Impure_addOwned___redArg(v_fvarId_2463_, v_a_2457_);
return v___x_2665_;
}
else
{
lean_object* v___x_2666_; uint8_t v___x_2667_; 
v___x_2666_ = lean_box(0);
v___x_2667_ = lean_nat_dec_le(v___x_2663_, v___x_2663_);
if (v___x_2667_ == 0)
{
if (v___x_2664_ == 0)
{
lean_object* v___x_2668_; 
lean_dec_ref(v_args_2661_);
v___x_2668_ = l_Lean_Compiler_LCNF_Check_Impure_addOwned___redArg(v_fvarId_2463_, v_a_2457_);
return v___x_2668_;
}
else
{
size_t v___x_2669_; size_t v___x_2670_; lean_object* v___x_2671_; 
v___x_2669_ = ((size_t)0ULL);
v___x_2670_ = lean_usize_of_nat(v___x_2663_);
v___x_2671_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Impure_checkLetDecl_spec__0(v_args_2661_, v___x_2669_, v___x_2670_, v___x_2666_, v_a_2457_, v_a_2458_, v_a_2459_, v_a_2460_, v_a_2461_);
lean_dec_ref(v_args_2661_);
v___y_2470_ = v___x_2671_;
goto v___jp_2469_;
}
}
else
{
size_t v___x_2672_; size_t v___x_2673_; lean_object* v___x_2674_; 
v___x_2672_ = ((size_t)0ULL);
v___x_2673_ = lean_usize_of_nat(v___x_2663_);
v___x_2674_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Impure_checkLetDecl_spec__0(v_args_2661_, v___x_2672_, v___x_2673_, v___x_2666_, v_a_2457_, v_a_2458_, v_a_2459_, v_a_2460_, v_a_2461_);
lean_dec_ref(v_args_2661_);
v___y_2470_ = v___x_2674_;
goto v___jp_2469_;
}
}
}
case 11:
{
lean_object* v_var_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; 
lean_dec_ref(v_type_2464_);
v_var_2675_ = lean_ctor_get(v_value_2465_, 1);
lean_inc(v_var_2675_);
lean_dec_ref(v_value_2465_);
v___x_2676_ = lean_unsigned_to_nat(1u);
v___x_2677_ = l_Lean_Compiler_LCNF_Check_Impure_consume(v_var_2675_, v___x_2676_, v_a_2457_, v_a_2458_, v_a_2459_, v_a_2460_, v_a_2461_);
if (lean_obj_tag(v___x_2677_) == 0)
{
lean_object* v___x_2678_; 
lean_dec_ref(v___x_2677_);
v___x_2678_ = l_Lean_Compiler_LCNF_Check_Impure_addOwned___redArg(v_fvarId_2463_, v_a_2457_);
return v___x_2678_;
}
else
{
lean_dec(v_fvarId_2463_);
return v___x_2677_;
}
}
case 12:
{
lean_object* v_var_2679_; lean_object* v_args_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; 
lean_dec_ref(v_type_2464_);
v_var_2679_ = lean_ctor_get(v_value_2465_, 0);
lean_inc(v_var_2679_);
v_args_2680_ = lean_ctor_get(v_value_2465_, 2);
lean_inc_ref(v_args_2680_);
lean_dec_ref(v_value_2465_);
v___x_2681_ = lean_unsigned_to_nat(1u);
v___x_2682_ = l_Lean_Compiler_LCNF_Check_Impure_consume(v_var_2679_, v___x_2681_, v_a_2457_, v_a_2458_, v_a_2459_, v_a_2460_, v_a_2461_);
if (lean_obj_tag(v___x_2682_) == 0)
{
lean_object* v___x_2683_; lean_object* v___x_2684_; uint8_t v___x_2685_; 
lean_dec_ref(v___x_2682_);
v___x_2683_ = lean_unsigned_to_nat(0u);
v___x_2684_ = lean_array_get_size(v_args_2680_);
v___x_2685_ = lean_nat_dec_lt(v___x_2683_, v___x_2684_);
if (v___x_2685_ == 0)
{
lean_object* v___x_2686_; 
lean_dec_ref(v_args_2680_);
v___x_2686_ = l_Lean_Compiler_LCNF_Check_Impure_addOwned___redArg(v_fvarId_2463_, v_a_2457_);
return v___x_2686_;
}
else
{
lean_object* v___x_2687_; uint8_t v___x_2688_; 
v___x_2687_ = lean_box(0);
v___x_2688_ = lean_nat_dec_le(v___x_2684_, v___x_2684_);
if (v___x_2688_ == 0)
{
if (v___x_2685_ == 0)
{
lean_object* v___x_2689_; 
lean_dec_ref(v_args_2680_);
v___x_2689_ = l_Lean_Compiler_LCNF_Check_Impure_addOwned___redArg(v_fvarId_2463_, v_a_2457_);
return v___x_2689_;
}
else
{
size_t v___x_2690_; size_t v___x_2691_; lean_object* v___x_2692_; 
v___x_2690_ = ((size_t)0ULL);
v___x_2691_ = lean_usize_of_nat(v___x_2684_);
v___x_2692_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Impure_checkLetDecl_spec__0(v_args_2680_, v___x_2690_, v___x_2691_, v___x_2687_, v_a_2457_, v_a_2458_, v_a_2459_, v_a_2460_, v_a_2461_);
lean_dec_ref(v_args_2680_);
v___y_2467_ = v___x_2692_;
goto v___jp_2466_;
}
}
else
{
size_t v___x_2693_; size_t v___x_2694_; lean_object* v___x_2695_; 
v___x_2693_ = ((size_t)0ULL);
v___x_2694_ = lean_usize_of_nat(v___x_2684_);
v___x_2695_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Impure_checkLetDecl_spec__0(v_args_2680_, v___x_2693_, v___x_2694_, v___x_2687_, v_a_2457_, v_a_2458_, v_a_2459_, v_a_2460_, v_a_2461_);
lean_dec_ref(v_args_2680_);
v___y_2467_ = v___x_2695_;
goto v___jp_2466_;
}
}
}
else
{
lean_dec_ref(v_args_2680_);
lean_dec(v_fvarId_2463_);
return v___x_2682_;
}
}
case 13:
{
lean_object* v_fvarId_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; 
v_fvarId_2696_ = lean_ctor_get(v_value_2465_, 1);
lean_inc(v_fvarId_2696_);
lean_dec_ref(v_value_2465_);
v___x_2697_ = lean_unsigned_to_nat(1u);
v___x_2698_ = l_Lean_Compiler_LCNF_Check_Impure_consume(v_fvarId_2696_, v___x_2697_, v_a_2457_, v_a_2458_, v_a_2459_, v_a_2460_, v_a_2461_);
if (lean_obj_tag(v___x_2698_) == 0)
{
lean_object* v___x_2700_; uint8_t v_isShared_2701_; uint8_t v_isSharedCheck_2708_; 
v_isSharedCheck_2708_ = !lean_is_exclusive(v___x_2698_);
if (v_isSharedCheck_2708_ == 0)
{
lean_object* v_unused_2709_; 
v_unused_2709_ = lean_ctor_get(v___x_2698_, 0);
lean_dec(v_unused_2709_);
v___x_2700_ = v___x_2698_;
v_isShared_2701_ = v_isSharedCheck_2708_;
goto v_resetjp_2699_;
}
else
{
lean_dec(v___x_2698_);
v___x_2700_ = lean_box(0);
v_isShared_2701_ = v_isSharedCheck_2708_;
goto v_resetjp_2699_;
}
v_resetjp_2699_:
{
uint8_t v___x_2702_; 
v___x_2702_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isPossibleRef(v_type_2464_);
lean_dec_ref(v_type_2464_);
if (v___x_2702_ == 0)
{
lean_object* v___x_2703_; lean_object* v___x_2705_; 
lean_dec(v_fvarId_2463_);
v___x_2703_ = lean_box(0);
if (v_isShared_2701_ == 0)
{
lean_ctor_set(v___x_2700_, 0, v___x_2703_);
v___x_2705_ = v___x_2700_;
goto v_reusejp_2704_;
}
else
{
lean_object* v_reuseFailAlloc_2706_; 
v_reuseFailAlloc_2706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2706_, 0, v___x_2703_);
v___x_2705_ = v_reuseFailAlloc_2706_;
goto v_reusejp_2704_;
}
v_reusejp_2704_:
{
return v___x_2705_;
}
}
else
{
lean_object* v___x_2707_; 
lean_del_object(v___x_2700_);
v___x_2707_ = l_Lean_Compiler_LCNF_Check_Impure_addOwned___redArg(v_fvarId_2463_, v_a_2457_);
return v___x_2707_;
}
}
}
else
{
lean_dec_ref(v_type_2464_);
lean_dec(v_fvarId_2463_);
return v___x_2698_;
}
}
default: 
{
lean_object* v_fvarId_2710_; lean_object* v___x_2711_; 
lean_dec_ref(v_type_2464_);
lean_dec(v_fvarId_2463_);
v_fvarId_2710_ = lean_ctor_get(v_value_2465_, 0);
lean_inc(v_fvarId_2710_);
lean_dec(v_value_2465_);
v___x_2711_ = l_Lean_Compiler_LCNF_Check_Impure_useVar(v_fvarId_2710_, v_a_2457_, v_a_2458_, v_a_2459_, v_a_2460_, v_a_2461_);
return v___x_2711_;
}
}
v___jp_2466_:
{
if (lean_obj_tag(v___y_2467_) == 0)
{
lean_object* v___x_2468_; 
lean_dec_ref(v___y_2467_);
v___x_2468_ = l_Lean_Compiler_LCNF_Check_Impure_addOwned___redArg(v_fvarId_2463_, v_a_2457_);
return v___x_2468_;
}
else
{
lean_dec(v_fvarId_2463_);
return v___y_2467_;
}
}
v___jp_2469_:
{
if (lean_obj_tag(v___y_2470_) == 0)
{
lean_object* v___x_2471_; 
lean_dec_ref(v___y_2470_);
v___x_2471_ = l_Lean_Compiler_LCNF_Check_Impure_addOwned___redArg(v_fvarId_2463_, v_a_2457_);
return v___x_2471_;
}
else
{
lean_dec(v_fvarId_2463_);
return v___y_2470_;
}
}
v___jp_2472_:
{
if (lean_obj_tag(v___y_2473_) == 0)
{
lean_object* v___x_2474_; 
lean_dec_ref(v___y_2473_);
v___x_2474_ = l_Lean_Compiler_LCNF_Check_Impure_addOwned___redArg(v_fvarId_2463_, v_a_2457_);
return v___x_2474_;
}
else
{
lean_dec(v_fvarId_2463_);
return v___y_2473_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Impure_checkLetDecl___boxed(lean_object* v_decl_2712_, lean_object* v_a_2713_, lean_object* v_a_2714_, lean_object* v_a_2715_, lean_object* v_a_2716_, lean_object* v_a_2717_, lean_object* v_a_2718_){
_start:
{
lean_object* v_res_2719_; 
v_res_2719_ = l_Lean_Compiler_LCNF_Check_Impure_checkLetDecl(v_decl_2712_, v_a_2713_, v_a_2714_, v_a_2715_, v_a_2716_, v_a_2717_);
lean_dec(v_a_2717_);
lean_dec_ref(v_a_2716_);
lean_dec(v_a_2715_);
lean_dec_ref(v_a_2714_);
lean_dec(v_a_2713_);
return v_res_2719_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Check_Impure_check_spec__0_spec__2___redArg(lean_object* v_a_2720_, lean_object* v_b_2721_, lean_object* v_x_2722_){
_start:
{
if (lean_obj_tag(v_x_2722_) == 0)
{
lean_dec(v_b_2721_);
lean_dec(v_a_2720_);
return v_x_2722_;
}
else
{
lean_object* v_key_2723_; lean_object* v_value_2724_; lean_object* v_tail_2725_; lean_object* v___x_2727_; uint8_t v_isShared_2728_; uint8_t v_isSharedCheck_2737_; 
v_key_2723_ = lean_ctor_get(v_x_2722_, 0);
v_value_2724_ = lean_ctor_get(v_x_2722_, 1);
v_tail_2725_ = lean_ctor_get(v_x_2722_, 2);
v_isSharedCheck_2737_ = !lean_is_exclusive(v_x_2722_);
if (v_isSharedCheck_2737_ == 0)
{
v___x_2727_ = v_x_2722_;
v_isShared_2728_ = v_isSharedCheck_2737_;
goto v_resetjp_2726_;
}
else
{
lean_inc(v_tail_2725_);
lean_inc(v_value_2724_);
lean_inc(v_key_2723_);
lean_dec(v_x_2722_);
v___x_2727_ = lean_box(0);
v_isShared_2728_ = v_isSharedCheck_2737_;
goto v_resetjp_2726_;
}
v_resetjp_2726_:
{
uint8_t v___x_2729_; 
v___x_2729_ = l_Lean_instBEqFVarId_beq(v_key_2723_, v_a_2720_);
if (v___x_2729_ == 0)
{
lean_object* v___x_2730_; lean_object* v___x_2732_; 
v___x_2730_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Check_Impure_check_spec__0_spec__2___redArg(v_a_2720_, v_b_2721_, v_tail_2725_);
if (v_isShared_2728_ == 0)
{
lean_ctor_set(v___x_2727_, 2, v___x_2730_);
v___x_2732_ = v___x_2727_;
goto v_reusejp_2731_;
}
else
{
lean_object* v_reuseFailAlloc_2733_; 
v_reuseFailAlloc_2733_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2733_, 0, v_key_2723_);
lean_ctor_set(v_reuseFailAlloc_2733_, 1, v_value_2724_);
lean_ctor_set(v_reuseFailAlloc_2733_, 2, v___x_2730_);
v___x_2732_ = v_reuseFailAlloc_2733_;
goto v_reusejp_2731_;
}
v_reusejp_2731_:
{
return v___x_2732_;
}
}
else
{
lean_object* v___x_2735_; 
lean_dec(v_value_2724_);
lean_dec(v_key_2723_);
if (v_isShared_2728_ == 0)
{
lean_ctor_set(v___x_2727_, 1, v_b_2721_);
lean_ctor_set(v___x_2727_, 0, v_a_2720_);
v___x_2735_ = v___x_2727_;
goto v_reusejp_2734_;
}
else
{
lean_object* v_reuseFailAlloc_2736_; 
v_reuseFailAlloc_2736_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2736_, 0, v_a_2720_);
lean_ctor_set(v_reuseFailAlloc_2736_, 1, v_b_2721_);
lean_ctor_set(v_reuseFailAlloc_2736_, 2, v_tail_2725_);
v___x_2735_ = v_reuseFailAlloc_2736_;
goto v_reusejp_2734_;
}
v_reusejp_2734_:
{
return v___x_2735_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Check_Impure_check_spec__0_spec__0___redArg(lean_object* v_a_2738_, lean_object* v_x_2739_){
_start:
{
if (lean_obj_tag(v_x_2739_) == 0)
{
uint8_t v___x_2740_; 
v___x_2740_ = 0;
return v___x_2740_;
}
else
{
lean_object* v_key_2741_; lean_object* v_tail_2742_; uint8_t v___x_2743_; 
v_key_2741_ = lean_ctor_get(v_x_2739_, 0);
v_tail_2742_ = lean_ctor_get(v_x_2739_, 2);
v___x_2743_ = l_Lean_instBEqFVarId_beq(v_key_2741_, v_a_2738_);
if (v___x_2743_ == 0)
{
v_x_2739_ = v_tail_2742_;
goto _start;
}
else
{
return v___x_2743_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Check_Impure_check_spec__0_spec__0___redArg___boxed(lean_object* v_a_2745_, lean_object* v_x_2746_){
_start:
{
uint8_t v_res_2747_; lean_object* v_r_2748_; 
v_res_2747_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Check_Impure_check_spec__0_spec__0___redArg(v_a_2745_, v_x_2746_);
lean_dec(v_x_2746_);
lean_dec(v_a_2745_);
v_r_2748_ = lean_box(v_res_2747_);
return v_r_2748_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Check_Impure_check_spec__0_spec__1_spec__2_spec__5___redArg(lean_object* v_x_2749_, lean_object* v_x_2750_){
_start:
{
if (lean_obj_tag(v_x_2750_) == 0)
{
return v_x_2749_;
}
else
{
lean_object* v_key_2751_; lean_object* v_value_2752_; lean_object* v_tail_2753_; lean_object* v___x_2755_; uint8_t v_isShared_2756_; uint8_t v_isSharedCheck_2776_; 
v_key_2751_ = lean_ctor_get(v_x_2750_, 0);
v_value_2752_ = lean_ctor_get(v_x_2750_, 1);
v_tail_2753_ = lean_ctor_get(v_x_2750_, 2);
v_isSharedCheck_2776_ = !lean_is_exclusive(v_x_2750_);
if (v_isSharedCheck_2776_ == 0)
{
v___x_2755_ = v_x_2750_;
v_isShared_2756_ = v_isSharedCheck_2776_;
goto v_resetjp_2754_;
}
else
{
lean_inc(v_tail_2753_);
lean_inc(v_value_2752_);
lean_inc(v_key_2751_);
lean_dec(v_x_2750_);
v___x_2755_ = lean_box(0);
v_isShared_2756_ = v_isSharedCheck_2776_;
goto v_resetjp_2754_;
}
v_resetjp_2754_:
{
lean_object* v___x_2757_; uint64_t v___x_2758_; uint64_t v___x_2759_; uint64_t v___x_2760_; uint64_t v_fold_2761_; uint64_t v___x_2762_; uint64_t v___x_2763_; uint64_t v___x_2764_; size_t v___x_2765_; size_t v___x_2766_; size_t v___x_2767_; size_t v___x_2768_; size_t v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2772_; 
v___x_2757_ = lean_array_get_size(v_x_2749_);
v___x_2758_ = l_Lean_instHashableFVarId_hash(v_key_2751_);
v___x_2759_ = 32ULL;
v___x_2760_ = lean_uint64_shift_right(v___x_2758_, v___x_2759_);
v_fold_2761_ = lean_uint64_xor(v___x_2758_, v___x_2760_);
v___x_2762_ = 16ULL;
v___x_2763_ = lean_uint64_shift_right(v_fold_2761_, v___x_2762_);
v___x_2764_ = lean_uint64_xor(v_fold_2761_, v___x_2763_);
v___x_2765_ = lean_uint64_to_usize(v___x_2764_);
v___x_2766_ = lean_usize_of_nat(v___x_2757_);
v___x_2767_ = ((size_t)1ULL);
v___x_2768_ = lean_usize_sub(v___x_2766_, v___x_2767_);
v___x_2769_ = lean_usize_land(v___x_2765_, v___x_2768_);
v___x_2770_ = lean_array_uget_borrowed(v_x_2749_, v___x_2769_);
lean_inc(v___x_2770_);
if (v_isShared_2756_ == 0)
{
lean_ctor_set(v___x_2755_, 2, v___x_2770_);
v___x_2772_ = v___x_2755_;
goto v_reusejp_2771_;
}
else
{
lean_object* v_reuseFailAlloc_2775_; 
v_reuseFailAlloc_2775_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2775_, 0, v_key_2751_);
lean_ctor_set(v_reuseFailAlloc_2775_, 1, v_value_2752_);
lean_ctor_set(v_reuseFailAlloc_2775_, 2, v___x_2770_);
v___x_2772_ = v_reuseFailAlloc_2775_;
goto v_reusejp_2771_;
}
v_reusejp_2771_:
{
lean_object* v___x_2773_; 
v___x_2773_ = lean_array_uset(v_x_2749_, v___x_2769_, v___x_2772_);
v_x_2749_ = v___x_2773_;
v_x_2750_ = v_tail_2753_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Check_Impure_check_spec__0_spec__1_spec__2___redArg(lean_object* v_i_2777_, lean_object* v_source_2778_, lean_object* v_target_2779_){
_start:
{
lean_object* v___x_2780_; uint8_t v___x_2781_; 
v___x_2780_ = lean_array_get_size(v_source_2778_);
v___x_2781_ = lean_nat_dec_lt(v_i_2777_, v___x_2780_);
if (v___x_2781_ == 0)
{
lean_dec_ref(v_source_2778_);
lean_dec(v_i_2777_);
return v_target_2779_;
}
else
{
lean_object* v_es_2782_; lean_object* v___x_2783_; lean_object* v_source_2784_; lean_object* v_target_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; 
v_es_2782_ = lean_array_fget(v_source_2778_, v_i_2777_);
v___x_2783_ = lean_box(0);
v_source_2784_ = lean_array_fset(v_source_2778_, v_i_2777_, v___x_2783_);
v_target_2785_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Check_Impure_check_spec__0_spec__1_spec__2_spec__5___redArg(v_target_2779_, v_es_2782_);
v___x_2786_ = lean_unsigned_to_nat(1u);
v___x_2787_ = lean_nat_add(v_i_2777_, v___x_2786_);
lean_dec(v_i_2777_);
v_i_2777_ = v___x_2787_;
v_source_2778_ = v_source_2784_;
v_target_2779_ = v_target_2785_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Check_Impure_check_spec__0_spec__1___redArg(lean_object* v_data_2789_){
_start:
{
lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v_nbuckets_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; 
v___x_2790_ = lean_array_get_size(v_data_2789_);
v___x_2791_ = lean_unsigned_to_nat(2u);
v_nbuckets_2792_ = lean_nat_mul(v___x_2790_, v___x_2791_);
v___x_2793_ = lean_unsigned_to_nat(0u);
v___x_2794_ = lean_box(0);
v___x_2795_ = lean_mk_array(v_nbuckets_2792_, v___x_2794_);
v___x_2796_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Check_Impure_check_spec__0_spec__1_spec__2___redArg(v___x_2793_, v_data_2789_, v___x_2795_);
return v___x_2796_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Check_Impure_check_spec__0___redArg(lean_object* v_m_2797_, lean_object* v_a_2798_, lean_object* v_b_2799_){
_start:
{
lean_object* v_size_2800_; lean_object* v_buckets_2801_; lean_object* v___x_2803_; uint8_t v_isShared_2804_; uint8_t v_isSharedCheck_2844_; 
v_size_2800_ = lean_ctor_get(v_m_2797_, 0);
v_buckets_2801_ = lean_ctor_get(v_m_2797_, 1);
v_isSharedCheck_2844_ = !lean_is_exclusive(v_m_2797_);
if (v_isSharedCheck_2844_ == 0)
{
v___x_2803_ = v_m_2797_;
v_isShared_2804_ = v_isSharedCheck_2844_;
goto v_resetjp_2802_;
}
else
{
lean_inc(v_buckets_2801_);
lean_inc(v_size_2800_);
lean_dec(v_m_2797_);
v___x_2803_ = lean_box(0);
v_isShared_2804_ = v_isSharedCheck_2844_;
goto v_resetjp_2802_;
}
v_resetjp_2802_:
{
lean_object* v___x_2805_; uint64_t v___x_2806_; uint64_t v___x_2807_; uint64_t v___x_2808_; uint64_t v_fold_2809_; uint64_t v___x_2810_; uint64_t v___x_2811_; uint64_t v___x_2812_; size_t v___x_2813_; size_t v___x_2814_; size_t v___x_2815_; size_t v___x_2816_; size_t v___x_2817_; lean_object* v_bkt_2818_; uint8_t v___x_2819_; 
v___x_2805_ = lean_array_get_size(v_buckets_2801_);
v___x_2806_ = l_Lean_instHashableFVarId_hash(v_a_2798_);
v___x_2807_ = 32ULL;
v___x_2808_ = lean_uint64_shift_right(v___x_2806_, v___x_2807_);
v_fold_2809_ = lean_uint64_xor(v___x_2806_, v___x_2808_);
v___x_2810_ = 16ULL;
v___x_2811_ = lean_uint64_shift_right(v_fold_2809_, v___x_2810_);
v___x_2812_ = lean_uint64_xor(v_fold_2809_, v___x_2811_);
v___x_2813_ = lean_uint64_to_usize(v___x_2812_);
v___x_2814_ = lean_usize_of_nat(v___x_2805_);
v___x_2815_ = ((size_t)1ULL);
v___x_2816_ = lean_usize_sub(v___x_2814_, v___x_2815_);
v___x_2817_ = lean_usize_land(v___x_2813_, v___x_2816_);
v_bkt_2818_ = lean_array_uget_borrowed(v_buckets_2801_, v___x_2817_);
v___x_2819_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Check_Impure_check_spec__0_spec__0___redArg(v_a_2798_, v_bkt_2818_);
if (v___x_2819_ == 0)
{
lean_object* v___x_2820_; lean_object* v_size_x27_2821_; lean_object* v___x_2822_; lean_object* v_buckets_x27_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; uint8_t v___x_2829_; 
v___x_2820_ = lean_unsigned_to_nat(1u);
v_size_x27_2821_ = lean_nat_add(v_size_2800_, v___x_2820_);
lean_dec(v_size_2800_);
lean_inc(v_bkt_2818_);
v___x_2822_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2822_, 0, v_a_2798_);
lean_ctor_set(v___x_2822_, 1, v_b_2799_);
lean_ctor_set(v___x_2822_, 2, v_bkt_2818_);
v_buckets_x27_2823_ = lean_array_uset(v_buckets_2801_, v___x_2817_, v___x_2822_);
v___x_2824_ = lean_unsigned_to_nat(4u);
v___x_2825_ = lean_nat_mul(v_size_x27_2821_, v___x_2824_);
v___x_2826_ = lean_unsigned_to_nat(3u);
v___x_2827_ = lean_nat_div(v___x_2825_, v___x_2826_);
lean_dec(v___x_2825_);
v___x_2828_ = lean_array_get_size(v_buckets_x27_2823_);
v___x_2829_ = lean_nat_dec_le(v___x_2827_, v___x_2828_);
lean_dec(v___x_2827_);
if (v___x_2829_ == 0)
{
lean_object* v_val_2830_; lean_object* v___x_2832_; 
v_val_2830_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Check_Impure_check_spec__0_spec__1___redArg(v_buckets_x27_2823_);
if (v_isShared_2804_ == 0)
{
lean_ctor_set(v___x_2803_, 1, v_val_2830_);
lean_ctor_set(v___x_2803_, 0, v_size_x27_2821_);
v___x_2832_ = v___x_2803_;
goto v_reusejp_2831_;
}
else
{
lean_object* v_reuseFailAlloc_2833_; 
v_reuseFailAlloc_2833_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2833_, 0, v_size_x27_2821_);
lean_ctor_set(v_reuseFailAlloc_2833_, 1, v_val_2830_);
v___x_2832_ = v_reuseFailAlloc_2833_;
goto v_reusejp_2831_;
}
v_reusejp_2831_:
{
return v___x_2832_;
}
}
else
{
lean_object* v___x_2835_; 
if (v_isShared_2804_ == 0)
{
lean_ctor_set(v___x_2803_, 1, v_buckets_x27_2823_);
lean_ctor_set(v___x_2803_, 0, v_size_x27_2821_);
v___x_2835_ = v___x_2803_;
goto v_reusejp_2834_;
}
else
{
lean_object* v_reuseFailAlloc_2836_; 
v_reuseFailAlloc_2836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2836_, 0, v_size_x27_2821_);
lean_ctor_set(v_reuseFailAlloc_2836_, 1, v_buckets_x27_2823_);
v___x_2835_ = v_reuseFailAlloc_2836_;
goto v_reusejp_2834_;
}
v_reusejp_2834_:
{
return v___x_2835_;
}
}
}
else
{
lean_object* v___x_2837_; lean_object* v_buckets_x27_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2842_; 
lean_inc(v_bkt_2818_);
v___x_2837_ = lean_box(0);
v_buckets_x27_2838_ = lean_array_uset(v_buckets_2801_, v___x_2817_, v___x_2837_);
v___x_2839_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Check_Impure_check_spec__0_spec__2___redArg(v_a_2798_, v_b_2799_, v_bkt_2818_);
v___x_2840_ = lean_array_uset(v_buckets_x27_2838_, v___x_2817_, v___x_2839_);
if (v_isShared_2804_ == 0)
{
lean_ctor_set(v___x_2803_, 1, v___x_2840_);
v___x_2842_ = v___x_2803_;
goto v_reusejp_2841_;
}
else
{
lean_object* v_reuseFailAlloc_2843_; 
v_reuseFailAlloc_2843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2843_, 0, v_size_2800_);
lean_ctor_set(v_reuseFailAlloc_2843_, 1, v___x_2840_);
v___x_2842_ = v_reuseFailAlloc_2843_;
goto v_reusejp_2841_;
}
v_reusejp_2841_:
{
return v___x_2842_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Impure_check_spec__1___redArg(lean_object* v_as_2845_, size_t v_sz_2846_, size_t v_i_2847_, lean_object* v_b_2848_, lean_object* v___y_2849_){
_start:
{
uint8_t v___x_2851_; 
v___x_2851_ = lean_usize_dec_lt(v_i_2847_, v_sz_2846_);
if (v___x_2851_ == 0)
{
lean_object* v___x_2852_; 
v___x_2852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2852_, 0, v_b_2848_);
return v___x_2852_;
}
else
{
lean_object* v_array_2853_; lean_object* v_start_2854_; lean_object* v_stop_2855_; uint8_t v___x_2856_; 
v_array_2853_ = lean_ctor_get(v_b_2848_, 0);
v_start_2854_ = lean_ctor_get(v_b_2848_, 1);
v_stop_2855_ = lean_ctor_get(v_b_2848_, 2);
v___x_2856_ = lean_nat_dec_lt(v_start_2854_, v_stop_2855_);
if (v___x_2856_ == 0)
{
lean_object* v___x_2857_; 
v___x_2857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2857_, 0, v_b_2848_);
return v___x_2857_;
}
else
{
lean_object* v___x_2859_; uint8_t v_isShared_2860_; uint8_t v_isSharedCheck_2898_; 
lean_inc(v_stop_2855_);
lean_inc(v_start_2854_);
lean_inc_ref(v_array_2853_);
v_isSharedCheck_2898_ = !lean_is_exclusive(v_b_2848_);
if (v_isSharedCheck_2898_ == 0)
{
lean_object* v_unused_2899_; lean_object* v_unused_2900_; lean_object* v_unused_2901_; 
v_unused_2899_ = lean_ctor_get(v_b_2848_, 2);
lean_dec(v_unused_2899_);
v_unused_2900_ = lean_ctor_get(v_b_2848_, 1);
lean_dec(v_unused_2900_);
v_unused_2901_ = lean_ctor_get(v_b_2848_, 0);
lean_dec(v_unused_2901_);
v___x_2859_ = v_b_2848_;
v_isShared_2860_ = v_isSharedCheck_2898_;
goto v_resetjp_2858_;
}
else
{
lean_dec(v_b_2848_);
v___x_2859_ = lean_box(0);
v_isShared_2860_ = v_isSharedCheck_2898_;
goto v_resetjp_2858_;
}
v_resetjp_2858_:
{
lean_object* v_a_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2866_; 
v_a_2861_ = lean_array_uget_borrowed(v_as_2845_, v_i_2847_);
v___x_2862_ = lean_array_fget(v_array_2853_, v_start_2854_);
v___x_2863_ = lean_unsigned_to_nat(1u);
v___x_2864_ = lean_nat_add(v_start_2854_, v___x_2863_);
lean_dec(v_start_2854_);
if (v_isShared_2860_ == 0)
{
lean_ctor_set(v___x_2859_, 1, v___x_2864_);
v___x_2866_ = v___x_2859_;
goto v_reusejp_2865_;
}
else
{
lean_object* v_reuseFailAlloc_2897_; 
v_reuseFailAlloc_2897_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2897_, 0, v_array_2853_);
lean_ctor_set(v_reuseFailAlloc_2897_, 1, v___x_2864_);
lean_ctor_set(v_reuseFailAlloc_2897_, 2, v_stop_2855_);
v___x_2866_ = v_reuseFailAlloc_2897_;
goto v_reusejp_2865_;
}
v_reusejp_2865_:
{
lean_object* v_substArg_2868_; lean_object* v___y_2869_; 
if (lean_obj_tag(v___x_2862_) == 0)
{
v_substArg_2868_ = v___x_2862_;
v___y_2869_ = v___y_2849_;
goto v___jp_2867_;
}
else
{
lean_object* v_fvarId_2886_; lean_object* v___x_2888_; uint8_t v_isShared_2889_; uint8_t v_isSharedCheck_2896_; 
v_fvarId_2886_ = lean_ctor_get(v___x_2862_, 0);
v_isSharedCheck_2896_ = !lean_is_exclusive(v___x_2862_);
if (v_isSharedCheck_2896_ == 0)
{
v___x_2888_ = v___x_2862_;
v_isShared_2889_ = v_isSharedCheck_2896_;
goto v_resetjp_2887_;
}
else
{
lean_inc(v_fvarId_2886_);
lean_dec(v___x_2862_);
v___x_2888_ = lean_box(0);
v_isShared_2889_ = v_isSharedCheck_2896_;
goto v_resetjp_2887_;
}
v_resetjp_2887_:
{
lean_object* v___x_2890_; lean_object* v_subst_2891_; lean_object* v___x_2893_; 
v___x_2890_ = lean_st_ref_get(v___y_2849_);
v_subst_2891_ = lean_ctor_get(v___x_2890_, 1);
lean_inc_ref(v_subst_2891_);
lean_dec(v___x_2890_);
lean_inc(v_fvarId_2886_);
if (v_isShared_2889_ == 0)
{
v___x_2893_ = v___x_2888_;
goto v_reusejp_2892_;
}
else
{
lean_object* v_reuseFailAlloc_2895_; 
v_reuseFailAlloc_2895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2895_, 0, v_fvarId_2886_);
v___x_2893_ = v_reuseFailAlloc_2895_;
goto v_reusejp_2892_;
}
v_reusejp_2892_:
{
lean_object* v___x_2894_; 
v___x_2894_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_Check_Impure_kill_spec__0___redArg(v_subst_2891_, v_fvarId_2886_, v___x_2893_);
lean_dec_ref(v___x_2893_);
lean_dec(v_fvarId_2886_);
lean_dec_ref(v_subst_2891_);
v_substArg_2868_ = v___x_2894_;
v___y_2869_ = v___y_2849_;
goto v___jp_2867_;
}
}
}
v___jp_2867_:
{
lean_object* v___x_2870_; lean_object* v_rc_2871_; lean_object* v_subst_2872_; lean_object* v___x_2874_; uint8_t v_isShared_2875_; uint8_t v_isSharedCheck_2885_; 
v___x_2870_ = lean_st_ref_take(v___y_2869_);
v_rc_2871_ = lean_ctor_get(v___x_2870_, 0);
v_subst_2872_ = lean_ctor_get(v___x_2870_, 1);
v_isSharedCheck_2885_ = !lean_is_exclusive(v___x_2870_);
if (v_isSharedCheck_2885_ == 0)
{
v___x_2874_ = v___x_2870_;
v_isShared_2875_ = v_isSharedCheck_2885_;
goto v_resetjp_2873_;
}
else
{
lean_inc(v_subst_2872_);
lean_inc(v_rc_2871_);
lean_dec(v___x_2870_);
v___x_2874_ = lean_box(0);
v_isShared_2875_ = v_isSharedCheck_2885_;
goto v_resetjp_2873_;
}
v_resetjp_2873_:
{
lean_object* v_fvarId_2876_; lean_object* v___x_2877_; lean_object* v___x_2879_; 
v_fvarId_2876_ = lean_ctor_get(v_a_2861_, 0);
lean_inc(v_fvarId_2876_);
v___x_2877_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Check_Impure_check_spec__0___redArg(v_subst_2872_, v_fvarId_2876_, v_substArg_2868_);
if (v_isShared_2875_ == 0)
{
lean_ctor_set(v___x_2874_, 1, v___x_2877_);
v___x_2879_ = v___x_2874_;
goto v_reusejp_2878_;
}
else
{
lean_object* v_reuseFailAlloc_2884_; 
v_reuseFailAlloc_2884_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2884_, 0, v_rc_2871_);
lean_ctor_set(v_reuseFailAlloc_2884_, 1, v___x_2877_);
v___x_2879_ = v_reuseFailAlloc_2884_;
goto v_reusejp_2878_;
}
v_reusejp_2878_:
{
lean_object* v___x_2880_; size_t v___x_2881_; size_t v___x_2882_; 
v___x_2880_ = lean_st_ref_set(v___y_2869_, v___x_2879_);
v___x_2881_ = ((size_t)1ULL);
v___x_2882_ = lean_usize_add(v_i_2847_, v___x_2881_);
v_i_2847_ = v___x_2882_;
v_b_2848_ = v___x_2866_;
goto _start;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Impure_check_spec__1___redArg___boxed(lean_object* v_as_2902_, lean_object* v_sz_2903_, lean_object* v_i_2904_, lean_object* v_b_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_){
_start:
{
size_t v_sz_boxed_2908_; size_t v_i_boxed_2909_; lean_object* v_res_2910_; 
v_sz_boxed_2908_ = lean_unbox_usize(v_sz_2903_);
lean_dec(v_sz_2903_);
v_i_boxed_2909_ = lean_unbox_usize(v_i_2904_);
lean_dec(v_i_2904_);
v_res_2910_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Impure_check_spec__1___redArg(v_as_2902_, v_sz_boxed_2908_, v_i_boxed_2909_, v_b_2905_, v___y_2906_);
lean_dec(v___y_2906_);
lean_dec_ref(v_as_2902_);
return v_res_2910_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Check_Impure_check___closed__1(void){
_start:
{
lean_object* v___x_2912_; lean_object* v___x_2913_; 
v___x_2912_ = ((lean_object*)(l_Lean_Compiler_LCNF_Check_Impure_check___closed__0));
v___x_2913_ = l_Lean_stringToMessageData(v___x_2912_);
return v___x_2913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Impure_check(lean_object* v_c_2914_, lean_object* v_a_2915_, lean_object* v_a_2916_, lean_object* v_a_2917_, lean_object* v_a_2918_, lean_object* v_a_2919_){
_start:
{
switch(lean_obj_tag(v_c_2914_))
{
case 0:
{
lean_object* v_decl_2921_; lean_object* v_k_2922_; lean_object* v___x_2923_; 
v_decl_2921_ = lean_ctor_get(v_c_2914_, 0);
lean_inc_ref(v_decl_2921_);
v_k_2922_ = lean_ctor_get(v_c_2914_, 1);
lean_inc_ref(v_k_2922_);
lean_dec_ref(v_c_2914_);
lean_inc_ref(v_decl_2921_);
v___x_2923_ = l_Lean_Compiler_LCNF_Check_Impure_checkLetDecl(v_decl_2921_, v_a_2915_, v_a_2916_, v_a_2917_, v_a_2918_, v_a_2919_);
if (lean_obj_tag(v___x_2923_) == 0)
{
lean_object* v___x_2924_; lean_object* v_lctx_2925_; lean_object* v_nextIdx_2926_; lean_object* v___x_2928_; uint8_t v_isShared_2929_; uint8_t v_isSharedCheck_2937_; 
lean_dec_ref(v___x_2923_);
v___x_2924_ = lean_st_ref_take(v_a_2917_);
v_lctx_2925_ = lean_ctor_get(v___x_2924_, 0);
v_nextIdx_2926_ = lean_ctor_get(v___x_2924_, 1);
v_isSharedCheck_2937_ = !lean_is_exclusive(v___x_2924_);
if (v_isSharedCheck_2937_ == 0)
{
v___x_2928_ = v___x_2924_;
v_isShared_2929_ = v_isSharedCheck_2937_;
goto v_resetjp_2927_;
}
else
{
lean_inc(v_nextIdx_2926_);
lean_inc(v_lctx_2925_);
lean_dec(v___x_2924_);
v___x_2928_ = lean_box(0);
v_isShared_2929_ = v_isSharedCheck_2937_;
goto v_resetjp_2927_;
}
v_resetjp_2927_:
{
uint8_t v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2933_; 
v___x_2930_ = 1;
v___x_2931_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_2930_, v_lctx_2925_, v_decl_2921_);
if (v_isShared_2929_ == 0)
{
lean_ctor_set(v___x_2928_, 0, v___x_2931_);
v___x_2933_ = v___x_2928_;
goto v_reusejp_2932_;
}
else
{
lean_object* v_reuseFailAlloc_2936_; 
v_reuseFailAlloc_2936_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2936_, 0, v___x_2931_);
lean_ctor_set(v_reuseFailAlloc_2936_, 1, v_nextIdx_2926_);
v___x_2933_ = v_reuseFailAlloc_2936_;
goto v_reusejp_2932_;
}
v_reusejp_2932_:
{
lean_object* v___x_2934_; 
v___x_2934_ = lean_st_ref_set(v_a_2917_, v___x_2933_);
v_c_2914_ = v_k_2922_;
goto _start;
}
}
}
else
{
lean_dec_ref(v_k_2922_);
lean_dec_ref(v_decl_2921_);
return v___x_2923_;
}
}
case 2:
{
lean_object* v_decl_2938_; lean_object* v_k_2939_; lean_object* v___x_2940_; lean_object* v_lctx_2941_; lean_object* v_nextIdx_2942_; lean_object* v___x_2944_; uint8_t v_isShared_2945_; uint8_t v_isSharedCheck_2953_; 
v_decl_2938_ = lean_ctor_get(v_c_2914_, 0);
lean_inc_ref(v_decl_2938_);
v_k_2939_ = lean_ctor_get(v_c_2914_, 1);
lean_inc_ref(v_k_2939_);
lean_dec_ref(v_c_2914_);
v___x_2940_ = lean_st_ref_take(v_a_2917_);
v_lctx_2941_ = lean_ctor_get(v___x_2940_, 0);
v_nextIdx_2942_ = lean_ctor_get(v___x_2940_, 1);
v_isSharedCheck_2953_ = !lean_is_exclusive(v___x_2940_);
if (v_isSharedCheck_2953_ == 0)
{
v___x_2944_ = v___x_2940_;
v_isShared_2945_ = v_isSharedCheck_2953_;
goto v_resetjp_2943_;
}
else
{
lean_inc(v_nextIdx_2942_);
lean_inc(v_lctx_2941_);
lean_dec(v___x_2940_);
v___x_2944_ = lean_box(0);
v_isShared_2945_ = v_isSharedCheck_2953_;
goto v_resetjp_2943_;
}
v_resetjp_2943_:
{
uint8_t v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2949_; 
v___x_2946_ = 1;
v___x_2947_ = l_Lean_Compiler_LCNF_LCtx_addFunDecl(v___x_2946_, v_lctx_2941_, v_decl_2938_);
if (v_isShared_2945_ == 0)
{
lean_ctor_set(v___x_2944_, 0, v___x_2947_);
v___x_2949_ = v___x_2944_;
goto v_reusejp_2948_;
}
else
{
lean_object* v_reuseFailAlloc_2952_; 
v_reuseFailAlloc_2952_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2952_, 0, v___x_2947_);
lean_ctor_set(v_reuseFailAlloc_2952_, 1, v_nextIdx_2942_);
v___x_2949_ = v_reuseFailAlloc_2952_;
goto v_reusejp_2948_;
}
v_reusejp_2948_:
{
lean_object* v___x_2950_; 
v___x_2950_ = lean_st_ref_set(v_a_2917_, v___x_2949_);
v_c_2914_ = v_k_2939_;
goto _start;
}
}
}
case 3:
{
lean_object* v_fvarId_2954_; lean_object* v_args_2955_; lean_object* v___x_2957_; uint8_t v_isShared_2958_; uint8_t v_isSharedCheck_3010_; 
v_fvarId_2954_ = lean_ctor_get(v_c_2914_, 0);
v_args_2955_ = lean_ctor_get(v_c_2914_, 1);
v_isSharedCheck_3010_ = !lean_is_exclusive(v_c_2914_);
if (v_isSharedCheck_3010_ == 0)
{
v___x_2957_ = v_c_2914_;
v_isShared_2958_ = v_isSharedCheck_3010_;
goto v_resetjp_2956_;
}
else
{
lean_inc(v_args_2955_);
lean_inc(v_fvarId_2954_);
lean_dec(v_c_2914_);
v___x_2957_ = lean_box(0);
v_isShared_2958_ = v_isSharedCheck_3010_;
goto v_resetjp_2956_;
}
v_resetjp_2956_:
{
uint8_t v___x_2959_; lean_object* v___x_2960_; 
v___x_2959_ = 1;
v___x_2960_ = l_Lean_Compiler_LCNF_getFunDecl(v___x_2959_, v_fvarId_2954_, v_a_2916_, v_a_2917_, v_a_2918_, v_a_2919_);
if (lean_obj_tag(v___x_2960_) == 0)
{
lean_object* v_a_2961_; lean_object* v_params_2962_; lean_object* v_value_2963_; lean_object* v___y_2965_; lean_object* v___y_2966_; lean_object* v___y_2967_; lean_object* v___y_2968_; lean_object* v___y_2969_; lean_object* v___x_2985_; lean_object* v___x_2986_; uint8_t v___x_2987_; 
v_a_2961_ = lean_ctor_get(v___x_2960_, 0);
lean_inc(v_a_2961_);
lean_dec_ref(v___x_2960_);
v_params_2962_ = lean_ctor_get(v_a_2961_, 2);
lean_inc_ref(v_params_2962_);
v_value_2963_ = lean_ctor_get(v_a_2961_, 4);
lean_inc_ref(v_value_2963_);
lean_dec(v_a_2961_);
v___x_2985_ = lean_array_get_size(v_args_2955_);
v___x_2986_ = lean_array_get_size(v_params_2962_);
v___x_2987_ = lean_nat_dec_eq(v___x_2985_, v___x_2986_);
if (v___x_2987_ == 0)
{
lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2993_; 
v___x_2988_ = lean_obj_once(&l_Lean_Compiler_LCNF_Check_Impure_check___closed__1, &l_Lean_Compiler_LCNF_Check_Impure_check___closed__1_once, _init_l_Lean_Compiler_LCNF_Check_Impure_check___closed__1);
v___x_2989_ = l_Nat_reprFast(v___x_2986_);
v___x_2990_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2990_, 0, v___x_2989_);
v___x_2991_ = l_Lean_MessageData_ofFormat(v___x_2990_);
if (v_isShared_2958_ == 0)
{
lean_ctor_set_tag(v___x_2957_, 7);
lean_ctor_set(v___x_2957_, 1, v___x_2991_);
lean_ctor_set(v___x_2957_, 0, v___x_2988_);
v___x_2993_ = v___x_2957_;
goto v_reusejp_2992_;
}
else
{
lean_object* v_reuseFailAlloc_3001_; 
v_reuseFailAlloc_3001_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3001_, 0, v___x_2988_);
lean_ctor_set(v_reuseFailAlloc_3001_, 1, v___x_2991_);
v___x_2993_ = v_reuseFailAlloc_3001_;
goto v_reusejp_2992_;
}
v_reusejp_2992_:
{
lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; 
v___x_2994_ = lean_obj_once(&l_Lean_Compiler_LCNF_Check_Impure_checkLetDecl___closed__12, &l_Lean_Compiler_LCNF_Check_Impure_checkLetDecl___closed__12_once, _init_l_Lean_Compiler_LCNF_Check_Impure_checkLetDecl___closed__12);
v___x_2995_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2995_, 0, v___x_2993_);
lean_ctor_set(v___x_2995_, 1, v___x_2994_);
v___x_2996_ = l_Nat_reprFast(v___x_2985_);
v___x_2997_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2997_, 0, v___x_2996_);
v___x_2998_ = l_Lean_MessageData_ofFormat(v___x_2997_);
v___x_2999_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2999_, 0, v___x_2995_);
lean_ctor_set(v___x_2999_, 1, v___x_2998_);
v___x_3000_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Impure_kill_spec__1___redArg(v___x_2999_, v_a_2916_, v_a_2917_, v_a_2918_, v_a_2919_);
if (lean_obj_tag(v___x_3000_) == 0)
{
lean_dec_ref(v___x_3000_);
v___y_2965_ = v_a_2915_;
v___y_2966_ = v_a_2916_;
v___y_2967_ = v_a_2917_;
v___y_2968_ = v_a_2918_;
v___y_2969_ = v_a_2919_;
goto v___jp_2964_;
}
else
{
lean_dec_ref(v_value_2963_);
lean_dec_ref(v_params_2962_);
lean_dec_ref(v_args_2955_);
return v___x_3000_;
}
}
}
else
{
lean_del_object(v___x_2957_);
v___y_2965_ = v_a_2915_;
v___y_2966_ = v_a_2916_;
v___y_2967_ = v_a_2917_;
v___y_2968_ = v_a_2918_;
v___y_2969_ = v_a_2919_;
goto v___jp_2964_;
}
v___jp_2964_:
{
lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; size_t v_sz_2973_; size_t v___x_2974_; lean_object* v___x_2975_; 
v___x_2970_ = lean_array_get_size(v_args_2955_);
v___x_2971_ = lean_unsigned_to_nat(0u);
v___x_2972_ = l_Array_toSubarray___redArg(v_args_2955_, v___x_2971_, v___x_2970_);
v_sz_2973_ = lean_array_size(v_params_2962_);
v___x_2974_ = ((size_t)0ULL);
v___x_2975_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Impure_check_spec__1___redArg(v_params_2962_, v_sz_2973_, v___x_2974_, v___x_2972_, v___y_2965_);
lean_dec_ref(v_params_2962_);
if (lean_obj_tag(v___x_2975_) == 0)
{
lean_dec_ref(v___x_2975_);
v_c_2914_ = v_value_2963_;
v_a_2915_ = v___y_2965_;
v_a_2916_ = v___y_2966_;
v_a_2917_ = v___y_2967_;
v_a_2918_ = v___y_2968_;
v_a_2919_ = v___y_2969_;
goto _start;
}
else
{
lean_object* v_a_2977_; lean_object* v___x_2979_; uint8_t v_isShared_2980_; uint8_t v_isSharedCheck_2984_; 
lean_dec_ref(v_value_2963_);
v_a_2977_ = lean_ctor_get(v___x_2975_, 0);
v_isSharedCheck_2984_ = !lean_is_exclusive(v___x_2975_);
if (v_isSharedCheck_2984_ == 0)
{
v___x_2979_ = v___x_2975_;
v_isShared_2980_ = v_isSharedCheck_2984_;
goto v_resetjp_2978_;
}
else
{
lean_inc(v_a_2977_);
lean_dec(v___x_2975_);
v___x_2979_ = lean_box(0);
v_isShared_2980_ = v_isSharedCheck_2984_;
goto v_resetjp_2978_;
}
v_resetjp_2978_:
{
lean_object* v___x_2982_; 
if (v_isShared_2980_ == 0)
{
v___x_2982_ = v___x_2979_;
goto v_reusejp_2981_;
}
else
{
lean_object* v_reuseFailAlloc_2983_; 
v_reuseFailAlloc_2983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2983_, 0, v_a_2977_);
v___x_2982_ = v_reuseFailAlloc_2983_;
goto v_reusejp_2981_;
}
v_reusejp_2981_:
{
return v___x_2982_;
}
}
}
}
}
else
{
lean_object* v_a_3002_; lean_object* v___x_3004_; uint8_t v_isShared_3005_; uint8_t v_isSharedCheck_3009_; 
lean_del_object(v___x_2957_);
lean_dec_ref(v_args_2955_);
v_a_3002_ = lean_ctor_get(v___x_2960_, 0);
v_isSharedCheck_3009_ = !lean_is_exclusive(v___x_2960_);
if (v_isSharedCheck_3009_ == 0)
{
v___x_3004_ = v___x_2960_;
v_isShared_3005_ = v_isSharedCheck_3009_;
goto v_resetjp_3003_;
}
else
{
lean_inc(v_a_3002_);
lean_dec(v___x_2960_);
v___x_3004_ = lean_box(0);
v_isShared_3005_ = v_isSharedCheck_3009_;
goto v_resetjp_3003_;
}
v_resetjp_3003_:
{
lean_object* v___x_3007_; 
if (v_isShared_3005_ == 0)
{
v___x_3007_ = v___x_3004_;
goto v_reusejp_3006_;
}
else
{
lean_object* v_reuseFailAlloc_3008_; 
v_reuseFailAlloc_3008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3008_, 0, v_a_3002_);
v___x_3007_ = v_reuseFailAlloc_3008_;
goto v_reusejp_3006_;
}
v_reusejp_3006_:
{
return v___x_3007_;
}
}
}
}
}
case 4:
{
lean_object* v_cases_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v_discr_3014_; lean_object* v_alts_3015_; lean_object* v___x_3016_; 
v_cases_3011_ = lean_ctor_get(v_c_2914_, 0);
lean_inc_ref(v_cases_3011_);
lean_dec_ref(v_c_2914_);
v___x_3012_ = lean_st_ref_get(v_a_2917_);
v___x_3013_ = lean_st_ref_get(v_a_2915_);
v_discr_3014_ = lean_ctor_get(v_cases_3011_, 2);
lean_inc(v_discr_3014_);
v_alts_3015_ = lean_ctor_get(v_cases_3011_, 3);
lean_inc_ref(v_alts_3015_);
lean_dec_ref(v_cases_3011_);
lean_inc(v_discr_3014_);
v___x_3016_ = l_Lean_Compiler_LCNF_Check_Impure_useVar(v_discr_3014_, v_a_2915_, v_a_2916_, v_a_2917_, v_a_2918_, v_a_2919_);
if (lean_obj_tag(v___x_3016_) == 0)
{
lean_object* v_lctx_3017_; lean_object* v___x_3018_; size_t v_sz_3019_; size_t v___x_3020_; lean_object* v___x_3021_; 
lean_dec_ref(v___x_3016_);
v_lctx_3017_ = lean_ctor_get(v___x_3012_, 0);
lean_inc_ref(v_lctx_3017_);
lean_dec(v___x_3012_);
v___x_3018_ = lean_box(0);
v_sz_3019_ = lean_array_size(v_alts_3015_);
v___x_3020_ = ((size_t)0ULL);
v___x_3021_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Impure_check_spec__2(v_lctx_3017_, v___x_3013_, v_discr_3014_, v_alts_3015_, v_sz_3019_, v___x_3020_, v___x_3018_, v_a_2915_, v_a_2916_, v_a_2917_, v_a_2918_, v_a_2919_);
lean_dec_ref(v_alts_3015_);
if (lean_obj_tag(v___x_3021_) == 0)
{
lean_object* v___x_3023_; uint8_t v_isShared_3024_; uint8_t v_isSharedCheck_3028_; 
v_isSharedCheck_3028_ = !lean_is_exclusive(v___x_3021_);
if (v_isSharedCheck_3028_ == 0)
{
lean_object* v_unused_3029_; 
v_unused_3029_ = lean_ctor_get(v___x_3021_, 0);
lean_dec(v_unused_3029_);
v___x_3023_ = v___x_3021_;
v_isShared_3024_ = v_isSharedCheck_3028_;
goto v_resetjp_3022_;
}
else
{
lean_dec(v___x_3021_);
v___x_3023_ = lean_box(0);
v_isShared_3024_ = v_isSharedCheck_3028_;
goto v_resetjp_3022_;
}
v_resetjp_3022_:
{
lean_object* v___x_3026_; 
if (v_isShared_3024_ == 0)
{
lean_ctor_set(v___x_3023_, 0, v___x_3018_);
v___x_3026_ = v___x_3023_;
goto v_reusejp_3025_;
}
else
{
lean_object* v_reuseFailAlloc_3027_; 
v_reuseFailAlloc_3027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3027_, 0, v___x_3018_);
v___x_3026_ = v_reuseFailAlloc_3027_;
goto v_reusejp_3025_;
}
v_reusejp_3025_:
{
return v___x_3026_;
}
}
}
else
{
return v___x_3021_;
}
}
else
{
lean_dec_ref(v_alts_3015_);
lean_dec(v_discr_3014_);
lean_dec(v___x_3013_);
lean_dec(v___x_3012_);
return v___x_3016_;
}
}
case 5:
{
lean_object* v_fvarId_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; 
v_fvarId_3030_ = lean_ctor_get(v_c_2914_, 0);
lean_inc(v_fvarId_3030_);
lean_dec_ref(v_c_2914_);
v___x_3031_ = lean_unsigned_to_nat(1u);
v___x_3032_ = l_Lean_Compiler_LCNF_Check_Impure_consume(v_fvarId_3030_, v___x_3031_, v_a_2915_, v_a_2916_, v_a_2917_, v_a_2918_, v_a_2919_);
if (lean_obj_tag(v___x_3032_) == 0)
{
lean_object* v___x_3033_; 
lean_dec_ref(v___x_3032_);
v___x_3033_ = l_Lean_Compiler_LCNF_Check_Impure_checkLeaks(v_a_2915_, v_a_2916_, v_a_2917_, v_a_2918_, v_a_2919_);
return v___x_3033_;
}
else
{
return v___x_3032_;
}
}
case 6:
{
lean_object* v___x_3035_; uint8_t v_isShared_3036_; uint8_t v_isSharedCheck_3041_; 
v_isSharedCheck_3041_ = !lean_is_exclusive(v_c_2914_);
if (v_isSharedCheck_3041_ == 0)
{
lean_object* v_unused_3042_; 
v_unused_3042_ = lean_ctor_get(v_c_2914_, 0);
lean_dec(v_unused_3042_);
v___x_3035_ = v_c_2914_;
v_isShared_3036_ = v_isSharedCheck_3041_;
goto v_resetjp_3034_;
}
else
{
lean_dec(v_c_2914_);
v___x_3035_ = lean_box(0);
v_isShared_3036_ = v_isSharedCheck_3041_;
goto v_resetjp_3034_;
}
v_resetjp_3034_:
{
lean_object* v___x_3037_; lean_object* v___x_3039_; 
v___x_3037_ = lean_box(0);
if (v_isShared_3036_ == 0)
{
lean_ctor_set_tag(v___x_3035_, 0);
lean_ctor_set(v___x_3035_, 0, v___x_3037_);
v___x_3039_ = v___x_3035_;
goto v_reusejp_3038_;
}
else
{
lean_object* v_reuseFailAlloc_3040_; 
v_reuseFailAlloc_3040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3040_, 0, v___x_3037_);
v___x_3039_ = v_reuseFailAlloc_3040_;
goto v_reusejp_3038_;
}
v_reusejp_3038_:
{
return v___x_3039_;
}
}
}
case 7:
{
lean_object* v_fvarId_3043_; lean_object* v_y_3044_; lean_object* v_k_3045_; lean_object* v___x_3046_; 
v_fvarId_3043_ = lean_ctor_get(v_c_2914_, 0);
lean_inc(v_fvarId_3043_);
v_y_3044_ = lean_ctor_get(v_c_2914_, 2);
lean_inc(v_y_3044_);
v_k_3045_ = lean_ctor_get(v_c_2914_, 3);
lean_inc_ref(v_k_3045_);
lean_dec_ref(v_c_2914_);
v___x_3046_ = l_Lean_Compiler_LCNF_Check_Impure_checkShared(v_fvarId_3043_, v_a_2915_, v_a_2916_, v_a_2917_, v_a_2918_, v_a_2919_);
if (lean_obj_tag(v___x_3046_) == 0)
{
lean_object* v___x_3047_; 
lean_dec_ref(v___x_3046_);
v___x_3047_ = l_Lean_Compiler_LCNF_Check_Impure_useArg(v_y_3044_, v_a_2915_, v_a_2916_, v_a_2917_, v_a_2918_, v_a_2919_);
if (lean_obj_tag(v___x_3047_) == 0)
{
lean_dec_ref(v___x_3047_);
v_c_2914_ = v_k_3045_;
goto _start;
}
else
{
lean_dec_ref(v_k_3045_);
return v___x_3047_;
}
}
else
{
lean_dec_ref(v_k_3045_);
lean_dec(v_y_3044_);
return v___x_3046_;
}
}
case 8:
{
lean_object* v_fvarId_3049_; lean_object* v_k_3050_; lean_object* v___x_3051_; 
v_fvarId_3049_ = lean_ctor_get(v_c_2914_, 0);
lean_inc(v_fvarId_3049_);
v_k_3050_ = lean_ctor_get(v_c_2914_, 3);
lean_inc_ref(v_k_3050_);
lean_dec_ref(v_c_2914_);
v___x_3051_ = l_Lean_Compiler_LCNF_Check_Impure_checkShared(v_fvarId_3049_, v_a_2915_, v_a_2916_, v_a_2917_, v_a_2918_, v_a_2919_);
if (lean_obj_tag(v___x_3051_) == 0)
{
lean_dec_ref(v___x_3051_);
v_c_2914_ = v_k_3050_;
goto _start;
}
else
{
lean_dec_ref(v_k_3050_);
return v___x_3051_;
}
}
case 9:
{
lean_object* v_fvarId_3053_; lean_object* v_k_3054_; lean_object* v___x_3055_; 
v_fvarId_3053_ = lean_ctor_get(v_c_2914_, 0);
lean_inc(v_fvarId_3053_);
v_k_3054_ = lean_ctor_get(v_c_2914_, 5);
lean_inc_ref(v_k_3054_);
lean_dec_ref(v_c_2914_);
v___x_3055_ = l_Lean_Compiler_LCNF_Check_Impure_checkShared(v_fvarId_3053_, v_a_2915_, v_a_2916_, v_a_2917_, v_a_2918_, v_a_2919_);
if (lean_obj_tag(v___x_3055_) == 0)
{
lean_dec_ref(v___x_3055_);
v_c_2914_ = v_k_3054_;
goto _start;
}
else
{
lean_dec_ref(v_k_3054_);
return v___x_3055_;
}
}
case 10:
{
lean_object* v_fvarId_3057_; lean_object* v_k_3058_; lean_object* v___x_3059_; 
v_fvarId_3057_ = lean_ctor_get(v_c_2914_, 0);
lean_inc(v_fvarId_3057_);
v_k_3058_ = lean_ctor_get(v_c_2914_, 2);
lean_inc_ref(v_k_3058_);
lean_dec_ref(v_c_2914_);
v___x_3059_ = l_Lean_Compiler_LCNF_Check_Impure_checkShared(v_fvarId_3057_, v_a_2915_, v_a_2916_, v_a_2917_, v_a_2918_, v_a_2919_);
if (lean_obj_tag(v___x_3059_) == 0)
{
lean_dec_ref(v___x_3059_);
v_c_2914_ = v_k_3058_;
goto _start;
}
else
{
lean_dec_ref(v_k_3058_);
return v___x_3059_;
}
}
case 11:
{
lean_object* v_fvarId_3061_; lean_object* v_n_3062_; lean_object* v_k_3063_; lean_object* v___x_3064_; 
v_fvarId_3061_ = lean_ctor_get(v_c_2914_, 0);
lean_inc(v_fvarId_3061_);
v_n_3062_ = lean_ctor_get(v_c_2914_, 1);
lean_inc(v_n_3062_);
v_k_3063_ = lean_ctor_get(v_c_2914_, 2);
lean_inc_ref(v_k_3063_);
lean_dec_ref(v_c_2914_);
v___x_3064_ = l_Lean_Compiler_LCNF_Check_Impure_inc(v_fvarId_3061_, v_n_3062_, v_a_2915_, v_a_2916_, v_a_2917_, v_a_2918_, v_a_2919_);
lean_dec(v_n_3062_);
if (lean_obj_tag(v___x_3064_) == 0)
{
lean_dec_ref(v___x_3064_);
v_c_2914_ = v_k_3063_;
goto _start;
}
else
{
lean_dec_ref(v_k_3063_);
return v___x_3064_;
}
}
case 12:
{
lean_object* v_fvarId_3066_; lean_object* v_n_3067_; lean_object* v_k_3068_; lean_object* v___x_3069_; 
v_fvarId_3066_ = lean_ctor_get(v_c_2914_, 0);
lean_inc(v_fvarId_3066_);
v_n_3067_ = lean_ctor_get(v_c_2914_, 1);
lean_inc(v_n_3067_);
v_k_3068_ = lean_ctor_get(v_c_2914_, 2);
lean_inc_ref(v_k_3068_);
lean_dec_ref(v_c_2914_);
v___x_3069_ = l_Lean_Compiler_LCNF_Check_Impure_consume(v_fvarId_3066_, v_n_3067_, v_a_2915_, v_a_2916_, v_a_2917_, v_a_2918_, v_a_2919_);
if (lean_obj_tag(v___x_3069_) == 0)
{
lean_dec_ref(v___x_3069_);
v_c_2914_ = v_k_3068_;
goto _start;
}
else
{
lean_dec_ref(v_k_3068_);
return v___x_3069_;
}
}
default: 
{
lean_object* v_fvarId_3071_; lean_object* v_k_3072_; lean_object* v___x_3073_; 
v_fvarId_3071_ = lean_ctor_get(v_c_2914_, 0);
lean_inc(v_fvarId_3071_);
v_k_3072_ = lean_ctor_get(v_c_2914_, 1);
lean_inc_ref(v_k_3072_);
lean_dec_ref(v_c_2914_);
v___x_3073_ = l_Lean_Compiler_LCNF_Check_Impure_kill(v_fvarId_3071_, v_a_2915_, v_a_2916_, v_a_2917_, v_a_2918_, v_a_2919_);
if (lean_obj_tag(v___x_3073_) == 0)
{
lean_dec_ref(v___x_3073_);
v_c_2914_ = v_k_3072_;
goto _start;
}
else
{
lean_dec_ref(v_k_3072_);
return v___x_3073_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Impure_check_spec__2(lean_object* v___x_3075_, lean_object* v_val_3076_, lean_object* v_discr_3077_, lean_object* v_as_3078_, size_t v_sz_3079_, size_t v_i_3080_, lean_object* v_b_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_){
_start:
{
lean_object* v_a_3089_; uint8_t v___x_3093_; 
v___x_3093_ = lean_usize_dec_lt(v_i_3080_, v_sz_3079_);
if (v___x_3093_ == 0)
{
lean_object* v___x_3094_; 
lean_dec(v_discr_3077_);
lean_dec_ref(v_val_3076_);
lean_dec_ref(v___x_3075_);
v___x_3094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3094_, 0, v_b_3081_);
return v___x_3094_;
}
else
{
lean_object* v___x_3095_; lean_object* v_nextIdx_3096_; lean_object* v___x_3098_; uint8_t v_isShared_3099_; uint8_t v_isSharedCheck_3120_; 
v___x_3095_ = lean_st_ref_take(v___y_3084_);
v_nextIdx_3096_ = lean_ctor_get(v___x_3095_, 1);
v_isSharedCheck_3120_ = !lean_is_exclusive(v___x_3095_);
if (v_isSharedCheck_3120_ == 0)
{
lean_object* v_unused_3121_; 
v_unused_3121_ = lean_ctor_get(v___x_3095_, 0);
lean_dec(v_unused_3121_);
v___x_3098_ = v___x_3095_;
v_isShared_3099_ = v_isSharedCheck_3120_;
goto v_resetjp_3097_;
}
else
{
lean_inc(v_nextIdx_3096_);
lean_dec(v___x_3095_);
v___x_3098_ = lean_box(0);
v_isShared_3099_ = v_isSharedCheck_3120_;
goto v_resetjp_3097_;
}
v_resetjp_3097_:
{
lean_object* v___x_3101_; 
lean_inc_ref(v___x_3075_);
if (v_isShared_3099_ == 0)
{
lean_ctor_set(v___x_3098_, 0, v___x_3075_);
v___x_3101_ = v___x_3098_;
goto v_reusejp_3100_;
}
else
{
lean_object* v_reuseFailAlloc_3119_; 
v_reuseFailAlloc_3119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3119_, 0, v___x_3075_);
lean_ctor_set(v_reuseFailAlloc_3119_, 1, v_nextIdx_3096_);
v___x_3101_ = v_reuseFailAlloc_3119_;
goto v_reusejp_3100_;
}
v_reusejp_3100_:
{
lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v_a_3105_; 
v___x_3102_ = lean_st_ref_set(v___y_3084_, v___x_3101_);
lean_inc_ref(v_val_3076_);
v___x_3103_ = lean_st_ref_set(v___y_3082_, v_val_3076_);
v___x_3104_ = lean_box(0);
v_a_3105_ = lean_array_uget_borrowed(v_as_3078_, v_i_3080_);
if (lean_obj_tag(v_a_3105_) == 1)
{
lean_object* v_info_3106_; lean_object* v_code_3107_; lean_object* v___y_3109_; lean_object* v___y_3110_; lean_object* v___y_3111_; lean_object* v___y_3112_; lean_object* v___y_3113_; uint8_t v___x_3115_; 
v_info_3106_ = lean_ctor_get(v_a_3105_, 0);
v_code_3107_ = lean_ctor_get(v_a_3105_, 1);
v___x_3115_ = l_Lean_Compiler_LCNF_CtorInfo_isScalar(v_info_3106_);
if (v___x_3115_ == 0)
{
v___y_3109_ = v___y_3082_;
v___y_3110_ = v___y_3083_;
v___y_3111_ = v___y_3084_;
v___y_3112_ = v___y_3085_;
v___y_3113_ = v___y_3086_;
goto v___jp_3108_;
}
else
{
lean_object* v___x_3116_; 
lean_inc(v_discr_3077_);
v___x_3116_ = l_Lean_Compiler_LCNF_Check_Impure_makeScalar___redArg(v_discr_3077_, v___y_3082_);
if (lean_obj_tag(v___x_3116_) == 0)
{
lean_dec_ref(v___x_3116_);
v___y_3109_ = v___y_3082_;
v___y_3110_ = v___y_3083_;
v___y_3111_ = v___y_3084_;
v___y_3112_ = v___y_3085_;
v___y_3113_ = v___y_3086_;
goto v___jp_3108_;
}
else
{
lean_dec(v_discr_3077_);
lean_dec_ref(v_val_3076_);
lean_dec_ref(v___x_3075_);
return v___x_3116_;
}
}
v___jp_3108_:
{
lean_object* v___x_3114_; 
lean_inc_ref(v_code_3107_);
v___x_3114_ = l_Lean_Compiler_LCNF_Check_Impure_check(v_code_3107_, v___y_3109_, v___y_3110_, v___y_3111_, v___y_3112_, v___y_3113_);
if (lean_obj_tag(v___x_3114_) == 0)
{
lean_dec_ref(v___x_3114_);
v_a_3089_ = v___x_3104_;
goto v___jp_3088_;
}
else
{
lean_dec(v_discr_3077_);
lean_dec_ref(v_val_3076_);
lean_dec_ref(v___x_3075_);
return v___x_3114_;
}
}
}
else
{
lean_object* v_code_3117_; lean_object* v___x_3118_; 
v_code_3117_ = lean_ctor_get(v_a_3105_, 0);
lean_inc_ref(v_code_3117_);
v___x_3118_ = l_Lean_Compiler_LCNF_Check_Impure_check(v_code_3117_, v___y_3082_, v___y_3083_, v___y_3084_, v___y_3085_, v___y_3086_);
if (lean_obj_tag(v___x_3118_) == 0)
{
lean_dec_ref(v___x_3118_);
v_a_3089_ = v___x_3104_;
goto v___jp_3088_;
}
else
{
lean_dec(v_discr_3077_);
lean_dec_ref(v_val_3076_);
lean_dec_ref(v___x_3075_);
return v___x_3118_;
}
}
}
}
}
v___jp_3088_:
{
size_t v___x_3090_; size_t v___x_3091_; 
v___x_3090_ = ((size_t)1ULL);
v___x_3091_ = lean_usize_add(v_i_3080_, v___x_3090_);
v_i_3080_ = v___x_3091_;
v_b_3081_ = v_a_3089_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Impure_check_spec__2___boxed(lean_object* v___x_3122_, lean_object* v_val_3123_, lean_object* v_discr_3124_, lean_object* v_as_3125_, lean_object* v_sz_3126_, lean_object* v_i_3127_, lean_object* v_b_3128_, lean_object* v___y_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_){
_start:
{
size_t v_sz_boxed_3135_; size_t v_i_boxed_3136_; lean_object* v_res_3137_; 
v_sz_boxed_3135_ = lean_unbox_usize(v_sz_3126_);
lean_dec(v_sz_3126_);
v_i_boxed_3136_ = lean_unbox_usize(v_i_3127_);
lean_dec(v_i_3127_);
v_res_3137_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Impure_check_spec__2(v___x_3122_, v_val_3123_, v_discr_3124_, v_as_3125_, v_sz_boxed_3135_, v_i_boxed_3136_, v_b_3128_, v___y_3129_, v___y_3130_, v___y_3131_, v___y_3132_, v___y_3133_);
lean_dec(v___y_3133_);
lean_dec_ref(v___y_3132_);
lean_dec(v___y_3131_);
lean_dec_ref(v___y_3130_);
lean_dec(v___y_3129_);
lean_dec_ref(v_as_3125_);
return v_res_3137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Impure_check___boxed(lean_object* v_c_3138_, lean_object* v_a_3139_, lean_object* v_a_3140_, lean_object* v_a_3141_, lean_object* v_a_3142_, lean_object* v_a_3143_, lean_object* v_a_3144_){
_start:
{
lean_object* v_res_3145_; 
v_res_3145_ = l_Lean_Compiler_LCNF_Check_Impure_check(v_c_3138_, v_a_3139_, v_a_3140_, v_a_3141_, v_a_3142_, v_a_3143_);
lean_dec(v_a_3143_);
lean_dec_ref(v_a_3142_);
lean_dec(v_a_3141_);
lean_dec_ref(v_a_3140_);
lean_dec(v_a_3139_);
return v_res_3145_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Check_Impure_check_spec__0(lean_object* v_00_u03b2_3146_, lean_object* v_m_3147_, lean_object* v_a_3148_, lean_object* v_b_3149_){
_start:
{
lean_object* v___x_3150_; 
v___x_3150_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Check_Impure_check_spec__0___redArg(v_m_3147_, v_a_3148_, v_b_3149_);
return v___x_3150_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Impure_check_spec__1(lean_object* v_as_3151_, size_t v_sz_3152_, size_t v_i_3153_, lean_object* v_b_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_){
_start:
{
lean_object* v___x_3161_; 
v___x_3161_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Impure_check_spec__1___redArg(v_as_3151_, v_sz_3152_, v_i_3153_, v_b_3154_, v___y_3155_);
return v___x_3161_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Impure_check_spec__1___boxed(lean_object* v_as_3162_, lean_object* v_sz_3163_, lean_object* v_i_3164_, lean_object* v_b_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_){
_start:
{
size_t v_sz_boxed_3172_; size_t v_i_boxed_3173_; lean_object* v_res_3174_; 
v_sz_boxed_3172_ = lean_unbox_usize(v_sz_3163_);
lean_dec(v_sz_3163_);
v_i_boxed_3173_ = lean_unbox_usize(v_i_3164_);
lean_dec(v_i_3164_);
v_res_3174_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Impure_check_spec__1(v_as_3162_, v_sz_boxed_3172_, v_i_boxed_3173_, v_b_3165_, v___y_3166_, v___y_3167_, v___y_3168_, v___y_3169_, v___y_3170_);
lean_dec(v___y_3170_);
lean_dec_ref(v___y_3169_);
lean_dec(v___y_3168_);
lean_dec_ref(v___y_3167_);
lean_dec(v___y_3166_);
lean_dec_ref(v_as_3162_);
return v_res_3174_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Check_Impure_check_spec__0_spec__0(lean_object* v_00_u03b2_3175_, lean_object* v_a_3176_, lean_object* v_x_3177_){
_start:
{
uint8_t v___x_3178_; 
v___x_3178_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Check_Impure_check_spec__0_spec__0___redArg(v_a_3176_, v_x_3177_);
return v___x_3178_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Check_Impure_check_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3179_, lean_object* v_a_3180_, lean_object* v_x_3181_){
_start:
{
uint8_t v_res_3182_; lean_object* v_r_3183_; 
v_res_3182_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Check_Impure_check_spec__0_spec__0(v_00_u03b2_3179_, v_a_3180_, v_x_3181_);
lean_dec(v_x_3181_);
lean_dec(v_a_3180_);
v_r_3183_ = lean_box(v_res_3182_);
return v_r_3183_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Check_Impure_check_spec__0_spec__1(lean_object* v_00_u03b2_3184_, lean_object* v_data_3185_){
_start:
{
lean_object* v___x_3186_; 
v___x_3186_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Check_Impure_check_spec__0_spec__1___redArg(v_data_3185_);
return v___x_3186_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Check_Impure_check_spec__0_spec__2(lean_object* v_00_u03b2_3187_, lean_object* v_a_3188_, lean_object* v_b_3189_, lean_object* v_x_3190_){
_start:
{
lean_object* v___x_3191_; 
v___x_3191_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Check_Impure_check_spec__0_spec__2___redArg(v_a_3188_, v_b_3189_, v_x_3190_);
return v___x_3191_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Check_Impure_check_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_3192_, lean_object* v_i_3193_, lean_object* v_source_3194_, lean_object* v_target_3195_){
_start:
{
lean_object* v___x_3196_; 
v___x_3196_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Check_Impure_check_spec__0_spec__1_spec__2___redArg(v_i_3193_, v_source_3194_, v_target_3195_);
return v___x_3196_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Check_Impure_check_spec__0_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_3197_, lean_object* v_x_3198_, lean_object* v_x_3199_){
_start:
{
lean_object* v___x_3200_; 
v___x_3200_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Check_Impure_check_spec__0_spec__1_spec__2_spec__5___redArg(v_x_3198_, v_x_3199_);
return v___x_3200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Impure_addParam(lean_object* v_param_3203_, lean_object* v_a_3204_, lean_object* v_a_3205_, lean_object* v_a_3206_, lean_object* v_a_3207_, lean_object* v_a_3208_){
_start:
{
lean_object* v___x_3210_; lean_object* v_lctx_3211_; lean_object* v_nextIdx_3212_; lean_object* v___x_3214_; uint8_t v_isShared_3215_; uint8_t v_isSharedCheck_3231_; 
v___x_3210_ = lean_st_ref_take(v_a_3206_);
v_lctx_3211_ = lean_ctor_get(v___x_3210_, 0);
v_nextIdx_3212_ = lean_ctor_get(v___x_3210_, 1);
v_isSharedCheck_3231_ = !lean_is_exclusive(v___x_3210_);
if (v_isSharedCheck_3231_ == 0)
{
v___x_3214_ = v___x_3210_;
v_isShared_3215_ = v_isSharedCheck_3231_;
goto v_resetjp_3213_;
}
else
{
lean_inc(v_nextIdx_3212_);
lean_inc(v_lctx_3211_);
lean_dec(v___x_3210_);
v___x_3214_ = lean_box(0);
v_isShared_3215_ = v_isSharedCheck_3231_;
goto v_resetjp_3213_;
}
v_resetjp_3213_:
{
uint8_t v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3219_; 
v___x_3216_ = 1;
lean_inc_ref(v_param_3203_);
v___x_3217_ = l_Lean_Compiler_LCNF_LCtx_addParam(v___x_3216_, v_lctx_3211_, v_param_3203_);
if (v_isShared_3215_ == 0)
{
lean_ctor_set(v___x_3214_, 0, v___x_3217_);
v___x_3219_ = v___x_3214_;
goto v_reusejp_3218_;
}
else
{
lean_object* v_reuseFailAlloc_3230_; 
v_reuseFailAlloc_3230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3230_, 0, v___x_3217_);
lean_ctor_set(v_reuseFailAlloc_3230_, 1, v_nextIdx_3212_);
v___x_3219_ = v_reuseFailAlloc_3230_;
goto v_reusejp_3218_;
}
v_reusejp_3218_:
{
lean_object* v___x_3220_; lean_object* v_fvarId_3221_; lean_object* v_type_3222_; uint8_t v_borrow_3223_; uint8_t v___x_3224_; 
v___x_3220_ = lean_st_ref_set(v_a_3206_, v___x_3219_);
v_fvarId_3221_ = lean_ctor_get(v_param_3203_, 0);
lean_inc(v_fvarId_3221_);
v_type_3222_ = lean_ctor_get(v_param_3203_, 2);
lean_inc_ref(v_type_3222_);
v_borrow_3223_ = lean_ctor_get_uint8(v_param_3203_, sizeof(void*)*3);
lean_dec_ref(v_param_3203_);
v___x_3224_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isPossibleRef(v_type_3222_);
lean_dec_ref(v_type_3222_);
if (v___x_3224_ == 0)
{
lean_object* v___x_3225_; lean_object* v___x_3226_; 
lean_dec(v_fvarId_3221_);
v___x_3225_ = lean_box(0);
v___x_3226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3226_, 0, v___x_3225_);
return v___x_3226_;
}
else
{
if (v_borrow_3223_ == 0)
{
lean_object* v___x_3227_; 
v___x_3227_ = l_Lean_Compiler_LCNF_Check_Impure_addOwned___redArg(v_fvarId_3221_, v_a_3204_);
return v___x_3227_;
}
else
{
lean_object* v___x_3228_; lean_object* v___x_3229_; 
v___x_3228_ = ((lean_object*)(l_Lean_Compiler_LCNF_Check_Impure_addParam___closed__0));
v___x_3229_ = l_Lean_Compiler_LCNF_Check_Impure_addBorrowed(v_fvarId_3221_, v___x_3228_, v_a_3204_, v_a_3205_, v_a_3206_, v_a_3207_, v_a_3208_);
return v___x_3229_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Impure_addParam___boxed(lean_object* v_param_3232_, lean_object* v_a_3233_, lean_object* v_a_3234_, lean_object* v_a_3235_, lean_object* v_a_3236_, lean_object* v_a_3237_, lean_object* v_a_3238_){
_start:
{
lean_object* v_res_3239_; 
v_res_3239_ = l_Lean_Compiler_LCNF_Check_Impure_addParam(v_param_3232_, v_a_3233_, v_a_3234_, v_a_3235_, v_a_3236_, v_a_3237_);
lean_dec(v_a_3237_);
lean_dec_ref(v_a_3236_);
lean_dec(v_a_3235_);
lean_dec_ref(v_a_3234_);
lean_dec(v_a_3233_);
return v_res_3239_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Check_Impure_instReprParam_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_3249_; lean_object* v___x_3250_; 
v___x_3249_ = lean_unsigned_to_nat(10u);
v___x_3250_ = lean_nat_to_int(v___x_3249_);
return v___x_3250_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Check_Impure_instReprParam_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_3254_; lean_object* v___x_3255_; 
v___x_3254_ = lean_unsigned_to_nat(14u);
v___x_3255_ = lean_nat_to_int(v___x_3254_);
return v___x_3255_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Check_Impure_instReprParam_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_3259_; lean_object* v___x_3260_; 
v___x_3259_ = lean_unsigned_to_nat(8u);
v___x_3260_ = lean_nat_to_int(v___x_3259_);
return v___x_3260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Impure_instReprParam_repr___redArg(lean_object* v_x_3264_){
_start:
{
lean_object* v_fvarId_3265_; lean_object* v_binderName_3266_; lean_object* v_type_3267_; uint8_t v_borrow_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; uint8_t v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; 
v_fvarId_3265_ = lean_ctor_get(v_x_3264_, 0);
lean_inc(v_fvarId_3265_);
v_binderName_3266_ = lean_ctor_get(v_x_3264_, 1);
lean_inc(v_binderName_3266_);
v_type_3267_ = lean_ctor_get(v_x_3264_, 2);
lean_inc_ref(v_type_3267_);
v_borrow_3268_ = lean_ctor_get_uint8(v_x_3264_, sizeof(void*)*3);
lean_dec_ref(v_x_3264_);
v___x_3269_ = ((lean_object*)(l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr___redArg___closed__5));
v___x_3270_ = ((lean_object*)(l_Lean_Compiler_LCNF_Check_Impure_instReprParam_repr___redArg___closed__3));
v___x_3271_ = lean_obj_once(&l_Lean_Compiler_LCNF_Check_Impure_instReprParam_repr___redArg___closed__4, &l_Lean_Compiler_LCNF_Check_Impure_instReprParam_repr___redArg___closed__4_once, _init_l_Lean_Compiler_LCNF_Check_Impure_instReprParam_repr___redArg___closed__4);
v___x_3272_ = lean_unsigned_to_nat(0u);
v___x_3273_ = l_Lean_Name_reprPrec(v_fvarId_3265_, v___x_3272_);
v___x_3274_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3274_, 0, v___x_3271_);
lean_ctor_set(v___x_3274_, 1, v___x_3273_);
v___x_3275_ = 0;
v___x_3276_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3276_, 0, v___x_3274_);
lean_ctor_set_uint8(v___x_3276_, sizeof(void*)*1, v___x_3275_);
v___x_3277_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3277_, 0, v___x_3270_);
lean_ctor_set(v___x_3277_, 1, v___x_3276_);
v___x_3278_ = ((lean_object*)(l_Array_repr___at___00Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr_spec__0___closed__2));
v___x_3279_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3279_, 0, v___x_3277_);
lean_ctor_set(v___x_3279_, 1, v___x_3278_);
v___x_3280_ = lean_box(1);
v___x_3281_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3281_, 0, v___x_3279_);
lean_ctor_set(v___x_3281_, 1, v___x_3280_);
v___x_3282_ = ((lean_object*)(l_Lean_Compiler_LCNF_Check_Impure_instReprParam_repr___redArg___closed__6));
v___x_3283_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3283_, 0, v___x_3281_);
lean_ctor_set(v___x_3283_, 1, v___x_3282_);
v___x_3284_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3284_, 0, v___x_3283_);
lean_ctor_set(v___x_3284_, 1, v___x_3269_);
v___x_3285_ = lean_obj_once(&l_Lean_Compiler_LCNF_Check_Impure_instReprParam_repr___redArg___closed__7, &l_Lean_Compiler_LCNF_Check_Impure_instReprParam_repr___redArg___closed__7_once, _init_l_Lean_Compiler_LCNF_Check_Impure_instReprParam_repr___redArg___closed__7);
v___x_3286_ = l_Lean_Name_reprPrec(v_binderName_3266_, v___x_3272_);
v___x_3287_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3287_, 0, v___x_3285_);
lean_ctor_set(v___x_3287_, 1, v___x_3286_);
v___x_3288_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3288_, 0, v___x_3287_);
lean_ctor_set_uint8(v___x_3288_, sizeof(void*)*1, v___x_3275_);
v___x_3289_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3289_, 0, v___x_3284_);
lean_ctor_set(v___x_3289_, 1, v___x_3288_);
v___x_3290_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3290_, 0, v___x_3289_);
lean_ctor_set(v___x_3290_, 1, v___x_3278_);
v___x_3291_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3291_, 0, v___x_3290_);
lean_ctor_set(v___x_3291_, 1, v___x_3280_);
v___x_3292_ = ((lean_object*)(l_Lean_Compiler_LCNF_Check_Impure_instReprParam_repr___redArg___closed__9));
v___x_3293_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3293_, 0, v___x_3291_);
lean_ctor_set(v___x_3293_, 1, v___x_3292_);
v___x_3294_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3294_, 0, v___x_3293_);
lean_ctor_set(v___x_3294_, 1, v___x_3269_);
v___x_3295_ = lean_obj_once(&l_Lean_Compiler_LCNF_Check_Impure_instReprParam_repr___redArg___closed__10, &l_Lean_Compiler_LCNF_Check_Impure_instReprParam_repr___redArg___closed__10_once, _init_l_Lean_Compiler_LCNF_Check_Impure_instReprParam_repr___redArg___closed__10);
v___x_3296_ = l_Lean_instReprExpr_repr(v_type_3267_, v___x_3272_);
v___x_3297_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3297_, 0, v___x_3295_);
lean_ctor_set(v___x_3297_, 1, v___x_3296_);
v___x_3298_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3298_, 0, v___x_3297_);
lean_ctor_set_uint8(v___x_3298_, sizeof(void*)*1, v___x_3275_);
v___x_3299_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3299_, 0, v___x_3294_);
lean_ctor_set(v___x_3299_, 1, v___x_3298_);
v___x_3300_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3300_, 0, v___x_3299_);
lean_ctor_set(v___x_3300_, 1, v___x_3278_);
v___x_3301_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3301_, 0, v___x_3300_);
lean_ctor_set(v___x_3301_, 1, v___x_3280_);
v___x_3302_ = ((lean_object*)(l_Lean_Compiler_LCNF_Check_Impure_instReprParam_repr___redArg___closed__12));
v___x_3303_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3303_, 0, v___x_3301_);
lean_ctor_set(v___x_3303_, 1, v___x_3302_);
v___x_3304_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3304_, 0, v___x_3303_);
lean_ctor_set(v___x_3304_, 1, v___x_3269_);
v___x_3305_ = l_Bool_repr___redArg(v_borrow_3268_);
v___x_3306_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3306_, 0, v___x_3271_);
lean_ctor_set(v___x_3306_, 1, v___x_3305_);
v___x_3307_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3307_, 0, v___x_3306_);
lean_ctor_set_uint8(v___x_3307_, sizeof(void*)*1, v___x_3275_);
v___x_3308_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3308_, 0, v___x_3304_);
lean_ctor_set(v___x_3308_, 1, v___x_3307_);
v___x_3309_ = lean_obj_once(&l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr___redArg___closed__18, &l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr___redArg___closed__18_once, _init_l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr___redArg___closed__18);
v___x_3310_ = ((lean_object*)(l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr___redArg___closed__19));
v___x_3311_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3311_, 0, v___x_3310_);
lean_ctor_set(v___x_3311_, 1, v___x_3308_);
v___x_3312_ = ((lean_object*)(l_Lean_Compiler_LCNF_Check_Impure_instReprVarRCInfo_repr___redArg___closed__20));
v___x_3313_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3313_, 0, v___x_3311_);
lean_ctor_set(v___x_3313_, 1, v___x_3312_);
v___x_3314_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3314_, 0, v___x_3309_);
lean_ctor_set(v___x_3314_, 1, v___x_3313_);
v___x_3315_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3315_, 0, v___x_3314_);
lean_ctor_set_uint8(v___x_3315_, sizeof(void*)*1, v___x_3275_);
return v___x_3315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Impure_instReprParam_repr(uint8_t v_pu_3316_, lean_object* v_x_3317_, lean_object* v_prec_3318_){
_start:
{
lean_object* v___x_3319_; 
v___x_3319_ = l_Lean_Compiler_LCNF_Check_Impure_instReprParam_repr___redArg(v_x_3317_);
return v___x_3319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Impure_instReprParam_repr___boxed(lean_object* v_pu_3320_, lean_object* v_x_3321_, lean_object* v_prec_3322_){
_start:
{
uint8_t v_pu_450__boxed_3323_; lean_object* v_res_3324_; 
v_pu_450__boxed_3323_ = lean_unbox(v_pu_3320_);
v_res_3324_ = l_Lean_Compiler_LCNF_Check_Impure_instReprParam_repr(v_pu_450__boxed_3323_, v_x_3321_, v_prec_3322_);
lean_dec(v_prec_3322_);
return v_res_3324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Impure_instReprParam(uint8_t v_pu_3325_){
_start:
{
lean_object* v___x_3326_; lean_object* v___x_3327_; 
v___x_3326_ = lean_box(v_pu_3325_);
v___x_3327_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Check_Impure_instReprParam_repr___boxed), 3, 1);
lean_closure_set(v___x_3327_, 0, v___x_3326_);
return v___x_3327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Impure_instReprParam___boxed(lean_object* v_pu_3328_){
_start:
{
uint8_t v_pu_5__boxed_3329_; lean_object* v_res_3330_; 
v_pu_5__boxed_3329_ = lean_unbox(v_pu_3328_);
v_res_3330_ = l_Lean_Compiler_LCNF_Check_Impure_instReprParam(v_pu_5__boxed_3329_);
return v_res_3330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_Check_Impure_checkDecl_spec__1___redArg(lean_object* v_f_3331_, lean_object* v_v_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_){
_start:
{
if (lean_obj_tag(v_v_3332_) == 0)
{
lean_object* v_code_3339_; lean_object* v___x_3340_; 
v_code_3339_ = lean_ctor_get(v_v_3332_, 0);
lean_inc_ref(v_code_3339_);
lean_dec_ref(v_v_3332_);
lean_inc(v___y_3337_);
lean_inc_ref(v___y_3336_);
lean_inc(v___y_3335_);
lean_inc_ref(v___y_3334_);
lean_inc(v___y_3333_);
v___x_3340_ = lean_apply_7(v_f_3331_, v_code_3339_, v___y_3333_, v___y_3334_, v___y_3335_, v___y_3336_, v___y_3337_, lean_box(0));
return v___x_3340_;
}
else
{
lean_object* v___x_3342_; uint8_t v_isShared_3343_; uint8_t v_isSharedCheck_3348_; 
lean_dec_ref(v_f_3331_);
v_isSharedCheck_3348_ = !lean_is_exclusive(v_v_3332_);
if (v_isSharedCheck_3348_ == 0)
{
lean_object* v_unused_3349_; 
v_unused_3349_ = lean_ctor_get(v_v_3332_, 0);
lean_dec(v_unused_3349_);
v___x_3342_ = v_v_3332_;
v_isShared_3343_ = v_isSharedCheck_3348_;
goto v_resetjp_3341_;
}
else
{
lean_dec(v_v_3332_);
v___x_3342_ = lean_box(0);
v_isShared_3343_ = v_isSharedCheck_3348_;
goto v_resetjp_3341_;
}
v_resetjp_3341_:
{
lean_object* v___x_3344_; lean_object* v___x_3346_; 
v___x_3344_ = lean_box(0);
if (v_isShared_3343_ == 0)
{
lean_ctor_set_tag(v___x_3342_, 0);
lean_ctor_set(v___x_3342_, 0, v___x_3344_);
v___x_3346_ = v___x_3342_;
goto v_reusejp_3345_;
}
else
{
lean_object* v_reuseFailAlloc_3347_; 
v_reuseFailAlloc_3347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3347_, 0, v___x_3344_);
v___x_3346_ = v_reuseFailAlloc_3347_;
goto v_reusejp_3345_;
}
v_reusejp_3345_:
{
return v___x_3346_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_Check_Impure_checkDecl_spec__1___redArg___boxed(lean_object* v_f_3350_, lean_object* v_v_3351_, lean_object* v___y_3352_, lean_object* v___y_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_){
_start:
{
lean_object* v_res_3358_; 
v_res_3358_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_Check_Impure_checkDecl_spec__1___redArg(v_f_3350_, v_v_3351_, v___y_3352_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_);
lean_dec(v___y_3356_);
lean_dec_ref(v___y_3355_);
lean_dec(v___y_3354_);
lean_dec_ref(v___y_3353_);
lean_dec(v___y_3352_);
return v_res_3358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_Check_Impure_checkDecl_spec__1(uint8_t v_pu_3359_, lean_object* v_f_3360_, lean_object* v_v_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_, lean_object* v___y_3366_){
_start:
{
lean_object* v___x_3368_; 
v___x_3368_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_Check_Impure_checkDecl_spec__1___redArg(v_f_3360_, v_v_3361_, v___y_3362_, v___y_3363_, v___y_3364_, v___y_3365_, v___y_3366_);
return v___x_3368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_Check_Impure_checkDecl_spec__1___boxed(lean_object* v_pu_3369_, lean_object* v_f_3370_, lean_object* v_v_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_){
_start:
{
uint8_t v_pu_boxed_3378_; lean_object* v_res_3379_; 
v_pu_boxed_3378_ = lean_unbox(v_pu_3369_);
v_res_3379_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_Check_Impure_checkDecl_spec__1(v_pu_boxed_3378_, v_f_3370_, v_v_3371_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_, v___y_3376_);
lean_dec(v___y_3376_);
lean_dec_ref(v___y_3375_);
lean_dec(v___y_3374_);
lean_dec_ref(v___y_3373_);
lean_dec(v___y_3372_);
return v_res_3379_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Impure_checkDecl_spec__0(lean_object* v_as_3380_, size_t v_i_3381_, size_t v_stop_3382_, lean_object* v_b_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_, lean_object* v___y_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_){
_start:
{
uint8_t v___x_3390_; 
v___x_3390_ = lean_usize_dec_eq(v_i_3381_, v_stop_3382_);
if (v___x_3390_ == 0)
{
lean_object* v___x_3391_; lean_object* v___x_3392_; 
v___x_3391_ = lean_array_uget_borrowed(v_as_3380_, v_i_3381_);
lean_inc(v___x_3391_);
v___x_3392_ = l_Lean_Compiler_LCNF_Check_Impure_addParam(v___x_3391_, v___y_3384_, v___y_3385_, v___y_3386_, v___y_3387_, v___y_3388_);
if (lean_obj_tag(v___x_3392_) == 0)
{
lean_object* v_a_3393_; size_t v___x_3394_; size_t v___x_3395_; 
v_a_3393_ = lean_ctor_get(v___x_3392_, 0);
lean_inc(v_a_3393_);
lean_dec_ref(v___x_3392_);
v___x_3394_ = ((size_t)1ULL);
v___x_3395_ = lean_usize_add(v_i_3381_, v___x_3394_);
v_i_3381_ = v___x_3395_;
v_b_3383_ = v_a_3393_;
goto _start;
}
else
{
return v___x_3392_;
}
}
else
{
lean_object* v___x_3397_; 
v___x_3397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3397_, 0, v_b_3383_);
return v___x_3397_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Impure_checkDecl_spec__0___boxed(lean_object* v_as_3398_, lean_object* v_i_3399_, lean_object* v_stop_3400_, lean_object* v_b_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_){
_start:
{
size_t v_i_boxed_3408_; size_t v_stop_boxed_3409_; lean_object* v_res_3410_; 
v_i_boxed_3408_ = lean_unbox_usize(v_i_3399_);
lean_dec(v_i_3399_);
v_stop_boxed_3409_ = lean_unbox_usize(v_stop_3400_);
lean_dec(v_stop_3400_);
v_res_3410_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Impure_checkDecl_spec__0(v_as_3398_, v_i_boxed_3408_, v_stop_boxed_3409_, v_b_3401_, v___y_3402_, v___y_3403_, v___y_3404_, v___y_3405_, v___y_3406_);
lean_dec(v___y_3406_);
lean_dec_ref(v___y_3405_);
lean_dec(v___y_3404_);
lean_dec_ref(v___y_3403_);
lean_dec(v___y_3402_);
lean_dec_ref(v_as_3398_);
return v_res_3410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Impure_checkDecl___lam__0(lean_object* v_toSignature_3411_, lean_object* v_code_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_){
_start:
{
lean_object* v___y_3420_; lean_object* v_params_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; uint8_t v___x_3425_; 
v_params_3422_ = lean_ctor_get(v_toSignature_3411_, 3);
v___x_3423_ = lean_unsigned_to_nat(0u);
v___x_3424_ = lean_array_get_size(v_params_3422_);
v___x_3425_ = lean_nat_dec_lt(v___x_3423_, v___x_3424_);
if (v___x_3425_ == 0)
{
lean_object* v___x_3426_; 
v___x_3426_ = l_Lean_Compiler_LCNF_Check_Impure_check(v_code_3412_, v___y_3413_, v___y_3414_, v___y_3415_, v___y_3416_, v___y_3417_);
return v___x_3426_;
}
else
{
lean_object* v___x_3427_; uint8_t v___x_3428_; 
v___x_3427_ = lean_box(0);
v___x_3428_ = lean_nat_dec_le(v___x_3424_, v___x_3424_);
if (v___x_3428_ == 0)
{
if (v___x_3425_ == 0)
{
lean_object* v___x_3429_; 
v___x_3429_ = l_Lean_Compiler_LCNF_Check_Impure_check(v_code_3412_, v___y_3413_, v___y_3414_, v___y_3415_, v___y_3416_, v___y_3417_);
return v___x_3429_;
}
else
{
size_t v___x_3430_; size_t v___x_3431_; lean_object* v___x_3432_; 
v___x_3430_ = ((size_t)0ULL);
v___x_3431_ = lean_usize_of_nat(v___x_3424_);
v___x_3432_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Impure_checkDecl_spec__0(v_params_3422_, v___x_3430_, v___x_3431_, v___x_3427_, v___y_3413_, v___y_3414_, v___y_3415_, v___y_3416_, v___y_3417_);
v___y_3420_ = v___x_3432_;
goto v___jp_3419_;
}
}
else
{
size_t v___x_3433_; size_t v___x_3434_; lean_object* v___x_3435_; 
v___x_3433_ = ((size_t)0ULL);
v___x_3434_ = lean_usize_of_nat(v___x_3424_);
v___x_3435_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Impure_checkDecl_spec__0(v_params_3422_, v___x_3433_, v___x_3434_, v___x_3427_, v___y_3413_, v___y_3414_, v___y_3415_, v___y_3416_, v___y_3417_);
v___y_3420_ = v___x_3435_;
goto v___jp_3419_;
}
}
v___jp_3419_:
{
if (lean_obj_tag(v___y_3420_) == 0)
{
lean_object* v___x_3421_; 
lean_dec_ref(v___y_3420_);
v___x_3421_ = l_Lean_Compiler_LCNF_Check_Impure_check(v_code_3412_, v___y_3413_, v___y_3414_, v___y_3415_, v___y_3416_, v___y_3417_);
return v___x_3421_;
}
else
{
lean_dec_ref(v_code_3412_);
return v___y_3420_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Impure_checkDecl___lam__0___boxed(lean_object* v_toSignature_3436_, lean_object* v_code_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_){
_start:
{
lean_object* v_res_3444_; 
v_res_3444_ = l_Lean_Compiler_LCNF_Check_Impure_checkDecl___lam__0(v_toSignature_3436_, v_code_3437_, v___y_3438_, v___y_3439_, v___y_3440_, v___y_3441_, v___y_3442_);
lean_dec(v___y_3442_);
lean_dec_ref(v___y_3441_);
lean_dec(v___y_3440_);
lean_dec_ref(v___y_3439_);
lean_dec(v___y_3438_);
lean_dec_ref(v_toSignature_3436_);
return v_res_3444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Impure_checkDecl(lean_object* v_decl_3445_, lean_object* v_a_3446_, lean_object* v_a_3447_, lean_object* v_a_3448_, lean_object* v_a_3449_, lean_object* v_a_3450_){
_start:
{
lean_object* v_toSignature_3452_; lean_object* v_value_3453_; lean_object* v___f_3454_; lean_object* v___x_3455_; 
v_toSignature_3452_ = lean_ctor_get(v_decl_3445_, 0);
lean_inc_ref(v_toSignature_3452_);
v_value_3453_ = lean_ctor_get(v_decl_3445_, 1);
lean_inc_ref(v_value_3453_);
lean_dec_ref(v_decl_3445_);
v___f_3454_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Check_Impure_checkDecl___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3454_, 0, v_toSignature_3452_);
v___x_3455_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_Check_Impure_checkDecl_spec__1___redArg(v___f_3454_, v_value_3453_, v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_, v_a_3450_);
return v___x_3455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Impure_checkDecl___boxed(lean_object* v_decl_3456_, lean_object* v_a_3457_, lean_object* v_a_3458_, lean_object* v_a_3459_, lean_object* v_a_3460_, lean_object* v_a_3461_, lean_object* v_a_3462_){
_start:
{
lean_object* v_res_3463_; 
v_res_3463_ = l_Lean_Compiler_LCNF_Check_Impure_checkDecl(v_decl_3456_, v_a_3457_, v_a_3458_, v_a_3459_, v_a_3460_, v_a_3461_);
lean_dec(v_a_3461_);
lean_dec_ref(v_a_3460_);
lean_dec(v_a_3459_);
lean_dec_ref(v_a_3458_);
lean_dec(v_a_3457_);
return v_res_3463_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_checkRC___closed__0(void){
_start:
{
lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; 
v___x_3464_ = lean_box(0);
v___x_3465_ = lean_unsigned_to_nat(16u);
v___x_3466_ = lean_mk_array(v___x_3465_, v___x_3464_);
return v___x_3466_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_checkRC___closed__1(void){
_start:
{
lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; 
v___x_3467_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_checkRC___closed__0, &l_Lean_Compiler_LCNF_Decl_checkRC___closed__0_once, _init_l_Lean_Compiler_LCNF_Decl_checkRC___closed__0);
v___x_3468_ = lean_unsigned_to_nat(0u);
v___x_3469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3469_, 0, v___x_3468_);
lean_ctor_set(v___x_3469_, 1, v___x_3467_);
return v___x_3469_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_checkRC___closed__2(void){
_start:
{
lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; 
v___x_3470_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_checkRC___closed__1, &l_Lean_Compiler_LCNF_Decl_checkRC___closed__1_once, _init_l_Lean_Compiler_LCNF_Decl_checkRC___closed__1);
v___x_3471_ = lean_box(1);
v___x_3472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3472_, 0, v___x_3471_);
lean_ctor_set(v___x_3472_, 1, v___x_3470_);
return v___x_3472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_checkRC(lean_object* v_decl_3473_, lean_object* v_a_3474_, lean_object* v_a_3475_, lean_object* v_a_3476_, lean_object* v_a_3477_){
_start:
{
lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; 
v___x_3479_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_checkRC___closed__2, &l_Lean_Compiler_LCNF_Decl_checkRC___closed__2_once, _init_l_Lean_Compiler_LCNF_Decl_checkRC___closed__2);
v___x_3480_ = lean_st_mk_ref(v___x_3479_);
v___x_3481_ = l_Lean_Compiler_LCNF_Check_Impure_checkDecl(v_decl_3473_, v___x_3480_, v_a_3474_, v_a_3475_, v_a_3476_, v_a_3477_);
if (lean_obj_tag(v___x_3481_) == 0)
{
lean_object* v_a_3482_; lean_object* v___x_3484_; uint8_t v_isShared_3485_; uint8_t v_isSharedCheck_3490_; 
v_a_3482_ = lean_ctor_get(v___x_3481_, 0);
v_isSharedCheck_3490_ = !lean_is_exclusive(v___x_3481_);
if (v_isSharedCheck_3490_ == 0)
{
v___x_3484_ = v___x_3481_;
v_isShared_3485_ = v_isSharedCheck_3490_;
goto v_resetjp_3483_;
}
else
{
lean_inc(v_a_3482_);
lean_dec(v___x_3481_);
v___x_3484_ = lean_box(0);
v_isShared_3485_ = v_isSharedCheck_3490_;
goto v_resetjp_3483_;
}
v_resetjp_3483_:
{
lean_object* v___x_3486_; lean_object* v___x_3488_; 
v___x_3486_ = lean_st_ref_get(v___x_3480_);
lean_dec(v___x_3480_);
lean_dec(v___x_3486_);
if (v_isShared_3485_ == 0)
{
v___x_3488_ = v___x_3484_;
goto v_reusejp_3487_;
}
else
{
lean_object* v_reuseFailAlloc_3489_; 
v_reuseFailAlloc_3489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3489_, 0, v_a_3482_);
v___x_3488_ = v_reuseFailAlloc_3489_;
goto v_reusejp_3487_;
}
v_reusejp_3487_:
{
return v___x_3488_;
}
}
}
else
{
lean_dec(v___x_3480_);
return v___x_3481_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_checkRC___boxed(lean_object* v_decl_3491_, lean_object* v_a_3492_, lean_object* v_a_3493_, lean_object* v_a_3494_, lean_object* v_a_3495_, lean_object* v_a_3496_){
_start:
{
lean_object* v_res_3497_; 
v_res_3497_ = l_Lean_Compiler_LCNF_Decl_checkRC(v_decl_3491_, v_a_3492_, v_a_3493_, v_a_3494_, v_a_3495_);
lean_dec(v_a_3495_);
lean_dec_ref(v_a_3494_);
lean_dec(v_a_3493_);
lean_dec_ref(v_a_3492_);
return v_res_3497_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_PrettyPrinter(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_CompatibleTypes(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_CheckRC(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Compiler_LCNF_PrettyPrinter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_CompatibleTypes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_LCNF_Check_Impure_deadInfo = _init_l_Lean_Compiler_LCNF_Check_Impure_deadInfo();
lean_mark_persistent(l_Lean_Compiler_LCNF_Check_Impure_deadInfo);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_LCNF_CheckRC(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Compiler_LCNF_PrettyPrinter(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_CompatibleTypes(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_CheckRC(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_PrettyPrinter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_CompatibleTypes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_CheckRC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_LCNF_CheckRC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_LCNF_CheckRC(builtin);
}
#ifdef __cplusplus
}
#endif
