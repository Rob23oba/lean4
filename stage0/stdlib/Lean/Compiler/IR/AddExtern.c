// Lean compiler output
// Module: Lean.Compiler.IR.AddExtern
// Imports: import Init.While import Lean.Compiler.IR.ToIR import Lean.Compiler.LCNF.ToImpureType import Lean.Compiler.LCNF.ToImpure import Lean.Compiler.LCNF.ExplicitBoxing import Lean.Compiler.LCNF.Internalize public import Lean.Compiler.ExternAttr import Lean.Compiler.LCNF.ExplicitRC import Lean.Compiler.Options
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
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Compiler_LCNF_toImpureType(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Compiler_LCNF_lowerResultType(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_internalize(uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_saveImpure___redArg(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_addBoxedVersions(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_runExplicitRc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Compiler_LCNF_recordFinalImpureDecl(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_CompilerM_run___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getOtherDeclMonoType(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_compiler_ignoreBorrowAnnotation;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t l_Lean_isMarkedBorrowed(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_saveMono___redArg(lean_object*, lean_object*);
lean_object* l_Lean_IR_toIR(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
extern lean_object* l_Lean_IR_tracePrefixOptionName;
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_addDecls(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_Compiler_LCNF_setDeclPublic(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono_spec__1_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono_spec__2(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono___closed__0 = (const lean_object*)&l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono___closed__0_value;
static const lean_ctor_object l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono___closed__1 = (const lean_object*)&l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono_spec__1_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure_spec__1___redArg___closed__0;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure_spec__1___redArg___closed__1;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure_spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure_spec__1___redArg___closed__2;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure_spec__1___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___lam__0(uint8_t, lean_object*, lean_object*, uint8_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___closed__0;
static lean_once_cell_t l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___closed__1;
static lean_once_cell_t l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___closed__2;
static lean_once_cell_t l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___closed__3;
static const lean_ctor_object l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___boxed__const__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + sizeof(size_t)*1, .m_other = 0, .m_tag = 0}, .m_objs = {(lean_object*)(size_t)(0ULL)}};
LEAN_EXPORT const lean_object* l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___boxed__const__1 = (const lean_object*)&l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___boxed__const__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addIr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "result"};
static const lean_object* l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addIr___closed__0 = (const lean_object*)&l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addIr___closed__0_value;
static const lean_ctor_object l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addIr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addIr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(180, 131, 177, 30, 113, 24, 63, 83)}};
static const lean_object* l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addIr___closed__1 = (const lean_object*)&l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addIr___closed__1_value;
static lean_once_cell_t l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addIr___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addIr___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addIr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addIr___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_add_extern(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_addExtern___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono_spec__0(lean_object* v_opts_1_, lean_object* v_opt_2_){
_start:
{
lean_object* v_name_3_; lean_object* v_defValue_4_; lean_object* v_map_5_; lean_object* v___x_6_; 
v_name_3_ = lean_ctor_get(v_opt_2_, 0);
v_defValue_4_ = lean_ctor_get(v_opt_2_, 1);
v_map_5_ = lean_ctor_get(v_opts_1_, 0);
v___x_6_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_5_, v_name_3_);
if (lean_obj_tag(v___x_6_) == 0)
{
uint8_t v___x_7_; 
v___x_7_ = lean_unbox(v_defValue_4_);
return v___x_7_;
}
else
{
lean_object* v_val_8_; 
v_val_8_ = lean_ctor_get(v___x_6_, 0);
lean_inc(v_val_8_);
lean_dec_ref(v___x_6_);
if (lean_obj_tag(v_val_8_) == 1)
{
uint8_t v_v_9_; 
v_v_9_ = lean_ctor_get_uint8(v_val_8_, 0);
lean_dec_ref(v_val_8_);
return v_v_9_;
}
else
{
uint8_t v___x_10_; 
lean_dec(v_val_8_);
v___x_10_ = lean_unbox(v_defValue_4_);
return v___x_10_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono_spec__0___boxed(lean_object* v_opts_11_, lean_object* v_opt_12_){
_start:
{
uint8_t v_res_13_; lean_object* v_r_14_; 
v_res_13_ = l_Lean_Option_get___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono_spec__0(v_opts_11_, v_opt_12_);
lean_dec_ref(v_opt_12_);
lean_dec_ref(v_opts_11_);
v_r_14_ = lean_box(v_res_13_);
return v_r_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono_spec__1_spec__1___redArg(lean_object* v___y_15_){
_start:
{
lean_object* v___x_17_; lean_object* v_ngen_18_; lean_object* v_namePrefix_19_; lean_object* v_idx_20_; lean_object* v___x_22_; uint8_t v_isShared_23_; uint8_t v_isSharedCheck_49_; 
v___x_17_ = lean_st_ref_get(v___y_15_);
v_ngen_18_ = lean_ctor_get(v___x_17_, 2);
lean_inc_ref(v_ngen_18_);
lean_dec(v___x_17_);
v_namePrefix_19_ = lean_ctor_get(v_ngen_18_, 0);
v_idx_20_ = lean_ctor_get(v_ngen_18_, 1);
v_isSharedCheck_49_ = !lean_is_exclusive(v_ngen_18_);
if (v_isSharedCheck_49_ == 0)
{
v___x_22_ = v_ngen_18_;
v_isShared_23_ = v_isSharedCheck_49_;
goto v_resetjp_21_;
}
else
{
lean_inc(v_idx_20_);
lean_inc(v_namePrefix_19_);
lean_dec(v_ngen_18_);
v___x_22_ = lean_box(0);
v_isShared_23_ = v_isSharedCheck_49_;
goto v_resetjp_21_;
}
v_resetjp_21_:
{
lean_object* v___x_24_; lean_object* v_env_25_; lean_object* v_nextMacroScope_26_; lean_object* v_auxDeclNGen_27_; lean_object* v_traceState_28_; lean_object* v_cache_29_; lean_object* v_messages_30_; lean_object* v_infoState_31_; lean_object* v_snapshotTasks_32_; lean_object* v___x_34_; uint8_t v_isShared_35_; uint8_t v_isSharedCheck_47_; 
v___x_24_ = lean_st_ref_take(v___y_15_);
v_env_25_ = lean_ctor_get(v___x_24_, 0);
v_nextMacroScope_26_ = lean_ctor_get(v___x_24_, 1);
v_auxDeclNGen_27_ = lean_ctor_get(v___x_24_, 3);
v_traceState_28_ = lean_ctor_get(v___x_24_, 4);
v_cache_29_ = lean_ctor_get(v___x_24_, 5);
v_messages_30_ = lean_ctor_get(v___x_24_, 6);
v_infoState_31_ = lean_ctor_get(v___x_24_, 7);
v_snapshotTasks_32_ = lean_ctor_get(v___x_24_, 8);
v_isSharedCheck_47_ = !lean_is_exclusive(v___x_24_);
if (v_isSharedCheck_47_ == 0)
{
lean_object* v_unused_48_; 
v_unused_48_ = lean_ctor_get(v___x_24_, 2);
lean_dec(v_unused_48_);
v___x_34_ = v___x_24_;
v_isShared_35_ = v_isSharedCheck_47_;
goto v_resetjp_33_;
}
else
{
lean_inc(v_snapshotTasks_32_);
lean_inc(v_infoState_31_);
lean_inc(v_messages_30_);
lean_inc(v_cache_29_);
lean_inc(v_traceState_28_);
lean_inc(v_auxDeclNGen_27_);
lean_inc(v_nextMacroScope_26_);
lean_inc(v_env_25_);
lean_dec(v___x_24_);
v___x_34_ = lean_box(0);
v_isShared_35_ = v_isSharedCheck_47_;
goto v_resetjp_33_;
}
v_resetjp_33_:
{
lean_object* v_r_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_40_; 
lean_inc(v_idx_20_);
lean_inc(v_namePrefix_19_);
v_r_36_ = l_Lean_Name_num___override(v_namePrefix_19_, v_idx_20_);
v___x_37_ = lean_unsigned_to_nat(1u);
v___x_38_ = lean_nat_add(v_idx_20_, v___x_37_);
lean_dec(v_idx_20_);
if (v_isShared_23_ == 0)
{
lean_ctor_set(v___x_22_, 1, v___x_38_);
v___x_40_ = v___x_22_;
goto v_reusejp_39_;
}
else
{
lean_object* v_reuseFailAlloc_46_; 
v_reuseFailAlloc_46_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_46_, 0, v_namePrefix_19_);
lean_ctor_set(v_reuseFailAlloc_46_, 1, v___x_38_);
v___x_40_ = v_reuseFailAlloc_46_;
goto v_reusejp_39_;
}
v_reusejp_39_:
{
lean_object* v___x_42_; 
if (v_isShared_35_ == 0)
{
lean_ctor_set(v___x_34_, 2, v___x_40_);
v___x_42_ = v___x_34_;
goto v_reusejp_41_;
}
else
{
lean_object* v_reuseFailAlloc_45_; 
v_reuseFailAlloc_45_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_45_, 0, v_env_25_);
lean_ctor_set(v_reuseFailAlloc_45_, 1, v_nextMacroScope_26_);
lean_ctor_set(v_reuseFailAlloc_45_, 2, v___x_40_);
lean_ctor_set(v_reuseFailAlloc_45_, 3, v_auxDeclNGen_27_);
lean_ctor_set(v_reuseFailAlloc_45_, 4, v_traceState_28_);
lean_ctor_set(v_reuseFailAlloc_45_, 5, v_cache_29_);
lean_ctor_set(v_reuseFailAlloc_45_, 6, v_messages_30_);
lean_ctor_set(v_reuseFailAlloc_45_, 7, v_infoState_31_);
lean_ctor_set(v_reuseFailAlloc_45_, 8, v_snapshotTasks_32_);
v___x_42_ = v_reuseFailAlloc_45_;
goto v_reusejp_41_;
}
v_reusejp_41_:
{
lean_object* v___x_43_; lean_object* v___x_44_; 
v___x_43_ = lean_st_ref_set(v___y_15_, v___x_42_);
v___x_44_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_44_, 0, v_r_36_);
return v___x_44_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono_spec__1_spec__1___redArg___boxed(lean_object* v___y_50_, lean_object* v___y_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono_spec__1_spec__1___redArg(v___y_50_);
lean_dec(v___y_50_);
return v_res_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono_spec__1(lean_object* v___y_53_, lean_object* v___y_54_){
_start:
{
lean_object* v___x_56_; lean_object* v_a_57_; lean_object* v___x_59_; uint8_t v_isShared_60_; uint8_t v_isSharedCheck_64_; 
v___x_56_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono_spec__1_spec__1___redArg(v___y_54_);
v_a_57_ = lean_ctor_get(v___x_56_, 0);
v_isSharedCheck_64_ = !lean_is_exclusive(v___x_56_);
if (v_isSharedCheck_64_ == 0)
{
v___x_59_ = v___x_56_;
v_isShared_60_ = v_isSharedCheck_64_;
goto v_resetjp_58_;
}
else
{
lean_inc(v_a_57_);
lean_dec(v___x_56_);
v___x_59_ = lean_box(0);
v_isShared_60_ = v_isSharedCheck_64_;
goto v_resetjp_58_;
}
v_resetjp_58_:
{
lean_object* v___x_62_; 
if (v_isShared_60_ == 0)
{
v___x_62_ = v___x_59_;
goto v_reusejp_61_;
}
else
{
lean_object* v_reuseFailAlloc_63_; 
v_reuseFailAlloc_63_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_63_, 0, v_a_57_);
v___x_62_ = v_reuseFailAlloc_63_;
goto v_reusejp_61_;
}
v_reusejp_61_:
{
return v___x_62_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono_spec__1___boxed(lean_object* v___y_65_, lean_object* v___y_66_, lean_object* v___y_67_){
_start:
{
lean_object* v_res_68_; 
v_res_68_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono_spec__1(v___y_65_, v___y_66_);
lean_dec(v___y_66_);
lean_dec_ref(v___y_65_);
return v_res_68_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono_spec__2(uint8_t v___x_69_, lean_object* v_b_70_, lean_object* v___y_71_, lean_object* v___y_72_){
_start:
{
lean_object* v_fst_74_; 
v_fst_74_ = lean_ctor_get(v_b_70_, 0);
lean_inc(v_fst_74_);
if (lean_obj_tag(v_fst_74_) == 7)
{
lean_object* v_snd_75_; lean_object* v___x_77_; uint8_t v_isShared_78_; uint8_t v_isSharedCheck_102_; 
v_snd_75_ = lean_ctor_get(v_b_70_, 1);
v_isSharedCheck_102_ = !lean_is_exclusive(v_b_70_);
if (v_isSharedCheck_102_ == 0)
{
lean_object* v_unused_103_; 
v_unused_103_ = lean_ctor_get(v_b_70_, 0);
lean_dec(v_unused_103_);
v___x_77_ = v_b_70_;
v_isShared_78_ = v_isSharedCheck_102_;
goto v_resetjp_76_;
}
else
{
lean_inc(v_snd_75_);
lean_dec(v_b_70_);
v___x_77_ = lean_box(0);
v_isShared_78_ = v_isSharedCheck_102_;
goto v_resetjp_76_;
}
v_resetjp_76_:
{
lean_object* v_binderName_79_; lean_object* v_binderType_80_; lean_object* v_body_81_; uint8_t v___y_83_; 
v_binderName_79_ = lean_ctor_get(v_fst_74_, 0);
lean_inc(v_binderName_79_);
v_binderType_80_ = lean_ctor_get(v_fst_74_, 1);
lean_inc_ref(v_binderType_80_);
v_body_81_ = lean_ctor_get(v_fst_74_, 2);
lean_inc_ref(v_body_81_);
lean_dec_ref(v_fst_74_);
if (v___x_69_ == 0)
{
uint8_t v___x_100_; 
v___x_100_ = l_Lean_isMarkedBorrowed(v_binderType_80_);
v___y_83_ = v___x_100_;
goto v___jp_82_;
}
else
{
uint8_t v___x_101_; 
v___x_101_ = 0;
v___y_83_ = v___x_101_;
goto v___jp_82_;
}
v___jp_82_:
{
lean_object* v___x_84_; 
v___x_84_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono_spec__1(v___y_71_, v___y_72_);
if (lean_obj_tag(v___x_84_) == 0)
{
lean_object* v_a_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_89_; 
v_a_85_ = lean_ctor_get(v___x_84_, 0);
lean_inc(v_a_85_);
lean_dec_ref(v___x_84_);
v___x_86_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_86_, 0, v_a_85_);
lean_ctor_set(v___x_86_, 1, v_binderName_79_);
lean_ctor_set(v___x_86_, 2, v_binderType_80_);
lean_ctor_set_uint8(v___x_86_, sizeof(void*)*3, v___y_83_);
v___x_87_ = lean_array_push(v_snd_75_, v___x_86_);
if (v_isShared_78_ == 0)
{
lean_ctor_set(v___x_77_, 1, v___x_87_);
lean_ctor_set(v___x_77_, 0, v_body_81_);
v___x_89_ = v___x_77_;
goto v_reusejp_88_;
}
else
{
lean_object* v_reuseFailAlloc_91_; 
v_reuseFailAlloc_91_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_91_, 0, v_body_81_);
lean_ctor_set(v_reuseFailAlloc_91_, 1, v___x_87_);
v___x_89_ = v_reuseFailAlloc_91_;
goto v_reusejp_88_;
}
v_reusejp_88_:
{
v_b_70_ = v___x_89_;
goto _start;
}
}
else
{
lean_object* v_a_92_; lean_object* v___x_94_; uint8_t v_isShared_95_; uint8_t v_isSharedCheck_99_; 
lean_dec_ref(v_body_81_);
lean_dec_ref(v_binderType_80_);
lean_dec(v_binderName_79_);
lean_del_object(v___x_77_);
lean_dec(v_snd_75_);
v_a_92_ = lean_ctor_get(v___x_84_, 0);
v_isSharedCheck_99_ = !lean_is_exclusive(v___x_84_);
if (v_isSharedCheck_99_ == 0)
{
v___x_94_ = v___x_84_;
v_isShared_95_ = v_isSharedCheck_99_;
goto v_resetjp_93_;
}
else
{
lean_inc(v_a_92_);
lean_dec(v___x_84_);
v___x_94_ = lean_box(0);
v_isShared_95_ = v_isSharedCheck_99_;
goto v_resetjp_93_;
}
v_resetjp_93_:
{
lean_object* v___x_97_; 
if (v_isShared_95_ == 0)
{
v___x_97_ = v___x_94_;
goto v_reusejp_96_;
}
else
{
lean_object* v_reuseFailAlloc_98_; 
v_reuseFailAlloc_98_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_98_, 0, v_a_92_);
v___x_97_ = v_reuseFailAlloc_98_;
goto v_reusejp_96_;
}
v_reusejp_96_:
{
return v___x_97_;
}
}
}
}
}
}
else
{
lean_object* v_snd_104_; lean_object* v___x_106_; uint8_t v_isShared_107_; uint8_t v_isSharedCheck_112_; 
v_snd_104_ = lean_ctor_get(v_b_70_, 1);
v_isSharedCheck_112_ = !lean_is_exclusive(v_b_70_);
if (v_isSharedCheck_112_ == 0)
{
lean_object* v_unused_113_; 
v_unused_113_ = lean_ctor_get(v_b_70_, 0);
lean_dec(v_unused_113_);
v___x_106_ = v_b_70_;
v_isShared_107_ = v_isSharedCheck_112_;
goto v_resetjp_105_;
}
else
{
lean_inc(v_snd_104_);
lean_dec(v_b_70_);
v___x_106_ = lean_box(0);
v_isShared_107_ = v_isSharedCheck_112_;
goto v_resetjp_105_;
}
v_resetjp_105_:
{
lean_object* v___x_109_; 
if (v_isShared_107_ == 0)
{
v___x_109_ = v___x_106_;
goto v_reusejp_108_;
}
else
{
lean_object* v_reuseFailAlloc_111_; 
v_reuseFailAlloc_111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_111_, 0, v_fst_74_);
lean_ctor_set(v_reuseFailAlloc_111_, 1, v_snd_104_);
v___x_109_ = v_reuseFailAlloc_111_;
goto v_reusejp_108_;
}
v_reusejp_108_:
{
lean_object* v___x_110_; 
v___x_110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_110_, 0, v___x_109_);
return v___x_110_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono_spec__2___boxed(lean_object* v___x_114_, lean_object* v_b_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_){
_start:
{
uint8_t v___x_1645__boxed_119_; lean_object* v_res_120_; 
v___x_1645__boxed_119_ = lean_unbox(v___x_114_);
v_res_120_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono_spec__2(v___x_1645__boxed_119_, v_b_115_, v___y_116_, v___y_117_);
lean_dec(v___y_117_);
lean_dec_ref(v___y_116_);
return v_res_120_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono(lean_object* v_externAttrData_126_, lean_object* v_declName_127_, lean_object* v_a_128_, lean_object* v_a_129_){
_start:
{
lean_object* v___x_131_; 
lean_inc(v_declName_127_);
v___x_131_ = l_Lean_Compiler_LCNF_getOtherDeclMonoType(v_declName_127_, v_a_128_, v_a_129_);
if (lean_obj_tag(v___x_131_) == 0)
{
lean_object* v_a_132_; lean_object* v_options_133_; lean_object* v___x_134_; lean_object* v___x_135_; uint8_t v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; 
v_a_132_ = lean_ctor_get(v___x_131_, 0);
lean_inc(v_a_132_);
lean_dec_ref(v___x_131_);
v_options_133_ = lean_ctor_get(v_a_128_, 2);
v___x_134_ = ((lean_object*)(l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono___closed__0));
v___x_135_ = l_Lean_Compiler_compiler_ignoreBorrowAnnotation;
v___x_136_ = l_Lean_Option_get___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono_spec__0(v_options_133_, v___x_135_);
lean_inc(v_a_132_);
v___x_137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_137_, 0, v_a_132_);
lean_ctor_set(v___x_137_, 1, v___x_134_);
v___x_138_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono_spec__2(v___x_136_, v___x_137_, v_a_128_, v_a_129_);
if (lean_obj_tag(v___x_138_) == 0)
{
lean_object* v_a_139_; lean_object* v_snd_140_; lean_object* v___x_141_; uint8_t v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; uint8_t v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; 
v_a_139_ = lean_ctor_get(v___x_138_, 0);
lean_inc(v_a_139_);
lean_dec_ref(v___x_138_);
v_snd_140_ = lean_ctor_get(v_a_139_, 1);
lean_inc(v_snd_140_);
lean_dec(v_a_139_);
v___x_141_ = lean_box(0);
v___x_142_ = 1;
v___x_143_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_143_, 0, v_declName_127_);
lean_ctor_set(v___x_143_, 1, v___x_141_);
lean_ctor_set(v___x_143_, 2, v_a_132_);
lean_ctor_set(v___x_143_, 3, v_snd_140_);
lean_ctor_set_uint8(v___x_143_, sizeof(void*)*4, v___x_142_);
v___x_144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_144_, 0, v_externAttrData_126_);
v___x_145_ = 0;
v___x_146_ = ((lean_object*)(l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono___closed__1));
v___x_147_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_147_, 0, v___x_143_);
lean_ctor_set(v___x_147_, 1, v___x_144_);
lean_ctor_set(v___x_147_, 2, v___x_146_);
lean_ctor_set_uint8(v___x_147_, sizeof(void*)*3, v___x_145_);
lean_inc_ref(v___x_147_);
v___x_148_ = l_Lean_Compiler_LCNF_Decl_saveMono___redArg(v___x_147_, v_a_129_);
if (lean_obj_tag(v___x_148_) == 0)
{
lean_object* v___x_150_; uint8_t v_isShared_151_; uint8_t v_isSharedCheck_155_; 
v_isSharedCheck_155_ = !lean_is_exclusive(v___x_148_);
if (v_isSharedCheck_155_ == 0)
{
lean_object* v_unused_156_; 
v_unused_156_ = lean_ctor_get(v___x_148_, 0);
lean_dec(v_unused_156_);
v___x_150_ = v___x_148_;
v_isShared_151_ = v_isSharedCheck_155_;
goto v_resetjp_149_;
}
else
{
lean_dec(v___x_148_);
v___x_150_ = lean_box(0);
v_isShared_151_ = v_isSharedCheck_155_;
goto v_resetjp_149_;
}
v_resetjp_149_:
{
lean_object* v___x_153_; 
if (v_isShared_151_ == 0)
{
lean_ctor_set(v___x_150_, 0, v___x_147_);
v___x_153_ = v___x_150_;
goto v_reusejp_152_;
}
else
{
lean_object* v_reuseFailAlloc_154_; 
v_reuseFailAlloc_154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_154_, 0, v___x_147_);
v___x_153_ = v_reuseFailAlloc_154_;
goto v_reusejp_152_;
}
v_reusejp_152_:
{
return v___x_153_;
}
}
}
else
{
lean_object* v_a_157_; lean_object* v___x_159_; uint8_t v_isShared_160_; uint8_t v_isSharedCheck_164_; 
lean_dec_ref(v___x_147_);
v_a_157_ = lean_ctor_get(v___x_148_, 0);
v_isSharedCheck_164_ = !lean_is_exclusive(v___x_148_);
if (v_isSharedCheck_164_ == 0)
{
v___x_159_ = v___x_148_;
v_isShared_160_ = v_isSharedCheck_164_;
goto v_resetjp_158_;
}
else
{
lean_inc(v_a_157_);
lean_dec(v___x_148_);
v___x_159_ = lean_box(0);
v_isShared_160_ = v_isSharedCheck_164_;
goto v_resetjp_158_;
}
v_resetjp_158_:
{
lean_object* v___x_162_; 
if (v_isShared_160_ == 0)
{
v___x_162_ = v___x_159_;
goto v_reusejp_161_;
}
else
{
lean_object* v_reuseFailAlloc_163_; 
v_reuseFailAlloc_163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_163_, 0, v_a_157_);
v___x_162_ = v_reuseFailAlloc_163_;
goto v_reusejp_161_;
}
v_reusejp_161_:
{
return v___x_162_;
}
}
}
}
else
{
lean_object* v_a_165_; lean_object* v___x_167_; uint8_t v_isShared_168_; uint8_t v_isSharedCheck_172_; 
lean_dec(v_a_132_);
lean_dec(v_declName_127_);
lean_dec(v_externAttrData_126_);
v_a_165_ = lean_ctor_get(v___x_138_, 0);
v_isSharedCheck_172_ = !lean_is_exclusive(v___x_138_);
if (v_isSharedCheck_172_ == 0)
{
v___x_167_ = v___x_138_;
v_isShared_168_ = v_isSharedCheck_172_;
goto v_resetjp_166_;
}
else
{
lean_inc(v_a_165_);
lean_dec(v___x_138_);
v___x_167_ = lean_box(0);
v_isShared_168_ = v_isSharedCheck_172_;
goto v_resetjp_166_;
}
v_resetjp_166_:
{
lean_object* v___x_170_; 
if (v_isShared_168_ == 0)
{
v___x_170_ = v___x_167_;
goto v_reusejp_169_;
}
else
{
lean_object* v_reuseFailAlloc_171_; 
v_reuseFailAlloc_171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_171_, 0, v_a_165_);
v___x_170_ = v_reuseFailAlloc_171_;
goto v_reusejp_169_;
}
v_reusejp_169_:
{
return v___x_170_;
}
}
}
}
else
{
lean_object* v_a_173_; lean_object* v___x_175_; uint8_t v_isShared_176_; uint8_t v_isSharedCheck_180_; 
lean_dec(v_declName_127_);
lean_dec(v_externAttrData_126_);
v_a_173_ = lean_ctor_get(v___x_131_, 0);
v_isSharedCheck_180_ = !lean_is_exclusive(v___x_131_);
if (v_isSharedCheck_180_ == 0)
{
v___x_175_ = v___x_131_;
v_isShared_176_ = v_isSharedCheck_180_;
goto v_resetjp_174_;
}
else
{
lean_inc(v_a_173_);
lean_dec(v___x_131_);
v___x_175_ = lean_box(0);
v_isShared_176_ = v_isSharedCheck_180_;
goto v_resetjp_174_;
}
v_resetjp_174_:
{
lean_object* v___x_178_; 
if (v_isShared_176_ == 0)
{
v___x_178_ = v___x_175_;
goto v_reusejp_177_;
}
else
{
lean_object* v_reuseFailAlloc_179_; 
v_reuseFailAlloc_179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_179_, 0, v_a_173_);
v___x_178_ = v_reuseFailAlloc_179_;
goto v_reusejp_177_;
}
v_reusejp_177_:
{
return v___x_178_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono___boxed(lean_object* v_externAttrData_181_, lean_object* v_declName_182_, lean_object* v_a_183_, lean_object* v_a_184_, lean_object* v_a_185_){
_start:
{
lean_object* v_res_186_; 
v_res_186_ = l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono(v_externAttrData_181_, v_declName_182_, v_a_183_, v_a_184_);
lean_dec(v_a_184_);
lean_dec_ref(v_a_183_);
return v_res_186_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono_spec__1_spec__1(lean_object* v___y_187_, lean_object* v___y_188_){
_start:
{
lean_object* v___x_190_; 
v___x_190_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono_spec__1_spec__1___redArg(v___y_188_);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono_spec__1_spec__1___boxed(lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_){
_start:
{
lean_object* v_res_194_; 
v_res_194_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono_spec__1_spec__1(v___y_191_, v___y_192_);
lean_dec(v___y_192_);
lean_dec_ref(v___y_191_);
return v_res_194_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_195_; 
v___x_195_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_195_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_196_; lean_object* v___x_197_; 
v___x_196_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure_spec__1___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure_spec__1___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure_spec__1___redArg___closed__0);
v___x_197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_197_, 0, v___x_196_);
return v___x_197_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_198_; lean_object* v___x_199_; 
v___x_198_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure_spec__1___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure_spec__1___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure_spec__1___redArg___closed__1);
v___x_199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_199_, 0, v___x_198_);
lean_ctor_set(v___x_199_, 1, v___x_198_);
return v___x_199_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure_spec__1___redArg(lean_object* v_as_200_, size_t v_sz_201_, size_t v_i_202_, lean_object* v_b_203_, lean_object* v___y_204_){
_start:
{
uint8_t v___x_206_; 
v___x_206_ = lean_usize_dec_lt(v_i_202_, v_sz_201_);
if (v___x_206_ == 0)
{
lean_object* v___x_207_; 
v___x_207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_207_, 0, v_b_203_);
return v___x_207_;
}
else
{
lean_object* v_a_208_; lean_object* v___x_209_; 
v_a_208_ = lean_array_uget_borrowed(v_as_200_, v_i_202_);
lean_inc(v_a_208_);
v___x_209_ = l_Lean_Compiler_LCNF_Decl_saveImpure___redArg(v_a_208_, v___y_204_);
if (lean_obj_tag(v___x_209_) == 0)
{
lean_object* v___x_210_; lean_object* v_toSignature_211_; lean_object* v_env_212_; lean_object* v_nextMacroScope_213_; lean_object* v_ngen_214_; lean_object* v_auxDeclNGen_215_; lean_object* v_traceState_216_; lean_object* v_messages_217_; lean_object* v_infoState_218_; lean_object* v_snapshotTasks_219_; lean_object* v___x_221_; uint8_t v_isShared_222_; uint8_t v_isSharedCheck_234_; 
lean_dec_ref(v___x_209_);
v___x_210_ = lean_st_ref_take(v___y_204_);
v_toSignature_211_ = lean_ctor_get(v_a_208_, 0);
v_env_212_ = lean_ctor_get(v___x_210_, 0);
v_nextMacroScope_213_ = lean_ctor_get(v___x_210_, 1);
v_ngen_214_ = lean_ctor_get(v___x_210_, 2);
v_auxDeclNGen_215_ = lean_ctor_get(v___x_210_, 3);
v_traceState_216_ = lean_ctor_get(v___x_210_, 4);
v_messages_217_ = lean_ctor_get(v___x_210_, 6);
v_infoState_218_ = lean_ctor_get(v___x_210_, 7);
v_snapshotTasks_219_ = lean_ctor_get(v___x_210_, 8);
v_isSharedCheck_234_ = !lean_is_exclusive(v___x_210_);
if (v_isSharedCheck_234_ == 0)
{
lean_object* v_unused_235_; 
v_unused_235_ = lean_ctor_get(v___x_210_, 5);
lean_dec(v_unused_235_);
v___x_221_ = v___x_210_;
v_isShared_222_ = v_isSharedCheck_234_;
goto v_resetjp_220_;
}
else
{
lean_inc(v_snapshotTasks_219_);
lean_inc(v_infoState_218_);
lean_inc(v_messages_217_);
lean_inc(v_traceState_216_);
lean_inc(v_auxDeclNGen_215_);
lean_inc(v_ngen_214_);
lean_inc(v_nextMacroScope_213_);
lean_inc(v_env_212_);
lean_dec(v___x_210_);
v___x_221_ = lean_box(0);
v_isShared_222_ = v_isSharedCheck_234_;
goto v_resetjp_220_;
}
v_resetjp_220_:
{
lean_object* v_name_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_227_; 
v_name_223_ = lean_ctor_get(v_toSignature_211_, 0);
lean_inc(v_name_223_);
v___x_224_ = l_Lean_Compiler_LCNF_recordFinalImpureDecl(v_env_212_, v_name_223_);
v___x_225_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure_spec__1___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure_spec__1___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure_spec__1___redArg___closed__2);
if (v_isShared_222_ == 0)
{
lean_ctor_set(v___x_221_, 5, v___x_225_);
lean_ctor_set(v___x_221_, 0, v___x_224_);
v___x_227_ = v___x_221_;
goto v_reusejp_226_;
}
else
{
lean_object* v_reuseFailAlloc_233_; 
v_reuseFailAlloc_233_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_233_, 0, v___x_224_);
lean_ctor_set(v_reuseFailAlloc_233_, 1, v_nextMacroScope_213_);
lean_ctor_set(v_reuseFailAlloc_233_, 2, v_ngen_214_);
lean_ctor_set(v_reuseFailAlloc_233_, 3, v_auxDeclNGen_215_);
lean_ctor_set(v_reuseFailAlloc_233_, 4, v_traceState_216_);
lean_ctor_set(v_reuseFailAlloc_233_, 5, v___x_225_);
lean_ctor_set(v_reuseFailAlloc_233_, 6, v_messages_217_);
lean_ctor_set(v_reuseFailAlloc_233_, 7, v_infoState_218_);
lean_ctor_set(v_reuseFailAlloc_233_, 8, v_snapshotTasks_219_);
v___x_227_ = v_reuseFailAlloc_233_;
goto v_reusejp_226_;
}
v_reusejp_226_:
{
lean_object* v___x_228_; lean_object* v___x_229_; size_t v___x_230_; size_t v___x_231_; 
v___x_228_ = lean_st_ref_set(v___y_204_, v___x_227_);
v___x_229_ = lean_box(0);
v___x_230_ = ((size_t)1ULL);
v___x_231_ = lean_usize_add(v_i_202_, v___x_230_);
v_i_202_ = v___x_231_;
v_b_203_ = v___x_229_;
goto _start;
}
}
}
else
{
return v___x_209_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure_spec__1___redArg___boxed(lean_object* v_as_236_, lean_object* v_sz_237_, lean_object* v_i_238_, lean_object* v_b_239_, lean_object* v___y_240_, lean_object* v___y_241_){
_start:
{
size_t v_sz_boxed_242_; size_t v_i_boxed_243_; lean_object* v_res_244_; 
v_sz_boxed_242_ = lean_unbox_usize(v_sz_237_);
lean_dec(v_sz_237_);
v_i_boxed_243_ = lean_unbox_usize(v_i_238_);
lean_dec(v_i_238_);
v_res_244_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure_spec__1___redArg(v_as_236_, v_sz_boxed_242_, v_i_boxed_243_, v_b_239_, v___y_240_);
lean_dec(v___y_240_);
lean_dec_ref(v_as_236_);
return v_res_244_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___lam__0(uint8_t v___x_245_, lean_object* v___x_246_, lean_object* v___x_247_, uint8_t v___x_248_, size_t v___x_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_){
_start:
{
lean_object* v___x_255_; 
v___x_255_ = l_Lean_Compiler_LCNF_Decl_internalize(v___x_245_, v___x_246_, v___x_247_, v___x_248_, v___y_250_, v___y_251_, v___y_252_, v___y_253_);
if (lean_obj_tag(v___x_255_) == 0)
{
lean_object* v_a_256_; lean_object* v___x_257_; 
v_a_256_ = lean_ctor_get(v___x_255_, 0);
lean_inc(v_a_256_);
lean_dec_ref(v___x_255_);
lean_inc(v_a_256_);
v___x_257_ = l_Lean_Compiler_LCNF_Decl_saveImpure___redArg(v_a_256_, v___y_253_);
if (lean_obj_tag(v___x_257_) == 0)
{
lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; 
lean_dec_ref(v___x_257_);
v___x_258_ = lean_unsigned_to_nat(1u);
v___x_259_ = lean_mk_empty_array_with_capacity(v___x_258_);
v___x_260_ = lean_array_push(v___x_259_, v_a_256_);
v___x_261_ = l_Lean_Compiler_LCNF_addBoxedVersions(v___x_260_, v___y_250_, v___y_251_, v___y_252_, v___y_253_);
if (lean_obj_tag(v___x_261_) == 0)
{
lean_object* v_a_262_; lean_object* v___x_263_; 
v_a_262_ = lean_ctor_get(v___x_261_, 0);
lean_inc(v_a_262_);
lean_dec_ref(v___x_261_);
v___x_263_ = l_Lean_Compiler_LCNF_runExplicitRc(v_a_262_, v___y_250_, v___y_251_, v___y_252_, v___y_253_);
if (lean_obj_tag(v___x_263_) == 0)
{
lean_object* v_a_264_; lean_object* v___x_265_; size_t v_sz_266_; lean_object* v___x_267_; 
v_a_264_ = lean_ctor_get(v___x_263_, 0);
lean_inc(v_a_264_);
lean_dec_ref(v___x_263_);
v___x_265_ = lean_box(0);
v_sz_266_ = lean_array_size(v_a_264_);
v___x_267_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure_spec__1___redArg(v_a_264_, v_sz_266_, v___x_249_, v___x_265_, v___y_253_);
if (lean_obj_tag(v___x_267_) == 0)
{
lean_object* v___x_269_; uint8_t v_isShared_270_; uint8_t v_isSharedCheck_274_; 
v_isSharedCheck_274_ = !lean_is_exclusive(v___x_267_);
if (v_isSharedCheck_274_ == 0)
{
lean_object* v_unused_275_; 
v_unused_275_ = lean_ctor_get(v___x_267_, 0);
lean_dec(v_unused_275_);
v___x_269_ = v___x_267_;
v_isShared_270_ = v_isSharedCheck_274_;
goto v_resetjp_268_;
}
else
{
lean_dec(v___x_267_);
v___x_269_ = lean_box(0);
v_isShared_270_ = v_isSharedCheck_274_;
goto v_resetjp_268_;
}
v_resetjp_268_:
{
lean_object* v___x_272_; 
if (v_isShared_270_ == 0)
{
lean_ctor_set(v___x_269_, 0, v_a_264_);
v___x_272_ = v___x_269_;
goto v_reusejp_271_;
}
else
{
lean_object* v_reuseFailAlloc_273_; 
v_reuseFailAlloc_273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_273_, 0, v_a_264_);
v___x_272_ = v_reuseFailAlloc_273_;
goto v_reusejp_271_;
}
v_reusejp_271_:
{
return v___x_272_;
}
}
}
else
{
lean_object* v_a_276_; lean_object* v___x_278_; uint8_t v_isShared_279_; uint8_t v_isSharedCheck_283_; 
lean_dec(v_a_264_);
v_a_276_ = lean_ctor_get(v___x_267_, 0);
v_isSharedCheck_283_ = !lean_is_exclusive(v___x_267_);
if (v_isSharedCheck_283_ == 0)
{
v___x_278_ = v___x_267_;
v_isShared_279_ = v_isSharedCheck_283_;
goto v_resetjp_277_;
}
else
{
lean_inc(v_a_276_);
lean_dec(v___x_267_);
v___x_278_ = lean_box(0);
v_isShared_279_ = v_isSharedCheck_283_;
goto v_resetjp_277_;
}
v_resetjp_277_:
{
lean_object* v___x_281_; 
if (v_isShared_279_ == 0)
{
v___x_281_ = v___x_278_;
goto v_reusejp_280_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_282_, 0, v_a_276_);
v___x_281_ = v_reuseFailAlloc_282_;
goto v_reusejp_280_;
}
v_reusejp_280_:
{
return v___x_281_;
}
}
}
}
else
{
return v___x_263_;
}
}
else
{
return v___x_261_;
}
}
else
{
lean_object* v_a_284_; lean_object* v___x_286_; uint8_t v_isShared_287_; uint8_t v_isSharedCheck_291_; 
lean_dec(v_a_256_);
v_a_284_ = lean_ctor_get(v___x_257_, 0);
v_isSharedCheck_291_ = !lean_is_exclusive(v___x_257_);
if (v_isSharedCheck_291_ == 0)
{
v___x_286_ = v___x_257_;
v_isShared_287_ = v_isSharedCheck_291_;
goto v_resetjp_285_;
}
else
{
lean_inc(v_a_284_);
lean_dec(v___x_257_);
v___x_286_ = lean_box(0);
v_isShared_287_ = v_isSharedCheck_291_;
goto v_resetjp_285_;
}
v_resetjp_285_:
{
lean_object* v___x_289_; 
if (v_isShared_287_ == 0)
{
v___x_289_ = v___x_286_;
goto v_reusejp_288_;
}
else
{
lean_object* v_reuseFailAlloc_290_; 
v_reuseFailAlloc_290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_290_, 0, v_a_284_);
v___x_289_ = v_reuseFailAlloc_290_;
goto v_reusejp_288_;
}
v_reusejp_288_:
{
return v___x_289_;
}
}
}
}
else
{
lean_object* v_a_292_; lean_object* v___x_294_; uint8_t v_isShared_295_; uint8_t v_isSharedCheck_299_; 
v_a_292_ = lean_ctor_get(v___x_255_, 0);
v_isSharedCheck_299_ = !lean_is_exclusive(v___x_255_);
if (v_isSharedCheck_299_ == 0)
{
v___x_294_ = v___x_255_;
v_isShared_295_ = v_isSharedCheck_299_;
goto v_resetjp_293_;
}
else
{
lean_inc(v_a_292_);
lean_dec(v___x_255_);
v___x_294_ = lean_box(0);
v_isShared_295_ = v_isSharedCheck_299_;
goto v_resetjp_293_;
}
v_resetjp_293_:
{
lean_object* v___x_297_; 
if (v_isShared_295_ == 0)
{
v___x_297_ = v___x_294_;
goto v_reusejp_296_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v_a_292_);
v___x_297_ = v_reuseFailAlloc_298_;
goto v_reusejp_296_;
}
v_reusejp_296_:
{
return v___x_297_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___lam__0___boxed(lean_object* v___x_300_, lean_object* v___x_301_, lean_object* v___x_302_, lean_object* v___x_303_, lean_object* v___x_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_){
_start:
{
uint8_t v___x_2775__boxed_310_; uint8_t v___x_2778__boxed_311_; size_t v___x_2779__boxed_312_; lean_object* v_res_313_; 
v___x_2775__boxed_310_ = lean_unbox(v___x_300_);
v___x_2778__boxed_311_ = lean_unbox(v___x_303_);
v___x_2779__boxed_312_ = lean_unbox_usize(v___x_304_);
lean_dec(v___x_304_);
v_res_313_ = l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___lam__0(v___x_2775__boxed_310_, v___x_301_, v___x_302_, v___x_2778__boxed_311_, v___x_2779__boxed_312_, v___y_305_, v___y_306_, v___y_307_, v___y_308_);
lean_dec(v___y_308_);
lean_dec_ref(v___y_307_);
lean_dec(v___y_306_);
lean_dec_ref(v___y_305_);
return v_res_313_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure_spec__0(size_t v_sz_314_, size_t v_i_315_, lean_object* v_bs_316_, lean_object* v___y_317_, lean_object* v___y_318_){
_start:
{
uint8_t v___x_320_; 
v___x_320_ = lean_usize_dec_lt(v_i_315_, v_sz_314_);
if (v___x_320_ == 0)
{
lean_object* v___x_321_; 
v___x_321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_321_, 0, v_bs_316_);
return v___x_321_;
}
else
{
lean_object* v_v_322_; lean_object* v_fvarId_323_; lean_object* v_binderName_324_; lean_object* v_type_325_; uint8_t v_borrow_326_; lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_350_; 
v_v_322_ = lean_array_uget(v_bs_316_, v_i_315_);
v_fvarId_323_ = lean_ctor_get(v_v_322_, 0);
v_binderName_324_ = lean_ctor_get(v_v_322_, 1);
v_type_325_ = lean_ctor_get(v_v_322_, 2);
v_borrow_326_ = lean_ctor_get_uint8(v_v_322_, sizeof(void*)*3);
v_isSharedCheck_350_ = !lean_is_exclusive(v_v_322_);
if (v_isSharedCheck_350_ == 0)
{
v___x_328_ = v_v_322_;
v_isShared_329_ = v_isSharedCheck_350_;
goto v_resetjp_327_;
}
else
{
lean_inc(v_type_325_);
lean_inc(v_binderName_324_);
lean_inc(v_fvarId_323_);
lean_dec(v_v_322_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_350_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
uint8_t v___x_330_; lean_object* v___x_331_; 
v___x_330_ = 0;
v___x_331_ = l_Lean_Compiler_LCNF_toImpureType(v_type_325_, v___x_330_, v___y_317_, v___y_318_);
if (lean_obj_tag(v___x_331_) == 0)
{
lean_object* v_a_332_; lean_object* v___x_333_; lean_object* v_bs_x27_334_; lean_object* v___x_336_; 
v_a_332_ = lean_ctor_get(v___x_331_, 0);
lean_inc(v_a_332_);
lean_dec_ref(v___x_331_);
v___x_333_ = lean_unsigned_to_nat(0u);
v_bs_x27_334_ = lean_array_uset(v_bs_316_, v_i_315_, v___x_333_);
if (v_isShared_329_ == 0)
{
lean_ctor_set(v___x_328_, 2, v_a_332_);
v___x_336_ = v___x_328_;
goto v_reusejp_335_;
}
else
{
lean_object* v_reuseFailAlloc_341_; 
v_reuseFailAlloc_341_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_341_, 0, v_fvarId_323_);
lean_ctor_set(v_reuseFailAlloc_341_, 1, v_binderName_324_);
lean_ctor_set(v_reuseFailAlloc_341_, 2, v_a_332_);
lean_ctor_set_uint8(v_reuseFailAlloc_341_, sizeof(void*)*3, v_borrow_326_);
v___x_336_ = v_reuseFailAlloc_341_;
goto v_reusejp_335_;
}
v_reusejp_335_:
{
size_t v___x_337_; size_t v___x_338_; lean_object* v___x_339_; 
v___x_337_ = ((size_t)1ULL);
v___x_338_ = lean_usize_add(v_i_315_, v___x_337_);
v___x_339_ = lean_array_uset(v_bs_x27_334_, v_i_315_, v___x_336_);
v_i_315_ = v___x_338_;
v_bs_316_ = v___x_339_;
goto _start;
}
}
else
{
lean_object* v_a_342_; lean_object* v___x_344_; uint8_t v_isShared_345_; uint8_t v_isSharedCheck_349_; 
lean_del_object(v___x_328_);
lean_dec(v_binderName_324_);
lean_dec(v_fvarId_323_);
lean_dec_ref(v_bs_316_);
v_a_342_ = lean_ctor_get(v___x_331_, 0);
v_isSharedCheck_349_ = !lean_is_exclusive(v___x_331_);
if (v_isSharedCheck_349_ == 0)
{
v___x_344_ = v___x_331_;
v_isShared_345_ = v_isSharedCheck_349_;
goto v_resetjp_343_;
}
else
{
lean_inc(v_a_342_);
lean_dec(v___x_331_);
v___x_344_ = lean_box(0);
v_isShared_345_ = v_isSharedCheck_349_;
goto v_resetjp_343_;
}
v_resetjp_343_:
{
lean_object* v___x_347_; 
if (v_isShared_345_ == 0)
{
v___x_347_ = v___x_344_;
goto v_reusejp_346_;
}
else
{
lean_object* v_reuseFailAlloc_348_; 
v_reuseFailAlloc_348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_348_, 0, v_a_342_);
v___x_347_ = v_reuseFailAlloc_348_;
goto v_reusejp_346_;
}
v_reusejp_346_:
{
return v___x_347_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure_spec__0___boxed(lean_object* v_sz_351_, lean_object* v_i_352_, lean_object* v_bs_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_){
_start:
{
size_t v_sz_boxed_357_; size_t v_i_boxed_358_; lean_object* v_res_359_; 
v_sz_boxed_357_ = lean_unbox_usize(v_sz_351_);
lean_dec(v_sz_351_);
v_i_boxed_358_ = lean_unbox_usize(v_i_352_);
lean_dec(v_i_352_);
v_res_359_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure_spec__0(v_sz_boxed_357_, v_i_boxed_358_, v_bs_353_, v___y_354_, v___y_355_);
lean_dec(v___y_355_);
lean_dec_ref(v___y_354_);
return v_res_359_;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___closed__0(void){
_start:
{
lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; 
v___x_360_ = lean_box(0);
v___x_361_ = lean_unsigned_to_nat(16u);
v___x_362_ = lean_mk_array(v___x_361_, v___x_360_);
return v___x_362_;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___closed__1(void){
_start:
{
lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; 
v___x_363_ = lean_obj_once(&l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___closed__0, &l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___closed__0_once, _init_l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___closed__0);
v___x_364_ = lean_unsigned_to_nat(0u);
v___x_365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_365_, 0, v___x_364_);
lean_ctor_set(v___x_365_, 1, v___x_363_);
return v___x_365_;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___closed__2(void){
_start:
{
lean_object* v___x_366_; lean_object* v___x_367_; 
v___x_366_ = lean_obj_once(&l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___closed__1, &l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___closed__1_once, _init_l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___closed__1);
v___x_367_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_367_, 0, v___x_366_);
lean_ctor_set(v___x_367_, 1, v___x_366_);
lean_ctor_set(v___x_367_, 2, v___x_366_);
lean_ctor_set(v___x_367_, 3, v___x_366_);
lean_ctor_set(v___x_367_, 4, v___x_366_);
lean_ctor_set(v___x_367_, 5, v___x_366_);
return v___x_367_;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___closed__3(void){
_start:
{
lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_368_ = lean_unsigned_to_nat(1u);
v___x_369_ = lean_obj_once(&l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___closed__2, &l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___closed__2_once, _init_l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___closed__2);
v___x_370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_370_, 0, v___x_369_);
lean_ctor_set(v___x_370_, 1, v___x_368_);
return v___x_370_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure(lean_object* v_externAttrData_373_, lean_object* v_decl_374_, lean_object* v_a_375_, lean_object* v_a_376_){
_start:
{
lean_object* v_toSignature_378_; lean_object* v___x_380_; uint8_t v_isShared_381_; uint8_t v_isSharedCheck_432_; 
v_toSignature_378_ = lean_ctor_get(v_decl_374_, 0);
v_isSharedCheck_432_ = !lean_is_exclusive(v_decl_374_);
if (v_isSharedCheck_432_ == 0)
{
lean_object* v_unused_433_; lean_object* v_unused_434_; 
v_unused_433_ = lean_ctor_get(v_decl_374_, 2);
lean_dec(v_unused_433_);
v_unused_434_ = lean_ctor_get(v_decl_374_, 1);
lean_dec(v_unused_434_);
v___x_380_ = v_decl_374_;
v_isShared_381_ = v_isSharedCheck_432_;
goto v_resetjp_379_;
}
else
{
lean_inc(v_toSignature_378_);
lean_dec(v_decl_374_);
v___x_380_ = lean_box(0);
v_isShared_381_ = v_isSharedCheck_432_;
goto v_resetjp_379_;
}
v_resetjp_379_:
{
lean_object* v_name_382_; lean_object* v_levelParams_383_; lean_object* v_type_384_; lean_object* v_params_385_; lean_object* v___x_387_; uint8_t v_isShared_388_; uint8_t v_isSharedCheck_431_; 
v_name_382_ = lean_ctor_get(v_toSignature_378_, 0);
v_levelParams_383_ = lean_ctor_get(v_toSignature_378_, 1);
v_type_384_ = lean_ctor_get(v_toSignature_378_, 2);
v_params_385_ = lean_ctor_get(v_toSignature_378_, 3);
v_isSharedCheck_431_ = !lean_is_exclusive(v_toSignature_378_);
if (v_isSharedCheck_431_ == 0)
{
v___x_387_ = v_toSignature_378_;
v_isShared_388_ = v_isSharedCheck_431_;
goto v_resetjp_386_;
}
else
{
lean_inc(v_params_385_);
lean_inc(v_type_384_);
lean_inc(v_levelParams_383_);
lean_inc(v_name_382_);
lean_dec(v_toSignature_378_);
v___x_387_ = lean_box(0);
v_isShared_388_ = v_isSharedCheck_431_;
goto v_resetjp_386_;
}
v_resetjp_386_:
{
lean_object* v___x_389_; lean_object* v___x_390_; 
v___x_389_ = lean_array_get_size(v_params_385_);
v___x_390_ = l_Lean_Compiler_LCNF_lowerResultType(v_type_384_, v___x_389_, v_a_375_, v_a_376_);
lean_dec_ref(v_type_384_);
if (lean_obj_tag(v___x_390_) == 0)
{
lean_object* v_a_391_; size_t v_sz_392_; size_t v___x_393_; lean_object* v___x_394_; 
v_a_391_ = lean_ctor_get(v___x_390_, 0);
lean_inc(v_a_391_);
lean_dec_ref(v___x_390_);
v_sz_392_ = lean_array_size(v_params_385_);
v___x_393_ = ((size_t)0ULL);
v___x_394_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure_spec__0(v_sz_392_, v___x_393_, v_params_385_, v_a_375_, v_a_376_);
if (lean_obj_tag(v___x_394_) == 0)
{
lean_object* v_a_395_; uint8_t v___x_396_; uint8_t v___x_397_; lean_object* v___x_399_; 
v_a_395_ = lean_ctor_get(v___x_394_, 0);
lean_inc(v_a_395_);
lean_dec_ref(v___x_394_);
v___x_396_ = 1;
v___x_397_ = 1;
if (v_isShared_388_ == 0)
{
lean_ctor_set(v___x_387_, 3, v_a_395_);
lean_ctor_set(v___x_387_, 2, v_a_391_);
v___x_399_ = v___x_387_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_414_; 
v_reuseFailAlloc_414_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_414_, 0, v_name_382_);
lean_ctor_set(v_reuseFailAlloc_414_, 1, v_levelParams_383_);
lean_ctor_set(v_reuseFailAlloc_414_, 2, v_a_391_);
lean_ctor_set(v_reuseFailAlloc_414_, 3, v_a_395_);
v___x_399_ = v_reuseFailAlloc_414_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
lean_object* v___x_400_; uint8_t v___x_401_; lean_object* v___x_402_; lean_object* v___x_404_; 
lean_ctor_set_uint8(v___x_399_, sizeof(void*)*4, v___x_397_);
v___x_400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_400_, 0, v_externAttrData_373_);
v___x_401_ = 0;
v___x_402_ = ((lean_object*)(l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono___closed__1));
if (v_isShared_381_ == 0)
{
lean_ctor_set(v___x_380_, 2, v___x_402_);
lean_ctor_set(v___x_380_, 1, v___x_400_);
lean_ctor_set(v___x_380_, 0, v___x_399_);
v___x_404_ = v___x_380_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v___x_399_);
lean_ctor_set(v_reuseFailAlloc_413_, 1, v___x_400_);
lean_ctor_set(v_reuseFailAlloc_413_, 2, v___x_402_);
v___x_404_ = v_reuseFailAlloc_413_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___f_409_; lean_object* v___x_410_; uint8_t v___x_411_; lean_object* v___x_412_; 
lean_ctor_set_uint8(v___x_404_, sizeof(void*)*3, v___x_401_);
v___x_405_ = lean_obj_once(&l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___closed__1, &l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___closed__1_once, _init_l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___closed__1);
v___x_406_ = lean_box(v___x_396_);
v___x_407_ = lean_box(v___x_401_);
v___x_408_ = ((lean_object*)(l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___boxed__const__1));
v___f_409_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___lam__0___boxed), 10, 5);
lean_closure_set(v___f_409_, 0, v___x_406_);
lean_closure_set(v___f_409_, 1, v___x_404_);
lean_closure_set(v___f_409_, 2, v___x_405_);
lean_closure_set(v___f_409_, 3, v___x_407_);
lean_closure_set(v___f_409_, 4, v___x_408_);
v___x_410_ = lean_obj_once(&l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___closed__3, &l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___closed__3_once, _init_l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___closed__3);
v___x_411_ = 2;
v___x_412_ = l_Lean_Compiler_LCNF_CompilerM_run___redArg(v___f_409_, v___x_410_, v___x_411_, v_a_375_, v_a_376_);
return v___x_412_;
}
}
}
else
{
lean_object* v_a_415_; lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_422_; 
lean_dec(v_a_391_);
lean_del_object(v___x_387_);
lean_dec(v_levelParams_383_);
lean_dec(v_name_382_);
lean_del_object(v___x_380_);
lean_dec(v_externAttrData_373_);
v_a_415_ = lean_ctor_get(v___x_394_, 0);
v_isSharedCheck_422_ = !lean_is_exclusive(v___x_394_);
if (v_isSharedCheck_422_ == 0)
{
v___x_417_ = v___x_394_;
v_isShared_418_ = v_isSharedCheck_422_;
goto v_resetjp_416_;
}
else
{
lean_inc(v_a_415_);
lean_dec(v___x_394_);
v___x_417_ = lean_box(0);
v_isShared_418_ = v_isSharedCheck_422_;
goto v_resetjp_416_;
}
v_resetjp_416_:
{
lean_object* v___x_420_; 
if (v_isShared_418_ == 0)
{
v___x_420_ = v___x_417_;
goto v_reusejp_419_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v_a_415_);
v___x_420_ = v_reuseFailAlloc_421_;
goto v_reusejp_419_;
}
v_reusejp_419_:
{
return v___x_420_;
}
}
}
}
else
{
lean_object* v_a_423_; lean_object* v___x_425_; uint8_t v_isShared_426_; uint8_t v_isSharedCheck_430_; 
lean_del_object(v___x_387_);
lean_dec_ref(v_params_385_);
lean_dec(v_levelParams_383_);
lean_dec(v_name_382_);
lean_del_object(v___x_380_);
lean_dec(v_externAttrData_373_);
v_a_423_ = lean_ctor_get(v___x_390_, 0);
v_isSharedCheck_430_ = !lean_is_exclusive(v___x_390_);
if (v_isSharedCheck_430_ == 0)
{
v___x_425_ = v___x_390_;
v_isShared_426_ = v_isSharedCheck_430_;
goto v_resetjp_424_;
}
else
{
lean_inc(v_a_423_);
lean_dec(v___x_390_);
v___x_425_ = lean_box(0);
v_isShared_426_ = v_isSharedCheck_430_;
goto v_resetjp_424_;
}
v_resetjp_424_:
{
lean_object* v___x_428_; 
if (v_isShared_426_ == 0)
{
v___x_428_ = v___x_425_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_429_; 
v_reuseFailAlloc_429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_429_, 0, v_a_423_);
v___x_428_ = v_reuseFailAlloc_429_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
return v___x_428_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___boxed(lean_object* v_externAttrData_435_, lean_object* v_decl_436_, lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_){
_start:
{
lean_object* v_res_440_; 
v_res_440_ = l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure(v_externAttrData_435_, v_decl_436_, v_a_437_, v_a_438_);
lean_dec(v_a_438_);
lean_dec_ref(v_a_437_);
return v_res_440_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure_spec__1(lean_object* v_as_441_, size_t v_sz_442_, size_t v_i_443_, lean_object* v_b_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_){
_start:
{
lean_object* v___x_450_; 
v___x_450_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure_spec__1___redArg(v_as_441_, v_sz_442_, v_i_443_, v_b_444_, v___y_448_);
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure_spec__1___boxed(lean_object* v_as_451_, lean_object* v_sz_452_, lean_object* v_i_453_, lean_object* v_b_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_){
_start:
{
size_t v_sz_boxed_460_; size_t v_i_boxed_461_; lean_object* v_res_462_; 
v_sz_boxed_460_ = lean_unbox_usize(v_sz_452_);
lean_dec(v_sz_452_);
v_i_boxed_461_ = lean_unbox_usize(v_i_453_);
lean_dec(v_i_453_);
v_res_462_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure_spec__1(v_as_451_, v_sz_boxed_460_, v_i_boxed_461_, v_b_454_, v___y_455_, v___y_456_, v___y_457_, v___y_458_);
lean_dec(v___y_458_);
lean_dec_ref(v___y_457_);
lean_dec(v___y_456_);
lean_dec_ref(v___y_455_);
lean_dec_ref(v_as_451_);
return v_res_462_;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addIr___closed__2(void){
_start:
{
lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; 
v___x_466_ = ((lean_object*)(l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addIr___closed__1));
v___x_467_ = l_Lean_IR_tracePrefixOptionName;
v___x_468_ = l_Lean_Name_append(v___x_467_, v___x_466_);
return v___x_468_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addIr(lean_object* v_decls_469_, lean_object* v_a_470_, lean_object* v_a_471_){
_start:
{
lean_object* v___x_473_; 
v___x_473_ = l_Lean_IR_toIR(v_decls_469_, v_a_470_, v_a_471_);
if (lean_obj_tag(v___x_473_) == 0)
{
lean_object* v_a_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; 
v_a_474_ = lean_ctor_get(v___x_473_, 0);
lean_inc(v_a_474_);
lean_dec_ref(v___x_473_);
v___x_475_ = ((lean_object*)(l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addIr___closed__1));
v___x_476_ = lean_obj_once(&l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addIr___closed__2, &l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addIr___closed__2_once, _init_l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addIr___closed__2);
lean_inc(v_a_474_);
v___x_477_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(v___x_476_, v___x_475_, v_a_474_, v_a_470_, v_a_471_);
if (lean_obj_tag(v___x_477_) == 0)
{
lean_object* v___x_478_; 
lean_dec_ref(v___x_477_);
v___x_478_ = l_Lean_IR_addDecls(v_a_474_, v_a_470_, v_a_471_);
lean_dec(v_a_474_);
return v___x_478_;
}
else
{
lean_dec(v_a_474_);
return v___x_477_;
}
}
else
{
lean_object* v_a_479_; lean_object* v___x_481_; uint8_t v_isShared_482_; uint8_t v_isSharedCheck_486_; 
v_a_479_ = lean_ctor_get(v___x_473_, 0);
v_isSharedCheck_486_ = !lean_is_exclusive(v___x_473_);
if (v_isSharedCheck_486_ == 0)
{
v___x_481_ = v___x_473_;
v_isShared_482_ = v_isSharedCheck_486_;
goto v_resetjp_480_;
}
else
{
lean_inc(v_a_479_);
lean_dec(v___x_473_);
v___x_481_ = lean_box(0);
v_isShared_482_ = v_isSharedCheck_486_;
goto v_resetjp_480_;
}
v_resetjp_480_:
{
lean_object* v___x_484_; 
if (v_isShared_482_ == 0)
{
v___x_484_ = v___x_481_;
goto v_reusejp_483_;
}
else
{
lean_object* v_reuseFailAlloc_485_; 
v_reuseFailAlloc_485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_485_, 0, v_a_479_);
v___x_484_ = v_reuseFailAlloc_485_;
goto v_reusejp_483_;
}
v_reusejp_483_:
{
return v___x_484_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addIr___boxed(lean_object* v_decls_487_, lean_object* v_a_488_, lean_object* v_a_489_, lean_object* v_a_490_){
_start:
{
lean_object* v_res_491_; 
v_res_491_ = l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addIr(v_decls_487_, v_a_488_, v_a_489_);
lean_dec(v_a_489_);
lean_dec_ref(v_a_488_);
lean_dec_ref(v_decls_487_);
return v_res_491_;
}
}
LEAN_EXPORT lean_object* lean_add_extern(lean_object* v_declName_492_, lean_object* v_externAttrData_493_, lean_object* v_a_494_, lean_object* v_a_495_){
_start:
{
lean_object* v___y_498_; lean_object* v___y_499_; uint8_t v___x_521_; 
v___x_521_ = l_Lean_isPrivateName(v_declName_492_);
if (v___x_521_ == 0)
{
lean_object* v___x_522_; lean_object* v_env_523_; lean_object* v_nextMacroScope_524_; lean_object* v_ngen_525_; lean_object* v_auxDeclNGen_526_; lean_object* v_traceState_527_; lean_object* v_messages_528_; lean_object* v_infoState_529_; lean_object* v_snapshotTasks_530_; lean_object* v___x_532_; uint8_t v_isShared_533_; uint8_t v_isSharedCheck_540_; 
v___x_522_ = lean_st_ref_take(v_a_495_);
v_env_523_ = lean_ctor_get(v___x_522_, 0);
v_nextMacroScope_524_ = lean_ctor_get(v___x_522_, 1);
v_ngen_525_ = lean_ctor_get(v___x_522_, 2);
v_auxDeclNGen_526_ = lean_ctor_get(v___x_522_, 3);
v_traceState_527_ = lean_ctor_get(v___x_522_, 4);
v_messages_528_ = lean_ctor_get(v___x_522_, 6);
v_infoState_529_ = lean_ctor_get(v___x_522_, 7);
v_snapshotTasks_530_ = lean_ctor_get(v___x_522_, 8);
v_isSharedCheck_540_ = !lean_is_exclusive(v___x_522_);
if (v_isSharedCheck_540_ == 0)
{
lean_object* v_unused_541_; 
v_unused_541_ = lean_ctor_get(v___x_522_, 5);
lean_dec(v_unused_541_);
v___x_532_ = v___x_522_;
v_isShared_533_ = v_isSharedCheck_540_;
goto v_resetjp_531_;
}
else
{
lean_inc(v_snapshotTasks_530_);
lean_inc(v_infoState_529_);
lean_inc(v_messages_528_);
lean_inc(v_traceState_527_);
lean_inc(v_auxDeclNGen_526_);
lean_inc(v_ngen_525_);
lean_inc(v_nextMacroScope_524_);
lean_inc(v_env_523_);
lean_dec(v___x_522_);
v___x_532_ = lean_box(0);
v_isShared_533_ = v_isSharedCheck_540_;
goto v_resetjp_531_;
}
v_resetjp_531_:
{
lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_537_; 
lean_inc(v_declName_492_);
v___x_534_ = l_Lean_Compiler_LCNF_setDeclPublic(v_env_523_, v_declName_492_);
v___x_535_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure_spec__1___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure_spec__1___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure_spec__1___redArg___closed__2);
if (v_isShared_533_ == 0)
{
lean_ctor_set(v___x_532_, 5, v___x_535_);
lean_ctor_set(v___x_532_, 0, v___x_534_);
v___x_537_ = v___x_532_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v___x_534_);
lean_ctor_set(v_reuseFailAlloc_539_, 1, v_nextMacroScope_524_);
lean_ctor_set(v_reuseFailAlloc_539_, 2, v_ngen_525_);
lean_ctor_set(v_reuseFailAlloc_539_, 3, v_auxDeclNGen_526_);
lean_ctor_set(v_reuseFailAlloc_539_, 4, v_traceState_527_);
lean_ctor_set(v_reuseFailAlloc_539_, 5, v___x_535_);
lean_ctor_set(v_reuseFailAlloc_539_, 6, v_messages_528_);
lean_ctor_set(v_reuseFailAlloc_539_, 7, v_infoState_529_);
lean_ctor_set(v_reuseFailAlloc_539_, 8, v_snapshotTasks_530_);
v___x_537_ = v_reuseFailAlloc_539_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
lean_object* v___x_538_; 
v___x_538_ = lean_st_ref_set(v_a_495_, v___x_537_);
v___y_498_ = v_a_494_;
v___y_499_ = v_a_495_;
goto v___jp_497_;
}
}
}
else
{
v___y_498_ = v_a_494_;
v___y_499_ = v_a_495_;
goto v___jp_497_;
}
v___jp_497_:
{
lean_object* v___x_500_; 
lean_inc(v_externAttrData_493_);
v___x_500_ = l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono(v_externAttrData_493_, v_declName_492_, v___y_498_, v___y_499_);
if (lean_obj_tag(v___x_500_) == 0)
{
lean_object* v_a_501_; lean_object* v___x_502_; 
v_a_501_ = lean_ctor_get(v___x_500_, 0);
lean_inc(v_a_501_);
lean_dec_ref(v___x_500_);
v___x_502_ = l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure(v_externAttrData_493_, v_a_501_, v___y_498_, v___y_499_);
if (lean_obj_tag(v___x_502_) == 0)
{
lean_object* v_a_503_; lean_object* v___x_504_; 
v_a_503_ = lean_ctor_get(v___x_502_, 0);
lean_inc(v_a_503_);
lean_dec_ref(v___x_502_);
v___x_504_ = l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addIr(v_a_503_, v___y_498_, v___y_499_);
lean_dec(v___y_499_);
lean_dec_ref(v___y_498_);
lean_dec(v_a_503_);
return v___x_504_;
}
else
{
lean_object* v_a_505_; lean_object* v___x_507_; uint8_t v_isShared_508_; uint8_t v_isSharedCheck_512_; 
lean_dec(v___y_499_);
lean_dec_ref(v___y_498_);
v_a_505_ = lean_ctor_get(v___x_502_, 0);
v_isSharedCheck_512_ = !lean_is_exclusive(v___x_502_);
if (v_isSharedCheck_512_ == 0)
{
v___x_507_ = v___x_502_;
v_isShared_508_ = v_isSharedCheck_512_;
goto v_resetjp_506_;
}
else
{
lean_inc(v_a_505_);
lean_dec(v___x_502_);
v___x_507_ = lean_box(0);
v_isShared_508_ = v_isSharedCheck_512_;
goto v_resetjp_506_;
}
v_resetjp_506_:
{
lean_object* v___x_510_; 
if (v_isShared_508_ == 0)
{
v___x_510_ = v___x_507_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v_a_505_);
v___x_510_ = v_reuseFailAlloc_511_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
return v___x_510_;
}
}
}
}
else
{
lean_object* v_a_513_; lean_object* v___x_515_; uint8_t v_isShared_516_; uint8_t v_isSharedCheck_520_; 
lean_dec(v___y_499_);
lean_dec_ref(v___y_498_);
lean_dec(v_externAttrData_493_);
v_a_513_ = lean_ctor_get(v___x_500_, 0);
v_isSharedCheck_520_ = !lean_is_exclusive(v___x_500_);
if (v_isSharedCheck_520_ == 0)
{
v___x_515_ = v___x_500_;
v_isShared_516_ = v_isSharedCheck_520_;
goto v_resetjp_514_;
}
else
{
lean_inc(v_a_513_);
lean_dec(v___x_500_);
v___x_515_ = lean_box(0);
v_isShared_516_ = v_isSharedCheck_520_;
goto v_resetjp_514_;
}
v_resetjp_514_:
{
lean_object* v___x_518_; 
if (v_isShared_516_ == 0)
{
v___x_518_ = v___x_515_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v_a_513_);
v___x_518_ = v_reuseFailAlloc_519_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
return v___x_518_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addExtern___boxed(lean_object* v_declName_542_, lean_object* v_externAttrData_543_, lean_object* v_a_544_, lean_object* v_a_545_, lean_object* v_a_546_){
_start:
{
lean_object* v_res_547_; 
v_res_547_ = lean_add_extern(v_declName_542_, v_externAttrData_543_, v_a_544_, v_a_545_);
return v_res_547_;
}
}
lean_object* runtime_initialize_Init_While(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_IR_ToIR(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_ToImpureType(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_ToImpure(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_ExplicitBoxing(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_Internalize(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_ExternAttr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_ExplicitRC(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_Options(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_IR_AddExtern(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_IR_ToIR(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_ToImpureType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_ToImpure(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_ExplicitBoxing(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_Internalize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_ExternAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_ExplicitRC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_Options(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_IR_AddExtern(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_While(uint8_t builtin);
lean_object* initialize_Lean_Compiler_IR_ToIR(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_ToImpureType(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_ToImpure(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_ExplicitBoxing(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_Internalize(uint8_t builtin);
lean_object* initialize_Lean_Compiler_ExternAttr(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_ExplicitRC(uint8_t builtin);
lean_object* initialize_Lean_Compiler_Options(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_IR_AddExtern(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_ToIR(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_ToImpureType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_ToImpure(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_ExplicitBoxing(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Internalize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_ExternAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_ExplicitRC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_Options(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_IR_AddExtern(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_IR_AddExtern(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_IR_AddExtern(builtin);
}
#ifdef __cplusplus
}
#endif
