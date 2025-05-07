// Lean compiler output
// Module: Lean.Elab.Tactic.BVDecide.Frontend.LRAT
// Imports: Lean.Elab.Tactic.BVDecide.Frontend.Attr Lean.Elab.Tactic.BVDecide.LRAT.Trim Lean.Elab.Tactic.BVDecide.External Std.Tactic.BVDecide.LRAT.Checker Std.Sat.CNF.Dimacs
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
lean_object* l_Lean_Elab_Tactic_BVDecide_External_satQuery___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_ofFile(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_prim_handle_put_str(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_determineSolver(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_remove_file(lean_object*, lean_object*);
lean_object* l_Lean_mkApp7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkAuxName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instToLevel;
lean_object* l_Lean_isTracingEnabledFor___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20_spec__20___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_prim_handle_flush(lean_object*, lean_object*);
extern lean_object* l_System_FilePath_exeExtension;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_System_FilePath_withExtension(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_determineSolver___redArg(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_System_FilePath_pathExists(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__1(lean_object*, lean_object*);
lean_object* l_IO_lazyPure___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at___Lean_PrettyPrinter_format_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isTracingEnabledFor___at___Lean_Elab_Term_traceAtCmdPos_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__3(lean_object*, lean_object*);
lean_object* l_Lean_instToExprProdOfToLevel___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToString(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at___Lean_Elab_Term_traceAtCmdPos_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
extern lean_object* l_Lean_instToExprNat;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_System_FilePath_parent(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__1(lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_create_tempfile(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_determineSolver___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_determineSolver___redArg___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_instToExprInt;
lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___Lean_Elab_Tactic_BVDecide_External_satQuery_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instToExprArrayOfToLevel___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_io_app_path(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_determineSolver_spec__0(lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_LRAT_parseLRATProof(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KVMap_findCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction;
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_IO_ofExcept___at___IO_FS_Stream_readJson_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Std_Sat_CNF_dimacs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__5(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_sat_solver;
lean_object* l_panic___at___Lean_modToFilePath_go_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_readBinFile(lean_object*, lean_object*);
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_ofFile___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_determineSolver_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_determineSolver_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = l_Lean_KVMap_findCore(x_1, x_3);
if (lean_obj_tag(x_5) == 0)
{
lean_inc(x_4);
return x_4;
}
else
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
return x_7;
}
else
{
lean_dec(x_6);
lean_inc(x_4);
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_determineSolver___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 2);
x_4 = l_Lean_Elab_Tactic_BVDecide_Frontend_sat_solver;
x_5 = l_Lean_Option_get___at___Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_determineSolver_spec__0(x_3, x_4);
x_6 = lean_mk_string_unchecked("", 0, 0);
x_7 = lean_string_dec_eq(x_5, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_2);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_5);
x_9 = lean_io_app_path(x_2);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_29; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_29 = l_System_FilePath_parent(x_10);
lean_dec(x_10);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_30 = lean_mk_string_unchecked("Init.Data.Option.BasicAux", 25, 25);
x_31 = lean_mk_string_unchecked("Option.get!", 11, 11);
x_32 = lean_unsigned_to_nat(21u);
x_33 = lean_unsigned_to_nat(14u);
x_34 = lean_mk_string_unchecked("value is none", 13, 13);
x_35 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_30, x_31, x_32, x_33, x_34);
lean_dec(x_34);
lean_dec(x_31);
lean_dec(x_30);
x_36 = l_panic___at___Lean_modToFilePath_go_spec__0(x_35);
x_12 = x_36;
goto block_28;
}
else
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_29, 0);
lean_inc(x_37);
lean_dec(x_29);
x_12 = x_37;
goto block_28;
}
block_28:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_13 = lean_mk_string_unchecked("cadical", 7, 7);
x_14 = l_System_FilePath_join(x_12, x_13);
x_15 = l_System_FilePath_exeExtension;
x_16 = l_System_FilePath_withExtension(x_14, x_15);
x_17 = l_System_FilePath_pathExists(x_16, x_11);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_unbox(x_18);
lean_dec(x_18);
if (x_19 == 0)
{
uint8_t x_20; 
lean_dec(x_16);
x_20 = !lean_is_exclusive(x_17);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_17, 0);
lean_dec(x_21);
lean_ctor_set(x_17, 0, x_13);
return x_17;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_dec(x_17);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_13);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec(x_13);
x_24 = !lean_is_exclusive(x_17);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_17, 0);
lean_dec(x_25);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_17, 1);
lean_inc(x_26);
lean_dec(x_17);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_16);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_9);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_39 = lean_ctor_get(x_9, 0);
x_40 = lean_ctor_get(x_1, 5);
x_41 = lean_io_error_to_string(x_39);
x_42 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_42, 0, x_41);
x_43 = l_Lean_MessageData_ofFormat(x_42);
lean_inc(x_40);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_40);
lean_ctor_set(x_44, 1, x_43);
lean_ctor_set(x_9, 0, x_44);
return x_9;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_45 = lean_ctor_get(x_9, 0);
x_46 = lean_ctor_get(x_9, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_9);
x_47 = lean_ctor_get(x_1, 5);
x_48 = lean_io_error_to_string(x_45);
x_49 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_49, 0, x_48);
x_50 = l_Lean_MessageData_ofFormat(x_49);
lean_inc(x_47);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_47);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_46);
return x_52;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_determineSolver(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_determineSolver___redArg(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_determineSolver_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Option_get___at___Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_determineSolver_spec__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_determineSolver___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_determineSolver___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_determineSolver___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_determineSolver(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_10 = lean_mk_string_unchecked("_expr_def", 9, 9);
x_11 = l_Lean_Name_mkStr1(x_10);
lean_inc(x_3);
x_12 = l_Lean_Elab_Term_mkAuxName(x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_mk_string_unchecked("_cert_def", 9, 9);
x_16 = l_Lean_Name_mkStr1(x_15);
lean_inc(x_3);
x_17 = l_Lean_Elab_Term_mkAuxName(x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_14);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_mk_string_unchecked("_reflection_def", 15, 15);
x_21 = l_Lean_Name_mkStr1(x_20);
x_22 = l_Lean_Elab_Term_mkAuxName(x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_19);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_22, 1);
x_26 = l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_determineSolver___redArg(x_7, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_29 = x_26;
} else {
 lean_dec_ref(x_26);
 x_29 = lean_box(0);
}
x_34 = lean_mk_string_unchecked("Meta", 4, 4);
x_35 = lean_mk_string_unchecked("Tactic", 6, 6);
x_36 = lean_mk_string_unchecked("sat", 3, 3);
x_37 = l_Lean_Name_mkStr3(x_34, x_35, x_36);
lean_inc(x_37);
x_38 = l_Lean_isTracingEnabledFor___at___Lean_Elab_Term_traceAtCmdPos_spec__0___redArg(x_37, x_7, x_28);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_unbox(x_39);
lean_dec(x_39);
if (x_40 == 0)
{
lean_object* x_41; 
lean_dec(x_37);
lean_free_object(x_22);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_dec(x_38);
x_30 = x_41;
goto block_33;
}
else
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_38);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_43 = lean_ctor_get(x_38, 1);
x_44 = lean_ctor_get(x_38, 0);
lean_dec(x_44);
x_45 = lean_mk_string_unchecked("Using SAT solver at '", 21, 21);
x_46 = l_Lean_stringToMessageData(x_45);
lean_dec(x_45);
lean_inc(x_27);
x_47 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_47, 0, x_27);
x_48 = l_Lean_MessageData_ofFormat(x_47);
lean_ctor_set_tag(x_38, 7);
lean_ctor_set(x_38, 1, x_48);
lean_ctor_set(x_38, 0, x_46);
x_49 = lean_mk_string_unchecked("'", 1, 1);
x_50 = l_Lean_stringToMessageData(x_49);
lean_dec(x_49);
lean_ctor_set_tag(x_22, 7);
lean_ctor_set(x_22, 1, x_50);
lean_ctor_set(x_22, 0, x_38);
x_51 = l_Lean_addTrace___at___Lean_Elab_Term_traceAtCmdPos_spec__1___redArg(x_37, x_22, x_5, x_6, x_7, x_8, x_43);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
lean_dec(x_51);
x_30 = x_52;
goto block_33;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_53 = lean_ctor_get(x_38, 1);
lean_inc(x_53);
lean_dec(x_38);
x_54 = lean_mk_string_unchecked("Using SAT solver at '", 21, 21);
x_55 = l_Lean_stringToMessageData(x_54);
lean_dec(x_54);
lean_inc(x_27);
x_56 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_56, 0, x_27);
x_57 = l_Lean_MessageData_ofFormat(x_56);
x_58 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_57);
x_59 = lean_mk_string_unchecked("'", 1, 1);
x_60 = l_Lean_stringToMessageData(x_59);
lean_dec(x_59);
lean_ctor_set_tag(x_22, 7);
lean_ctor_set(x_22, 1, x_60);
lean_ctor_set(x_22, 0, x_58);
x_61 = l_Lean_addTrace___at___Lean_Elab_Term_traceAtCmdPos_spec__1___redArg(x_37, x_22, x_5, x_6, x_7, x_8, x_53);
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
lean_dec(x_61);
x_30 = x_62;
goto block_33;
}
}
block_33:
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_31, 0, x_13);
lean_ctor_set(x_31, 1, x_18);
lean_ctor_set(x_31, 2, x_24);
lean_ctor_set(x_31, 3, x_27);
lean_ctor_set(x_31, 4, x_1);
lean_ctor_set(x_31, 5, x_2);
if (lean_is_scalar(x_29)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_29;
}
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
else
{
uint8_t x_63; 
lean_free_object(x_22);
lean_dec(x_24);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_2);
lean_dec(x_1);
x_63 = !lean_is_exclusive(x_26);
if (x_63 == 0)
{
return x_26;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_26, 0);
x_65 = lean_ctor_get(x_26, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_26);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_22, 0);
x_68 = lean_ctor_get(x_22, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_22);
x_69 = l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_determineSolver___redArg(x_7, x_68);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
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
x_77 = lean_mk_string_unchecked("Meta", 4, 4);
x_78 = lean_mk_string_unchecked("Tactic", 6, 6);
x_79 = lean_mk_string_unchecked("sat", 3, 3);
x_80 = l_Lean_Name_mkStr3(x_77, x_78, x_79);
lean_inc(x_80);
x_81 = l_Lean_isTracingEnabledFor___at___Lean_Elab_Term_traceAtCmdPos_spec__0___redArg(x_80, x_7, x_71);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_unbox(x_82);
lean_dec(x_82);
if (x_83 == 0)
{
lean_object* x_84; 
lean_dec(x_80);
x_84 = lean_ctor_get(x_81, 1);
lean_inc(x_84);
lean_dec(x_81);
x_73 = x_84;
goto block_76;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_85 = lean_ctor_get(x_81, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_86 = x_81;
} else {
 lean_dec_ref(x_81);
 x_86 = lean_box(0);
}
x_87 = lean_mk_string_unchecked("Using SAT solver at '", 21, 21);
x_88 = l_Lean_stringToMessageData(x_87);
lean_dec(x_87);
lean_inc(x_70);
x_89 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_89, 0, x_70);
x_90 = l_Lean_MessageData_ofFormat(x_89);
if (lean_is_scalar(x_86)) {
 x_91 = lean_alloc_ctor(7, 2, 0);
} else {
 x_91 = x_86;
 lean_ctor_set_tag(x_91, 7);
}
lean_ctor_set(x_91, 0, x_88);
lean_ctor_set(x_91, 1, x_90);
x_92 = lean_mk_string_unchecked("'", 1, 1);
x_93 = l_Lean_stringToMessageData(x_92);
lean_dec(x_92);
x_94 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_94, 0, x_91);
lean_ctor_set(x_94, 1, x_93);
x_95 = l_Lean_addTrace___at___Lean_Elab_Term_traceAtCmdPos_spec__1___redArg(x_80, x_94, x_5, x_6, x_7, x_8, x_85);
x_96 = lean_ctor_get(x_95, 1);
lean_inc(x_96);
lean_dec(x_95);
x_73 = x_96;
goto block_76;
}
block_76:
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_74, 0, x_13);
lean_ctor_set(x_74, 1, x_18);
lean_ctor_set(x_74, 2, x_67);
lean_ctor_set(x_74, 3, x_70);
lean_ctor_set(x_74, 4, x_1);
lean_ctor_set(x_74, 5, x_2);
if (lean_is_scalar(x_72)) {
 x_75 = lean_alloc_ctor(0, 2, 0);
} else {
 x_75 = x_72;
}
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_73);
return x_75;
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_dec(x_67);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_2);
lean_dec(x_1);
x_97 = lean_ctor_get(x_69, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_69, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_99 = x_69;
} else {
 lean_dec_ref(x_69);
 x_99 = lean_box(0);
}
if (lean_is_scalar(x_99)) {
 x_100 = lean_alloc_ctor(1, 2, 0);
} else {
 x_100 = x_99;
}
lean_ctor_set(x_100, 0, x_97);
lean_ctor_set(x_100, 1, x_98);
return x_100;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_5 = lean_mk_string_unchecked("Array", 5, 5);
x_6 = l_Lean_Name_mkStr1(x_5);
x_7 = lean_box(0);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
lean_inc(x_9);
x_10 = l_Lean_Expr_const___override(x_6, x_9);
x_11 = lean_mk_string_unchecked("Int", 3, 3);
x_12 = l_Lean_Name_mkStr1(x_11);
x_13 = l_Lean_Expr_const___override(x_12, x_8);
lean_inc(x_13);
lean_inc(x_10);
x_14 = l_Lean_Expr_app___override(x_10, x_13);
x_15 = lean_mk_string_unchecked("Nat", 3, 3);
x_16 = l_Lean_Name_mkStr1(x_15);
x_17 = l_Lean_Expr_const___override(x_16, x_8);
switch (lean_obj_tag(x_4)) {
case 0:
{
uint8_t x_18; 
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_2);
x_18 = !lean_is_exclusive(x_4);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_19 = lean_ctor_get(x_4, 0);
x_20 = lean_ctor_get(x_4, 1);
x_21 = lean_mk_string_unchecked("Std", 3, 3);
x_22 = lean_mk_string_unchecked("Tactic", 6, 6);
x_23 = lean_mk_string_unchecked("BVDecide", 8, 8);
x_24 = lean_mk_string_unchecked("LRAT", 4, 4);
x_25 = lean_mk_string_unchecked("Action", 6, 6);
x_26 = lean_mk_string_unchecked("addEmpty", 8, 8);
x_27 = l_Lean_Name_mkStr6(x_21, x_22, x_23, x_24, x_25, x_26);
lean_inc(x_9);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 1, x_9);
lean_ctor_set(x_4, 0, x_7);
x_28 = l_Lean_Expr_const___override(x_27, x_4);
x_29 = l_Lean_mkNatLit(x_19);
x_30 = lean_mk_string_unchecked("List", 4, 4);
x_31 = lean_mk_string_unchecked("toArray", 7, 7);
lean_inc(x_30);
x_32 = l_Lean_Name_mkStr2(x_30, x_31);
lean_inc(x_9);
x_33 = l_Lean_Expr_const___override(x_32, x_9);
x_34 = lean_mk_string_unchecked("nil", 3, 3);
lean_inc(x_30);
x_35 = l_Lean_Name_mkStr2(x_30, x_34);
lean_inc(x_9);
x_36 = l_Lean_Expr_const___override(x_35, x_9);
lean_inc(x_17);
x_37 = l_Lean_Expr_app___override(x_36, x_17);
x_38 = lean_mk_string_unchecked("cons", 4, 4);
x_39 = l_Lean_Name_mkStr2(x_30, x_38);
x_40 = l_Lean_Expr_const___override(x_39, x_9);
lean_inc(x_17);
x_41 = l_Lean_Expr_app___override(x_40, x_17);
x_42 = lean_array_to_list(x_20);
x_43 = l___private_Lean_ToExpr_0__Lean_List_toExprAux(lean_box(0), x_1, x_37, x_41, x_42);
lean_dec(x_37);
lean_inc(x_17);
x_44 = l_Lean_mkAppB(x_33, x_17, x_43);
x_45 = l_Lean_mkApp4(x_28, x_14, x_17, x_29, x_44);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_46 = lean_ctor_get(x_4, 0);
x_47 = lean_ctor_get(x_4, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_4);
x_48 = lean_mk_string_unchecked("Std", 3, 3);
x_49 = lean_mk_string_unchecked("Tactic", 6, 6);
x_50 = lean_mk_string_unchecked("BVDecide", 8, 8);
x_51 = lean_mk_string_unchecked("LRAT", 4, 4);
x_52 = lean_mk_string_unchecked("Action", 6, 6);
x_53 = lean_mk_string_unchecked("addEmpty", 8, 8);
x_54 = l_Lean_Name_mkStr6(x_48, x_49, x_50, x_51, x_52, x_53);
lean_inc(x_9);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_7);
lean_ctor_set(x_55, 1, x_9);
x_56 = l_Lean_Expr_const___override(x_54, x_55);
x_57 = l_Lean_mkNatLit(x_46);
x_58 = lean_mk_string_unchecked("List", 4, 4);
x_59 = lean_mk_string_unchecked("toArray", 7, 7);
lean_inc(x_58);
x_60 = l_Lean_Name_mkStr2(x_58, x_59);
lean_inc(x_9);
x_61 = l_Lean_Expr_const___override(x_60, x_9);
x_62 = lean_mk_string_unchecked("nil", 3, 3);
lean_inc(x_58);
x_63 = l_Lean_Name_mkStr2(x_58, x_62);
lean_inc(x_9);
x_64 = l_Lean_Expr_const___override(x_63, x_9);
lean_inc(x_17);
x_65 = l_Lean_Expr_app___override(x_64, x_17);
x_66 = lean_mk_string_unchecked("cons", 4, 4);
x_67 = l_Lean_Name_mkStr2(x_58, x_66);
x_68 = l_Lean_Expr_const___override(x_67, x_9);
lean_inc(x_17);
x_69 = l_Lean_Expr_app___override(x_68, x_17);
x_70 = lean_array_to_list(x_47);
x_71 = l___private_Lean_ToExpr_0__Lean_List_toExprAux(lean_box(0), x_1, x_65, x_69, x_70);
lean_dec(x_65);
lean_inc(x_17);
x_72 = l_Lean_mkAppB(x_61, x_17, x_71);
x_73 = l_Lean_mkApp4(x_56, x_14, x_17, x_57, x_72);
return x_73;
}
}
case 1:
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec(x_10);
lean_dec(x_3);
x_74 = lean_ctor_get(x_4, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_4, 1);
lean_inc(x_75);
x_76 = lean_ctor_get(x_4, 2);
lean_inc(x_76);
lean_dec(x_4);
x_77 = lean_mk_string_unchecked("Std", 3, 3);
x_78 = lean_mk_string_unchecked("Tactic", 6, 6);
x_79 = lean_mk_string_unchecked("BVDecide", 8, 8);
x_80 = lean_mk_string_unchecked("LRAT", 4, 4);
x_81 = lean_mk_string_unchecked("Action", 6, 6);
x_82 = lean_mk_string_unchecked("addRup", 6, 6);
x_83 = l_Lean_Name_mkStr6(x_77, x_78, x_79, x_80, x_81, x_82);
lean_inc(x_9);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_7);
lean_ctor_set(x_84, 1, x_9);
x_85 = l_Lean_Expr_const___override(x_83, x_84);
x_86 = l_Lean_mkNatLit(x_74);
x_87 = lean_mk_string_unchecked("List", 4, 4);
x_88 = lean_mk_string_unchecked("toArray", 7, 7);
lean_inc(x_87);
x_89 = l_Lean_Name_mkStr2(x_87, x_88);
lean_inc(x_9);
x_90 = l_Lean_Expr_const___override(x_89, x_9);
x_91 = lean_mk_string_unchecked("nil", 3, 3);
lean_inc(x_87);
x_92 = l_Lean_Name_mkStr2(x_87, x_91);
lean_inc(x_9);
x_93 = l_Lean_Expr_const___override(x_92, x_9);
lean_inc(x_13);
lean_inc(x_93);
x_94 = l_Lean_Expr_app___override(x_93, x_13);
x_95 = lean_mk_string_unchecked("cons", 4, 4);
x_96 = l_Lean_Name_mkStr2(x_87, x_95);
x_97 = l_Lean_Expr_const___override(x_96, x_9);
lean_inc(x_13);
lean_inc(x_97);
x_98 = l_Lean_Expr_app___override(x_97, x_13);
x_99 = lean_array_to_list(x_75);
x_100 = l___private_Lean_ToExpr_0__Lean_List_toExprAux(lean_box(0), x_2, x_94, x_98, x_99);
lean_dec(x_94);
lean_inc(x_90);
x_101 = l_Lean_mkAppB(x_90, x_13, x_100);
lean_inc(x_17);
x_102 = l_Lean_Expr_app___override(x_93, x_17);
lean_inc(x_17);
x_103 = l_Lean_Expr_app___override(x_97, x_17);
x_104 = lean_array_to_list(x_76);
x_105 = l___private_Lean_ToExpr_0__Lean_List_toExprAux(lean_box(0), x_1, x_102, x_103, x_104);
lean_dec(x_102);
lean_inc(x_17);
x_106 = l_Lean_mkAppB(x_90, x_17, x_105);
x_107 = l_Lean_mkApp5(x_85, x_14, x_17, x_86, x_101, x_106);
return x_107;
}
case 2:
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; 
x_108 = lean_ctor_get(x_4, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_4, 1);
lean_inc(x_109);
x_110 = lean_ctor_get(x_4, 2);
lean_inc(x_110);
x_111 = lean_ctor_get(x_4, 3);
lean_inc(x_111);
x_112 = lean_ctor_get(x_4, 4);
lean_inc(x_112);
lean_dec(x_4);
x_113 = lean_mk_string_unchecked("List", 4, 4);
x_114 = lean_mk_string_unchecked("toArray", 7, 7);
x_115 = lean_mk_string_unchecked("nil", 3, 3);
lean_inc(x_113);
x_116 = l_Lean_Name_mkStr2(x_113, x_115);
x_117 = lean_mk_string_unchecked("cons", 4, 4);
lean_inc(x_113);
x_118 = l_Lean_Name_mkStr2(x_113, x_117);
x_119 = !lean_is_exclusive(x_110);
if (x_119 == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; uint8_t x_166; 
x_120 = lean_ctor_get(x_110, 0);
x_121 = lean_ctor_get(x_110, 1);
x_122 = lean_mk_string_unchecked("Std", 3, 3);
x_123 = lean_mk_string_unchecked("Tactic", 6, 6);
x_124 = lean_mk_string_unchecked("BVDecide", 8, 8);
x_125 = lean_mk_string_unchecked("LRAT", 4, 4);
x_126 = lean_mk_string_unchecked("Action", 6, 6);
x_127 = lean_mk_string_unchecked("addRat", 6, 6);
x_128 = l_Lean_Name_mkStr2(x_113, x_114);
lean_inc(x_9);
x_129 = l_Lean_Expr_const___override(x_116, x_9);
lean_inc(x_13);
lean_inc(x_129);
x_130 = l_Lean_Expr_app___override(x_129, x_13);
lean_inc(x_9);
x_131 = l_Lean_Expr_const___override(x_118, x_9);
lean_inc(x_13);
lean_inc(x_131);
x_132 = l_Lean_Expr_app___override(x_131, x_13);
x_133 = lean_array_to_list(x_109);
x_134 = l_Lean_Name_mkStr6(x_122, x_123, x_124, x_125, x_126, x_127);
lean_inc(x_9);
lean_ctor_set_tag(x_110, 1);
lean_ctor_set(x_110, 1, x_9);
lean_ctor_set(x_110, 0, x_7);
x_135 = l_Lean_Expr_const___override(x_128, x_9);
x_136 = l___private_Lean_ToExpr_0__Lean_List_toExprAux(lean_box(0), x_2, x_130, x_132, x_133);
lean_dec(x_130);
x_137 = lean_mk_string_unchecked("Bool", 4, 4);
lean_inc(x_137);
x_138 = l_Lean_Name_mkStr1(x_137);
lean_inc(x_110);
x_139 = l_Lean_Expr_const___override(x_134, x_110);
x_140 = l_Lean_mkNatLit(x_108);
lean_inc(x_135);
x_141 = l_Lean_mkAppB(x_135, x_13, x_136);
x_160 = l_Lean_Expr_const___override(x_138, x_8);
x_161 = lean_mk_string_unchecked("Prod", 4, 4);
x_162 = lean_mk_string_unchecked("mk", 2, 2);
x_163 = l_Lean_Name_mkStr2(x_161, x_162);
lean_inc(x_110);
x_164 = l_Lean_Expr_const___override(x_163, x_110);
x_165 = l_Lean_mkNatLit(x_120);
x_166 = lean_unbox(x_121);
lean_dec(x_121);
if (x_166 == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_167 = lean_mk_string_unchecked("false", 5, 5);
x_168 = l_Lean_Name_mkStr2(x_137, x_167);
x_169 = l_Lean_Expr_const___override(x_168, x_8);
lean_inc(x_17);
x_170 = l_Lean_mkApp4(x_164, x_17, x_160, x_165, x_169);
x_142 = x_170;
goto block_159;
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_171 = lean_mk_string_unchecked("true", 4, 4);
x_172 = l_Lean_Name_mkStr2(x_137, x_171);
x_173 = l_Lean_Expr_const___override(x_172, x_8);
lean_inc(x_17);
x_174 = l_Lean_mkApp4(x_164, x_17, x_160, x_165, x_173);
x_142 = x_174;
goto block_159;
}
block_159:
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
lean_inc(x_17);
lean_inc(x_129);
x_143 = l_Lean_Expr_app___override(x_129, x_17);
lean_inc(x_17);
lean_inc(x_131);
x_144 = l_Lean_Expr_app___override(x_131, x_17);
x_145 = lean_array_to_list(x_111);
x_146 = l___private_Lean_ToExpr_0__Lean_List_toExprAux(lean_box(0), x_1, x_143, x_144, x_145);
lean_dec(x_143);
lean_inc(x_17);
lean_inc(x_135);
x_147 = l_Lean_mkAppB(x_135, x_17, x_146);
lean_inc(x_17);
x_148 = l_Lean_Expr_app___override(x_10, x_17);
x_149 = lean_mk_string_unchecked("Prod", 4, 4);
x_150 = l_Lean_Name_mkStr1(x_149);
x_151 = l_Lean_Expr_const___override(x_150, x_110);
lean_inc(x_17);
x_152 = l_Lean_mkAppB(x_151, x_17, x_148);
lean_inc(x_152);
x_153 = l_Lean_Expr_app___override(x_129, x_152);
lean_inc(x_152);
x_154 = l_Lean_Expr_app___override(x_131, x_152);
x_155 = lean_array_to_list(x_112);
x_156 = l___private_Lean_ToExpr_0__Lean_List_toExprAux(lean_box(0), x_3, x_153, x_154, x_155);
lean_dec(x_153);
x_157 = l_Lean_mkAppB(x_135, x_152, x_156);
x_158 = l_Lean_mkApp7(x_139, x_14, x_17, x_140, x_141, x_142, x_147, x_157);
return x_158;
}
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; uint8_t x_222; 
x_175 = lean_ctor_get(x_110, 0);
x_176 = lean_ctor_get(x_110, 1);
lean_inc(x_176);
lean_inc(x_175);
lean_dec(x_110);
x_177 = lean_mk_string_unchecked("Std", 3, 3);
x_178 = lean_mk_string_unchecked("Tactic", 6, 6);
x_179 = lean_mk_string_unchecked("BVDecide", 8, 8);
x_180 = lean_mk_string_unchecked("LRAT", 4, 4);
x_181 = lean_mk_string_unchecked("Action", 6, 6);
x_182 = lean_mk_string_unchecked("addRat", 6, 6);
x_183 = l_Lean_Name_mkStr2(x_113, x_114);
lean_inc(x_9);
x_184 = l_Lean_Expr_const___override(x_116, x_9);
lean_inc(x_13);
lean_inc(x_184);
x_185 = l_Lean_Expr_app___override(x_184, x_13);
lean_inc(x_9);
x_186 = l_Lean_Expr_const___override(x_118, x_9);
lean_inc(x_13);
lean_inc(x_186);
x_187 = l_Lean_Expr_app___override(x_186, x_13);
x_188 = lean_array_to_list(x_109);
x_189 = l_Lean_Name_mkStr6(x_177, x_178, x_179, x_180, x_181, x_182);
lean_inc(x_9);
x_190 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_190, 0, x_7);
lean_ctor_set(x_190, 1, x_9);
x_191 = l_Lean_Expr_const___override(x_183, x_9);
x_192 = l___private_Lean_ToExpr_0__Lean_List_toExprAux(lean_box(0), x_2, x_185, x_187, x_188);
lean_dec(x_185);
x_193 = lean_mk_string_unchecked("Bool", 4, 4);
lean_inc(x_193);
x_194 = l_Lean_Name_mkStr1(x_193);
lean_inc(x_190);
x_195 = l_Lean_Expr_const___override(x_189, x_190);
x_196 = l_Lean_mkNatLit(x_108);
lean_inc(x_191);
x_197 = l_Lean_mkAppB(x_191, x_13, x_192);
x_216 = l_Lean_Expr_const___override(x_194, x_8);
x_217 = lean_mk_string_unchecked("Prod", 4, 4);
x_218 = lean_mk_string_unchecked("mk", 2, 2);
x_219 = l_Lean_Name_mkStr2(x_217, x_218);
lean_inc(x_190);
x_220 = l_Lean_Expr_const___override(x_219, x_190);
x_221 = l_Lean_mkNatLit(x_175);
x_222 = lean_unbox(x_176);
lean_dec(x_176);
if (x_222 == 0)
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
x_223 = lean_mk_string_unchecked("false", 5, 5);
x_224 = l_Lean_Name_mkStr2(x_193, x_223);
x_225 = l_Lean_Expr_const___override(x_224, x_8);
lean_inc(x_17);
x_226 = l_Lean_mkApp4(x_220, x_17, x_216, x_221, x_225);
x_198 = x_226;
goto block_215;
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_227 = lean_mk_string_unchecked("true", 4, 4);
x_228 = l_Lean_Name_mkStr2(x_193, x_227);
x_229 = l_Lean_Expr_const___override(x_228, x_8);
lean_inc(x_17);
x_230 = l_Lean_mkApp4(x_220, x_17, x_216, x_221, x_229);
x_198 = x_230;
goto block_215;
}
block_215:
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
lean_inc(x_17);
lean_inc(x_184);
x_199 = l_Lean_Expr_app___override(x_184, x_17);
lean_inc(x_17);
lean_inc(x_186);
x_200 = l_Lean_Expr_app___override(x_186, x_17);
x_201 = lean_array_to_list(x_111);
x_202 = l___private_Lean_ToExpr_0__Lean_List_toExprAux(lean_box(0), x_1, x_199, x_200, x_201);
lean_dec(x_199);
lean_inc(x_17);
lean_inc(x_191);
x_203 = l_Lean_mkAppB(x_191, x_17, x_202);
lean_inc(x_17);
x_204 = l_Lean_Expr_app___override(x_10, x_17);
x_205 = lean_mk_string_unchecked("Prod", 4, 4);
x_206 = l_Lean_Name_mkStr1(x_205);
x_207 = l_Lean_Expr_const___override(x_206, x_190);
lean_inc(x_17);
x_208 = l_Lean_mkAppB(x_207, x_17, x_204);
lean_inc(x_208);
x_209 = l_Lean_Expr_app___override(x_184, x_208);
lean_inc(x_208);
x_210 = l_Lean_Expr_app___override(x_186, x_208);
x_211 = lean_array_to_list(x_112);
x_212 = l___private_Lean_ToExpr_0__Lean_List_toExprAux(lean_box(0), x_3, x_209, x_210, x_211);
lean_dec(x_209);
x_213 = l_Lean_mkAppB(x_191, x_208, x_212);
x_214 = l_Lean_mkApp7(x_195, x_14, x_17, x_196, x_197, x_198, x_203, x_213);
return x_214;
}
}
}
default: 
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; 
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_2);
x_231 = lean_ctor_get(x_4, 0);
lean_inc(x_231);
lean_dec(x_4);
x_232 = lean_mk_string_unchecked("Std", 3, 3);
x_233 = lean_mk_string_unchecked("Tactic", 6, 6);
x_234 = lean_mk_string_unchecked("BVDecide", 8, 8);
x_235 = lean_mk_string_unchecked("LRAT", 4, 4);
x_236 = lean_mk_string_unchecked("Action", 6, 6);
x_237 = lean_mk_string_unchecked("del", 3, 3);
x_238 = l_Lean_Name_mkStr6(x_232, x_233, x_234, x_235, x_236, x_237);
lean_inc(x_9);
x_239 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_239, 0, x_7);
lean_ctor_set(x_239, 1, x_9);
x_240 = l_Lean_Expr_const___override(x_238, x_239);
x_241 = lean_mk_string_unchecked("List", 4, 4);
x_242 = lean_mk_string_unchecked("toArray", 7, 7);
lean_inc(x_241);
x_243 = l_Lean_Name_mkStr2(x_241, x_242);
lean_inc(x_9);
x_244 = l_Lean_Expr_const___override(x_243, x_9);
x_245 = lean_mk_string_unchecked("nil", 3, 3);
lean_inc(x_241);
x_246 = l_Lean_Name_mkStr2(x_241, x_245);
lean_inc(x_9);
x_247 = l_Lean_Expr_const___override(x_246, x_9);
lean_inc(x_17);
x_248 = l_Lean_Expr_app___override(x_247, x_17);
x_249 = lean_mk_string_unchecked("cons", 4, 4);
x_250 = l_Lean_Name_mkStr2(x_241, x_249);
x_251 = l_Lean_Expr_const___override(x_250, x_9);
lean_inc(x_17);
x_252 = l_Lean_Expr_app___override(x_251, x_17);
x_253 = lean_array_to_list(x_231);
x_254 = l___private_Lean_ToExpr_0__Lean_List_toExprAux(lean_box(0), x_1, x_248, x_252, x_253);
lean_dec(x_248);
lean_inc(x_17);
x_255 = l_Lean_mkAppB(x_244, x_17, x_254);
x_256 = l_Lean_mkApp3(x_240, x_14, x_17, x_255);
return x_256;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_1 = l_Lean_instToExprNat;
x_2 = l_Lean_instToLevel;
x_3 = l_Lean_instToExprArrayOfToLevel___redArg(x_2, x_1);
x_4 = l_Lean_instToExprInt;
x_5 = l_Lean_instToExprProdOfToLevel___redArg(x_2, x_2, x_1, x_3);
x_6 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0), 4, 3);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_4);
lean_closure_set(x_6, 2, x_5);
x_7 = lean_mk_string_unchecked("Std", 3, 3);
x_8 = lean_mk_string_unchecked("Tactic", 6, 6);
x_9 = lean_mk_string_unchecked("BVDecide", 8, 8);
x_10 = lean_mk_string_unchecked("LRAT", 4, 4);
x_11 = lean_mk_string_unchecked("IntAction", 9, 9);
x_12 = l_Lean_Name_mkStr5(x_7, x_8, x_9, x_10, x_11);
x_13 = lean_box(0);
x_14 = l_Lean_Expr_const___override(x_12, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_6);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_mk_string_unchecked("Parsing LRAT file", 17, 17);
x_6 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = l_Lean_MessageData_ofFormat(x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Tactic_BVDecide_LRAT_parseLRATProof(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_IO_lazyPure___redArg(x_1, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_mk_string_unchecked("SAT solver produced invalid LRAT: ", 34, 34);
x_10 = l_Lean_stringToMessageData(x_9);
lean_dec(x_9);
x_11 = l_Lean_stringToMessageData(x_8);
lean_dec(x_8);
x_12 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_mk_string_unchecked("", 0, 0);
x_14 = l_Lean_stringToMessageData(x_13);
lean_dec(x_13);
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_throwError___at___Lean_Elab_Tactic_BVDecide_External_satQuery_spec__0(lean_box(0), x_15, x_2, x_3, x_7);
return x_16;
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_5);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_5, 0);
lean_dec(x_18);
x_19 = lean_ctor_get(x_6, 0);
lean_inc(x_19);
lean_dec(x_6);
lean_ctor_set(x_5, 0, x_19);
return x_5;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_5, 1);
lean_inc(x_20);
lean_dec(x_5);
x_21 = lean_ctor_get(x_6, 0);
lean_inc(x_21);
lean_dec(x_6);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Tactic_BVDecide_LRAT_trim(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_mk_string_unchecked("Trimming LRAT proof", 19, 19);
x_6 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = l_Lean_MessageData_ofFormat(x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_2, 5);
x_6 = l_IO_lazyPure___redArg(x_1, x_4);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
x_10 = l_IO_ofExcept___at___IO_FS_Stream_readJson_spec__0(lean_box(0), x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
lean_free_object(x_6);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
return x_10;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_10);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_10, 0);
x_17 = lean_io_error_to_string(x_16);
x_18 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = l_Lean_MessageData_ofFormat(x_18);
lean_inc(x_5);
lean_ctor_set(x_6, 1, x_19);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_10, 0, x_6);
return x_10;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_10, 0);
x_21 = lean_ctor_get(x_10, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_10);
x_22 = lean_io_error_to_string(x_20);
x_23 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = l_Lean_MessageData_ofFormat(x_23);
lean_inc(x_5);
lean_ctor_set(x_6, 1, x_24);
lean_ctor_set(x_6, 0, x_5);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_6);
lean_ctor_set(x_25, 1, x_21);
return x_25;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_6, 0);
x_27 = lean_ctor_get(x_6, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_6);
x_28 = l_IO_ofExcept___at___IO_FS_Stream_readJson_spec__0(lean_box(0), x_26, x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_31 = x_28;
} else {
 lean_dec_ref(x_28);
 x_31 = lean_box(0);
}
if (lean_is_scalar(x_31)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_31;
}
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_33 = lean_ctor_get(x_28, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_28, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_35 = x_28;
} else {
 lean_dec_ref(x_28);
 x_35 = lean_box(0);
}
x_36 = lean_io_error_to_string(x_33);
x_37 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = l_Lean_MessageData_ofFormat(x_37);
lean_inc(x_5);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_5);
lean_ctor_set(x_39, 1, x_38);
if (lean_is_scalar(x_35)) {
 x_40 = lean_alloc_ctor(1, 2, 0);
} else {
 x_40 = x_35;
}
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_34);
return x_40;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_FS_readBinFile(x_1, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__0___boxed), 4, 0);
x_10 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__1___boxed), 2, 1);
lean_closure_set(x_10, 0, x_7);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__2___boxed), 4, 1);
lean_closure_set(x_11, 0, x_10);
x_12 = lean_mk_string_unchecked("Meta", 4, 4);
x_13 = lean_mk_string_unchecked("Tactic", 6, 6);
x_14 = lean_mk_string_unchecked("sat", 3, 3);
x_15 = l_Lean_Name_mkStr3(x_12, x_13, x_14);
x_42 = lean_box(1);
x_43 = lean_mk_string_unchecked("", 0, 0);
x_44 = lean_unbox(x_42);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_43);
lean_inc(x_15);
x_45 = l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20___redArg(x_15, x_9, x_11, x_44, x_43, x_3, x_4, x_8);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_64; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
lean_inc(x_46);
x_48 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__3___boxed), 2, 1);
lean_closure_set(x_48, 0, x_46);
lean_inc(x_15);
x_49 = l_Lean_isTracingEnabledFor___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20_spec__20___redArg(x_15, x_3, x_47);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__4___boxed), 4, 0);
x_53 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__5___boxed), 4, 1);
lean_closure_set(x_53, 0, x_48);
x_64 = lean_unbox(x_50);
lean_dec(x_50);
if (x_64 == 0)
{
x_54 = x_2;
x_55 = x_46;
x_56 = x_3;
x_57 = x_4;
x_58 = x_51;
goto block_63;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_65 = lean_mk_string_unchecked("LRAT proof has ", 15, 15);
x_66 = lean_array_get_size(x_46);
x_67 = l___private_Init_Data_Repr_0__Nat_reprFast(x_66);
x_68 = lean_string_append(x_65, x_67);
lean_dec(x_67);
x_69 = lean_mk_string_unchecked(" steps before trimming", 22, 22);
x_70 = lean_string_append(x_68, x_69);
lean_dec(x_69);
x_71 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_71, 0, x_70);
x_72 = l_Lean_MessageData_ofFormat(x_71);
lean_inc(x_15);
x_73 = l_Lean_addTrace___at___Lean_PrettyPrinter_format_spec__1(x_15, x_72, x_3, x_4, x_51);
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
lean_dec(x_73);
x_54 = x_2;
x_55 = x_46;
x_56 = x_3;
x_57 = x_4;
x_58 = x_74;
goto block_63;
}
block_63:
{
if (x_54 == 0)
{
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_43);
x_16 = x_55;
x_17 = x_56;
x_18 = x_57;
x_19 = x_58;
goto block_41;
}
else
{
uint8_t x_59; lean_object* x_60; 
lean_dec(x_55);
x_59 = lean_unbox(x_42);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_15);
x_60 = l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20___redArg(x_15, x_52, x_53, x_59, x_43, x_56, x_57, x_58);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_16 = x_61;
x_17 = x_56;
x_18 = x_57;
x_19 = x_62;
goto block_41;
}
else
{
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_15);
return x_60;
}
}
}
}
else
{
lean_dec(x_43);
lean_dec(x_15);
lean_dec(x_4);
lean_dec(x_3);
return x_45;
}
block_41:
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
lean_inc(x_15);
x_20 = l_Lean_isTracingEnabledFor___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20_spec__20___redArg(x_15, x_17, x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_unbox(x_21);
lean_dec(x_21);
if (x_22 == 0)
{
uint8_t x_23; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_15);
x_23 = !lean_is_exclusive(x_20);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_20, 0);
lean_dec(x_24);
lean_ctor_set(x_20, 0, x_16);
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_dec(x_20);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_16);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_27 = lean_ctor_get(x_20, 1);
lean_inc(x_27);
lean_dec(x_20);
x_28 = lean_mk_string_unchecked("LRAT proof has ", 15, 15);
x_29 = lean_array_get_size(x_16);
x_30 = l___private_Init_Data_Repr_0__Nat_reprFast(x_29);
x_31 = lean_string_append(x_28, x_30);
lean_dec(x_30);
x_32 = lean_mk_string_unchecked(" steps after trimming", 21, 21);
x_33 = lean_string_append(x_31, x_32);
lean_dec(x_32);
x_34 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = l_Lean_MessageData_ofFormat(x_34);
x_36 = l_Lean_addTrace___at___Lean_PrettyPrinter_format_spec__1(x_15, x_35, x_17, x_18, x_27);
lean_dec(x_18);
lean_dec(x_17);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_36, 0);
lean_dec(x_38);
lean_ctor_set(x_36, 0, x_16);
return x_36;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_16);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
else
{
uint8_t x_75; 
lean_dec(x_4);
x_75 = !lean_is_exclusive(x_6);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_76 = lean_ctor_get(x_6, 0);
x_77 = lean_ctor_get(x_3, 5);
lean_inc(x_77);
lean_dec(x_3);
x_78 = lean_io_error_to_string(x_76);
x_79 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_79, 0, x_78);
x_80 = l_Lean_MessageData_ofFormat(x_79);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_77);
lean_ctor_set(x_81, 1, x_80);
lean_ctor_set(x_6, 0, x_81);
return x_6;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_82 = lean_ctor_get(x_6, 0);
x_83 = lean_ctor_get(x_6, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_6);
x_84 = lean_ctor_get(x_3, 5);
lean_inc(x_84);
lean_dec(x_3);
x_85 = lean_io_error_to_string(x_82);
x_86 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_86, 0, x_85);
x_87 = l_Lean_MessageData_ofFormat(x_86);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_84);
lean_ctor_set(x_88, 1, x_87);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_83);
return x_89;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__3(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__4(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__5(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load(x_1, x_6, x_3, x_4, x_5);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_ofFile(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load(x_1, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = l_Std_Tactic_BVDecide_LRAT_lratProofToString(x_8);
lean_dec(x_8);
lean_ctor_set(x_6, 0, x_9);
return x_6;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_6, 0);
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_6);
x_12 = l_Std_Tactic_BVDecide_LRAT_lratProofToString(x_10);
lean_dec(x_10);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_6);
if (x_14 == 0)
{
return x_6;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_6, 0);
x_16 = lean_ctor_get(x_6, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_6);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_ofFile___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_ofFile(x_1, x_6, x_3, x_4, x_5);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_io_remove_file(x_1, x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
lean_dec(x_2);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_5);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_5, 0);
x_12 = lean_io_error_to_string(x_11);
x_13 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = l_Lean_MessageData_ofFormat(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set(x_5, 0, x_15);
return x_5;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_5, 0);
x_17 = lean_ctor_get(x_5, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_5);
x_18 = lean_io_error_to_string(x_16);
x_19 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = l_Lean_MessageData_ofFormat(x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_2);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_17);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_2, 5);
lean_inc(x_5);
x_6 = lean_io_create_tempfile(x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
lean_inc(x_10);
x_11 = lean_apply_5(x_1, x_9, x_10, x_2, x_3, x_8);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_12);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_12);
x_15 = l_IO_FS_withTempFile___at___Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__0___redArg___lam__0(x_10, x_5, x_14, x_13);
lean_dec(x_14);
lean_dec(x_10);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
lean_ctor_set(x_15, 0, x_12);
return x_15;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
uint8_t x_20; 
lean_dec(x_12);
x_20 = !lean_is_exclusive(x_15);
if (x_20 == 0)
{
return x_15;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_15, 0);
x_22 = lean_ctor_get(x_15, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_15);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_11, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_11, 1);
lean_inc(x_25);
lean_dec(x_11);
x_26 = lean_box(0);
x_27 = l_IO_FS_withTempFile___at___Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__0___redArg___lam__0(x_10, x_5, x_26, x_25);
lean_dec(x_10);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
lean_ctor_set_tag(x_27, 1);
lean_ctor_set(x_27, 0, x_24);
return x_27;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_24);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
else
{
uint8_t x_32; 
lean_dec(x_24);
x_32 = !lean_is_exclusive(x_27);
if (x_32 == 0)
{
return x_27;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_27, 0);
x_34 = lean_ctor_get(x_27, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_27);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
else
{
uint8_t x_36; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_6);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_6, 0);
x_38 = lean_io_error_to_string(x_37);
x_39 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_39, 0, x_38);
x_40 = l_Lean_MessageData_ofFormat(x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_5);
lean_ctor_set(x_41, 1, x_40);
lean_ctor_set(x_6, 0, x_41);
return x_6;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_42 = lean_ctor_get(x_6, 0);
x_43 = lean_ctor_get(x_6, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_6);
x_44 = lean_io_error_to_string(x_42);
x_45 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_45, 0, x_44);
x_46 = l_Lean_MessageData_ofFormat(x_45);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_5);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_43);
return x_48;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_FS_withTempFile___at___Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__0___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_mk_string_unchecked("Serializing SAT problem to DIMACS file", 38, 38);
x_6 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = l_Lean_MessageData_ofFormat(x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Sat_CNF_dimacs(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_mk_string_unchecked("Running SAT solver", 18, 18);
x_6 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = l_Lean_MessageData_ofFormat(x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_mk_string_unchecked("Obtaining LRAT certificate", 26, 26);
x_6 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = l_Lean_MessageData_ofFormat(x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_3, 5);
x_7 = l_IO_lazyPure___redArg(x_1, x_5);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = lean_io_prim_handle_put_str(x_2, x_9, x_10);
lean_dec(x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_io_prim_handle_flush(x_2, x_12);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
lean_free_object(x_7);
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
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_13);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_13, 0);
x_20 = lean_io_error_to_string(x_19);
x_21 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = l_Lean_MessageData_ofFormat(x_21);
lean_inc(x_6);
lean_ctor_set(x_7, 1, x_22);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_13, 0, x_7);
return x_13;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_13, 0);
x_24 = lean_ctor_get(x_13, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_13);
x_25 = lean_io_error_to_string(x_23);
x_26 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = l_Lean_MessageData_ofFormat(x_26);
lean_inc(x_6);
lean_ctor_set(x_7, 1, x_27);
lean_ctor_set(x_7, 0, x_6);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_7);
lean_ctor_set(x_28, 1, x_24);
return x_28;
}
}
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_11);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_11, 0);
x_31 = lean_io_error_to_string(x_30);
x_32 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = l_Lean_MessageData_ofFormat(x_32);
lean_inc(x_6);
lean_ctor_set(x_7, 1, x_33);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_11, 0, x_7);
return x_11;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_34 = lean_ctor_get(x_11, 0);
x_35 = lean_ctor_get(x_11, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_11);
x_36 = lean_io_error_to_string(x_34);
x_37 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = l_Lean_MessageData_ofFormat(x_37);
lean_inc(x_6);
lean_ctor_set(x_7, 1, x_38);
lean_ctor_set(x_7, 0, x_6);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_7);
lean_ctor_set(x_39, 1, x_35);
return x_39;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_7, 0);
x_41 = lean_ctor_get(x_7, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_7);
x_42 = lean_io_prim_handle_put_str(x_2, x_40, x_41);
lean_dec(x_40);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_44 = lean_io_prim_handle_flush(x_2, x_43);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_47 = x_44;
} else {
 lean_dec_ref(x_44);
 x_47 = lean_box(0);
}
if (lean_is_scalar(x_47)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_47;
}
lean_ctor_set(x_48, 0, x_45);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_49 = lean_ctor_get(x_44, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_44, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_51 = x_44;
} else {
 lean_dec_ref(x_44);
 x_51 = lean_box(0);
}
x_52 = lean_io_error_to_string(x_49);
x_53 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_53, 0, x_52);
x_54 = l_Lean_MessageData_ofFormat(x_53);
lean_inc(x_6);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_6);
lean_ctor_set(x_55, 1, x_54);
if (lean_is_scalar(x_51)) {
 x_56 = lean_alloc_ctor(1, 2, 0);
} else {
 x_56 = x_51;
}
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_50);
return x_56;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_57 = lean_ctor_get(x_42, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_42, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_59 = x_42;
} else {
 lean_dec_ref(x_42);
 x_59 = lean_box(0);
}
x_60 = lean_io_error_to_string(x_57);
x_61 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_61, 0, x_60);
x_62 = l_Lean_MessageData_ofFormat(x_61);
lean_inc(x_6);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_6);
lean_ctor_set(x_63, 1, x_62);
if (lean_is_scalar(x_59)) {
 x_64 = lean_alloc_ctor(1, 2, 0);
} else {
 x_64 = x_59;
}
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_58);
return x_64;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_15 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__4___boxed), 5, 2);
lean_closure_set(x_15, 0, x_1);
lean_closure_set(x_15, 1, x_10);
x_16 = lean_mk_string_unchecked("Meta", 4, 4);
x_17 = lean_mk_string_unchecked("Tactic", 6, 6);
x_18 = lean_mk_string_unchecked("sat", 3, 3);
x_19 = l_Lean_Name_mkStr3(x_16, x_17, x_18);
x_20 = lean_box(1);
x_21 = lean_mk_string_unchecked("", 0, 0);
x_22 = lean_unbox(x_20);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_21);
lean_inc(x_19);
x_23 = l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20___redArg(x_19, x_2, x_15, x_22, x_21, x_12, x_13, x_14);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_box(x_6);
lean_inc(x_4);
x_26 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_External_satQuery___boxed), 8, 5);
lean_closure_set(x_26, 0, x_3);
lean_closure_set(x_26, 1, x_11);
lean_closure_set(x_26, 2, x_4);
lean_closure_set(x_26, 3, x_5);
lean_closure_set(x_26, 4, x_25);
x_27 = lean_unbox(x_20);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_21);
lean_inc(x_19);
x_28 = l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20___redArg(x_19, x_7, x_26, x_27, x_21, x_12, x_13, x_24);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_4);
x_30 = !lean_is_exclusive(x_28);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_28, 0);
lean_dec(x_31);
x_32 = !lean_is_exclusive(x_29);
if (x_32 == 0)
{
return x_28;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_29, 0);
lean_inc(x_33);
lean_dec(x_29);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_28, 0, x_34);
return x_28;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_28, 1);
lean_inc(x_35);
lean_dec(x_28);
x_36 = lean_ctor_get(x_29, 0);
lean_inc(x_36);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 x_37 = x_29;
} else {
 lean_dec_ref(x_29);
 x_37 = lean_box(0);
}
if (lean_is_scalar(x_37)) {
 x_38 = lean_alloc_ctor(0, 1, 0);
} else {
 x_38 = x_37;
}
lean_ctor_set(x_38, 0, x_36);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_35);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; 
x_40 = lean_ctor_get(x_28, 1);
lean_inc(x_40);
lean_dec(x_28);
x_41 = lean_box(x_8);
x_42 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_ofFile___boxed), 5, 2);
lean_closure_set(x_42, 0, x_4);
lean_closure_set(x_42, 1, x_41);
x_43 = lean_unbox(x_20);
x_44 = l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20___redArg(x_19, x_9, x_42, x_43, x_21, x_12, x_13, x_40);
if (lean_obj_tag(x_44) == 0)
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_44, 0);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_44, 0, x_47);
return x_44;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_48 = lean_ctor_get(x_44, 0);
x_49 = lean_ctor_get(x_44, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_44);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_48);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_49);
return x_51;
}
}
else
{
uint8_t x_52; 
x_52 = !lean_is_exclusive(x_44);
if (x_52 == 0)
{
return x_44;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_44, 0);
x_54 = lean_ctor_get(x_44, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_44);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
}
else
{
uint8_t x_56; 
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_4);
x_56 = !lean_is_exclusive(x_28);
if (x_56 == 0)
{
return x_28;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_28, 0);
x_58 = lean_ctor_get(x_28, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_28);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
uint8_t x_60; 
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_60 = !lean_is_exclusive(x_23);
if (x_60 == 0)
{
return x_23;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_23, 0);
x_62 = lean_ctor_get(x_23, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_23);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__0___boxed), 4, 0);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__1___boxed), 2, 1);
lean_closure_set(x_11, 0, x_1);
x_12 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__2___boxed), 4, 0);
x_13 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__3___boxed), 4, 0);
x_14 = lean_box(x_6);
x_15 = lean_box(x_4);
x_16 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__5___boxed), 14, 9);
lean_closure_set(x_16, 0, x_11);
lean_closure_set(x_16, 1, x_10);
lean_closure_set(x_16, 2, x_2);
lean_closure_set(x_16, 3, x_3);
lean_closure_set(x_16, 4, x_5);
lean_closure_set(x_16, 5, x_14);
lean_closure_set(x_16, 6, x_12);
lean_closure_set(x_16, 7, x_15);
lean_closure_set(x_16, 8, x_13);
x_17 = l_IO_FS_withTempFile___at___Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__0___redArg(x_16, x_7, x_8, x_9);
return x_17;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__0___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_IO_FS_withTempFile___at___Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__0___redArg___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__3(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__4(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; uint8_t x_16; lean_object* x_17; 
x_15 = lean_unbox(x_6);
lean_dec(x_6);
x_16 = lean_unbox(x_8);
lean_dec(x_8);
x_17 = l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__5(x_1, x_2, x_3, x_4, x_5, x_15, x_7, x_16, x_9, x_10, x_11, x_12, x_13, x_14);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_4);
lean_dec(x_4);
x_11 = lean_unbox(x_6);
lean_dec(x_6);
x_12 = l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal(x_1, x_2, x_3, x_10, x_5, x_11, x_7, x_8, x_9);
return x_12;
}
}
lean_object* initialize_Lean_Elab_Tactic_BVDecide_Frontend_Attr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_BVDecide_LRAT_Trim(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_BVDecide_External(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Tactic_BVDecide_LRAT_Checker(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Sat_CNF_Dimacs(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_BVDecide_Frontend_LRAT(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_BVDecide_Frontend_Attr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_BVDecide_LRAT_Trim(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_BVDecide_External(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_LRAT_Checker(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Sat_CNF_Dimacs(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
