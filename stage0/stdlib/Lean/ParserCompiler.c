// Lean compiler output
// Module: Lean.ParserCompiler
// Imports: Lean.Meta.ReduceEval Lean.Meta.WHNF Lean.KeyedDeclsAttribute Lean.ParserCompiler.Attribute Lean.Parser.Extension
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
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_parserNodeKind_x3f___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_ParserCompiler_parserNodeKind_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_registerParserCompiler___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_parserNodeKind_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_parserNodeKind_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isOptParam(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Parser_registerParserAttributeHook(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_ParserCompiler_compileParserExpr_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Attribute_add(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_reduceEval___at___Lean_ParserCompiler_parserNodeKind_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_replaceParserTy___redArg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_value_x21(lean_object*, uint8_t);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_ConstantInfo_value_x3f(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_Context_tyName___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_getFVar_x21(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileEmbeddedParsers___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_replace_expr(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* l_Lean_evalConstCheck___at___Lean_KeyedDeclsAttribute_init_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_replaceParserTy___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_ParserCompiler_parserNodeKind_x3f_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_Context_tyName___boxed(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l_Lean_Meta_lambdaLetTelescope___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_ParserCompiler_compileParserExpr_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_registerParserCompiler(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_ParserCompiler_compileParserExpr_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_zipIdx___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_ParserCompiler_compileParserExpr_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* lean_mk_syntax_ident(lean_object*);
lean_object* l_Lean_ParserCompiler_CombinatorAttribute_getDeclFor_x3f(lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileEmbeddedParsers___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_ParserCompiler_compileParserExpr_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_ParserCompiler_compileParserExpr_spec__1___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescope___at___Lean_Meta_mapForallTelescope_x27_spec__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_ParserCompiler_compileParserExpr_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_Context_tyName___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileParserExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___lam__0(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_Context_tyName(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_unfoldDefinition_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_ParserCompiler_compileParserExpr_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_TransparencyMode_lt(uint8_t, uint8_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_ParserCompiler_CombinatorAttribute_setDeclFor(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_reduceEval___at___Lean_ParserCompiler_parserNodeKind_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_replaceParserTy(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileParserExpr(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileEmbeddedParsers(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_parserNodeKind_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_ParserCompiler_compileParserExpr_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_ParserCompiler_compileParserExpr_spec__0___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileEmbeddedParsers___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_parserNodeKind_x3f___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfCore_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
lean_object* l_Lean_addAndCompile(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConst(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_replaceParserTy___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___lam__2(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getConstInfo___at_____private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_Context_tyName___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_3, 3);
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_Context_tyName(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_ParserCompiler_Context_tyName___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_Context_tyName___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_ParserCompiler_Context_tyName___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_Context_tyName___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_ParserCompiler_Context_tyName(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_14; 
x_14 = l_Lean_Expr_isOptParam(x_2);
if (x_14 == 0)
{
x_3 = x_2;
goto block_13;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = l_Lean_Expr_appFn_x21(x_2);
lean_dec(x_2);
x_16 = l_Lean_Expr_appArg_x21(x_15);
lean_dec(x_15);
x_3 = x_16;
goto block_13;
}
block_13:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
lean_inc(x_5);
x_6 = l_Lean_Name_mkStr3(x_4, x_5, x_5);
x_7 = l_Lean_Expr_isConstOf(x_3, x_6);
lean_dec(x_6);
lean_dec(x_3);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = l_Lean_ParserCompiler_Context_tyName___redArg(x_1);
x_10 = lean_box(0);
x_11 = l_Lean_Expr_const___override(x_9, x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_replaceParserTy___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = lean_replace_expr(x_3, x_2);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_replaceParserTy(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_ParserCompiler_replaceParserTy___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_replaceParserTy___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_ParserCompiler_replaceParserTy___redArg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_replaceParserTy___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_ParserCompiler_replaceParserTy(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceEval___at___Lean_ParserCompiler_parserNodeKind_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_47; uint8_t x_48; uint8_t x_49; 
x_7 = lean_box(1);
x_8 = lean_ctor_get(x_2, 0);
x_47 = lean_ctor_get_uint8(x_8, 9);
x_48 = lean_unbox(x_7);
x_49 = l_Lean_Meta_TransparencyMode_lt(x_47, x_48);
if (x_49 == 0)
{
x_9 = x_47;
goto block_46;
}
else
{
uint8_t x_50; 
x_50 = lean_unbox(x_7);
x_9 = x_50;
goto block_46;
}
block_46:
{
uint8_t x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; lean_object* x_27; uint64_t x_28; lean_object* x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; 
x_10 = lean_ctor_get_uint8(x_8, 0);
x_11 = lean_ctor_get_uint8(x_8, 1);
x_12 = lean_ctor_get_uint8(x_8, 2);
x_13 = lean_ctor_get_uint8(x_8, 3);
x_14 = lean_ctor_get_uint8(x_8, 4);
x_15 = lean_ctor_get_uint8(x_8, 5);
x_16 = lean_ctor_get_uint8(x_8, 6);
x_17 = lean_ctor_get_uint8(x_8, 7);
x_18 = lean_ctor_get_uint8(x_8, 8);
x_19 = lean_ctor_get_uint8(x_8, 10);
x_20 = lean_ctor_get_uint8(x_8, 11);
x_21 = lean_ctor_get_uint8(x_8, 12);
x_22 = lean_ctor_get_uint8(x_8, 13);
x_23 = lean_ctor_get_uint8(x_8, 14);
x_24 = lean_ctor_get_uint8(x_8, 15);
x_25 = lean_ctor_get_uint8(x_8, 16);
x_26 = lean_ctor_get_uint8(x_8, 17);
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
lean_ctor_set_uint8(x_27, 9, x_9);
lean_ctor_set_uint8(x_27, 10, x_19);
lean_ctor_set_uint8(x_27, 11, x_20);
lean_ctor_set_uint8(x_27, 12, x_21);
lean_ctor_set_uint8(x_27, 13, x_22);
lean_ctor_set_uint8(x_27, 14, x_23);
lean_ctor_set_uint8(x_27, 15, x_24);
lean_ctor_set_uint8(x_27, 16, x_25);
lean_ctor_set_uint8(x_27, 17, x_26);
x_28 = lean_ctor_get_uint64(x_2, sizeof(void*)*7);
x_29 = lean_unsigned_to_nat(2u);
x_30 = lean_uint64_of_nat(x_29);
x_31 = lean_uint64_shift_right(x_28, x_30);
x_32 = lean_uint64_shift_left(x_31, x_30);
x_33 = l_Lean_Meta_TransparencyMode_toUInt64(x_9);
x_34 = lean_uint64_lor(x_32, x_33);
x_35 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 8);
x_36 = lean_ctor_get(x_2, 1);
x_37 = lean_ctor_get(x_2, 2);
x_38 = lean_ctor_get(x_2, 3);
x_39 = lean_ctor_get(x_2, 4);
x_40 = lean_ctor_get(x_2, 5);
x_41 = lean_ctor_get(x_2, 6);
x_42 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 9);
x_43 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 10);
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
x_45 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName(x_1, x_44, x_3, x_4, x_5, x_6);
return x_45;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_ParserCompiler_parserNodeKind_x3f_spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_12; 
x_12 = lean_usize_dec_eq(x_3, x_4);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_13 = lean_mk_string_unchecked("Lean", 4, 4);
x_14 = lean_mk_string_unchecked("Parser", 6, 6);
x_15 = lean_array_uget(x_2, x_3);
x_21 = lean_ctor_get(x_15, 0);
lean_inc(x_21);
lean_inc(x_1);
x_22 = l_Lean_LocalContext_getFVar_x21(x_1, x_21);
lean_dec(x_21);
x_23 = lean_ctor_get(x_22, 3);
lean_inc(x_23);
lean_dec(x_22);
x_16 = x_23;
goto block_20;
block_20:
{
lean_object* x_17; uint8_t x_18; 
lean_inc(x_14);
x_17 = l_Lean_Name_mkStr3(x_13, x_14, x_14);
x_18 = l_Lean_Expr_isConstOf(x_16, x_17);
lean_dec(x_17);
lean_dec(x_16);
if (x_18 == 0)
{
lean_dec(x_15);
x_6 = x_5;
goto block_11;
}
else
{
lean_object* x_19; 
x_19 = lean_array_push(x_5, x_15);
x_6 = x_19;
goto block_11;
}
}
}
else
{
lean_dec(x_1);
return x_5;
}
block_11:
{
lean_object* x_7; size_t x_8; size_t x_9; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_usize_of_nat(x_7);
x_9 = lean_usize_add(x_3, x_8);
x_3 = x_9;
x_5 = x_6;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_parserNodeKind_x3f___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_ParserCompiler_parserNodeKind_x3f(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_parserNodeKind_x3f___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_9 = lean_unsigned_to_nat(0u);
x_24 = l_Array_zipIdx___redArg(x_2, x_9);
x_25 = lean_array_get_size(x_24);
x_26 = lean_mk_empty_array_with_capacity(x_9);
x_27 = lean_nat_dec_lt(x_9, x_25);
if (x_27 == 0)
{
lean_dec(x_25);
lean_dec(x_24);
x_10 = x_26;
goto block_23;
}
else
{
uint8_t x_28; 
x_28 = lean_nat_dec_le(x_25, x_25);
if (x_28 == 0)
{
lean_dec(x_25);
lean_dec(x_24);
x_10 = x_26;
goto block_23;
}
else
{
lean_object* x_29; size_t x_30; size_t x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_4, 2);
lean_inc(x_29);
x_30 = lean_usize_of_nat(x_9);
x_31 = lean_usize_of_nat(x_25);
lean_dec(x_25);
x_32 = l_Array_foldlMUnsafe_fold___at___Lean_ParserCompiler_parserNodeKind_x3f_spec__1(x_29, x_24, x_30, x_31, x_26);
lean_dec(x_24);
x_10 = x_32;
goto block_23;
}
}
block_23:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_array_get_size(x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_dec_eq(x_11, x_12);
lean_dec(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_8);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_array_fget(x_10, x_9);
lean_dec(x_10);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l_Lean_Expr_getAppNumArgs(x_1);
x_19 = lean_nat_sub(x_18, x_17);
lean_dec(x_17);
lean_dec(x_18);
x_20 = lean_nat_sub(x_19, x_12);
lean_dec(x_19);
x_21 = l_Lean_Expr_getRevArg_x21(x_1, x_20);
x_22 = l_Lean_ParserCompiler_parserNodeKind_x3f(x_21, x_4, x_5, x_6, x_7, x_8);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_parserNodeKind_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_14; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_14 = l_Lean_Meta_whnfCore_go(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
if (lean_obj_tag(x_15) == 6)
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; 
x_34 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_parserNodeKind_x3f___lam__0___boxed), 7, 0);
x_35 = lean_box(0);
x_36 = lean_unbox(x_35);
x_37 = l_Lean_Meta_lambdaLetTelescope___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg(x_15, x_34, x_36, x_2, x_3, x_4, x_5, x_16);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
lean_inc(x_15);
x_38 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_parserNodeKind_x3f___lam__1___boxed), 8, 1);
lean_closure_set(x_38, 0, x_15);
x_39 = lean_mk_string_unchecked("Lean", 4, 4);
x_40 = lean_mk_string_unchecked("Parser", 6, 6);
x_65 = lean_mk_string_unchecked("leadingNode", 11, 11);
lean_inc(x_40);
lean_inc(x_39);
x_66 = l_Lean_Name_mkStr3(x_39, x_40, x_65);
x_67 = lean_unsigned_to_nat(3u);
x_68 = l_Lean_Expr_isAppOfArity(x_15, x_66, x_67);
lean_dec(x_66);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_69 = lean_mk_string_unchecked("trailingNode", 12, 12);
lean_inc(x_40);
lean_inc(x_39);
x_70 = l_Lean_Name_mkStr3(x_39, x_40, x_69);
x_71 = lean_unsigned_to_nat(4u);
x_72 = l_Lean_Expr_isAppOfArity(x_15, x_70, x_71);
lean_dec(x_70);
x_41 = x_72;
goto block_64;
}
else
{
x_41 = x_68;
goto block_64;
}
block_64:
{
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_42 = lean_mk_string_unchecked("node", 4, 4);
lean_inc(x_40);
lean_inc(x_39);
x_43 = l_Lean_Name_mkStr3(x_39, x_40, x_42);
x_44 = lean_unsigned_to_nat(2u);
x_45 = l_Lean_Expr_isAppOfArity(x_15, x_43, x_44);
lean_dec(x_43);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_46 = lean_mk_string_unchecked("withAntiquot", 12, 12);
x_47 = l_Lean_Name_mkStr3(x_39, x_40, x_46);
x_48 = l_Lean_Expr_isAppOfArity(x_15, x_47, x_44);
lean_dec(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = l_Lean_Expr_getAppFn(x_15);
lean_dec(x_15);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_50 = lean_infer_type(x_49, x_2, x_3, x_4, x_5, x_16);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = l_Lean_Meta_forallTelescope___at___Lean_Meta_mapForallTelescope_x27_spec__0(lean_box(0), x_51, x_38, x_48, x_2, x_3, x_4, x_5, x_52);
return x_53;
}
else
{
uint8_t x_54; 
lean_dec(x_38);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_54 = !lean_is_exclusive(x_50);
if (x_54 == 0)
{
return x_50;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_50, 0);
x_56 = lean_ctor_get(x_50, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_50);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_38);
x_58 = lean_unsigned_to_nat(1u);
x_59 = l_Lean_Expr_getAppNumArgs(x_15);
x_60 = lean_nat_sub(x_59, x_58);
lean_dec(x_59);
x_61 = lean_nat_sub(x_60, x_58);
lean_dec(x_60);
x_62 = l_Lean_Expr_getRevArg_x21(x_15, x_61);
lean_dec(x_15);
x_1 = x_62;
x_6 = x_16;
goto _start;
}
}
else
{
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
goto block_33;
}
}
else
{
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
goto block_33;
}
}
}
block_33:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = l_Lean_Expr_getAppNumArgs(x_15);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_sub(x_17, x_18);
lean_dec(x_17);
x_20 = l_Lean_Expr_getRevArg_x21(x_15, x_19);
lean_dec(x_15);
x_21 = l_Lean_Meta_reduceEval___at___Lean_ParserCompiler_parserNodeKind_x3f_spec__0(x_20, x_2, x_3, x_4, x_5, x_16);
lean_dec(x_2);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_21, 0, x_24);
return x_21;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_21, 0);
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_21);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_25);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = lean_ctor_get(x_21, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_21, 1);
lean_inc(x_30);
lean_dec(x_21);
x_31 = l_Lean_Exception_isInterrupt(x_29);
if (x_31 == 0)
{
uint8_t x_32; 
x_32 = l_Lean_Exception_isRuntime(x_29);
x_7 = x_30;
x_8 = x_29;
x_9 = x_32;
goto block_13;
}
else
{
x_7 = x_30;
x_8 = x_29;
x_9 = x_31;
goto block_13;
}
}
}
}
else
{
uint8_t x_73; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_73 = !lean_is_exclusive(x_14);
if (x_73 == 0)
{
return x_14;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_14, 0);
x_75 = lean_ctor_get(x_14, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_14);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
block_13:
{
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_8);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_7);
return x_11;
}
else
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_7);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceEval___at___Lean_ParserCompiler_parserNodeKind_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_reduceEval___at___Lean_ParserCompiler_parserNodeKind_x3f_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_ParserCompiler_parserNodeKind_x3f_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at___Lean_ParserCompiler_parserNodeKind_x3f_spec__1(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_parserNodeKind_x3f___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_ParserCompiler_parserNodeKind_x3f___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_parserNodeKind_x3f___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_ParserCompiler_parserNodeKind_x3f___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_ParserCompiler_compileParserExpr_spec__0___redArg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_3, x_4);
if (x_11 == 0)
{
lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_24; lean_object* x_25; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_usize_of_nat(x_12);
x_14 = lean_usize_sub(x_3, x_13);
x_24 = lean_array_uget(x_2, x_14);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_25 = lean_infer_type(x_24, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
lean_inc(x_1);
x_28 = l_Lean_ParserCompiler_replaceParserTy___redArg(x_1, x_26);
lean_dec(x_26);
x_15 = x_28;
x_16 = x_27;
goto block_23;
}
else
{
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_25, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_25, 1);
lean_inc(x_30);
lean_dec(x_25);
x_15 = x_29;
x_16 = x_30;
goto block_23;
}
else
{
lean_dec(x_5);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_25, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_25, 1);
lean_inc(x_32);
lean_dec(x_25);
x_3 = x_14;
x_5 = x_31;
x_10 = x_32;
goto _start;
}
else
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_25;
}
}
}
block_23:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_17 = lean_mk_string_unchecked("_", 1, 1);
x_18 = l_Lean_Name_mkStr1(x_17);
x_19 = lean_box(0);
x_20 = lean_unbox(x_19);
x_21 = l_Lean_Expr_forallE___override(x_18, x_15, x_5, x_20);
x_3 = x_14;
x_5 = x_21;
x_10 = x_16;
goto _start;
}
}
else
{
lean_object* x_34; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_5);
lean_ctor_set(x_34, 1, x_10);
return x_34;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_ParserCompiler_compileParserExpr_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_foldrMUnsafe_fold___at___Lean_ParserCompiler_compileParserExpr_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_ParserCompiler_compileParserExpr_spec__1___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_ParserCompiler_compileParserExpr_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_6, 1);
x_23 = lean_nat_dec_lt(x_8, x_22);
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_7);
lean_ctor_set(x_24, 1, x_13);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = l_Lean_instInhabitedExpr;
x_26 = lean_array_get(x_25, x_1, x_8);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_27 = lean_infer_type(x_26, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_alloc_closure((void*)(l_Std_Range_forIn_x27_loop___at___Lean_ParserCompiler_compileParserExpr_spec__1___redArg___lam__0___boxed), 7, 0);
x_31 = lean_box(0);
x_32 = lean_unbox(x_31);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_33 = l_Lean_Meta_forallTelescope___at___Lean_Meta_mapForallTelescope_x27_spec__0(lean_box(0), x_28, x_30, x_32, x_9, x_10, x_11, x_12, x_29);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_array_get(x_25, x_2, x_8);
x_37 = l_Lean_ParserCompiler_Context_tyName___redArg(x_3);
x_38 = l_Lean_Expr_isConstOf(x_34, x_37);
lean_dec(x_37);
lean_dec(x_34);
if (x_38 == 0)
{
x_14 = x_7;
x_15 = x_36;
x_16 = x_35;
goto block_21;
}
else
{
lean_object* x_39; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_3);
x_39 = l_Lean_ParserCompiler_compileParserExpr___redArg(x_3, x_4, x_5, x_36, x_9, x_10, x_11, x_12, x_35);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_14 = x_7;
x_15 = x_40;
x_16 = x_41;
goto block_21;
}
else
{
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
return x_39;
}
}
}
else
{
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
return x_33;
}
}
else
{
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
return x_27;
}
}
block_21:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = l_Lean_Expr_app___override(x_14, x_15);
x_18 = lean_ctor_get(x_6, 2);
x_19 = lean_nat_add(x_8, x_18);
lean_dec(x_8);
x_7 = x_17;
x_8 = x_19;
x_13 = x_16;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_ParserCompiler_compileParserExpr_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Std_Range_forIn_x27_loop___at___Lean_ParserCompiler_compileParserExpr_spec__1___redArg(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_12, x_13, x_14, x_15, x_16);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___lam__0(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_11 = l_Lean_ParserCompiler_compileParserExpr___redArg(x_1, x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; lean_object* x_21; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_box(0);
x_15 = lean_box(1);
x_16 = lean_box(1);
x_17 = lean_unbox(x_14);
x_18 = lean_unbox(x_15);
x_19 = lean_unbox(x_14);
x_20 = lean_unbox(x_16);
x_21 = l_Lean_Meta_mkLambdaFVars(x_4, x_12, x_17, x_18, x_19, x_20, x_6, x_7, x_8, x_9, x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_21;
}
else
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_14 = l_Lean_Expr_const___override(x_1, x_2);
x_15 = lean_box(0);
x_16 = l_Lean_Expr_sort___override(x_15);
x_17 = l_Lean_Expr_getAppNumArgs(x_3);
lean_inc(x_17);
x_18 = lean_mk_array(x_17, x_16);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_sub(x_17, x_19);
lean_dec(x_17);
x_21 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_3, x_18, x_20);
x_22 = lean_unsigned_to_nat(0u);
x_27 = lean_array_get_size(x_7);
x_28 = lean_array_get_size(x_21);
x_29 = lean_nat_dec_le(x_27, x_28);
if (x_29 == 0)
{
lean_dec(x_27);
x_23 = x_28;
goto block_26;
}
else
{
lean_dec(x_28);
x_23 = x_27;
goto block_26;
}
block_26:
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set(x_24, 2, x_19);
x_25 = l_Std_Range_forIn_x27_loop___at___Lean_ParserCompiler_compileParserExpr_spec__1___redArg(x_7, x_21, x_4, x_5, x_6, x_24, x_14, x_22, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_24);
lean_dec(x_21);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___lam__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_box(0);
lean_inc(x_5);
x_12 = l_Lean_Expr_const___override(x_5, x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_13 = lean_infer_type(x_12, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_box(x_3);
x_17 = lean_box(x_4);
x_18 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserExpr___redArg___lam__1___boxed), 13, 6);
lean_closure_set(x_18, 0, x_5);
lean_closure_set(x_18, 1, x_11);
lean_closure_set(x_18, 2, x_1);
lean_closure_set(x_18, 3, x_2);
lean_closure_set(x_18, 4, x_16);
lean_closure_set(x_18, 5, x_17);
x_19 = lean_box(0);
x_20 = lean_unbox(x_19);
x_21 = l_Lean_Meta_forallTelescope___at___Lean_Meta_mapForallTelescope_x27_spec__0(lean_box(0), x_14, x_18, x_20, x_6, x_7, x_8, x_9, x_15);
return x_21;
}
else
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_9 = l_Lean_ParserCompiler_Context_tyName___redArg(x_1);
x_10 = lean_box(0);
x_11 = l_Lean_Expr_const___override(x_9, x_10);
x_12 = lean_array_get_size(x_2);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_lt(x_13, x_12);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_8);
return x_15;
}
else
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_17 = lean_usize_of_nat(x_13);
x_18 = l_Array_foldrMUnsafe_fold___at___Lean_ParserCompiler_compileParserExpr_spec__0___redArg(x_1, x_2, x_16, x_17, x_11, x_4, x_5, x_6, x_7, x_8);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_10 = l_Lean_Meta_whnfCore_go(x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
switch (lean_obj_tag(x_11)) {
case 1:
{
uint8_t x_12; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_10, 0);
lean_dec(x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
case 6:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_dec(x_10);
x_17 = lean_box(x_2);
x_18 = lean_box(x_3);
x_19 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserExpr___redArg___lam__0___boxed), 10, 3);
lean_closure_set(x_19, 0, x_1);
lean_closure_set(x_19, 1, x_17);
lean_closure_set(x_19, 2, x_18);
x_20 = lean_box(0);
x_21 = lean_unbox(x_20);
x_22 = l_Lean_Meta_lambdaLetTelescope___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg(x_11, x_19, x_21, x_5, x_6, x_7, x_8, x_16);
return x_22;
}
default: 
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_10, 1);
lean_inc(x_23);
lean_dec(x_10);
x_24 = l_Lean_Expr_getAppFn(x_11);
if (lean_obj_tag(x_24) == 4)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_st_ref_get(x_8, x_23);
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
x_30 = lean_ctor_get(x_27, 0);
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_ctor_get(x_1, 2);
lean_inc(x_31);
lean_inc(x_30);
x_32 = l_Lean_ParserCompiler_CombinatorAttribute_getDeclFor_x3f(x_31, x_30, x_25);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; 
lean_inc(x_25);
x_33 = l_Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0(x_25, x_5, x_6, x_7, x_8, x_28);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_alloc_closure((void*)(l_Std_Range_forIn_x27_loop___at___Lean_ParserCompiler_compileParserExpr_spec__1___redArg___lam__0___boxed), 7, 0);
x_37 = l_Lean_ConstantInfo_type(x_34);
x_38 = lean_box(0);
x_39 = lean_unbox(x_38);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_37);
x_40 = l_Lean_Meta_forallTelescope___at___Lean_Meta_mapForallTelescope_x27_spec__0(lean_box(0), x_37, x_36, x_39, x_5, x_6, x_7, x_8, x_35);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_290; lean_object* x_345; lean_object* x_346; uint8_t x_347; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_43 = x_40;
} else {
 lean_dec_ref(x_40);
 x_43 = lean_box(0);
}
lean_inc(x_1);
x_44 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserExpr___redArg___lam__4___boxed), 8, 1);
lean_closure_set(x_44, 0, x_1);
x_45 = lean_ctor_get(x_1, 0);
lean_inc(x_45);
lean_inc(x_45);
lean_inc(x_25);
x_46 = l_Lean_Name_append(x_25, x_45);
x_47 = lean_mk_string_unchecked("Lean", 4, 4);
x_48 = lean_mk_string_unchecked("Parser", 6, 6);
x_345 = lean_mk_string_unchecked("TrailingParser", 14, 14);
lean_inc(x_48);
lean_inc(x_47);
x_346 = l_Lean_Name_mkStr3(x_47, x_48, x_345);
x_347 = l_Lean_Expr_isConstOf(x_41, x_346);
lean_dec(x_346);
if (x_347 == 0)
{
lean_object* x_348; uint8_t x_349; 
lean_inc_n(x_48, 2);
lean_inc(x_47);
x_348 = l_Lean_Name_mkStr3(x_47, x_48, x_48);
x_349 = l_Lean_Expr_isConstOf(x_41, x_348);
lean_dec(x_348);
lean_dec(x_41);
x_290 = x_349;
goto block_344;
}
else
{
lean_dec(x_41);
x_290 = x_347;
goto block_344;
}
block_82:
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; 
x_56 = lean_mk_string_unchecked("Attr", 4, 4);
x_57 = lean_mk_string_unchecked("simple", 6, 6);
x_58 = l_Lean_Name_mkStr4(x_47, x_48, x_56, x_57);
lean_inc(x_55);
x_59 = lean_mk_syntax_ident(x_55);
x_60 = lean_mk_syntax_ident(x_49);
x_61 = lean_unsigned_to_nat(1u);
x_62 = lean_mk_empty_array_with_capacity(x_61);
x_63 = lean_array_push(x_62, x_60);
x_64 = lean_mk_string_unchecked("null", 4, 4);
x_65 = l_Lean_Name_mkStr1(x_64);
x_66 = lean_box(2);
x_67 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_65);
lean_ctor_set(x_67, 2, x_63);
x_68 = lean_unsigned_to_nat(2u);
x_69 = lean_mk_empty_array_with_capacity(x_68);
x_70 = lean_array_push(x_69, x_59);
x_71 = lean_array_push(x_70, x_67);
x_72 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_72, 0, x_66);
lean_ctor_set(x_72, 1, x_58);
lean_ctor_set(x_72, 2, x_71);
x_73 = lean_box(0);
x_74 = lean_unbox(x_73);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_46);
x_75 = l_Lean_Attribute_add(x_46, x_55, x_72, x_74, x_53, x_54, x_52);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
lean_dec(x_75);
x_77 = l_Lean_ParserCompiler_compileParserExpr___redArg___lam__2(x_11, x_1, x_2, x_3, x_46, x_51, x_50, x_53, x_54, x_76);
return x_77;
}
else
{
uint8_t x_78; 
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_46);
lean_dec(x_11);
lean_dec(x_1);
x_78 = !lean_is_exclusive(x_75);
if (x_78 == 0)
{
return x_75;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_75, 0);
x_80 = lean_ctor_get(x_75, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_75);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
block_289:
{
lean_object* x_89; lean_object* x_90; 
lean_inc(x_1);
x_89 = l_Lean_ParserCompiler_replaceParserTy___redArg(x_1, x_83);
lean_dec(x_83);
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_1);
x_90 = l_Lean_ParserCompiler_compileParserExpr___redArg(x_1, x_2, x_3, x_89, x_84, x_85, x_86, x_87, x_88);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; uint8_t x_93; lean_object* x_94; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
x_93 = lean_unbox(x_38);
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_37);
x_94 = l_Lean_Meta_forallTelescope___at___Lean_Meta_mapForallTelescope_x27_spec__0(lean_box(0), x_37, x_44, x_93, x_84, x_85, x_86, x_87, x_92);
if (lean_obj_tag(x_94) == 0)
{
uint8_t x_95; 
x_95 = !lean_is_exclusive(x_94);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; lean_object* x_104; lean_object* x_105; 
x_96 = lean_ctor_get(x_94, 0);
x_97 = lean_ctor_get(x_94, 1);
x_98 = lean_box(0);
lean_inc(x_46);
x_99 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_99, 0, x_46);
lean_ctor_set(x_99, 1, x_98);
lean_ctor_set(x_99, 2, x_96);
x_100 = lean_box(0);
x_101 = lean_box(1);
lean_inc(x_46);
lean_ctor_set_tag(x_94, 1);
lean_ctor_set(x_94, 1, x_98);
lean_ctor_set(x_94, 0, x_46);
x_102 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_102, 0, x_99);
lean_ctor_set(x_102, 1, x_91);
lean_ctor_set(x_102, 2, x_100);
lean_ctor_set(x_102, 3, x_94);
x_103 = lean_unbox(x_101);
lean_ctor_set_uint8(x_102, sizeof(void*)*4, x_103);
x_104 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_104, 0, x_102);
lean_inc(x_87);
lean_inc(x_86);
x_105 = l_Lean_addAndCompile(x_104, x_86, x_87, x_97);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; uint8_t x_108; 
x_106 = lean_ctor_get(x_105, 1);
lean_inc(x_106);
lean_dec(x_105);
x_107 = lean_st_ref_take(x_87, x_106);
x_108 = !lean_is_exclusive(x_107);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; 
x_109 = lean_ctor_get(x_107, 0);
x_110 = lean_ctor_get(x_107, 1);
x_111 = lean_ctor_get(x_109, 0);
lean_inc(x_111);
lean_inc(x_46);
x_112 = l_Lean_ParserCompiler_CombinatorAttribute_setDeclFor(x_31, x_111, x_25, x_46);
x_113 = lean_ctor_get(x_109, 1);
lean_inc(x_113);
x_114 = lean_ctor_get(x_109, 2);
lean_inc(x_114);
x_115 = lean_ctor_get(x_109, 3);
lean_inc(x_115);
x_116 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_116);
x_117 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_117, 0, x_116);
lean_inc(x_117);
lean_ctor_set(x_107, 1, x_117);
lean_ctor_set(x_107, 0, x_117);
x_118 = lean_ctor_get(x_109, 5);
lean_inc(x_118);
x_119 = lean_ctor_get(x_109, 6);
lean_inc(x_119);
x_120 = lean_ctor_get(x_109, 7);
lean_inc(x_120);
lean_dec(x_109);
x_121 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_121, 0, x_112);
lean_ctor_set(x_121, 1, x_113);
lean_ctor_set(x_121, 2, x_114);
lean_ctor_set(x_121, 3, x_115);
lean_ctor_set(x_121, 4, x_107);
lean_ctor_set(x_121, 5, x_118);
lean_ctor_set(x_121, 6, x_119);
lean_ctor_set(x_121, 7, x_120);
x_122 = lean_st_ref_set(x_87, x_121, x_110);
x_123 = lean_ctor_get(x_122, 1);
lean_inc(x_123);
lean_dec(x_122);
x_124 = lean_st_ref_take(x_85, x_123);
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_124, 1);
lean_inc(x_126);
lean_dec(x_124);
x_127 = lean_ctor_get(x_125, 0);
lean_inc(x_127);
lean_inc(x_116);
x_128 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_128, 0, x_116);
lean_inc(x_116);
x_129 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_129, 0, x_116);
lean_inc(x_116);
x_130 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_130, 0, x_116);
x_131 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_131, 0, x_116);
lean_inc(x_131);
lean_inc(x_128);
x_132 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_132, 0, x_128);
lean_ctor_set(x_132, 1, x_129);
lean_ctor_set(x_132, 2, x_130);
lean_ctor_set(x_132, 3, x_128);
lean_ctor_set(x_132, 4, x_131);
lean_ctor_set(x_132, 5, x_131);
x_133 = lean_ctor_get(x_125, 2);
lean_inc(x_133);
x_134 = lean_ctor_get(x_125, 3);
lean_inc(x_134);
x_135 = lean_ctor_get(x_125, 4);
lean_inc(x_135);
lean_dec(x_125);
x_136 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_136, 0, x_127);
lean_ctor_set(x_136, 1, x_132);
lean_ctor_set(x_136, 2, x_133);
lean_ctor_set(x_136, 3, x_134);
lean_ctor_set(x_136, 4, x_135);
x_137 = lean_st_ref_set(x_85, x_136, x_126);
x_138 = lean_ctor_get(x_137, 1);
lean_inc(x_138);
lean_dec(x_137);
x_139 = l_Lean_Expr_isConst(x_37);
lean_dec(x_37);
if (x_139 == 0)
{
lean_object* x_140; 
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_34);
x_140 = l_Lean_ParserCompiler_compileParserExpr___redArg___lam__2(x_11, x_1, x_2, x_3, x_46, x_84, x_85, x_86, x_87, x_138);
return x_140;
}
else
{
uint8_t x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_unbox(x_38);
x_142 = l_Lean_ConstantInfo_value_x21(x_34, x_141);
lean_dec(x_34);
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_84);
x_143 = l_Lean_ParserCompiler_parserNodeKind_x3f(x_142, x_84, x_85, x_86, x_87, x_138);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; 
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; lean_object* x_146; 
lean_dec(x_48);
lean_dec(x_47);
x_145 = lean_ctor_get(x_143, 1);
lean_inc(x_145);
lean_dec(x_143);
x_146 = l_Lean_ParserCompiler_compileParserExpr___redArg___lam__2(x_11, x_1, x_2, x_3, x_46, x_84, x_85, x_86, x_87, x_145);
return x_146;
}
else
{
if (x_2 == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_147 = lean_ctor_get(x_143, 1);
lean_inc(x_147);
lean_dec(x_143);
x_148 = lean_ctor_get(x_144, 0);
lean_inc(x_148);
lean_dec(x_144);
x_149 = lean_ctor_get(x_1, 1);
lean_inc(x_149);
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
lean_dec(x_149);
x_151 = lean_ctor_get(x_150, 1);
lean_inc(x_151);
lean_dec(x_150);
x_49 = x_148;
x_50 = x_85;
x_51 = x_84;
x_52 = x_147;
x_53 = x_86;
x_54 = x_87;
x_55 = x_151;
goto block_82;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_152 = lean_ctor_get(x_143, 1);
lean_inc(x_152);
lean_dec(x_143);
x_153 = lean_ctor_get(x_144, 0);
lean_inc(x_153);
lean_dec(x_144);
x_154 = lean_ctor_get(x_1, 1);
lean_inc(x_154);
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
lean_dec(x_154);
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
lean_dec(x_155);
x_49 = x_153;
x_50 = x_85;
x_51 = x_84;
x_52 = x_152;
x_53 = x_86;
x_54 = x_87;
x_55 = x_156;
goto block_82;
}
}
}
else
{
uint8_t x_157; 
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_11);
lean_dec(x_1);
x_157 = !lean_is_exclusive(x_143);
if (x_157 == 0)
{
return x_143;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_158 = lean_ctor_get(x_143, 0);
x_159 = lean_ctor_get(x_143, 1);
lean_inc(x_159);
lean_inc(x_158);
lean_dec(x_143);
x_160 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_160, 0, x_158);
lean_ctor_set(x_160, 1, x_159);
return x_160;
}
}
}
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; uint8_t x_192; 
x_161 = lean_ctor_get(x_107, 0);
x_162 = lean_ctor_get(x_107, 1);
lean_inc(x_162);
lean_inc(x_161);
lean_dec(x_107);
x_163 = lean_ctor_get(x_161, 0);
lean_inc(x_163);
lean_inc(x_46);
x_164 = l_Lean_ParserCompiler_CombinatorAttribute_setDeclFor(x_31, x_163, x_25, x_46);
x_165 = lean_ctor_get(x_161, 1);
lean_inc(x_165);
x_166 = lean_ctor_get(x_161, 2);
lean_inc(x_166);
x_167 = lean_ctor_get(x_161, 3);
lean_inc(x_167);
x_168 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_168);
x_169 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_169, 0, x_168);
lean_inc(x_169);
x_170 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_169);
x_171 = lean_ctor_get(x_161, 5);
lean_inc(x_171);
x_172 = lean_ctor_get(x_161, 6);
lean_inc(x_172);
x_173 = lean_ctor_get(x_161, 7);
lean_inc(x_173);
lean_dec(x_161);
x_174 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_174, 0, x_164);
lean_ctor_set(x_174, 1, x_165);
lean_ctor_set(x_174, 2, x_166);
lean_ctor_set(x_174, 3, x_167);
lean_ctor_set(x_174, 4, x_170);
lean_ctor_set(x_174, 5, x_171);
lean_ctor_set(x_174, 6, x_172);
lean_ctor_set(x_174, 7, x_173);
x_175 = lean_st_ref_set(x_87, x_174, x_162);
x_176 = lean_ctor_get(x_175, 1);
lean_inc(x_176);
lean_dec(x_175);
x_177 = lean_st_ref_take(x_85, x_176);
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_177, 1);
lean_inc(x_179);
lean_dec(x_177);
x_180 = lean_ctor_get(x_178, 0);
lean_inc(x_180);
lean_inc(x_168);
x_181 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_181, 0, x_168);
lean_inc(x_168);
x_182 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_182, 0, x_168);
lean_inc(x_168);
x_183 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_183, 0, x_168);
x_184 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_184, 0, x_168);
lean_inc(x_184);
lean_inc(x_181);
x_185 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_185, 0, x_181);
lean_ctor_set(x_185, 1, x_182);
lean_ctor_set(x_185, 2, x_183);
lean_ctor_set(x_185, 3, x_181);
lean_ctor_set(x_185, 4, x_184);
lean_ctor_set(x_185, 5, x_184);
x_186 = lean_ctor_get(x_178, 2);
lean_inc(x_186);
x_187 = lean_ctor_get(x_178, 3);
lean_inc(x_187);
x_188 = lean_ctor_get(x_178, 4);
lean_inc(x_188);
lean_dec(x_178);
x_189 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_189, 0, x_180);
lean_ctor_set(x_189, 1, x_185);
lean_ctor_set(x_189, 2, x_186);
lean_ctor_set(x_189, 3, x_187);
lean_ctor_set(x_189, 4, x_188);
x_190 = lean_st_ref_set(x_85, x_189, x_179);
x_191 = lean_ctor_get(x_190, 1);
lean_inc(x_191);
lean_dec(x_190);
x_192 = l_Lean_Expr_isConst(x_37);
lean_dec(x_37);
if (x_192 == 0)
{
lean_object* x_193; 
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_34);
x_193 = l_Lean_ParserCompiler_compileParserExpr___redArg___lam__2(x_11, x_1, x_2, x_3, x_46, x_84, x_85, x_86, x_87, x_191);
return x_193;
}
else
{
uint8_t x_194; lean_object* x_195; lean_object* x_196; 
x_194 = lean_unbox(x_38);
x_195 = l_Lean_ConstantInfo_value_x21(x_34, x_194);
lean_dec(x_34);
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_84);
x_196 = l_Lean_ParserCompiler_parserNodeKind_x3f(x_195, x_84, x_85, x_86, x_87, x_191);
if (lean_obj_tag(x_196) == 0)
{
lean_object* x_197; 
x_197 = lean_ctor_get(x_196, 0);
lean_inc(x_197);
if (lean_obj_tag(x_197) == 0)
{
lean_object* x_198; lean_object* x_199; 
lean_dec(x_48);
lean_dec(x_47);
x_198 = lean_ctor_get(x_196, 1);
lean_inc(x_198);
lean_dec(x_196);
x_199 = l_Lean_ParserCompiler_compileParserExpr___redArg___lam__2(x_11, x_1, x_2, x_3, x_46, x_84, x_85, x_86, x_87, x_198);
return x_199;
}
else
{
if (x_2 == 0)
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_200 = lean_ctor_get(x_196, 1);
lean_inc(x_200);
lean_dec(x_196);
x_201 = lean_ctor_get(x_197, 0);
lean_inc(x_201);
lean_dec(x_197);
x_202 = lean_ctor_get(x_1, 1);
lean_inc(x_202);
x_203 = lean_ctor_get(x_202, 0);
lean_inc(x_203);
lean_dec(x_202);
x_204 = lean_ctor_get(x_203, 1);
lean_inc(x_204);
lean_dec(x_203);
x_49 = x_201;
x_50 = x_85;
x_51 = x_84;
x_52 = x_200;
x_53 = x_86;
x_54 = x_87;
x_55 = x_204;
goto block_82;
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_205 = lean_ctor_get(x_196, 1);
lean_inc(x_205);
lean_dec(x_196);
x_206 = lean_ctor_get(x_197, 0);
lean_inc(x_206);
lean_dec(x_197);
x_207 = lean_ctor_get(x_1, 1);
lean_inc(x_207);
x_208 = lean_ctor_get(x_207, 0);
lean_inc(x_208);
lean_dec(x_207);
x_209 = lean_ctor_get(x_208, 0);
lean_inc(x_209);
lean_dec(x_208);
x_49 = x_206;
x_50 = x_85;
x_51 = x_84;
x_52 = x_205;
x_53 = x_86;
x_54 = x_87;
x_55 = x_209;
goto block_82;
}
}
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_11);
lean_dec(x_1);
x_210 = lean_ctor_get(x_196, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_196, 1);
lean_inc(x_211);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 lean_ctor_release(x_196, 1);
 x_212 = x_196;
} else {
 lean_dec_ref(x_196);
 x_212 = lean_box(0);
}
if (lean_is_scalar(x_212)) {
 x_213 = lean_alloc_ctor(1, 2, 0);
} else {
 x_213 = x_212;
}
lean_ctor_set(x_213, 0, x_210);
lean_ctor_set(x_213, 1, x_211);
return x_213;
}
}
}
}
else
{
uint8_t x_214; 
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_37);
lean_dec(x_34);
lean_dec(x_31);
lean_dec(x_25);
lean_dec(x_11);
lean_dec(x_1);
x_214 = !lean_is_exclusive(x_105);
if (x_214 == 0)
{
return x_105;
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_215 = lean_ctor_get(x_105, 0);
x_216 = lean_ctor_get(x_105, 1);
lean_inc(x_216);
lean_inc(x_215);
lean_dec(x_105);
x_217 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_217, 0, x_215);
lean_ctor_set(x_217, 1, x_216);
return x_217;
}
}
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; uint8_t x_226; lean_object* x_227; lean_object* x_228; 
x_218 = lean_ctor_get(x_94, 0);
x_219 = lean_ctor_get(x_94, 1);
lean_inc(x_219);
lean_inc(x_218);
lean_dec(x_94);
x_220 = lean_box(0);
lean_inc(x_46);
x_221 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_221, 0, x_46);
lean_ctor_set(x_221, 1, x_220);
lean_ctor_set(x_221, 2, x_218);
x_222 = lean_box(0);
x_223 = lean_box(1);
lean_inc(x_46);
x_224 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_224, 0, x_46);
lean_ctor_set(x_224, 1, x_220);
x_225 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_225, 0, x_221);
lean_ctor_set(x_225, 1, x_91);
lean_ctor_set(x_225, 2, x_222);
lean_ctor_set(x_225, 3, x_224);
x_226 = lean_unbox(x_223);
lean_ctor_set_uint8(x_225, sizeof(void*)*4, x_226);
x_227 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_227, 0, x_225);
lean_inc(x_87);
lean_inc(x_86);
x_228 = l_Lean_addAndCompile(x_227, x_86, x_87, x_219);
if (lean_obj_tag(x_228) == 0)
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; uint8_t x_263; 
x_229 = lean_ctor_get(x_228, 1);
lean_inc(x_229);
lean_dec(x_228);
x_230 = lean_st_ref_take(x_87, x_229);
x_231 = lean_ctor_get(x_230, 0);
lean_inc(x_231);
x_232 = lean_ctor_get(x_230, 1);
lean_inc(x_232);
if (lean_is_exclusive(x_230)) {
 lean_ctor_release(x_230, 0);
 lean_ctor_release(x_230, 1);
 x_233 = x_230;
} else {
 lean_dec_ref(x_230);
 x_233 = lean_box(0);
}
x_234 = lean_ctor_get(x_231, 0);
lean_inc(x_234);
lean_inc(x_46);
x_235 = l_Lean_ParserCompiler_CombinatorAttribute_setDeclFor(x_31, x_234, x_25, x_46);
x_236 = lean_ctor_get(x_231, 1);
lean_inc(x_236);
x_237 = lean_ctor_get(x_231, 2);
lean_inc(x_237);
x_238 = lean_ctor_get(x_231, 3);
lean_inc(x_238);
x_239 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_239);
x_240 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_240, 0, x_239);
lean_inc(x_240);
if (lean_is_scalar(x_233)) {
 x_241 = lean_alloc_ctor(0, 2, 0);
} else {
 x_241 = x_233;
}
lean_ctor_set(x_241, 0, x_240);
lean_ctor_set(x_241, 1, x_240);
x_242 = lean_ctor_get(x_231, 5);
lean_inc(x_242);
x_243 = lean_ctor_get(x_231, 6);
lean_inc(x_243);
x_244 = lean_ctor_get(x_231, 7);
lean_inc(x_244);
lean_dec(x_231);
x_245 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_245, 0, x_235);
lean_ctor_set(x_245, 1, x_236);
lean_ctor_set(x_245, 2, x_237);
lean_ctor_set(x_245, 3, x_238);
lean_ctor_set(x_245, 4, x_241);
lean_ctor_set(x_245, 5, x_242);
lean_ctor_set(x_245, 6, x_243);
lean_ctor_set(x_245, 7, x_244);
x_246 = lean_st_ref_set(x_87, x_245, x_232);
x_247 = lean_ctor_get(x_246, 1);
lean_inc(x_247);
lean_dec(x_246);
x_248 = lean_st_ref_take(x_85, x_247);
x_249 = lean_ctor_get(x_248, 0);
lean_inc(x_249);
x_250 = lean_ctor_get(x_248, 1);
lean_inc(x_250);
lean_dec(x_248);
x_251 = lean_ctor_get(x_249, 0);
lean_inc(x_251);
lean_inc(x_239);
x_252 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_252, 0, x_239);
lean_inc(x_239);
x_253 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_253, 0, x_239);
lean_inc(x_239);
x_254 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_254, 0, x_239);
x_255 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_255, 0, x_239);
lean_inc(x_255);
lean_inc(x_252);
x_256 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_256, 0, x_252);
lean_ctor_set(x_256, 1, x_253);
lean_ctor_set(x_256, 2, x_254);
lean_ctor_set(x_256, 3, x_252);
lean_ctor_set(x_256, 4, x_255);
lean_ctor_set(x_256, 5, x_255);
x_257 = lean_ctor_get(x_249, 2);
lean_inc(x_257);
x_258 = lean_ctor_get(x_249, 3);
lean_inc(x_258);
x_259 = lean_ctor_get(x_249, 4);
lean_inc(x_259);
lean_dec(x_249);
x_260 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_260, 0, x_251);
lean_ctor_set(x_260, 1, x_256);
lean_ctor_set(x_260, 2, x_257);
lean_ctor_set(x_260, 3, x_258);
lean_ctor_set(x_260, 4, x_259);
x_261 = lean_st_ref_set(x_85, x_260, x_250);
x_262 = lean_ctor_get(x_261, 1);
lean_inc(x_262);
lean_dec(x_261);
x_263 = l_Lean_Expr_isConst(x_37);
lean_dec(x_37);
if (x_263 == 0)
{
lean_object* x_264; 
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_34);
x_264 = l_Lean_ParserCompiler_compileParserExpr___redArg___lam__2(x_11, x_1, x_2, x_3, x_46, x_84, x_85, x_86, x_87, x_262);
return x_264;
}
else
{
uint8_t x_265; lean_object* x_266; lean_object* x_267; 
x_265 = lean_unbox(x_38);
x_266 = l_Lean_ConstantInfo_value_x21(x_34, x_265);
lean_dec(x_34);
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_84);
x_267 = l_Lean_ParserCompiler_parserNodeKind_x3f(x_266, x_84, x_85, x_86, x_87, x_262);
if (lean_obj_tag(x_267) == 0)
{
lean_object* x_268; 
x_268 = lean_ctor_get(x_267, 0);
lean_inc(x_268);
if (lean_obj_tag(x_268) == 0)
{
lean_object* x_269; lean_object* x_270; 
lean_dec(x_48);
lean_dec(x_47);
x_269 = lean_ctor_get(x_267, 1);
lean_inc(x_269);
lean_dec(x_267);
x_270 = l_Lean_ParserCompiler_compileParserExpr___redArg___lam__2(x_11, x_1, x_2, x_3, x_46, x_84, x_85, x_86, x_87, x_269);
return x_270;
}
else
{
if (x_2 == 0)
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; 
x_271 = lean_ctor_get(x_267, 1);
lean_inc(x_271);
lean_dec(x_267);
x_272 = lean_ctor_get(x_268, 0);
lean_inc(x_272);
lean_dec(x_268);
x_273 = lean_ctor_get(x_1, 1);
lean_inc(x_273);
x_274 = lean_ctor_get(x_273, 0);
lean_inc(x_274);
lean_dec(x_273);
x_275 = lean_ctor_get(x_274, 1);
lean_inc(x_275);
lean_dec(x_274);
x_49 = x_272;
x_50 = x_85;
x_51 = x_84;
x_52 = x_271;
x_53 = x_86;
x_54 = x_87;
x_55 = x_275;
goto block_82;
}
else
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; 
x_276 = lean_ctor_get(x_267, 1);
lean_inc(x_276);
lean_dec(x_267);
x_277 = lean_ctor_get(x_268, 0);
lean_inc(x_277);
lean_dec(x_268);
x_278 = lean_ctor_get(x_1, 1);
lean_inc(x_278);
x_279 = lean_ctor_get(x_278, 0);
lean_inc(x_279);
lean_dec(x_278);
x_280 = lean_ctor_get(x_279, 0);
lean_inc(x_280);
lean_dec(x_279);
x_49 = x_277;
x_50 = x_85;
x_51 = x_84;
x_52 = x_276;
x_53 = x_86;
x_54 = x_87;
x_55 = x_280;
goto block_82;
}
}
}
else
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; 
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_11);
lean_dec(x_1);
x_281 = lean_ctor_get(x_267, 0);
lean_inc(x_281);
x_282 = lean_ctor_get(x_267, 1);
lean_inc(x_282);
if (lean_is_exclusive(x_267)) {
 lean_ctor_release(x_267, 0);
 lean_ctor_release(x_267, 1);
 x_283 = x_267;
} else {
 lean_dec_ref(x_267);
 x_283 = lean_box(0);
}
if (lean_is_scalar(x_283)) {
 x_284 = lean_alloc_ctor(1, 2, 0);
} else {
 x_284 = x_283;
}
lean_ctor_set(x_284, 0, x_281);
lean_ctor_set(x_284, 1, x_282);
return x_284;
}
}
}
else
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; 
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_37);
lean_dec(x_34);
lean_dec(x_31);
lean_dec(x_25);
lean_dec(x_11);
lean_dec(x_1);
x_285 = lean_ctor_get(x_228, 0);
lean_inc(x_285);
x_286 = lean_ctor_get(x_228, 1);
lean_inc(x_286);
if (lean_is_exclusive(x_228)) {
 lean_ctor_release(x_228, 0);
 lean_ctor_release(x_228, 1);
 x_287 = x_228;
} else {
 lean_dec_ref(x_228);
 x_287 = lean_box(0);
}
if (lean_is_scalar(x_287)) {
 x_288 = lean_alloc_ctor(1, 2, 0);
} else {
 x_288 = x_287;
}
lean_ctor_set(x_288, 0, x_285);
lean_ctor_set(x_288, 1, x_286);
return x_288;
}
}
}
else
{
lean_dec(x_91);
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_37);
lean_dec(x_34);
lean_dec(x_31);
lean_dec(x_25);
lean_dec(x_11);
lean_dec(x_1);
return x_94;
}
}
else
{
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_44);
lean_dec(x_37);
lean_dec(x_34);
lean_dec(x_31);
lean_dec(x_25);
lean_dec(x_11);
lean_dec(x_1);
return x_90;
}
}
block_344:
{
if (x_290 == 0)
{
uint8_t x_291; lean_object* x_292; 
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_44);
lean_dec(x_37);
lean_dec(x_34);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_25);
x_291 = lean_unbox(x_38);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_11);
x_292 = l_Lean_Meta_unfoldDefinition_x3f(x_11, x_291, x_5, x_6, x_7, x_8, x_42);
if (lean_obj_tag(x_292) == 0)
{
lean_object* x_293; 
x_293 = lean_ctor_get(x_292, 0);
lean_inc(x_293);
if (lean_obj_tag(x_293) == 0)
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; 
lean_dec(x_1);
x_294 = lean_ctor_get(x_292, 1);
lean_inc(x_294);
lean_dec(x_292);
x_295 = lean_mk_string_unchecked("don't know how to generate ", 27, 27);
x_296 = l_Lean_stringToMessageData(x_295);
lean_dec(x_295);
x_297 = l_Lean_MessageData_ofName(x_45);
if (lean_is_scalar(x_43)) {
 x_298 = lean_alloc_ctor(7, 2, 0);
} else {
 x_298 = x_43;
 lean_ctor_set_tag(x_298, 7);
}
lean_ctor_set(x_298, 0, x_296);
lean_ctor_set(x_298, 1, x_297);
x_299 = lean_mk_string_unchecked(" for non-parser combinator '", 28, 28);
x_300 = l_Lean_stringToMessageData(x_299);
lean_dec(x_299);
if (lean_is_scalar(x_29)) {
 x_301 = lean_alloc_ctor(7, 2, 0);
} else {
 x_301 = x_29;
 lean_ctor_set_tag(x_301, 7);
}
lean_ctor_set(x_301, 0, x_298);
lean_ctor_set(x_301, 1, x_300);
x_302 = l_Lean_MessageData_ofExpr(x_11);
x_303 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_303, 0, x_301);
lean_ctor_set(x_303, 1, x_302);
x_304 = lean_mk_string_unchecked("'", 1, 1);
x_305 = l_Lean_stringToMessageData(x_304);
lean_dec(x_304);
x_306 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_306, 0, x_303);
lean_ctor_set(x_306, 1, x_305);
x_307 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_306, x_5, x_6, x_7, x_8, x_294);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_307;
}
else
{
lean_object* x_308; lean_object* x_309; 
lean_dec(x_45);
lean_dec(x_43);
lean_dec(x_29);
lean_dec(x_11);
x_308 = lean_ctor_get(x_292, 1);
lean_inc(x_308);
lean_dec(x_292);
x_309 = lean_ctor_get(x_293, 0);
lean_inc(x_309);
lean_dec(x_293);
x_4 = x_309;
x_9 = x_308;
goto _start;
}
}
else
{
uint8_t x_311; 
lean_dec(x_45);
lean_dec(x_43);
lean_dec(x_29);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_311 = !lean_is_exclusive(x_292);
if (x_311 == 0)
{
return x_292;
}
else
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; 
x_312 = lean_ctor_get(x_292, 0);
x_313 = lean_ctor_get(x_292, 1);
lean_inc(x_313);
lean_inc(x_312);
lean_dec(x_292);
x_314 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_314, 0, x_312);
lean_ctor_set(x_314, 1, x_313);
return x_314;
}
}
}
else
{
uint8_t x_315; lean_object* x_316; 
x_315 = lean_unbox(x_38);
lean_inc(x_34);
x_316 = l_Lean_ConstantInfo_value_x3f(x_34, x_315);
if (lean_obj_tag(x_316) == 0)
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; 
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_44);
lean_dec(x_37);
lean_dec(x_34);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_25);
lean_dec(x_1);
x_317 = lean_mk_string_unchecked("don't know how to generate ", 27, 27);
x_318 = l_Lean_stringToMessageData(x_317);
lean_dec(x_317);
x_319 = l_Lean_MessageData_ofName(x_45);
if (lean_is_scalar(x_43)) {
 x_320 = lean_alloc_ctor(7, 2, 0);
} else {
 x_320 = x_43;
 lean_ctor_set_tag(x_320, 7);
}
lean_ctor_set(x_320, 0, x_318);
lean_ctor_set(x_320, 1, x_319);
x_321 = lean_mk_string_unchecked(" for non-definition '", 21, 21);
x_322 = l_Lean_stringToMessageData(x_321);
lean_dec(x_321);
if (lean_is_scalar(x_29)) {
 x_323 = lean_alloc_ctor(7, 2, 0);
} else {
 x_323 = x_29;
 lean_ctor_set_tag(x_323, 7);
}
lean_ctor_set(x_323, 0, x_320);
lean_ctor_set(x_323, 1, x_322);
x_324 = l_Lean_MessageData_ofExpr(x_11);
x_325 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_325, 0, x_323);
lean_ctor_set(x_325, 1, x_324);
x_326 = lean_mk_string_unchecked("'", 1, 1);
x_327 = l_Lean_stringToMessageData(x_326);
lean_dec(x_326);
x_328 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_328, 0, x_325);
lean_ctor_set(x_328, 1, x_327);
x_329 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_328, x_5, x_6, x_7, x_8, x_42);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_329;
}
else
{
lean_object* x_330; lean_object* x_331; 
lean_dec(x_45);
x_330 = lean_ctor_get(x_316, 0);
lean_inc(x_330);
lean_dec(x_316);
x_331 = l_Lean_Environment_getModuleIdxFor_x3f(x_30, x_25);
lean_dec(x_30);
if (lean_obj_tag(x_331) == 0)
{
lean_dec(x_43);
lean_dec(x_29);
x_83 = x_330;
x_84 = x_5;
x_85 = x_6;
x_86 = x_7;
x_87 = x_8;
x_88 = x_42;
goto block_289;
}
else
{
lean_dec(x_331);
if (x_3 == 0)
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; uint8_t x_340; 
lean_dec(x_330);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_44);
lean_dec(x_37);
lean_dec(x_34);
lean_dec(x_31);
lean_dec(x_11);
lean_dec(x_1);
x_332 = lean_mk_string_unchecked("refusing to generate code for imported parser declaration '", 59, 59);
x_333 = l_Lean_stringToMessageData(x_332);
lean_dec(x_332);
x_334 = l_Lean_MessageData_ofName(x_25);
if (lean_is_scalar(x_43)) {
 x_335 = lean_alloc_ctor(7, 2, 0);
} else {
 x_335 = x_43;
 lean_ctor_set_tag(x_335, 7);
}
lean_ctor_set(x_335, 0, x_333);
lean_ctor_set(x_335, 1, x_334);
x_336 = lean_mk_string_unchecked("'; use `@[run_parser_attribute_hooks]` on its definition instead.", 65, 65);
x_337 = l_Lean_stringToMessageData(x_336);
lean_dec(x_336);
if (lean_is_scalar(x_29)) {
 x_338 = lean_alloc_ctor(7, 2, 0);
} else {
 x_338 = x_29;
 lean_ctor_set_tag(x_338, 7);
}
lean_ctor_set(x_338, 0, x_335);
lean_ctor_set(x_338, 1, x_337);
x_339 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_338, x_5, x_6, x_7, x_8, x_42);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_340 = !lean_is_exclusive(x_339);
if (x_340 == 0)
{
return x_339;
}
else
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; 
x_341 = lean_ctor_get(x_339, 0);
x_342 = lean_ctor_get(x_339, 1);
lean_inc(x_342);
lean_inc(x_341);
lean_dec(x_339);
x_343 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_343, 0, x_341);
lean_ctor_set(x_343, 1, x_342);
return x_343;
}
}
else
{
lean_dec(x_43);
lean_dec(x_29);
x_83 = x_330;
x_84 = x_5;
x_85 = x_6;
x_86 = x_7;
x_87 = x_8;
x_88 = x_42;
goto block_289;
}
}
}
}
}
}
else
{
lean_dec(x_37);
lean_dec(x_34);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_25);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_40;
}
}
else
{
uint8_t x_350; 
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_25);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_350 = !lean_is_exclusive(x_33);
if (x_350 == 0)
{
return x_33;
}
else
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; 
x_351 = lean_ctor_get(x_33, 0);
x_352 = lean_ctor_get(x_33, 1);
lean_inc(x_352);
lean_inc(x_351);
lean_dec(x_33);
x_353 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_353, 0, x_351);
lean_ctor_set(x_353, 1, x_352);
return x_353;
}
}
}
else
{
lean_object* x_354; lean_object* x_355; 
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_25);
x_354 = lean_ctor_get(x_32, 0);
lean_inc(x_354);
lean_dec(x_32);
x_355 = l_Lean_ParserCompiler_compileParserExpr___redArg___lam__2(x_11, x_1, x_2, x_3, x_354, x_5, x_6, x_7, x_8, x_28);
return x_355;
}
}
else
{
lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; 
lean_dec(x_24);
lean_dec(x_1);
x_356 = lean_mk_string_unchecked("call of unknown parser at '", 27, 27);
x_357 = l_Lean_stringToMessageData(x_356);
lean_dec(x_356);
x_358 = l_Lean_MessageData_ofExpr(x_11);
x_359 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_359, 0, x_357);
lean_ctor_set(x_359, 1, x_358);
x_360 = lean_mk_string_unchecked("'", 1, 1);
x_361 = l_Lean_stringToMessageData(x_360);
lean_dec(x_360);
x_362 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_362, 0, x_359);
lean_ctor_set(x_362, 1, x_361);
x_363 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_362, x_5, x_6, x_7, x_8, x_23);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_363;
}
}
}
}
else
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileParserExpr(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_ParserCompiler_compileParserExpr___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_ParserCompiler_compileParserExpr_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_foldrMUnsafe_fold___at___Lean_ParserCompiler_compileParserExpr_spec__0___redArg(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_ParserCompiler_compileParserExpr_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = l_Array_foldrMUnsafe_fold___at___Lean_ParserCompiler_compileParserExpr_spec__0(x_1, x_2, x_3, x_12, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_ParserCompiler_compileParserExpr_spec__1___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_Range_forIn_x27_loop___at___Lean_ParserCompiler_compileParserExpr_spec__1___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_ParserCompiler_compileParserExpr_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_unbox(x_4);
lean_dec(x_4);
x_15 = lean_unbox(x_5);
lean_dec(x_5);
x_16 = l_Std_Range_forIn_x27_loop___at___Lean_ParserCompiler_compileParserExpr_spec__1___redArg(x_1, x_2, x_3, x_14, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_ParserCompiler_compileParserExpr_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_17 = lean_unbox(x_5);
lean_dec(x_5);
x_18 = lean_unbox(x_6);
lean_dec(x_6);
x_19 = l_Std_Range_forIn_x27_loop___at___Lean_ParserCompiler_compileParserExpr_spec__1(x_1, x_2, x_3, x_4, x_17, x_18, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_2);
lean_dec(x_2);
x_12 = lean_unbox(x_3);
lean_dec(x_3);
x_13 = l_Lean_ParserCompiler_compileParserExpr___redArg___lam__0(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_unbox(x_5);
lean_dec(x_5);
x_15 = lean_unbox(x_6);
lean_dec(x_6);
x_16 = l_Lean_ParserCompiler_compileParserExpr___redArg___lam__1(x_1, x_2, x_3, x_4, x_14, x_15, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_8);
lean_dec(x_7);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_3);
lean_dec(x_3);
x_12 = lean_unbox(x_4);
lean_dec(x_4);
x_13 = l_Lean_ParserCompiler_compileParserExpr___redArg___lam__2(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_ParserCompiler_compileParserExpr___redArg___lam__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_2);
lean_dec(x_2);
x_11 = lean_unbox(x_3);
lean_dec(x_3);
x_12 = l_Lean_ParserCompiler_compileParserExpr___redArg(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileParserExpr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_3);
lean_dec(x_3);
x_12 = lean_unbox(x_4);
lean_dec(x_4);
x_13 = l_Lean_ParserCompiler_compileParserExpr(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileEmbeddedParsers___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
switch (lean_obj_tag(x_3)) {
case 1:
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_3, 1);
lean_inc(x_20);
lean_dec(x_3);
x_3 = x_20;
goto _start;
}
case 2:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_3, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_3, 2);
lean_inc(x_23);
lean_dec(x_3);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_24 = l_Lean_ParserCompiler_compileEmbeddedParsers___redArg(x_1, x_2, x_22, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_3 = x_23;
x_8 = x_25;
goto _start;
}
else
{
lean_dec(x_23);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_24;
}
}
case 3:
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_3, 2);
lean_inc(x_27);
lean_dec(x_3);
x_3 = x_27;
goto _start;
}
case 4:
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_3, 3);
lean_inc(x_29);
lean_dec(x_3);
x_3 = x_29;
goto _start;
}
case 8:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; 
x_31 = lean_ctor_get(x_3, 0);
lean_inc(x_31);
lean_dec(x_3);
x_32 = lean_box(0);
x_33 = lean_box(0);
x_34 = l_Lean_Expr_const___override(x_31, x_33);
x_35 = lean_unbox(x_32);
x_36 = l_Lean_ParserCompiler_compileParserExpr___redArg(x_1, x_2, x_35, x_34, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_36) == 0)
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_36, 0);
lean_dec(x_38);
x_39 = lean_box(0);
lean_ctor_set(x_36, 0, x_39);
return x_36;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_36, 1);
lean_inc(x_40);
lean_dec(x_36);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
return x_42;
}
}
else
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_36);
if (x_43 == 0)
{
return x_36;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_36, 0);
x_45 = lean_ctor_get(x_36, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_36);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
case 9:
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_3, 2);
lean_inc(x_47);
lean_dec(x_3);
x_3 = x_47;
goto _start;
}
case 10:
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_3, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_3, 2);
lean_inc(x_50);
lean_dec(x_3);
x_9 = x_49;
x_10 = x_50;
x_11 = x_4;
x_12 = x_5;
x_13 = x_6;
x_14 = x_7;
x_15 = x_8;
goto block_19;
}
case 11:
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_3, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_3, 2);
lean_inc(x_52);
lean_dec(x_3);
x_9 = x_51;
x_10 = x_52;
x_11 = x_4;
x_12 = x_5;
x_13 = x_6;
x_14 = x_7;
x_15 = x_8;
goto block_19;
}
default: 
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_53 = lean_box(0);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_8);
return x_54;
}
}
block_19:
{
lean_object* x_16; 
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_1);
x_16 = l_Lean_ParserCompiler_compileEmbeddedParsers___redArg(x_1, x_2, x_9, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_3 = x_10;
x_4 = x_11;
x_5 = x_12;
x_6 = x_13;
x_7 = x_14;
x_8 = x_17;
goto _start;
}
else
{
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_1);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileEmbeddedParsers(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_ParserCompiler_compileEmbeddedParsers___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileEmbeddedParsers___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_Lean_ParserCompiler_compileEmbeddedParsers___redArg(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileEmbeddedParsers___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = l_Lean_ParserCompiler_compileEmbeddedParsers(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; lean_object* x_82; 
lean_inc(x_3);
x_82 = l_Lean_getConstInfo___at_____private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0(x_3, x_5, x_6, x_7);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; uint8_t x_90; lean_object* x_95; lean_object* x_96; uint8_t x_97; uint8_t x_183; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_85 = l_Lean_ConstantInfo_type(x_83);
lean_dec(x_83);
x_86 = lean_mk_string_unchecked("Lean", 4, 4);
x_95 = lean_mk_string_unchecked("ParserDescr", 11, 11);
lean_inc(x_86);
x_96 = l_Lean_Name_mkStr2(x_86, x_95);
x_183 = l_Lean_Expr_isConstOf(x_85, x_96);
if (x_183 == 0)
{
lean_object* x_184; lean_object* x_185; uint8_t x_186; 
x_184 = lean_mk_string_unchecked("TrailingParserDescr", 19, 19);
lean_inc(x_86);
x_185 = l_Lean_Name_mkStr2(x_86, x_184);
x_186 = l_Lean_Expr_isConstOf(x_85, x_185);
lean_dec(x_185);
lean_dec(x_85);
x_97 = x_186;
goto block_182;
}
else
{
lean_dec(x_85);
x_97 = x_183;
goto block_182;
}
block_94:
{
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_87);
x_91 = lean_mk_string_unchecked("TrailingParserDescr", 19, 19);
x_92 = l_Lean_Name_mkStr2(x_86, x_91);
x_93 = l_Lean_evalConstCheck___at___Lean_KeyedDeclsAttribute_init_spec__0(lean_box(0), x_92, x_3, x_5, x_6, x_88);
x_8 = x_89;
x_9 = x_93;
goto block_81;
}
else
{
lean_dec(x_88);
lean_dec(x_86);
lean_dec(x_3);
x_8 = x_89;
x_9 = x_87;
goto block_81;
}
}
block_182:
{
lean_object* x_98; 
x_98 = lean_box(1);
if (x_97 == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; size_t x_103; lean_object* x_104; lean_object* x_105; size_t x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; uint8_t x_139; uint8_t x_140; uint8_t x_141; uint8_t x_142; uint8_t x_143; uint8_t x_144; uint8_t x_145; uint8_t x_146; uint8_t x_147; uint8_t x_148; uint8_t x_149; uint64_t x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; uint8_t x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
lean_dec(x_96);
lean_dec(x_86);
x_99 = lean_box(0);
x_100 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_101 = lean_unsigned_to_nat(2u);
x_102 = lean_unsigned_to_nat(5u);
x_103 = lean_usize_of_nat(x_102);
x_104 = lean_usize_to_nat(x_103);
x_105 = lean_nat_pow(x_101, x_104);
lean_dec(x_104);
x_106 = lean_usize_of_nat(x_105);
lean_dec(x_105);
x_107 = lean_usize_to_nat(x_106);
x_108 = lean_mk_empty_array_with_capacity(x_107);
lean_dec(x_107);
lean_inc(x_108);
x_109 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_109, 0, x_108);
x_110 = lean_unsigned_to_nat(0u);
lean_inc(x_100);
x_111 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_111, 0, x_100);
lean_inc(x_100);
x_112 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_112, 0, x_100);
lean_inc(x_100);
x_113 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_113, 0, x_100);
lean_inc(x_100);
x_114 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_114, 0, x_100);
lean_inc(x_100);
x_115 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_115, 0, x_100);
lean_inc(x_100);
x_116 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_116, 0, x_100);
lean_inc(x_111);
x_117 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_117, 0, x_110);
lean_ctor_set(x_117, 1, x_110);
lean_ctor_set(x_117, 2, x_110);
lean_ctor_set(x_117, 3, x_111);
lean_ctor_set(x_117, 4, x_112);
lean_ctor_set(x_117, 5, x_113);
lean_ctor_set(x_117, 6, x_114);
lean_ctor_set(x_117, 7, x_115);
lean_ctor_set(x_117, 8, x_116);
lean_inc(x_100);
x_118 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_118, 0, x_100);
lean_inc(x_100);
x_119 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_119, 0, x_100);
lean_inc(x_100);
x_120 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_120, 0, x_100);
lean_inc(x_100);
x_121 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_121, 0, x_100);
lean_inc(x_121);
lean_inc(x_118);
x_122 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_122, 0, x_118);
lean_ctor_set(x_122, 1, x_119);
lean_ctor_set(x_122, 2, x_120);
lean_ctor_set(x_122, 3, x_118);
lean_ctor_set(x_122, 4, x_121);
lean_ctor_set(x_122, 5, x_121);
lean_inc(x_108);
x_123 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_123, 0, x_108);
lean_inc(x_108);
x_124 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_108);
lean_ctor_set(x_124, 2, x_110);
lean_ctor_set(x_124, 3, x_110);
lean_ctor_set_usize(x_124, 4, x_103);
lean_inc(x_100);
x_125 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_125, 0, x_100);
lean_inc_n(x_111, 2);
x_126 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_126, 0, x_111);
lean_ctor_set(x_126, 1, x_111);
lean_ctor_set(x_126, 2, x_111);
lean_ctor_set(x_126, 3, x_125);
x_127 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_127, 0, x_117);
lean_ctor_set(x_127, 1, x_122);
lean_ctor_set(x_127, 2, x_99);
lean_ctor_set(x_127, 3, x_124);
lean_ctor_set(x_127, 4, x_126);
x_128 = lean_st_mk_ref(x_127, x_84);
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_128, 1);
lean_inc(x_130);
lean_dec(x_128);
x_131 = lean_box(1);
x_132 = lean_box(0);
x_133 = lean_box(2);
x_134 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_134, 0, x_100);
x_135 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_135, 0, x_109);
lean_ctor_set(x_135, 1, x_108);
lean_ctor_set(x_135, 2, x_110);
lean_ctor_set(x_135, 3, x_110);
lean_ctor_set_usize(x_135, 4, x_103);
x_136 = lean_box(0);
x_137 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_137, 0, x_97);
lean_ctor_set_uint8(x_137, 1, x_97);
lean_ctor_set_uint8(x_137, 2, x_97);
lean_ctor_set_uint8(x_137, 3, x_97);
lean_ctor_set_uint8(x_137, 4, x_97);
x_138 = lean_unbox(x_98);
lean_ctor_set_uint8(x_137, 5, x_138);
x_139 = lean_unbox(x_98);
lean_ctor_set_uint8(x_137, 6, x_139);
lean_ctor_set_uint8(x_137, 7, x_97);
x_140 = lean_unbox(x_98);
lean_ctor_set_uint8(x_137, 8, x_140);
x_141 = lean_unbox(x_131);
lean_ctor_set_uint8(x_137, 9, x_141);
x_142 = lean_unbox(x_132);
lean_ctor_set_uint8(x_137, 10, x_142);
x_143 = lean_unbox(x_98);
lean_ctor_set_uint8(x_137, 11, x_143);
x_144 = lean_unbox(x_98);
lean_ctor_set_uint8(x_137, 12, x_144);
x_145 = lean_unbox(x_98);
lean_ctor_set_uint8(x_137, 13, x_145);
x_146 = lean_unbox(x_133);
lean_ctor_set_uint8(x_137, 14, x_146);
x_147 = lean_unbox(x_98);
lean_ctor_set_uint8(x_137, 15, x_147);
x_148 = lean_unbox(x_98);
lean_ctor_set_uint8(x_137, 16, x_148);
x_149 = lean_unbox(x_98);
lean_ctor_set_uint8(x_137, 17, x_149);
x_150 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_137);
x_151 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_151, 0, x_134);
lean_ctor_set(x_151, 1, x_135);
lean_ctor_set(x_151, 2, x_99);
x_152 = lean_mk_empty_array_with_capacity(x_110);
x_153 = lean_box(0);
x_154 = lean_box(0);
x_155 = l_Lean_Name_isAnonymous(x_2);
x_156 = l_Lean_Expr_const___override(x_3, x_136);
x_157 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_157, 0, x_137);
lean_ctor_set(x_157, 1, x_99);
lean_ctor_set(x_157, 2, x_151);
lean_ctor_set(x_157, 3, x_152);
lean_ctor_set(x_157, 4, x_153);
lean_ctor_set(x_157, 5, x_110);
lean_ctor_set(x_157, 6, x_154);
lean_ctor_set_uint64(x_157, sizeof(void*)*7, x_150);
lean_ctor_set_uint8(x_157, sizeof(void*)*7 + 8, x_97);
lean_ctor_set_uint8(x_157, sizeof(void*)*7 + 9, x_97);
lean_ctor_set_uint8(x_157, sizeof(void*)*7 + 10, x_97);
x_158 = lean_box(0);
lean_inc(x_129);
x_159 = l_Lean_ParserCompiler_compileParserExpr___redArg(x_1, x_4, x_155, x_156, x_157, x_129, x_5, x_6, x_130);
if (lean_obj_tag(x_159) == 0)
{
lean_object* x_160; lean_object* x_161; uint8_t x_162; 
x_160 = lean_ctor_get(x_159, 1);
lean_inc(x_160);
lean_dec(x_159);
x_161 = lean_st_ref_get(x_129, x_160);
lean_dec(x_129);
x_162 = !lean_is_exclusive(x_161);
if (x_162 == 0)
{
lean_object* x_163; 
x_163 = lean_ctor_get(x_161, 0);
lean_dec(x_163);
lean_ctor_set(x_161, 0, x_158);
return x_161;
}
else
{
lean_object* x_164; lean_object* x_165; 
x_164 = lean_ctor_get(x_161, 1);
lean_inc(x_164);
lean_dec(x_161);
x_165 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_165, 0, x_158);
lean_ctor_set(x_165, 1, x_164);
return x_165;
}
}
else
{
lean_dec(x_129);
if (lean_obj_tag(x_159) == 0)
{
uint8_t x_166; 
x_166 = !lean_is_exclusive(x_159);
if (x_166 == 0)
{
lean_object* x_167; 
x_167 = lean_ctor_get(x_159, 0);
lean_dec(x_167);
lean_ctor_set_tag(x_159, 0);
lean_ctor_set(x_159, 0, x_158);
return x_159;
}
else
{
lean_object* x_168; lean_object* x_169; 
x_168 = lean_ctor_get(x_159, 1);
lean_inc(x_168);
lean_dec(x_159);
x_169 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_169, 0, x_158);
lean_ctor_set(x_169, 1, x_168);
return x_169;
}
}
else
{
uint8_t x_170; 
x_170 = !lean_is_exclusive(x_159);
if (x_170 == 0)
{
return x_159;
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_171 = lean_ctor_get(x_159, 0);
x_172 = lean_ctor_get(x_159, 1);
lean_inc(x_172);
lean_inc(x_171);
lean_dec(x_159);
x_173 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_173, 0, x_171);
lean_ctor_set(x_173, 1, x_172);
return x_173;
}
}
}
}
else
{
lean_object* x_174; 
lean_inc(x_3);
x_174 = l_Lean_evalConstCheck___at___Lean_KeyedDeclsAttribute_init_spec__0(lean_box(0), x_96, x_3, x_5, x_6, x_84);
if (lean_obj_tag(x_174) == 0)
{
uint8_t x_175; 
lean_dec(x_86);
lean_dec(x_3);
x_175 = lean_unbox(x_98);
x_8 = x_175;
x_9 = x_174;
goto block_81;
}
else
{
lean_object* x_176; lean_object* x_177; uint8_t x_178; 
x_176 = lean_ctor_get(x_174, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_174, 1);
lean_inc(x_177);
x_178 = l_Lean_Exception_isInterrupt(x_176);
if (x_178 == 0)
{
uint8_t x_179; uint8_t x_180; 
x_179 = l_Lean_Exception_isRuntime(x_176);
lean_dec(x_176);
x_180 = lean_unbox(x_98);
x_87 = x_174;
x_88 = x_177;
x_89 = x_180;
x_90 = x_179;
goto block_94;
}
else
{
uint8_t x_181; 
lean_dec(x_176);
x_181 = lean_unbox(x_98);
x_87 = x_174;
x_88 = x_177;
x_89 = x_181;
x_90 = x_178;
goto block_94;
}
}
}
}
}
else
{
uint8_t x_187; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_187 = !lean_is_exclusive(x_82);
if (x_187 == 0)
{
return x_82;
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_188 = lean_ctor_get(x_82, 0);
x_189 = lean_ctor_get(x_82, 1);
lean_inc(x_189);
lean_inc(x_188);
lean_dec(x_82);
x_190 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_190, 0, x_188);
lean_ctor_set(x_190, 1, x_189);
return x_190;
}
}
block_81:
{
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; lean_object* x_16; lean_object* x_17; size_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; uint8_t x_52; uint8_t x_53; uint8_t x_54; uint8_t x_55; uint8_t x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; uint64_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; uint8_t x_67; uint8_t x_68; lean_object* x_69; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_box(0);
x_13 = lean_unsigned_to_nat(2u);
x_14 = lean_unsigned_to_nat(5u);
x_15 = lean_usize_of_nat(x_14);
x_16 = lean_usize_to_nat(x_15);
x_17 = lean_nat_pow(x_13, x_16);
lean_dec(x_16);
x_18 = lean_usize_of_nat(x_17);
lean_dec(x_17);
x_19 = lean_usize_to_nat(x_18);
x_20 = lean_mk_empty_array_with_capacity(x_19);
lean_dec(x_19);
x_21 = lean_unsigned_to_nat(0u);
x_22 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_22);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_22);
lean_inc(x_22);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_22);
lean_inc(x_22);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_22);
lean_inc(x_22);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_22);
lean_inc(x_22);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_22);
lean_inc(x_22);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_22);
lean_inc(x_23);
x_29 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_29, 0, x_21);
lean_ctor_set(x_29, 1, x_21);
lean_ctor_set(x_29, 2, x_21);
lean_ctor_set(x_29, 3, x_23);
lean_ctor_set(x_29, 4, x_24);
lean_ctor_set(x_29, 5, x_25);
lean_ctor_set(x_29, 6, x_26);
lean_ctor_set(x_29, 7, x_27);
lean_ctor_set(x_29, 8, x_28);
lean_inc(x_22);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_22);
lean_inc(x_22);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_22);
lean_inc(x_22);
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_22);
lean_inc(x_22);
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_22);
lean_inc(x_33);
lean_inc(x_30);
x_34 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_34, 0, x_30);
lean_ctor_set(x_34, 1, x_31);
lean_ctor_set(x_34, 2, x_32);
lean_ctor_set(x_34, 3, x_30);
lean_ctor_set(x_34, 4, x_33);
lean_ctor_set(x_34, 5, x_33);
lean_inc(x_20);
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_20);
lean_inc(x_20);
x_36 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_20);
lean_ctor_set(x_36, 2, x_21);
lean_ctor_set(x_36, 3, x_21);
lean_ctor_set_usize(x_36, 4, x_15);
lean_inc(x_22);
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_22);
lean_inc_n(x_23, 2);
x_38 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_38, 0, x_23);
lean_ctor_set(x_38, 1, x_23);
lean_ctor_set(x_38, 2, x_23);
lean_ctor_set(x_38, 3, x_37);
x_39 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_39, 0, x_29);
lean_ctor_set(x_39, 1, x_34);
lean_ctor_set(x_39, 2, x_12);
lean_ctor_set(x_39, 3, x_36);
lean_ctor_set(x_39, 4, x_38);
x_40 = lean_st_mk_ref(x_39, x_11);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
lean_inc(x_20);
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_20);
x_44 = lean_box(1);
x_45 = lean_box(0);
x_46 = lean_box(2);
x_47 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_47, 0, x_22);
x_48 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_48, 0, x_43);
lean_ctor_set(x_48, 1, x_20);
lean_ctor_set(x_48, 2, x_21);
lean_ctor_set(x_48, 3, x_21);
lean_ctor_set_usize(x_48, 4, x_15);
x_49 = lean_box(0);
x_50 = lean_alloc_ctor(0, 0, 18);
x_51 = lean_unbox(x_49);
lean_ctor_set_uint8(x_50, 0, x_51);
x_52 = lean_unbox(x_49);
lean_ctor_set_uint8(x_50, 1, x_52);
x_53 = lean_unbox(x_49);
lean_ctor_set_uint8(x_50, 2, x_53);
x_54 = lean_unbox(x_49);
lean_ctor_set_uint8(x_50, 3, x_54);
x_55 = lean_unbox(x_49);
lean_ctor_set_uint8(x_50, 4, x_55);
lean_ctor_set_uint8(x_50, 5, x_8);
lean_ctor_set_uint8(x_50, 6, x_8);
x_56 = lean_unbox(x_49);
lean_ctor_set_uint8(x_50, 7, x_56);
lean_ctor_set_uint8(x_50, 8, x_8);
x_57 = lean_unbox(x_44);
lean_ctor_set_uint8(x_50, 9, x_57);
x_58 = lean_unbox(x_45);
lean_ctor_set_uint8(x_50, 10, x_58);
lean_ctor_set_uint8(x_50, 11, x_8);
lean_ctor_set_uint8(x_50, 12, x_8);
lean_ctor_set_uint8(x_50, 13, x_8);
x_59 = lean_unbox(x_46);
lean_ctor_set_uint8(x_50, 14, x_59);
lean_ctor_set_uint8(x_50, 15, x_8);
lean_ctor_set_uint8(x_50, 16, x_8);
lean_ctor_set_uint8(x_50, 17, x_8);
x_60 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_50);
x_61 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_61, 0, x_47);
lean_ctor_set(x_61, 1, x_48);
lean_ctor_set(x_61, 2, x_12);
x_62 = lean_mk_empty_array_with_capacity(x_21);
x_63 = lean_box(0);
x_64 = lean_box(0);
x_65 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_65, 0, x_50);
lean_ctor_set(x_65, 1, x_12);
lean_ctor_set(x_65, 2, x_61);
lean_ctor_set(x_65, 3, x_62);
lean_ctor_set(x_65, 4, x_63);
lean_ctor_set(x_65, 5, x_21);
lean_ctor_set(x_65, 6, x_64);
lean_ctor_set_uint64(x_65, sizeof(void*)*7, x_60);
x_66 = lean_unbox(x_49);
lean_ctor_set_uint8(x_65, sizeof(void*)*7 + 8, x_66);
x_67 = lean_unbox(x_49);
lean_ctor_set_uint8(x_65, sizeof(void*)*7 + 9, x_67);
x_68 = lean_unbox(x_49);
lean_ctor_set_uint8(x_65, sizeof(void*)*7 + 10, x_68);
lean_inc(x_41);
x_69 = l_Lean_ParserCompiler_compileEmbeddedParsers___redArg(x_1, x_4, x_10, x_65, x_41, x_5, x_6, x_42);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = lean_st_ref_get(x_41, x_71);
lean_dec(x_41);
x_73 = !lean_is_exclusive(x_72);
if (x_73 == 0)
{
lean_object* x_74; 
x_74 = lean_ctor_get(x_72, 0);
lean_dec(x_74);
lean_ctor_set(x_72, 0, x_70);
return x_72;
}
else
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_72, 1);
lean_inc(x_75);
lean_dec(x_72);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_70);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
else
{
lean_dec(x_41);
return x_69;
}
}
else
{
uint8_t x_77; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_77 = !lean_is_exclusive(x_9);
if (x_77 == 0)
{
return x_9;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_9, 0);
x_79 = lean_ctor_get(x_9, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_9);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_registerParserCompiler___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___boxed), 7, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = l_Lean_Parser_registerParserAttributeHook(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_registerParserCompiler(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_ParserCompiler_registerParserCompiler___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_4);
lean_dec(x_4);
x_9 = l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0(x_1, x_2, x_3, x_8, x_5, x_6, x_7);
lean_dec(x_2);
return x_9;
}
}
lean_object* initialize_Lean_Meta_ReduceEval(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_WHNF(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_KeyedDeclsAttribute(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_ParserCompiler_Attribute(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Parser_Extension(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_ParserCompiler(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_ReduceEval(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_WHNF(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_KeyedDeclsAttribute(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ParserCompiler_Attribute(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Extension(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
