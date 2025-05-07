// Lean compiler output
// Module: Lake.DSL.DeclUtil
// Imports: Lake.Util.Binder Lake.Util.Name Lake.Config.Meta Lean.Parser.Command Lean.Elab.Command
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
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___Lean_Elab_Term_mkFreshIdent___at___Lake_DSL_mkConfigDeclIdent_spec__0_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_simpleDeclSig;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_declValStruct;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___Lean_Elab_Term_mkFreshIdent___at___Lake_DSL_mkConfigDeclIdent_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lake_DSL_mkConfigFields_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getHeadInfo(lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_elabConfig___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getString(lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___Lake_DSL_mkConfigFields_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_simpleBinder;
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM___at___Lake_DSL_mkConfigFields_spec__3___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_optConfig;
lean_object* l_instMonadEIO___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabCommand(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___Lake_DSL_mkConfigFields_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_expandOptSimpleBinder___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_identOrStr;
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*, uint8_t);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lake_DSL_mkConfigFields_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_elabConfig___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_NameMap_find_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Lean_throwErrorAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_bracketedSimpleBinder;
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_declValWhere;
LEAN_EXPORT lean_object* l_Lake_DSL_mkConfigFields___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_elabConfig___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshIdent___at___Lake_DSL_mkConfigDeclIdent_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
lean_object* l_Lean_Elab_Command_getRef(lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
lean_object* l_Lean_Syntax_TSepArray_getElems___redArg(lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkSep(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_elabConfig___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getCurrMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_instMonadExceptOfExceptionCommandElabM;
lean_object* l_Lean_mkOptionalNode(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_packageDeclName;
LEAN_EXPORT lean_object* l_Lake_DSL_mkConfigDeclIdent___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_expandIdentOrStrAsIdent(lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_elabConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_structVal;
lean_object* lean_usize_to_nat(size_t);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_DSL_declValDo;
lean_object* l_Lean_Elab_addCompletionInfo___at___Lean_Elab_elabSetOption___at___Lean_withSetOptionIn_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___Lean_Elab_Term_mkFreshIdent___at___Lake_DSL_mkConfigDeclIdent_spec__0_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshIdent___at___Lake_DSL_mkConfigDeclIdent_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_declField;
lean_object* l_Lean_Elab_Command_withFreshMacroScope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_expandAttrs(lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_elabConfig___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lake_DSL_mkConfigFields_spec__1_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Lean_logAt___at___Lean_logErrorAt___at___Lean_Elab_logException___at___Lean_Elab_Command_runLinters_spec__0_spec__0_spec__0(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_instAddErrorMessageContextCommandElabM;
lean_object* l_Lean_Elab_Command_getMainModule___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_mkConfigFields(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___Lean_Elab_Term_mkFreshIdent___at___Lake_DSL_mkConfigDeclIdent_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_seqRight(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM___at___Lake_DSL_mkConfigFields_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_instMonadRefCommandElabM;
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM___at___Lake_DSL_mkConfigFields_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_withMacroExpansion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
uint8_t l_Lean_NameMap_contains(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lake_DSL_mkConfigFields_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_expandOptSimpleBinder(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_mkConfigDeclIdent(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_elabConfig___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lake_DSL_packageDeclName() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_mk_string_unchecked("_package", 8, 8);
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_expandAttrs(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_mk_empty_array_with_capacity(x_2);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_mk_string_unchecked("Lean", 4, 4);
x_6 = lean_mk_string_unchecked("Parser", 6, 6);
x_7 = lean_mk_string_unchecked("Term", 4, 4);
x_8 = lean_mk_string_unchecked("attributes", 10, 10);
x_9 = l_Lean_Name_mkStr4(x_5, x_6, x_7, x_8);
lean_inc(x_4);
x_10 = l_Lean_Syntax_isOfKind(x_4, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_4);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_mk_empty_array_with_capacity(x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = l_Lean_Syntax_getArg(x_4, x_13);
lean_dec(x_4);
x_15 = l_Lean_Syntax_getArgs(x_14);
lean_dec(x_14);
x_16 = l_Lean_Syntax_TSepArray_getElems___redArg(x_15);
lean_dec(x_15);
return x_16;
}
}
}
}
static lean_object* _init_l_Lake_DSL_identOrStr() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_1 = lean_mk_string_unchecked("identOrStr", 10, 10);
x_2 = lean_mk_string_unchecked("Lake", 4, 4);
x_3 = lean_mk_string_unchecked("DSL", 3, 3);
lean_inc(x_1);
x_4 = l_Lean_Name_mkStr3(x_2, x_3, x_1);
x_5 = lean_mk_string_unchecked("orelse", 6, 6);
x_6 = l_Lean_Name_mkStr1(x_5);
x_7 = lean_mk_string_unchecked("ident", 5, 5);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_mk_string_unchecked("str", 3, 3);
x_11 = l_Lean_Name_mkStr1(x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_9);
lean_ctor_set(x_13, 2, x_12);
x_14 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_4);
lean_ctor_set(x_14, 2, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_expandIdentOrStrAsIdent(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_2 = lean_mk_string_unchecked("Lake", 4, 4);
x_3 = lean_mk_string_unchecked("DSL", 3, 3);
x_4 = lean_mk_string_unchecked("identOrStr", 10, 10);
x_5 = l_Lean_Name_mkStr3(x_2, x_3, x_4);
lean_inc(x_1);
x_6 = l_Lean_Syntax_isOfKind(x_1, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; 
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
x_10 = lean_mk_string_unchecked("ident", 5, 5);
x_11 = l_Lean_Name_mkStr1(x_10);
lean_inc(x_9);
x_12 = l_Lean_Syntax_isOfKind(x_9, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_mk_string_unchecked("str", 3, 3);
x_14 = l_Lean_Name_mkStr1(x_13);
lean_inc(x_9);
x_15 = l_Lean_Syntax_isOfKind(x_9, x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_9);
x_16 = lean_box(0);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = l_Lean_TSyntax_getString(x_9);
x_18 = lean_box(0);
x_19 = l_Lean_Name_str___override(x_18, x_17);
x_20 = l_Lean_mkIdentFrom(x_9, x_19, x_12);
lean_dec(x_9);
return x_20;
}
}
else
{
return x_9;
}
}
}
}
static lean_object* _init_l_Lake_DSL_declField() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_1 = lean_mk_string_unchecked("declField", 9, 9);
x_2 = lean_mk_string_unchecked("Lake", 4, 4);
x_3 = lean_mk_string_unchecked("DSL", 3, 3);
lean_inc(x_1);
x_4 = l_Lean_Name_mkStr3(x_2, x_3, x_1);
x_5 = lean_mk_string_unchecked("andthen", 7, 7);
x_6 = l_Lean_Name_mkStr1(x_5);
x_7 = lean_mk_string_unchecked("ident", 5, 5);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_mk_string_unchecked(" := ", 4, 4);
x_11 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_11, 0, x_10);
lean_inc(x_6);
x_12 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_12, 0, x_6);
lean_ctor_set(x_12, 1, x_9);
lean_ctor_set(x_12, 2, x_11);
x_13 = lean_mk_string_unchecked("term", 4, 4);
x_14 = l_Lean_Name_mkStr1(x_13);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_17, 0, x_6);
lean_ctor_set(x_17, 1, x_12);
lean_ctor_set(x_17, 2, x_16);
x_18 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_4);
lean_ctor_set(x_18, 2, x_17);
return x_18;
}
}
static lean_object* _init_l_Lake_DSL_structVal() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_1 = lean_mk_string_unchecked("structVal", 9, 9);
x_2 = lean_mk_string_unchecked("Lake", 4, 4);
x_3 = lean_mk_string_unchecked("DSL", 3, 3);
lean_inc(x_1);
x_4 = l_Lean_Name_mkStr3(x_2, x_3, x_1);
x_5 = lean_mk_string_unchecked("andthen", 7, 7);
x_6 = l_Lean_Name_mkStr1(x_5);
x_7 = lean_mk_string_unchecked("{", 1, 1);
x_8 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_mk_string_unchecked("structInstFields", 16, 16);
x_10 = l_Lean_Name_mkStr1(x_9);
x_11 = lean_mk_string_unchecked("sepByIndentSemicolon", 20, 20);
x_12 = l_Lean_Name_mkStr1(x_11);
x_13 = l_Lake_DSL_declField;
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_14);
lean_inc(x_6);
x_16 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_16, 0, x_6);
lean_ctor_set(x_16, 1, x_8);
lean_ctor_set(x_16, 2, x_15);
x_17 = lean_mk_string_unchecked("}", 1, 1);
x_18 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_19, 0, x_6);
lean_ctor_set(x_19, 1, x_16);
lean_ctor_set(x_19, 2, x_18);
x_20 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_4);
lean_ctor_set(x_20, 2, x_19);
return x_20;
}
}
static lean_object* _init_l_Lake_DSL_declValDo() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_1 = lean_mk_string_unchecked("declValDo", 9, 9);
x_2 = lean_mk_string_unchecked("Lake", 4, 4);
x_3 = lean_mk_string_unchecked("DSL", 3, 3);
lean_inc(x_1);
x_4 = l_Lean_Name_mkStr3(x_2, x_3, x_1);
x_5 = lean_mk_string_unchecked("andthen", 7, 7);
x_6 = l_Lean_Name_mkStr1(x_5);
x_7 = lean_mk_string_unchecked("ppSpace", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_mk_string_unchecked("Lean", 4, 4);
x_11 = lean_mk_string_unchecked("Parser", 6, 6);
x_12 = lean_mk_string_unchecked("Term", 4, 4);
x_13 = lean_mk_string_unchecked("do", 2, 2);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_14 = l_Lean_Name_mkStr4(x_10, x_11, x_12, x_13);
x_15 = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(x_15, 0, x_14);
lean_inc(x_6);
x_16 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_16, 0, x_6);
lean_ctor_set(x_16, 1, x_9);
lean_ctor_set(x_16, 2, x_15);
x_17 = lean_mk_string_unchecked("optional", 8, 8);
x_18 = l_Lean_Name_mkStr1(x_17);
x_19 = lean_mk_string_unchecked("whereDecls", 10, 10);
x_20 = l_Lean_Name_mkStr4(x_10, x_11, x_12, x_19);
x_21 = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_18);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_23, 0, x_6);
lean_ctor_set(x_23, 1, x_16);
lean_ctor_set(x_23, 2, x_22);
x_24 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_24, 0, x_1);
lean_ctor_set(x_24, 1, x_4);
lean_ctor_set(x_24, 2, x_23);
return x_24;
}
}
static lean_object* _init_l_Lake_DSL_declValStruct() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_1 = lean_mk_string_unchecked("declValStruct", 13, 13);
x_2 = lean_mk_string_unchecked("Lake", 4, 4);
x_3 = lean_mk_string_unchecked("DSL", 3, 3);
lean_inc(x_1);
x_4 = l_Lean_Name_mkStr3(x_2, x_3, x_1);
x_5 = lean_mk_string_unchecked("andthen", 7, 7);
x_6 = l_Lean_Name_mkStr1(x_5);
x_7 = lean_mk_string_unchecked("ppSpace", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = l_Lake_DSL_structVal;
lean_inc(x_6);
x_11 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_9);
lean_ctor_set(x_11, 2, x_10);
x_12 = lean_mk_string_unchecked("optional", 8, 8);
x_13 = l_Lean_Name_mkStr1(x_12);
x_14 = lean_mk_string_unchecked("Lean", 4, 4);
x_15 = lean_mk_string_unchecked("Parser", 6, 6);
x_16 = lean_mk_string_unchecked("Term", 4, 4);
x_17 = lean_mk_string_unchecked("whereDecls", 10, 10);
x_18 = l_Lean_Name_mkStr4(x_14, x_15, x_16, x_17);
x_19 = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_13);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_21, 0, x_6);
lean_ctor_set(x_21, 1, x_11);
lean_ctor_set(x_21, 2, x_20);
x_22 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_22, 0, x_1);
lean_ctor_set(x_22, 1, x_4);
lean_ctor_set(x_22, 2, x_21);
return x_22;
}
}
static lean_object* _init_l_Lake_DSL_declValWhere() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_1 = lean_mk_string_unchecked("declValWhere", 12, 12);
x_2 = lean_mk_string_unchecked("Lake", 4, 4);
x_3 = lean_mk_string_unchecked("DSL", 3, 3);
lean_inc(x_1);
x_4 = l_Lean_Name_mkStr3(x_2, x_3, x_1);
x_5 = lean_mk_string_unchecked("andthen", 7, 7);
x_6 = l_Lean_Name_mkStr1(x_5);
x_7 = lean_mk_string_unchecked(" where ", 7, 7);
x_8 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_mk_string_unchecked("structInstFields", 16, 16);
x_10 = l_Lean_Name_mkStr1(x_9);
x_11 = lean_mk_string_unchecked("sepByIndentSemicolon", 20, 20);
x_12 = l_Lean_Name_mkStr1(x_11);
x_13 = l_Lake_DSL_declField;
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_14);
lean_inc(x_6);
x_16 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_16, 0, x_6);
lean_ctor_set(x_16, 1, x_8);
lean_ctor_set(x_16, 2, x_15);
x_17 = lean_mk_string_unchecked("optional", 8, 8);
x_18 = l_Lean_Name_mkStr1(x_17);
x_19 = lean_mk_string_unchecked("Lean", 4, 4);
x_20 = lean_mk_string_unchecked("Parser", 6, 6);
x_21 = lean_mk_string_unchecked("Term", 4, 4);
x_22 = lean_mk_string_unchecked("whereDecls", 10, 10);
x_23 = l_Lean_Name_mkStr4(x_19, x_20, x_21, x_22);
x_24 = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_18);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_26, 0, x_6);
lean_ctor_set(x_26, 1, x_16);
lean_ctor_set(x_26, 2, x_25);
x_27 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_27, 0, x_1);
lean_ctor_set(x_27, 1, x_4);
lean_ctor_set(x_27, 2, x_26);
return x_27;
}
}
static lean_object* _init_l_Lake_DSL_simpleDeclSig() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_1 = lean_mk_string_unchecked("simpleDeclSig", 13, 13);
x_2 = lean_mk_string_unchecked("Lake", 4, 4);
x_3 = lean_mk_string_unchecked("DSL", 3, 3);
lean_inc(x_1);
x_4 = l_Lean_Name_mkStr3(x_2, x_3, x_1);
x_5 = lean_mk_string_unchecked("andthen", 7, 7);
x_6 = l_Lean_Name_mkStr1(x_5);
x_7 = lean_mk_string_unchecked("ident", 5, 5);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_mk_string_unchecked("Lean", 4, 4);
x_11 = lean_mk_string_unchecked("Parser", 6, 6);
x_12 = lean_mk_string_unchecked("Term", 4, 4);
x_13 = lean_mk_string_unchecked("typeSpec", 8, 8);
lean_inc(x_11);
lean_inc(x_10);
x_14 = l_Lean_Name_mkStr4(x_10, x_11, x_12, x_13);
x_15 = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(x_15, 0, x_14);
lean_inc(x_6);
x_16 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_16, 0, x_6);
lean_ctor_set(x_16, 1, x_9);
lean_ctor_set(x_16, 2, x_15);
x_17 = lean_mk_string_unchecked("Command", 7, 7);
x_18 = lean_mk_string_unchecked("declValSimple", 13, 13);
x_19 = l_Lean_Name_mkStr4(x_10, x_11, x_17, x_18);
x_20 = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_21, 0, x_6);
lean_ctor_set(x_21, 1, x_16);
lean_ctor_set(x_21, 2, x_20);
x_22 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_22, 0, x_1);
lean_ctor_set(x_22, 1, x_4);
lean_ctor_set(x_22, 2, x_21);
return x_22;
}
}
static lean_object* _init_l_Lake_DSL_optConfig() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_1 = lean_mk_string_unchecked("optConfig", 9, 9);
x_2 = lean_mk_string_unchecked("Lake", 4, 4);
x_3 = lean_mk_string_unchecked("DSL", 3, 3);
lean_inc(x_1);
x_4 = l_Lean_Name_mkStr3(x_2, x_3, x_1);
x_5 = lean_mk_string_unchecked("optional", 8, 8);
x_6 = l_Lean_Name_mkStr1(x_5);
x_7 = lean_mk_string_unchecked("orelse", 6, 6);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = l_Lake_DSL_declValWhere;
x_10 = l_Lake_DSL_declValStruct;
x_11 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_9);
lean_ctor_set(x_11, 2, x_10);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_6);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_4);
lean_ctor_set(x_13, 2, x_12);
return x_13;
}
}
static lean_object* _init_l_Lake_DSL_bracketedSimpleBinder() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_1 = lean_mk_string_unchecked("bracketedSimpleBinder", 21, 21);
x_2 = lean_mk_string_unchecked("Lake", 4, 4);
x_3 = lean_mk_string_unchecked("DSL", 3, 3);
lean_inc(x_1);
x_4 = l_Lean_Name_mkStr3(x_2, x_3, x_1);
x_5 = lean_mk_string_unchecked("andthen", 7, 7);
x_6 = l_Lean_Name_mkStr1(x_5);
x_7 = lean_mk_string_unchecked("(", 1, 1);
x_8 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_mk_string_unchecked("ident", 5, 5);
x_10 = l_Lean_Name_mkStr1(x_9);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
lean_inc(x_6);
x_12 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_12, 0, x_6);
lean_ctor_set(x_12, 1, x_8);
lean_ctor_set(x_12, 2, x_11);
x_13 = lean_mk_string_unchecked("optional", 8, 8);
x_14 = l_Lean_Name_mkStr1(x_13);
x_15 = lean_mk_string_unchecked(" : ", 3, 3);
x_16 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_mk_string_unchecked("term", 4, 4);
x_18 = l_Lean_Name_mkStr1(x_17);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
lean_inc(x_6);
x_21 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_21, 0, x_6);
lean_ctor_set(x_21, 1, x_16);
lean_ctor_set(x_21, 2, x_20);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_14);
lean_ctor_set(x_22, 1, x_21);
lean_inc(x_6);
x_23 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_23, 0, x_6);
lean_ctor_set(x_23, 1, x_12);
lean_ctor_set(x_23, 2, x_22);
x_24 = lean_mk_string_unchecked(")", 1, 1);
x_25 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_26, 0, x_6);
lean_ctor_set(x_26, 1, x_23);
lean_ctor_set(x_26, 2, x_25);
x_27 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_27, 0, x_1);
lean_ctor_set(x_27, 1, x_4);
lean_ctor_set(x_27, 2, x_26);
return x_27;
}
}
static lean_object* _init_l_Lake_DSL_simpleBinder() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_1 = lean_mk_string_unchecked("simpleBinder", 12, 12);
x_2 = lean_mk_string_unchecked("Lake", 4, 4);
x_3 = lean_mk_string_unchecked("DSL", 3, 3);
lean_inc(x_1);
x_4 = l_Lean_Name_mkStr3(x_2, x_3, x_1);
x_5 = lean_mk_string_unchecked("orelse", 6, 6);
x_6 = l_Lean_Name_mkStr1(x_5);
x_7 = lean_mk_string_unchecked("ident", 5, 5);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = l_Lake_DSL_bracketedSimpleBinder;
x_11 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_9);
lean_ctor_set(x_11, 2, x_10);
x_12 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_4);
lean_ctor_set(x_12, 2, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_expandOptSimpleBinder(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_4 = lean_ctor_get(x_2, 5);
x_5 = lean_box(0);
x_6 = lean_unbox(x_5);
x_7 = l_Lean_SourceInfo_fromRef(x_4, x_6);
x_8 = lean_mk_string_unchecked("Lean", 4, 4);
x_9 = lean_mk_string_unchecked("Parser", 6, 6);
x_10 = lean_mk_string_unchecked("Term", 4, 4);
x_11 = lean_mk_string_unchecked("hole", 4, 4);
x_12 = l_Lean_Name_mkStr4(x_8, x_9, x_10, x_11);
x_13 = lean_mk_string_unchecked("_", 1, 1);
lean_inc(x_7);
x_14 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Lean_Syntax_node1(x_7, x_12, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_3);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
lean_dec(x_1);
x_18 = lean_mk_string_unchecked("Lake", 4, 4);
x_19 = lean_mk_string_unchecked("DSL", 3, 3);
x_20 = lean_mk_string_unchecked("simpleBinder", 12, 12);
lean_inc(x_19);
lean_inc(x_18);
x_21 = l_Lean_Name_mkStr3(x_18, x_19, x_20);
lean_inc(x_17);
x_22 = l_Lean_Syntax_isOfKind(x_17, x_21);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
x_23 = lean_ctor_get(x_2, 5);
x_24 = l_Lean_SourceInfo_fromRef(x_23, x_22);
x_25 = lean_mk_string_unchecked("Lean", 4, 4);
x_26 = lean_mk_string_unchecked("Parser", 6, 6);
x_27 = lean_mk_string_unchecked("Term", 4, 4);
x_28 = lean_mk_string_unchecked("hole", 4, 4);
x_29 = l_Lean_Name_mkStr4(x_25, x_26, x_27, x_28);
x_30 = lean_mk_string_unchecked("_", 1, 1);
lean_inc(x_24);
x_31 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_31, 0, x_24);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Lean_Syntax_node1(x_24, x_29, x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_3);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_34 = lean_unsigned_to_nat(0u);
x_35 = l_Lean_Syntax_getArg(x_17, x_34);
lean_dec(x_17);
x_36 = lean_mk_string_unchecked("ident", 5, 5);
x_37 = l_Lean_Name_mkStr1(x_36);
lean_inc(x_35);
x_38 = l_Lean_Syntax_isOfKind(x_35, x_37);
lean_dec(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_mk_string_unchecked("bracketedSimpleBinder", 21, 21);
x_40 = l_Lean_Name_mkStr3(x_18, x_19, x_39);
lean_inc(x_35);
x_41 = l_Lean_Syntax_isOfKind(x_35, x_40);
lean_dec(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_35);
x_42 = lean_ctor_get(x_2, 5);
x_43 = l_Lean_SourceInfo_fromRef(x_42, x_38);
x_44 = lean_mk_string_unchecked("Lean", 4, 4);
x_45 = lean_mk_string_unchecked("Parser", 6, 6);
x_46 = lean_mk_string_unchecked("Term", 4, 4);
x_47 = lean_mk_string_unchecked("hole", 4, 4);
x_48 = l_Lean_Name_mkStr4(x_44, x_45, x_46, x_47);
x_49 = lean_mk_string_unchecked("_", 1, 1);
lean_inc(x_43);
x_50 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_50, 0, x_43);
lean_ctor_set(x_50, 1, x_49);
x_51 = l_Lean_Syntax_node1(x_43, x_48, x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_3);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_53 = lean_unsigned_to_nat(1u);
x_54 = l_Lean_Syntax_getArg(x_35, x_53);
x_77 = lean_unsigned_to_nat(2u);
x_78 = l_Lean_Syntax_getArg(x_35, x_77);
lean_dec(x_35);
x_79 = l_Lean_Syntax_isNone(x_78);
if (x_79 == 0)
{
uint8_t x_80; 
lean_inc(x_78);
x_80 = l_Lean_Syntax_matchesNull(x_78, x_77);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_78);
lean_dec(x_54);
x_81 = lean_ctor_get(x_2, 5);
x_82 = l_Lean_SourceInfo_fromRef(x_81, x_38);
x_83 = lean_mk_string_unchecked("Lean", 4, 4);
x_84 = lean_mk_string_unchecked("Parser", 6, 6);
x_85 = lean_mk_string_unchecked("Term", 4, 4);
x_86 = lean_mk_string_unchecked("hole", 4, 4);
x_87 = l_Lean_Name_mkStr4(x_83, x_84, x_85, x_86);
x_88 = lean_mk_string_unchecked("_", 1, 1);
lean_inc(x_82);
x_89 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_89, 0, x_82);
lean_ctor_set(x_89, 1, x_88);
x_90 = l_Lean_Syntax_node1(x_82, x_87, x_89);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_3);
return x_91;
}
else
{
lean_object* x_92; 
x_92 = l_Lean_Syntax_getArg(x_78, x_53);
lean_dec(x_78);
x_55 = x_2;
x_56 = x_3;
x_57 = x_92;
goto block_76;
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_78);
x_93 = lean_ctor_get(x_2, 5);
x_94 = lean_mk_string_unchecked("Lean", 4, 4);
x_95 = lean_mk_string_unchecked("Parser", 6, 6);
x_96 = lean_mk_string_unchecked("Term", 4, 4);
x_97 = lean_mk_string_unchecked("hole", 4, 4);
x_98 = lean_mk_string_unchecked("_", 1, 1);
x_99 = l_Lean_SourceInfo_fromRef(x_93, x_38);
x_100 = l_Lean_Name_mkStr4(x_94, x_95, x_96, x_97);
lean_inc(x_99);
x_101 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_98);
x_102 = l_Lean_Syntax_node1(x_99, x_100, x_101);
x_55 = x_2;
x_56 = x_3;
x_57 = x_102;
goto block_76;
}
block_76:
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_58 = lean_ctor_get(x_55, 5);
x_59 = l_Lean_SourceInfo_fromRef(x_58, x_38);
x_60 = lean_mk_string_unchecked("Lean", 4, 4);
x_61 = lean_mk_string_unchecked("Parser", 6, 6);
x_62 = lean_mk_string_unchecked("Term", 4, 4);
x_63 = lean_mk_string_unchecked("typeAscription", 14, 14);
x_64 = l_Lean_Name_mkStr4(x_60, x_61, x_62, x_63);
x_65 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_59);
x_66 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_66, 0, x_59);
lean_ctor_set(x_66, 1, x_65);
x_67 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_59);
x_68 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_68, 0, x_59);
lean_ctor_set(x_68, 1, x_67);
x_69 = lean_mk_string_unchecked("null", 4, 4);
x_70 = l_Lean_Name_mkStr1(x_69);
lean_inc(x_59);
x_71 = l_Lean_Syntax_node1(x_59, x_70, x_57);
x_72 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_59);
x_73 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_73, 0, x_59);
lean_ctor_set(x_73, 1, x_72);
x_74 = l_Lean_Syntax_node5(x_59, x_64, x_66, x_54, x_68, x_71, x_73);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_56);
return x_75;
}
}
}
else
{
lean_object* x_103; 
lean_dec(x_19);
lean_dec(x_18);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_35);
lean_ctor_set(x_103, 1, x_3);
return x_103;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_expandOptSimpleBinder___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_DSL_expandOptSimpleBinder(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___Lake_DSL_mkConfigFields_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_6 = lean_box(1);
x_7 = lean_box(0);
x_8 = lean_unbox(x_6);
x_9 = lean_unbox(x_7);
x_10 = l_Lean_logAt___at___Lean_logErrorAt___at___Lean_Elab_logException___at___Lean_Elab_Command_runLinters_spec__0_spec__0_spec__0(x_1, x_2, x_8, x_9, x_3, x_4, x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lake_DSL_mkConfigFields_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_17; 
x_17 = lean_usize_dec_lt(x_5, x_4);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_7);
lean_dec(x_1);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_6);
lean_ctor_set(x_18, 1, x_9);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_19 = lean_array_uget(x_3, x_5);
x_20 = lean_mk_string_unchecked("Lake", 4, 4);
x_21 = lean_mk_string_unchecked("DSL", 3, 3);
x_22 = lean_mk_string_unchecked("declField", 9, 9);
x_23 = l_Lean_Name_mkStr3(x_20, x_21, x_22);
lean_inc(x_19);
x_24 = l_Lean_Syntax_isOfKind(x_19, x_23);
lean_dec(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
lean_dec(x_6);
lean_dec(x_1);
x_25 = lean_mk_string_unchecked("ill-formed field declaration syntax", 35, 35);
x_26 = l_Lean_stringToMessageData(x_25);
lean_dec(x_25);
x_27 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__3___redArg(x_19, x_26, x_7, x_8, x_9);
lean_dec(x_7);
lean_dec(x_19);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
return x_27;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_27);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; size_t x_40; lean_object* x_41; lean_object* x_42; size_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_32 = lean_unsigned_to_nat(0u);
x_33 = lean_unsigned_to_nat(2u);
x_34 = l_Lean_Syntax_getArg(x_19, x_32);
x_35 = l_Lean_Syntax_getId(x_34);
lean_inc(x_35);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
x_37 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_37);
x_39 = lean_unsigned_to_nat(5u);
x_40 = lean_usize_of_nat(x_39);
x_41 = lean_usize_to_nat(x_40);
x_42 = lean_nat_pow(x_33, x_41);
lean_dec(x_41);
x_43 = lean_usize_of_nat(x_42);
lean_dec(x_42);
x_44 = lean_usize_to_nat(x_43);
x_45 = lean_mk_empty_array_with_capacity(x_44);
lean_dec(x_44);
lean_inc(x_45);
x_46 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_46, 0, x_45);
x_47 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
lean_ctor_set(x_47, 2, x_32);
lean_ctor_set(x_47, 3, x_32);
lean_ctor_set_usize(x_47, 4, x_40);
x_48 = lean_box(0);
x_49 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_49, 0, x_38);
lean_ctor_set(x_49, 1, x_47);
lean_ctor_set(x_49, 2, x_48);
lean_inc(x_1);
lean_inc(x_19);
x_50 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_50, 0, x_19);
lean_ctor_set(x_50, 1, x_36);
lean_ctor_set(x_50, 2, x_49);
lean_ctor_set(x_50, 3, x_1);
x_51 = l_Lean_Elab_addCompletionInfo___at___Lean_Elab_elabSetOption___at___Lean_withSetOptionIn_spec__0_spec__0(x_50, x_7, x_8, x_9);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_53 = x_51;
} else {
 lean_dec_ref(x_51);
 x_53 = lean_box(0);
}
x_54 = l_Lean_NameMap_find_x3f(lean_box(0), x_2, x_35);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_19);
x_55 = lean_mk_string_unchecked("unknown '", 9, 9);
x_56 = l_Lean_stringToMessageData(x_55);
lean_dec(x_55);
x_57 = lean_box(0);
x_58 = lean_unbox(x_57);
lean_inc(x_1);
x_59 = l_Lean_MessageData_ofConstName(x_1, x_58);
if (lean_is_scalar(x_53)) {
 x_60 = lean_alloc_ctor(7, 2, 0);
} else {
 x_60 = x_53;
 lean_ctor_set_tag(x_60, 7);
}
lean_ctor_set(x_60, 0, x_56);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_mk_string_unchecked("' field '", 9, 9);
x_62 = l_Lean_stringToMessageData(x_61);
lean_dec(x_61);
x_63 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_62);
x_64 = l_Lean_MessageData_ofName(x_35);
x_65 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
x_66 = lean_mk_string_unchecked("'", 1, 1);
x_67 = l_Lean_stringToMessageData(x_66);
lean_dec(x_66);
x_68 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_67);
lean_inc(x_7);
x_69 = l_Lean_logWarningAt___at___Lake_DSL_mkConfigFields_spec__0(x_34, x_68, x_7, x_8, x_52);
lean_dec(x_34);
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
lean_dec(x_69);
x_10 = x_6;
x_11 = x_70;
goto block_16;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_79; 
x_71 = lean_ctor_get(x_54, 0);
lean_inc(x_71);
lean_dec(x_54);
x_72 = l_Lean_Syntax_getArg(x_19, x_33);
lean_dec(x_19);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
x_79 = lean_ctor_get_uint8(x_71, sizeof(void*)*2);
lean_dec(x_71);
if (x_79 == 0)
{
if (x_24 == 0)
{
lean_dec(x_35);
x_74 = x_6;
x_75 = x_52;
goto block_78;
}
else
{
uint8_t x_80; 
x_80 = l_Lean_NameMap_contains(lean_box(0), x_6, x_73);
if (x_80 == 0)
{
lean_dec(x_35);
x_74 = x_6;
x_75 = x_52;
goto block_78;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_81 = lean_mk_string_unchecked("redefined field '", 17, 17);
x_82 = l_Lean_stringToMessageData(x_81);
lean_dec(x_81);
lean_inc(x_73);
x_83 = l_Lean_MessageData_ofName(x_73);
lean_inc(x_83);
x_84 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
x_85 = lean_mk_string_unchecked("' ('", 4, 4);
x_86 = l_Lean_stringToMessageData(x_85);
lean_dec(x_85);
x_87 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_87, 0, x_84);
lean_ctor_set(x_87, 1, x_86);
x_88 = l_Lean_MessageData_ofName(x_35);
x_89 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
x_90 = lean_mk_string_unchecked("' is an alias of '", 18, 18);
x_91 = l_Lean_stringToMessageData(x_90);
lean_dec(x_90);
x_92 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_92, 0, x_89);
lean_ctor_set(x_92, 1, x_91);
x_93 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_83);
x_94 = lean_mk_string_unchecked("')", 2, 2);
x_95 = l_Lean_stringToMessageData(x_94);
lean_dec(x_94);
x_96 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_96, 0, x_93);
lean_ctor_set(x_96, 1, x_95);
lean_inc(x_7);
x_97 = l_Lean_logWarningAt___at___Lake_DSL_mkConfigFields_spec__0(x_34, x_96, x_7, x_8, x_52);
x_98 = lean_ctor_get(x_97, 1);
lean_inc(x_98);
lean_dec(x_97);
x_74 = x_6;
x_75 = x_98;
goto block_78;
}
}
}
else
{
lean_dec(x_35);
x_74 = x_6;
x_75 = x_52;
goto block_78;
}
block_78:
{
lean_object* x_76; lean_object* x_77; 
if (lean_is_scalar(x_53)) {
 x_76 = lean_alloc_ctor(0, 2, 0);
} else {
 x_76 = x_53;
}
lean_ctor_set(x_76, 0, x_34);
lean_ctor_set(x_76, 1, x_72);
x_77 = l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(x_74, x_73, x_76);
x_10 = x_77;
x_11 = x_75;
goto block_16;
}
}
}
}
block_16:
{
lean_object* x_12; size_t x_13; size_t x_14; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_usize_of_nat(x_12);
x_14 = lean_usize_add(x_5, x_13);
x_5 = x_14;
x_6 = x_10;
x_9 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lake_DSL_mkConfigFields_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_17; 
x_17 = lean_usize_dec_lt(x_5, x_4);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_7);
lean_dec(x_1);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_6);
lean_ctor_set(x_18, 1, x_9);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_19 = lean_array_uget(x_3, x_5);
x_20 = lean_mk_string_unchecked("Lake", 4, 4);
x_21 = lean_mk_string_unchecked("DSL", 3, 3);
x_22 = lean_mk_string_unchecked("declField", 9, 9);
x_23 = l_Lean_Name_mkStr3(x_20, x_21, x_22);
lean_inc(x_19);
x_24 = l_Lean_Syntax_isOfKind(x_19, x_23);
lean_dec(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
lean_dec(x_6);
lean_dec(x_1);
x_25 = lean_mk_string_unchecked("ill-formed field declaration syntax", 35, 35);
x_26 = l_Lean_stringToMessageData(x_25);
lean_dec(x_25);
x_27 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__3___redArg(x_19, x_26, x_7, x_8, x_9);
lean_dec(x_7);
lean_dec(x_19);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
return x_27;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_27);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; size_t x_40; lean_object* x_41; lean_object* x_42; size_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_32 = lean_unsigned_to_nat(0u);
x_33 = lean_unsigned_to_nat(2u);
x_34 = l_Lean_Syntax_getArg(x_19, x_32);
x_35 = l_Lean_Syntax_getId(x_34);
lean_inc(x_35);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
x_37 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_37);
x_39 = lean_unsigned_to_nat(5u);
x_40 = lean_usize_of_nat(x_39);
x_41 = lean_usize_to_nat(x_40);
x_42 = lean_nat_pow(x_33, x_41);
lean_dec(x_41);
x_43 = lean_usize_of_nat(x_42);
lean_dec(x_42);
x_44 = lean_usize_to_nat(x_43);
x_45 = lean_mk_empty_array_with_capacity(x_44);
lean_dec(x_44);
lean_inc(x_45);
x_46 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_46, 0, x_45);
x_47 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
lean_ctor_set(x_47, 2, x_32);
lean_ctor_set(x_47, 3, x_32);
lean_ctor_set_usize(x_47, 4, x_40);
x_48 = lean_box(0);
x_49 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_49, 0, x_38);
lean_ctor_set(x_49, 1, x_47);
lean_ctor_set(x_49, 2, x_48);
lean_inc(x_1);
lean_inc(x_19);
x_50 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_50, 0, x_19);
lean_ctor_set(x_50, 1, x_36);
lean_ctor_set(x_50, 2, x_49);
lean_ctor_set(x_50, 3, x_1);
x_51 = l_Lean_Elab_addCompletionInfo___at___Lean_Elab_elabSetOption___at___Lean_withSetOptionIn_spec__0_spec__0(x_50, x_7, x_8, x_9);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_53 = x_51;
} else {
 lean_dec_ref(x_51);
 x_53 = lean_box(0);
}
x_54 = l_Lean_NameMap_find_x3f(lean_box(0), x_2, x_35);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_19);
x_55 = lean_mk_string_unchecked("unknown '", 9, 9);
x_56 = l_Lean_stringToMessageData(x_55);
lean_dec(x_55);
x_57 = lean_box(0);
x_58 = lean_unbox(x_57);
lean_inc(x_1);
x_59 = l_Lean_MessageData_ofConstName(x_1, x_58);
if (lean_is_scalar(x_53)) {
 x_60 = lean_alloc_ctor(7, 2, 0);
} else {
 x_60 = x_53;
 lean_ctor_set_tag(x_60, 7);
}
lean_ctor_set(x_60, 0, x_56);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_mk_string_unchecked("' field '", 9, 9);
x_62 = l_Lean_stringToMessageData(x_61);
lean_dec(x_61);
x_63 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_62);
x_64 = l_Lean_MessageData_ofName(x_35);
x_65 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
x_66 = lean_mk_string_unchecked("'", 1, 1);
x_67 = l_Lean_stringToMessageData(x_66);
lean_dec(x_66);
x_68 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_67);
lean_inc(x_7);
x_69 = l_Lean_logWarningAt___at___Lake_DSL_mkConfigFields_spec__0(x_34, x_68, x_7, x_8, x_52);
lean_dec(x_34);
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
lean_dec(x_69);
x_10 = x_6;
x_11 = x_70;
goto block_16;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_79; 
x_71 = lean_ctor_get(x_54, 0);
lean_inc(x_71);
lean_dec(x_54);
x_72 = l_Lean_Syntax_getArg(x_19, x_33);
lean_dec(x_19);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
x_79 = lean_ctor_get_uint8(x_71, sizeof(void*)*2);
lean_dec(x_71);
if (x_79 == 0)
{
if (x_24 == 0)
{
lean_dec(x_35);
x_74 = x_6;
x_75 = x_52;
goto block_78;
}
else
{
uint8_t x_80; 
x_80 = l_Lean_NameMap_contains(lean_box(0), x_6, x_73);
if (x_80 == 0)
{
lean_dec(x_35);
x_74 = x_6;
x_75 = x_52;
goto block_78;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_81 = lean_mk_string_unchecked("redefined field '", 17, 17);
x_82 = l_Lean_stringToMessageData(x_81);
lean_dec(x_81);
lean_inc(x_73);
x_83 = l_Lean_MessageData_ofName(x_73);
lean_inc(x_83);
x_84 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
x_85 = lean_mk_string_unchecked("' ('", 4, 4);
x_86 = l_Lean_stringToMessageData(x_85);
lean_dec(x_85);
x_87 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_87, 0, x_84);
lean_ctor_set(x_87, 1, x_86);
x_88 = l_Lean_MessageData_ofName(x_35);
x_89 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
x_90 = lean_mk_string_unchecked("' is an alias of '", 18, 18);
x_91 = l_Lean_stringToMessageData(x_90);
lean_dec(x_90);
x_92 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_92, 0, x_89);
lean_ctor_set(x_92, 1, x_91);
x_93 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_83);
x_94 = lean_mk_string_unchecked("')", 2, 2);
x_95 = l_Lean_stringToMessageData(x_94);
lean_dec(x_94);
x_96 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_96, 0, x_93);
lean_ctor_set(x_96, 1, x_95);
lean_inc(x_7);
x_97 = l_Lean_logWarningAt___at___Lake_DSL_mkConfigFields_spec__0(x_34, x_96, x_7, x_8, x_52);
x_98 = lean_ctor_get(x_97, 1);
lean_inc(x_98);
lean_dec(x_97);
x_74 = x_6;
x_75 = x_98;
goto block_78;
}
}
}
else
{
lean_dec(x_35);
x_74 = x_6;
x_75 = x_52;
goto block_78;
}
block_78:
{
lean_object* x_76; lean_object* x_77; 
if (lean_is_scalar(x_53)) {
 x_76 = lean_alloc_ctor(0, 2, 0);
} else {
 x_76 = x_53;
}
lean_ctor_set(x_76, 0, x_34);
lean_ctor_set(x_76, 1, x_72);
x_77 = l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(x_74, x_73, x_76);
x_10 = x_77;
x_11 = x_75;
goto block_16;
}
}
}
}
block_16:
{
lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_usize_of_nat(x_12);
x_14 = lean_usize_add(x_5, x_13);
x_15 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lake_DSL_mkConfigFields_spec__1_spec__1(x_1, x_2, x_3, x_4, x_14, x_10, x_7, x_8, x_11);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM___at___Lake_DSL_mkConfigFields_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 3);
lean_inc(x_8);
lean_dec(x_2);
x_9 = l_Lean_RBNode_foldM___at___Lake_DSL_mkConfigFields_spec__3___redArg(x_1, x_5, x_3);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = !lean_is_exclusive(x_7);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_13 = lean_ctor_get(x_7, 0);
x_14 = lean_ctor_get(x_7, 1);
x_15 = lean_box(1);
x_16 = lean_box(0);
x_17 = lean_box(0);
x_18 = lean_unbox(x_17);
x_19 = l_Lean_SourceInfo_fromRef(x_16, x_18);
x_20 = lean_mk_string_unchecked("Lean", 4, 4);
x_21 = lean_mk_string_unchecked("Parser", 6, 6);
x_22 = lean_mk_string_unchecked("Term", 4, 4);
x_23 = lean_mk_string_unchecked("structInstField", 15, 15);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
x_24 = l_Lean_Name_mkStr4(x_20, x_21, x_22, x_23);
x_25 = lean_mk_string_unchecked("structInstLVal", 14, 14);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
x_26 = l_Lean_Name_mkStr4(x_20, x_21, x_22, x_25);
x_27 = lean_unbox(x_15);
x_28 = l_Lean_mkIdentFrom(x_13, x_6, x_27);
lean_dec(x_13);
x_29 = lean_mk_string_unchecked("null", 4, 4);
x_30 = l_Lean_Name_mkStr1(x_29);
x_31 = l_Array_mkArray0(lean_box(0));
lean_inc(x_30);
lean_inc(x_19);
x_32 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_32, 0, x_19);
lean_ctor_set(x_32, 1, x_30);
lean_ctor_set(x_32, 2, x_31);
lean_inc(x_32);
lean_inc(x_19);
x_33 = l_Lean_Syntax_node2(x_19, x_26, x_28, x_32);
x_34 = lean_mk_string_unchecked("structInstFieldDef", 18, 18);
x_35 = l_Lean_Name_mkStr4(x_20, x_21, x_22, x_34);
x_36 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_19);
lean_ctor_set_tag(x_7, 2);
lean_ctor_set(x_7, 1, x_36);
lean_ctor_set(x_7, 0, x_19);
lean_inc(x_19);
x_37 = l_Lean_Syntax_node2(x_19, x_35, x_7, x_14);
lean_inc(x_32);
lean_inc(x_19);
x_38 = l_Lean_Syntax_node3(x_19, x_30, x_32, x_32, x_37);
x_39 = l_Lean_Syntax_node2(x_19, x_24, x_33, x_38);
x_40 = lean_array_push(x_10, x_39);
x_1 = x_40;
x_2 = x_8;
x_3 = x_11;
goto _start;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_42 = lean_ctor_get(x_7, 0);
x_43 = lean_ctor_get(x_7, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_7);
x_44 = lean_box(1);
x_45 = lean_box(0);
x_46 = lean_box(0);
x_47 = lean_unbox(x_46);
x_48 = l_Lean_SourceInfo_fromRef(x_45, x_47);
x_49 = lean_mk_string_unchecked("Lean", 4, 4);
x_50 = lean_mk_string_unchecked("Parser", 6, 6);
x_51 = lean_mk_string_unchecked("Term", 4, 4);
x_52 = lean_mk_string_unchecked("structInstField", 15, 15);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
x_53 = l_Lean_Name_mkStr4(x_49, x_50, x_51, x_52);
x_54 = lean_mk_string_unchecked("structInstLVal", 14, 14);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
x_55 = l_Lean_Name_mkStr4(x_49, x_50, x_51, x_54);
x_56 = lean_unbox(x_44);
x_57 = l_Lean_mkIdentFrom(x_42, x_6, x_56);
lean_dec(x_42);
x_58 = lean_mk_string_unchecked("null", 4, 4);
x_59 = l_Lean_Name_mkStr1(x_58);
x_60 = l_Array_mkArray0(lean_box(0));
lean_inc(x_59);
lean_inc(x_48);
x_61 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_61, 0, x_48);
lean_ctor_set(x_61, 1, x_59);
lean_ctor_set(x_61, 2, x_60);
lean_inc(x_61);
lean_inc(x_48);
x_62 = l_Lean_Syntax_node2(x_48, x_55, x_57, x_61);
x_63 = lean_mk_string_unchecked("structInstFieldDef", 18, 18);
x_64 = l_Lean_Name_mkStr4(x_49, x_50, x_51, x_63);
x_65 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_48);
x_66 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_66, 0, x_48);
lean_ctor_set(x_66, 1, x_65);
lean_inc(x_48);
x_67 = l_Lean_Syntax_node2(x_48, x_64, x_66, x_43);
lean_inc(x_61);
lean_inc(x_48);
x_68 = l_Lean_Syntax_node3(x_48, x_59, x_61, x_61, x_67);
x_69 = l_Lean_Syntax_node2(x_48, x_53, x_62, x_68);
x_70 = lean_array_push(x_10, x_69);
x_1 = x_70;
x_2 = x_8;
x_3 = x_11;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM___at___Lake_DSL_mkConfigFields_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_RBNode_foldM___at___Lake_DSL_mkConfigFields_spec__3___redArg(x_1, x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_mkConfigFields(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; size_t x_8; lean_object* x_9; size_t x_10; lean_object* x_11; 
x_7 = lean_box(0);
x_8 = lean_array_size(x_3);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_usize_of_nat(x_9);
x_11 = l_Array_forIn_x27Unsafe_loop___at___Lake_DSL_mkConfigFields_spec__1(x_1, x_2, x_3, x_8, x_10, x_7, x_4, x_5, x_6);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_mk_empty_array_with_capacity(x_9);
x_15 = l_Lean_RBNode_foldM___at___Lake_DSL_mkConfigFields_spec__3___redArg(x_14, x_12, x_13);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_mk_string_unchecked("Lean", 4, 4);
x_19 = lean_mk_string_unchecked("Parser", 6, 6);
x_20 = lean_mk_string_unchecked("Term", 4, 4);
x_21 = lean_mk_string_unchecked("structInstFields", 16, 16);
x_22 = l_Lean_Name_mkStr4(x_18, x_19, x_20, x_21);
x_23 = l_Array_empty(lean_box(0));
x_24 = lean_mk_string_unchecked("null", 4, 4);
x_25 = l_Lean_Name_mkStr1(x_24);
x_26 = lean_box(2);
x_27 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
lean_ctor_set(x_27, 2, x_23);
x_28 = l_Lean_Syntax_mkSep(x_17, x_27);
lean_dec(x_17);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_mk_empty_array_with_capacity(x_29);
x_31 = lean_array_push(x_30, x_28);
x_32 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_32, 0, x_26);
lean_ctor_set(x_32, 1, x_22);
lean_ctor_set(x_32, 2, x_31);
lean_ctor_set(x_15, 0, x_32);
return x_15;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_33 = lean_ctor_get(x_15, 0);
x_34 = lean_ctor_get(x_15, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_15);
x_35 = lean_mk_string_unchecked("Lean", 4, 4);
x_36 = lean_mk_string_unchecked("Parser", 6, 6);
x_37 = lean_mk_string_unchecked("Term", 4, 4);
x_38 = lean_mk_string_unchecked("structInstFields", 16, 16);
x_39 = l_Lean_Name_mkStr4(x_35, x_36, x_37, x_38);
x_40 = l_Array_empty(lean_box(0));
x_41 = lean_mk_string_unchecked("null", 4, 4);
x_42 = l_Lean_Name_mkStr1(x_41);
x_43 = lean_box(2);
x_44 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
lean_ctor_set(x_44, 2, x_40);
x_45 = l_Lean_Syntax_mkSep(x_33, x_44);
lean_dec(x_33);
x_46 = lean_unsigned_to_nat(1u);
x_47 = lean_mk_empty_array_with_capacity(x_46);
x_48 = lean_array_push(x_47, x_45);
x_49 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_49, 0, x_43);
lean_ctor_set(x_49, 1, x_39);
lean_ctor_set(x_49, 2, x_48);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_34);
return x_50;
}
}
else
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_11);
if (x_51 == 0)
{
return x_11;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_11, 0);
x_53 = lean_ctor_get(x_11, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_11);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___Lake_DSL_mkConfigFields_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_logWarningAt___at___Lake_DSL_mkConfigFields_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lake_DSL_mkConfigFields_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_12 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lake_DSL_mkConfigFields_spec__1_spec__1(x_1, x_2, x_3, x_10, x_11, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lake_DSL_mkConfigFields_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_12 = l_Array_forIn_x27Unsafe_loop___at___Lake_DSL_mkConfigFields_spec__1(x_1, x_2, x_3, x_10, x_11, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM___at___Lake_DSL_mkConfigFields_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_RBNode_foldM___at___Lake_DSL_mkConfigFields_spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_mkConfigFields___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_DSL_mkConfigFields(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___Lean_Elab_Term_mkFreshIdent___at___Lake_DSL_mkConfigDeclIdent_spec__0_spec__0___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = l_Lean_Elab_Command_getMainModule___redArg(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_Lean_Elab_Command_getCurrMacroScope(x_2, x_3, x_7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = l_Lean_addMacroScope(x_6, x_1, x_10);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_8);
x_14 = l_Lean_addMacroScope(x_6, x_1, x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___Lean_Elab_Term_mkFreshIdent___at___Lake_DSL_mkConfigDeclIdent_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_mk_string_unchecked("x", 1, 1);
x_5 = l_Lean_Name_mkStr1(x_4);
x_6 = lean_alloc_closure((void*)(l_Lean_Elab_Term_mkFreshBinderName___at___Lean_Elab_Term_mkFreshIdent___at___Lake_DSL_mkConfigDeclIdent_spec__0_spec__0___lam__0___boxed), 4, 1);
lean_closure_set(x_6, 0, x_5);
x_7 = l_Lean_Elab_Command_withFreshMacroScope(lean_box(0), x_6, x_1, x_2, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshIdent___at___Lake_DSL_mkConfigDeclIdent_spec__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Term_mkFreshBinderName___at___Lean_Elab_Term_mkFreshIdent___at___Lake_DSL_mkConfigDeclIdent_spec__0_spec__0(x_3, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = l_Lean_mkIdentFrom(x_1, x_8, x_2);
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
x_12 = l_Lean_mkIdentFrom(x_1, x_10, x_2);
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
LEAN_EXPORT lean_object* l_Lake_DSL_mkConfigDeclIdent(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_5 = l_Lean_Elab_Command_getRef(x_2, x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_box(0);
x_9 = lean_unbox(x_8);
x_10 = l_Lean_Elab_Term_mkFreshIdent___at___Lake_DSL_mkConfigDeclIdent_spec__0(x_6, x_9, x_2, x_3, x_7);
lean_dec(x_6);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_3);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = l_Lake_DSL_expandIdentOrStrAsIdent(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_4);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___Lean_Elab_Term_mkFreshIdent___at___Lake_DSL_mkConfigDeclIdent_spec__0_spec__0___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_mkFreshBinderName___at___Lean_Elab_Term_mkFreshIdent___at___Lake_DSL_mkConfigDeclIdent_spec__0_spec__0___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___Lean_Elab_Term_mkFreshIdent___at___Lake_DSL_mkConfigDeclIdent_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_mkFreshBinderName___at___Lean_Elab_Term_mkFreshIdent___at___Lake_DSL_mkConfigDeclIdent_spec__0_spec__0(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshIdent___at___Lake_DSL_mkConfigDeclIdent_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_Lean_Elab_Term_mkFreshIdent___at___Lake_DSL_mkConfigDeclIdent_spec__0(x_1, x_6, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_mkConfigDeclIdent___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_DSL_mkConfigDeclIdent(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_elabConfig___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_elabConfig___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
x_8 = lean_apply_3(x_3, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_apply_4(x_4, x_9, x_5, x_6, x_10);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_12 = !lean_is_exclusive(x_8);
if (x_12 == 0)
{
return x_8;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_8, 0);
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_8);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_elabConfig___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_13 = l_Lake_DSL_mkConfigFields(x_2, x_12, x_7, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_mk_string_unchecked("where", 5, 5);
x_17 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_17, 0, x_6);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_mk_string_unchecked("Lean", 4, 4);
x_19 = lean_mk_string_unchecked("Parser", 6, 6);
x_20 = lean_mk_string_unchecked("Command", 7, 7);
x_21 = lean_mk_string_unchecked("whereStructInst", 15, 15);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
x_22 = l_Lean_Name_mkStr4(x_18, x_19, x_20, x_21);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_180; 
x_180 = lean_box(0);
x_23 = x_180;
goto block_179;
}
else
{
uint8_t x_181; 
x_181 = !lean_is_exclusive(x_8);
if (x_181 == 0)
{
x_23 = x_8;
goto block_179;
}
else
{
lean_object* x_182; lean_object* x_183; 
x_182 = lean_ctor_get(x_8, 0);
lean_inc(x_182);
lean_dec(x_8);
x_183 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_183, 0, x_182);
x_23 = x_183;
goto block_179;
}
}
block_179:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_24 = lean_unsigned_to_nat(3u);
x_25 = l_Lean_Elab_Command_getRef(x_9, x_10, x_15);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_Lean_Elab_Command_getCurrMacroScope(x_9, x_10, x_27);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_30 = lean_ctor_get(x_28, 1);
x_31 = lean_ctor_get(x_28, 0);
lean_dec(x_31);
x_32 = l_Lean_Elab_Command_getMainModule___redArg(x_10, x_30);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_34 = lean_ctor_get(x_32, 1);
x_35 = lean_ctor_get(x_32, 0);
lean_dec(x_35);
x_36 = lean_mk_empty_array_with_capacity(x_24);
x_37 = lean_array_push(x_36, x_17);
x_38 = l_Lean_mkOptionalNode(x_23);
x_39 = lean_array_push(x_37, x_14);
x_40 = lean_array_push(x_39, x_38);
x_41 = lean_box(2);
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_22);
lean_ctor_set(x_43, 2, x_40);
x_44 = lean_unbox(x_42);
x_45 = l_Lean_SourceInfo_fromRef(x_26, x_44);
lean_dec(x_26);
x_46 = lean_mk_string_unchecked("declaration", 11, 11);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
x_47 = l_Lean_Name_mkStr4(x_18, x_19, x_20, x_46);
x_48 = lean_mk_string_unchecked("declModifiers", 13, 13);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
x_49 = l_Lean_Name_mkStr4(x_18, x_19, x_20, x_48);
x_50 = lean_mk_string_unchecked("null", 4, 4);
x_51 = l_Lean_Name_mkStr1(x_50);
x_52 = l_Array_mkArray0(lean_box(0));
lean_inc(x_51);
lean_inc(x_45);
x_53 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_53, 0, x_45);
lean_ctor_set(x_53, 1, x_51);
lean_ctor_set(x_53, 2, x_52);
lean_inc_n(x_53, 6);
lean_inc(x_45);
x_54 = l_Lean_Syntax_node6(x_45, x_49, x_53, x_53, x_53, x_53, x_53, x_53);
x_55 = lean_mk_string_unchecked("definition", 10, 10);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
x_56 = l_Lean_Name_mkStr4(x_18, x_19, x_20, x_55);
x_57 = lean_mk_string_unchecked("def", 3, 3);
lean_inc(x_45);
lean_ctor_set_tag(x_32, 2);
lean_ctor_set(x_32, 1, x_57);
lean_ctor_set(x_32, 0, x_45);
x_58 = lean_mk_string_unchecked("declId", 6, 6);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
x_59 = l_Lean_Name_mkStr4(x_18, x_19, x_20, x_58);
x_60 = lean_unsigned_to_nat(0u);
x_61 = lean_mk_empty_array_with_capacity(x_60);
lean_inc(x_51);
x_62 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_62, 0, x_41);
lean_ctor_set(x_62, 1, x_51);
lean_ctor_set(x_62, 2, x_61);
x_63 = lean_unsigned_to_nat(2u);
x_64 = lean_mk_empty_array_with_capacity(x_63);
x_65 = lean_array_push(x_64, x_3);
x_66 = lean_array_push(x_65, x_62);
x_67 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_67, 0, x_41);
lean_ctor_set(x_67, 1, x_59);
lean_ctor_set(x_67, 2, x_66);
x_68 = lean_mk_string_unchecked("optDeclSig", 10, 10);
lean_inc(x_19);
lean_inc(x_18);
x_69 = l_Lean_Name_mkStr4(x_18, x_19, x_20, x_68);
x_70 = lean_mk_string_unchecked("Term", 4, 4);
x_71 = lean_mk_string_unchecked("typeSpec", 8, 8);
x_72 = l_Lean_Name_mkStr4(x_18, x_19, x_70, x_71);
x_73 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_45);
lean_ctor_set_tag(x_28, 2);
lean_ctor_set(x_28, 1, x_73);
lean_ctor_set(x_28, 0, x_45);
lean_inc(x_45);
x_74 = l_Lean_Syntax_node2(x_45, x_72, x_28, x_4);
lean_inc(x_45);
x_75 = l_Lean_Syntax_node1(x_45, x_51, x_74);
lean_inc(x_53);
lean_inc(x_45);
x_76 = l_Lean_Syntax_node2(x_45, x_69, x_53, x_75);
lean_inc(x_45);
x_77 = l_Lean_Syntax_node5(x_45, x_56, x_32, x_67, x_76, x_43, x_53);
x_78 = l_Lean_Syntax_node2(x_45, x_47, x_54, x_77);
lean_inc(x_78);
x_79 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCommand), 4, 1);
lean_closure_set(x_79, 0, x_78);
x_80 = l_Lean_Elab_Command_withMacroExpansion(lean_box(0), x_5, x_78, x_79, x_9, x_10, x_34);
return x_80;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_81 = lean_ctor_get(x_32, 1);
lean_inc(x_81);
lean_dec(x_32);
x_82 = lean_mk_empty_array_with_capacity(x_24);
x_83 = lean_array_push(x_82, x_17);
x_84 = l_Lean_mkOptionalNode(x_23);
x_85 = lean_array_push(x_83, x_14);
x_86 = lean_array_push(x_85, x_84);
x_87 = lean_box(2);
x_88 = lean_box(0);
x_89 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_22);
lean_ctor_set(x_89, 2, x_86);
x_90 = lean_unbox(x_88);
x_91 = l_Lean_SourceInfo_fromRef(x_26, x_90);
lean_dec(x_26);
x_92 = lean_mk_string_unchecked("declaration", 11, 11);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
x_93 = l_Lean_Name_mkStr4(x_18, x_19, x_20, x_92);
x_94 = lean_mk_string_unchecked("declModifiers", 13, 13);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
x_95 = l_Lean_Name_mkStr4(x_18, x_19, x_20, x_94);
x_96 = lean_mk_string_unchecked("null", 4, 4);
x_97 = l_Lean_Name_mkStr1(x_96);
x_98 = l_Array_mkArray0(lean_box(0));
lean_inc(x_97);
lean_inc(x_91);
x_99 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_99, 0, x_91);
lean_ctor_set(x_99, 1, x_97);
lean_ctor_set(x_99, 2, x_98);
lean_inc_n(x_99, 6);
lean_inc(x_91);
x_100 = l_Lean_Syntax_node6(x_91, x_95, x_99, x_99, x_99, x_99, x_99, x_99);
x_101 = lean_mk_string_unchecked("definition", 10, 10);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
x_102 = l_Lean_Name_mkStr4(x_18, x_19, x_20, x_101);
x_103 = lean_mk_string_unchecked("def", 3, 3);
lean_inc(x_91);
x_104 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_104, 0, x_91);
lean_ctor_set(x_104, 1, x_103);
x_105 = lean_mk_string_unchecked("declId", 6, 6);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
x_106 = l_Lean_Name_mkStr4(x_18, x_19, x_20, x_105);
x_107 = lean_unsigned_to_nat(0u);
x_108 = lean_mk_empty_array_with_capacity(x_107);
lean_inc(x_97);
x_109 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_109, 0, x_87);
lean_ctor_set(x_109, 1, x_97);
lean_ctor_set(x_109, 2, x_108);
x_110 = lean_unsigned_to_nat(2u);
x_111 = lean_mk_empty_array_with_capacity(x_110);
x_112 = lean_array_push(x_111, x_3);
x_113 = lean_array_push(x_112, x_109);
x_114 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_114, 0, x_87);
lean_ctor_set(x_114, 1, x_106);
lean_ctor_set(x_114, 2, x_113);
x_115 = lean_mk_string_unchecked("optDeclSig", 10, 10);
lean_inc(x_19);
lean_inc(x_18);
x_116 = l_Lean_Name_mkStr4(x_18, x_19, x_20, x_115);
x_117 = lean_mk_string_unchecked("Term", 4, 4);
x_118 = lean_mk_string_unchecked("typeSpec", 8, 8);
x_119 = l_Lean_Name_mkStr4(x_18, x_19, x_117, x_118);
x_120 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_91);
lean_ctor_set_tag(x_28, 2);
lean_ctor_set(x_28, 1, x_120);
lean_ctor_set(x_28, 0, x_91);
lean_inc(x_91);
x_121 = l_Lean_Syntax_node2(x_91, x_119, x_28, x_4);
lean_inc(x_91);
x_122 = l_Lean_Syntax_node1(x_91, x_97, x_121);
lean_inc(x_99);
lean_inc(x_91);
x_123 = l_Lean_Syntax_node2(x_91, x_116, x_99, x_122);
lean_inc(x_91);
x_124 = l_Lean_Syntax_node5(x_91, x_102, x_104, x_114, x_123, x_89, x_99);
x_125 = l_Lean_Syntax_node2(x_91, x_93, x_100, x_124);
lean_inc(x_125);
x_126 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCommand), 4, 1);
lean_closure_set(x_126, 0, x_125);
x_127 = l_Lean_Elab_Command_withMacroExpansion(lean_box(0), x_5, x_125, x_126, x_9, x_10, x_81);
return x_127;
}
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_128 = lean_ctor_get(x_28, 1);
lean_inc(x_128);
lean_dec(x_28);
x_129 = l_Lean_Elab_Command_getMainModule___redArg(x_10, x_128);
x_130 = lean_ctor_get(x_129, 1);
lean_inc(x_130);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 x_131 = x_129;
} else {
 lean_dec_ref(x_129);
 x_131 = lean_box(0);
}
x_132 = lean_mk_empty_array_with_capacity(x_24);
x_133 = lean_array_push(x_132, x_17);
x_134 = l_Lean_mkOptionalNode(x_23);
x_135 = lean_array_push(x_133, x_14);
x_136 = lean_array_push(x_135, x_134);
x_137 = lean_box(2);
x_138 = lean_box(0);
x_139 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_139, 0, x_137);
lean_ctor_set(x_139, 1, x_22);
lean_ctor_set(x_139, 2, x_136);
x_140 = lean_unbox(x_138);
x_141 = l_Lean_SourceInfo_fromRef(x_26, x_140);
lean_dec(x_26);
x_142 = lean_mk_string_unchecked("declaration", 11, 11);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
x_143 = l_Lean_Name_mkStr4(x_18, x_19, x_20, x_142);
x_144 = lean_mk_string_unchecked("declModifiers", 13, 13);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
x_145 = l_Lean_Name_mkStr4(x_18, x_19, x_20, x_144);
x_146 = lean_mk_string_unchecked("null", 4, 4);
x_147 = l_Lean_Name_mkStr1(x_146);
x_148 = l_Array_mkArray0(lean_box(0));
lean_inc(x_147);
lean_inc(x_141);
x_149 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_149, 0, x_141);
lean_ctor_set(x_149, 1, x_147);
lean_ctor_set(x_149, 2, x_148);
lean_inc_n(x_149, 6);
lean_inc(x_141);
x_150 = l_Lean_Syntax_node6(x_141, x_145, x_149, x_149, x_149, x_149, x_149, x_149);
x_151 = lean_mk_string_unchecked("definition", 10, 10);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
x_152 = l_Lean_Name_mkStr4(x_18, x_19, x_20, x_151);
x_153 = lean_mk_string_unchecked("def", 3, 3);
lean_inc(x_141);
if (lean_is_scalar(x_131)) {
 x_154 = lean_alloc_ctor(2, 2, 0);
} else {
 x_154 = x_131;
 lean_ctor_set_tag(x_154, 2);
}
lean_ctor_set(x_154, 0, x_141);
lean_ctor_set(x_154, 1, x_153);
x_155 = lean_mk_string_unchecked("declId", 6, 6);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
x_156 = l_Lean_Name_mkStr4(x_18, x_19, x_20, x_155);
x_157 = lean_unsigned_to_nat(0u);
x_158 = lean_mk_empty_array_with_capacity(x_157);
lean_inc(x_147);
x_159 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_159, 0, x_137);
lean_ctor_set(x_159, 1, x_147);
lean_ctor_set(x_159, 2, x_158);
x_160 = lean_unsigned_to_nat(2u);
x_161 = lean_mk_empty_array_with_capacity(x_160);
x_162 = lean_array_push(x_161, x_3);
x_163 = lean_array_push(x_162, x_159);
x_164 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_164, 0, x_137);
lean_ctor_set(x_164, 1, x_156);
lean_ctor_set(x_164, 2, x_163);
x_165 = lean_mk_string_unchecked("optDeclSig", 10, 10);
lean_inc(x_19);
lean_inc(x_18);
x_166 = l_Lean_Name_mkStr4(x_18, x_19, x_20, x_165);
x_167 = lean_mk_string_unchecked("Term", 4, 4);
x_168 = lean_mk_string_unchecked("typeSpec", 8, 8);
x_169 = l_Lean_Name_mkStr4(x_18, x_19, x_167, x_168);
x_170 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_141);
x_171 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_171, 0, x_141);
lean_ctor_set(x_171, 1, x_170);
lean_inc(x_141);
x_172 = l_Lean_Syntax_node2(x_141, x_169, x_171, x_4);
lean_inc(x_141);
x_173 = l_Lean_Syntax_node1(x_141, x_147, x_172);
lean_inc(x_149);
lean_inc(x_141);
x_174 = l_Lean_Syntax_node2(x_141, x_166, x_149, x_173);
lean_inc(x_141);
x_175 = l_Lean_Syntax_node5(x_141, x_152, x_154, x_164, x_174, x_139, x_149);
x_176 = l_Lean_Syntax_node2(x_141, x_143, x_150, x_175);
lean_inc(x_176);
x_177 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCommand), 4, 1);
lean_closure_set(x_177, 0, x_176);
x_178 = l_Lean_Elab_Command_withMacroExpansion(lean_box(0), x_5, x_176, x_177, x_9, x_10, x_130);
return x_178;
}
}
}
else
{
uint8_t x_184; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_184 = !lean_is_exclusive(x_13);
if (x_184 == 0)
{
return x_13;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_185 = lean_ctor_get(x_13, 0);
x_186 = lean_ctor_get(x_13, 1);
lean_inc(x_186);
lean_inc(x_185);
lean_dec(x_13);
x_187 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_187, 0, x_185);
lean_ctor_set(x_187, 1, x_186);
return x_187;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_elabConfig(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_9 = lean_alloc_closure((void*)(l_Lake_DSL_elabConfig___lam__0___boxed), 5, 0);
x_10 = lean_alloc_closure((void*)(l_Lake_DSL_elabConfig___lam__1), 7, 0);
x_11 = l_instMonadEIO(lean_box(0));
x_12 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
lean_inc(x_14);
x_15 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_15, 0, x_14);
x_16 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_16, 0, x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_closure((void*)(l_instMonadEIO___lam__1), 5, 0);
x_19 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_19, 0, x_18);
x_20 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_20, 0, x_19);
x_21 = lean_alloc_closure((void*)(l_instMonadEIO___lam__2), 5, 0);
x_22 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_22, 0, x_21);
x_23 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_23, 0, x_22);
x_24 = lean_alloc_closure((void*)(l_EStateM_seqRight), 7, 2);
lean_closure_set(x_24, 0, lean_box(0));
lean_closure_set(x_24, 1, lean_box(0));
x_25 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_25, 0, x_24);
x_26 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_26, 0, x_25);
x_27 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_27, 0, x_17);
lean_ctor_set(x_27, 1, x_9);
lean_ctor_set(x_27, 2, x_20);
lean_ctor_set(x_27, 3, x_23);
lean_ctor_set(x_27, 4, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_10);
x_29 = l_Lean_Elab_Command_instMonadRefCommandElabM;
x_30 = lean_mk_string_unchecked("Lake", 4, 4);
x_31 = lean_mk_string_unchecked("DSL", 3, 3);
x_32 = lean_mk_string_unchecked("optConfig", 9, 9);
lean_inc(x_31);
lean_inc(x_30);
x_33 = l_Lean_Name_mkStr3(x_30, x_31, x_32);
lean_inc(x_5);
x_34 = l_Lean_Syntax_isOfKind(x_5, x_33);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_35 = l_Lean_Elab_Command_instMonadExceptOfExceptionCommandElabM;
x_36 = l_Lean_Elab_Command_instAddErrorMessageContextCommandElabM;
x_37 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_29);
lean_ctor_set(x_37, 2, x_36);
x_38 = lean_mk_string_unchecked("ill-formed configuration syntax", 31, 31);
x_39 = l_Lean_stringToMessageData(x_38);
lean_dec(x_38);
x_40 = l_Lean_throwErrorAt(lean_box(0), lean_box(0), x_28, x_37, x_5, x_39);
x_41 = lean_apply_3(x_40, x_6, x_7, x_8);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_42 = lean_unsigned_to_nat(0u);
x_43 = l_Lean_Syntax_getArg(x_5, x_42);
lean_inc(x_43);
x_44 = l_Lean_Syntax_matchesNull(x_43, x_42);
if (x_44 == 0)
{
lean_object* x_45; uint8_t x_46; 
x_45 = lean_unsigned_to_nat(1u);
lean_inc(x_43);
x_46 = l_Lean_Syntax_matchesNull(x_43, x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_43);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_47 = l_Lean_Elab_Command_instMonadExceptOfExceptionCommandElabM;
x_48 = l_Lean_Elab_Command_instAddErrorMessageContextCommandElabM;
x_49 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_29);
lean_ctor_set(x_49, 2, x_48);
x_50 = lean_mk_string_unchecked("ill-formed configuration syntax", 31, 31);
x_51 = l_Lean_stringToMessageData(x_50);
lean_dec(x_50);
x_52 = l_Lean_throwErrorAt(lean_box(0), lean_box(0), x_28, x_49, x_5, x_51);
x_53 = lean_apply_3(x_52, x_6, x_7, x_8);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_54 = l_Lean_Syntax_getArg(x_43, x_42);
lean_dec(x_43);
x_55 = lean_mk_string_unchecked("declValWhere", 12, 12);
lean_inc(x_31);
lean_inc(x_30);
x_56 = l_Lean_Name_mkStr3(x_30, x_31, x_55);
lean_inc(x_54);
x_57 = l_Lean_Syntax_isOfKind(x_54, x_56);
lean_dec(x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_58 = lean_mk_string_unchecked("declValStruct", 13, 13);
lean_inc(x_31);
lean_inc(x_30);
x_59 = l_Lean_Name_mkStr3(x_30, x_31, x_58);
lean_inc(x_54);
x_60 = l_Lean_Syntax_isOfKind(x_54, x_59);
lean_dec(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_54);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_61 = l_Lean_Elab_Command_instMonadExceptOfExceptionCommandElabM;
x_62 = l_Lean_Elab_Command_instAddErrorMessageContextCommandElabM;
x_63 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_29);
lean_ctor_set(x_63, 2, x_62);
x_64 = lean_mk_string_unchecked("ill-formed configuration syntax", 31, 31);
x_65 = l_Lean_stringToMessageData(x_64);
lean_dec(x_64);
x_66 = l_Lean_throwErrorAt(lean_box(0), lean_box(0), x_28, x_63, x_5, x_65);
x_67 = lean_apply_3(x_66, x_6, x_7, x_8);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_68 = l_Lean_Syntax_getArg(x_54, x_42);
x_69 = lean_mk_string_unchecked("structVal", 9, 9);
x_70 = l_Lean_Name_mkStr3(x_30, x_31, x_69);
lean_inc(x_68);
x_71 = l_Lean_Syntax_isOfKind(x_68, x_70);
lean_dec(x_70);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_68);
lean_dec(x_54);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_72 = l_Lean_Elab_Command_instMonadExceptOfExceptionCommandElabM;
x_73 = l_Lean_Elab_Command_instAddErrorMessageContextCommandElabM;
x_74 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_29);
lean_ctor_set(x_74, 2, x_73);
x_75 = lean_mk_string_unchecked("ill-formed configuration syntax", 31, 31);
x_76 = l_Lean_stringToMessageData(x_75);
lean_dec(x_75);
x_77 = l_Lean_throwErrorAt(lean_box(0), lean_box(0), x_28, x_74, x_5, x_76);
x_78 = lean_apply_3(x_77, x_6, x_7, x_8);
return x_78;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_79 = l_Lean_Syntax_getArg(x_68, x_45);
x_80 = lean_mk_string_unchecked("Lean", 4, 4);
x_81 = lean_mk_string_unchecked("Parser", 6, 6);
x_82 = lean_mk_string_unchecked("Term", 4, 4);
x_83 = lean_mk_string_unchecked("structInstFields", 16, 16);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_80);
x_84 = l_Lean_Name_mkStr4(x_80, x_81, x_82, x_83);
lean_inc(x_79);
x_85 = l_Lean_Syntax_isOfKind(x_79, x_84);
lean_dec(x_84);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_68);
lean_dec(x_54);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_86 = l_Lean_Elab_Command_instMonadExceptOfExceptionCommandElabM;
x_87 = l_Lean_Elab_Command_instAddErrorMessageContextCommandElabM;
x_88 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_29);
lean_ctor_set(x_88, 2, x_87);
x_89 = lean_mk_string_unchecked("ill-formed configuration syntax", 31, 31);
x_90 = l_Lean_stringToMessageData(x_89);
lean_dec(x_89);
x_91 = l_Lean_throwErrorAt(lean_box(0), lean_box(0), x_28, x_88, x_5, x_90);
x_92 = lean_apply_3(x_91, x_6, x_7, x_8);
return x_92;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_104; uint8_t x_105; 
x_93 = l_Lean_Syntax_getArg(x_79, x_42);
lean_dec(x_79);
x_104 = l_Lean_Syntax_getArg(x_54, x_45);
lean_dec(x_54);
x_105 = l_Lean_Syntax_isNone(x_104);
if (x_105 == 0)
{
uint8_t x_106; 
lean_inc(x_104);
x_106 = l_Lean_Syntax_matchesNull(x_104, x_45);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec(x_104);
lean_dec(x_93);
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_68);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_107 = l_Lean_Elab_Command_instMonadExceptOfExceptionCommandElabM;
x_108 = l_Lean_Elab_Command_instAddErrorMessageContextCommandElabM;
x_109 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_29);
lean_ctor_set(x_109, 2, x_108);
x_110 = lean_mk_string_unchecked("ill-formed configuration syntax", 31, 31);
x_111 = l_Lean_stringToMessageData(x_110);
lean_dec(x_110);
x_112 = l_Lean_throwErrorAt(lean_box(0), lean_box(0), x_28, x_109, x_5, x_111);
x_113 = lean_apply_3(x_112, x_6, x_7, x_8);
return x_113;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; 
x_114 = l_Lean_Syntax_getArg(x_104, x_42);
lean_dec(x_104);
x_115 = lean_mk_string_unchecked("whereDecls", 10, 10);
x_116 = l_Lean_Name_mkStr4(x_80, x_81, x_82, x_115);
lean_inc(x_114);
x_117 = l_Lean_Syntax_isOfKind(x_114, x_116);
lean_dec(x_116);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
lean_dec(x_114);
lean_dec(x_93);
lean_dec(x_68);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_118 = l_Lean_Elab_Command_instMonadExceptOfExceptionCommandElabM;
x_119 = l_Lean_Elab_Command_instAddErrorMessageContextCommandElabM;
x_120 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_29);
lean_ctor_set(x_120, 2, x_119);
x_121 = lean_mk_string_unchecked("ill-formed configuration syntax", 31, 31);
x_122 = l_Lean_stringToMessageData(x_121);
lean_dec(x_121);
x_123 = l_Lean_throwErrorAt(lean_box(0), lean_box(0), x_28, x_120, x_5, x_122);
x_124 = lean_apply_3(x_123, x_6, x_7, x_8);
return x_124;
}
else
{
lean_object* x_125; 
lean_dec(x_28);
x_125 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_125, 0, x_114);
x_94 = x_125;
x_95 = x_6;
x_96 = x_7;
x_97 = x_8;
goto block_103;
}
}
}
else
{
lean_object* x_126; 
lean_dec(x_104);
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_28);
x_126 = lean_box(0);
x_94 = x_126;
x_95 = x_6;
x_96 = x_7;
x_97 = x_8;
goto block_103;
}
block_103:
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_98 = l_Lean_Syntax_getArgs(x_93);
lean_dec(x_93);
x_99 = l_Lean_Syntax_getArg(x_68, x_42);
lean_dec(x_68);
x_100 = l_Lean_Syntax_getHeadInfo(x_99);
lean_dec(x_99);
x_101 = l_Lean_Syntax_TSepArray_getElems___redArg(x_98);
lean_dec(x_98);
x_102 = l_Lake_DSL_elabConfig___lam__2(x_2, x_1, x_3, x_4, x_5, x_100, x_101, x_94, x_95, x_96, x_97);
lean_dec(x_101);
return x_102;
}
}
}
}
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; 
lean_dec(x_31);
lean_dec(x_30);
x_127 = l_Lean_Syntax_getArg(x_54, x_45);
x_128 = lean_mk_string_unchecked("Lean", 4, 4);
x_129 = lean_mk_string_unchecked("Parser", 6, 6);
x_130 = lean_mk_string_unchecked("Term", 4, 4);
x_131 = lean_mk_string_unchecked("structInstFields", 16, 16);
lean_inc(x_130);
lean_inc(x_129);
lean_inc(x_128);
x_132 = l_Lean_Name_mkStr4(x_128, x_129, x_130, x_131);
lean_inc(x_127);
x_133 = l_Lean_Syntax_isOfKind(x_127, x_132);
lean_dec(x_132);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
lean_dec(x_130);
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_127);
lean_dec(x_54);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_134 = l_Lean_Elab_Command_instMonadExceptOfExceptionCommandElabM;
x_135 = l_Lean_Elab_Command_instAddErrorMessageContextCommandElabM;
x_136 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_29);
lean_ctor_set(x_136, 2, x_135);
x_137 = lean_mk_string_unchecked("ill-formed configuration syntax", 31, 31);
x_138 = l_Lean_stringToMessageData(x_137);
lean_dec(x_137);
x_139 = l_Lean_throwErrorAt(lean_box(0), lean_box(0), x_28, x_136, x_5, x_138);
x_140 = lean_apply_3(x_139, x_6, x_7, x_8);
return x_140;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_152; lean_object* x_153; uint8_t x_154; 
x_141 = l_Lean_Syntax_getArg(x_127, x_42);
lean_dec(x_127);
x_152 = lean_unsigned_to_nat(2u);
x_153 = l_Lean_Syntax_getArg(x_54, x_152);
x_154 = l_Lean_Syntax_isNone(x_153);
if (x_154 == 0)
{
uint8_t x_155; 
lean_inc(x_153);
x_155 = l_Lean_Syntax_matchesNull(x_153, x_45);
if (x_155 == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
lean_dec(x_153);
lean_dec(x_141);
lean_dec(x_130);
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_54);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_156 = l_Lean_Elab_Command_instMonadExceptOfExceptionCommandElabM;
x_157 = l_Lean_Elab_Command_instAddErrorMessageContextCommandElabM;
x_158 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_158, 0, x_156);
lean_ctor_set(x_158, 1, x_29);
lean_ctor_set(x_158, 2, x_157);
x_159 = lean_mk_string_unchecked("ill-formed configuration syntax", 31, 31);
x_160 = l_Lean_stringToMessageData(x_159);
lean_dec(x_159);
x_161 = l_Lean_throwErrorAt(lean_box(0), lean_box(0), x_28, x_158, x_5, x_160);
x_162 = lean_apply_3(x_161, x_6, x_7, x_8);
return x_162;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; uint8_t x_166; 
x_163 = l_Lean_Syntax_getArg(x_153, x_42);
lean_dec(x_153);
x_164 = lean_mk_string_unchecked("whereDecls", 10, 10);
x_165 = l_Lean_Name_mkStr4(x_128, x_129, x_130, x_164);
lean_inc(x_163);
x_166 = l_Lean_Syntax_isOfKind(x_163, x_165);
lean_dec(x_165);
if (x_166 == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
lean_dec(x_163);
lean_dec(x_141);
lean_dec(x_54);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_167 = l_Lean_Elab_Command_instMonadExceptOfExceptionCommandElabM;
x_168 = l_Lean_Elab_Command_instAddErrorMessageContextCommandElabM;
x_169 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_169, 0, x_167);
lean_ctor_set(x_169, 1, x_29);
lean_ctor_set(x_169, 2, x_168);
x_170 = lean_mk_string_unchecked("ill-formed configuration syntax", 31, 31);
x_171 = l_Lean_stringToMessageData(x_170);
lean_dec(x_170);
x_172 = l_Lean_throwErrorAt(lean_box(0), lean_box(0), x_28, x_169, x_5, x_171);
x_173 = lean_apply_3(x_172, x_6, x_7, x_8);
return x_173;
}
else
{
lean_object* x_174; 
lean_dec(x_28);
x_174 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_174, 0, x_163);
x_142 = x_174;
x_143 = x_6;
x_144 = x_7;
x_145 = x_8;
goto block_151;
}
}
}
else
{
lean_object* x_175; 
lean_dec(x_153);
lean_dec(x_130);
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_28);
x_175 = lean_box(0);
x_142 = x_175;
x_143 = x_6;
x_144 = x_7;
x_145 = x_8;
goto block_151;
}
block_151:
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_146 = l_Lean_Syntax_getArgs(x_141);
lean_dec(x_141);
x_147 = l_Lean_Syntax_getArg(x_54, x_42);
lean_dec(x_54);
x_148 = l_Lean_Syntax_getHeadInfo(x_147);
lean_dec(x_147);
x_149 = l_Lean_Syntax_TSepArray_getElems___redArg(x_146);
lean_dec(x_146);
x_150 = l_Lake_DSL_elabConfig___lam__2(x_2, x_1, x_3, x_4, x_5, x_148, x_149, x_142, x_143, x_144, x_145);
lean_dec(x_149);
return x_150;
}
}
}
}
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
lean_dec(x_43);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_28);
x_176 = lean_box(2);
x_177 = lean_mk_empty_array_with_capacity(x_42);
x_178 = lean_box(0);
x_179 = l_Lake_DSL_elabConfig___lam__2(x_2, x_1, x_3, x_4, x_5, x_176, x_177, x_178, x_6, x_7, x_8);
lean_dec(x_177);
return x_179;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_elabConfig___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_DSL_elabConfig___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_elabConfig___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lake_DSL_elabConfig___lam__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_elabConfig___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_DSL_elabConfig(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_9;
}
}
lean_object* initialize_Lake_Util_Binder(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_Name(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Config_Meta(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Parser_Command(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Command(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_DSL_DeclUtil(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Util_Binder(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Name(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Meta(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Command(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Command(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_DSL_packageDeclName = _init_l_Lake_DSL_packageDeclName();
lean_mark_persistent(l_Lake_DSL_packageDeclName);
l_Lake_DSL_identOrStr = _init_l_Lake_DSL_identOrStr();
lean_mark_persistent(l_Lake_DSL_identOrStr);
l_Lake_DSL_declField = _init_l_Lake_DSL_declField();
lean_mark_persistent(l_Lake_DSL_declField);
l_Lake_DSL_structVal = _init_l_Lake_DSL_structVal();
lean_mark_persistent(l_Lake_DSL_structVal);
l_Lake_DSL_declValDo = _init_l_Lake_DSL_declValDo();
lean_mark_persistent(l_Lake_DSL_declValDo);
l_Lake_DSL_declValStruct = _init_l_Lake_DSL_declValStruct();
lean_mark_persistent(l_Lake_DSL_declValStruct);
l_Lake_DSL_declValWhere = _init_l_Lake_DSL_declValWhere();
lean_mark_persistent(l_Lake_DSL_declValWhere);
l_Lake_DSL_simpleDeclSig = _init_l_Lake_DSL_simpleDeclSig();
lean_mark_persistent(l_Lake_DSL_simpleDeclSig);
l_Lake_DSL_optConfig = _init_l_Lake_DSL_optConfig();
lean_mark_persistent(l_Lake_DSL_optConfig);
l_Lake_DSL_bracketedSimpleBinder = _init_l_Lake_DSL_bracketedSimpleBinder();
lean_mark_persistent(l_Lake_DSL_bracketedSimpleBinder);
l_Lake_DSL_simpleBinder = _init_l_Lake_DSL_simpleBinder();
lean_mark_persistent(l_Lake_DSL_simpleBinder);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
