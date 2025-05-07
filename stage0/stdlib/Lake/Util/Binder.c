// Lean compiler output
// Module: Lake.Util.Binder
// Imports: Lean.Parser.Term Lean.Elab.Term Lean.Expr
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
LEAN_EXPORT lean_object* l_Lake_instCoeBracketedBinderBinder;
LEAN_EXPORT lean_object* l_Lake_instCoeDepArrowTerm;
LEAN_EXPORT lean_object* l_Lake_expandBinder(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lake_expandBinders___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_expandBinderType___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_424_(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_expandBinderCore_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_orelse_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprBinderSyntaxView;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lake_getBinderIds_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_expandBinders_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkDepArrow___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_expandBinderModifier___boxed(lean_object*);
lean_object* l___private_Init_Meta_0__Lean_Syntax_reprSyntax____x40_Init_Meta___hyg_2026_(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instCoeHoleBinderIdent;
LEAN_EXPORT lean_object* l_Lake_expandBinderModifier(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_expandBinderCore_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_bracketedBinder_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instCoeTermArgument___lam__0(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instCoeHoleTerm;
lean_object* l_Lean_Parser_orelse(lean_object*, lean_object*);
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Option_repr___at_____private_Lake_Util_Binder_0__Lake_reprBinderSyntaxView____x40_Lake_Util_Binder___hyg_339__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedBinderSyntaxView;
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l___private_Init_Meta_0__Lean_Syntax_reprTSyntax___redArg____x40_Init_Meta___hyg_2266_(lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_BinderSyntaxView_mkArgument(lean_object*);
LEAN_EXPORT lean_object* l_Lake_binder_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getNumArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lake_expandBinderIdent(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instCoeBinderDeclBinder;
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Array_mkArray1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instCoeNamedArgumentArgument;
LEAN_EXPORT lean_object* l_Lake_instCoeBinderIdentFunBinder;
LEAN_EXPORT lean_object* l_Lake_instCoeTermArgument___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_expandBinderCore(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_binderIdent_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_expandBinders_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lake_getBinderIds_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instCoeBinderIdentBinder___lam__0(lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_BinderSyntaxView_mkDepArrow(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instCoeIdentBinderIdent;
lean_object* l_Array_empty(lean_object*);
LEAN_EXPORT lean_object* l_Lake_expandOptType(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Binder_0__Lake_reprBinderSyntaxView___redArg____x40_Lake_Util_Binder___hyg_339_(lean_object*);
lean_object* l_Lean_Parser_Term_binderIdent_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_repr___at_____private_Lake_Util_Binder_0__Lake_reprBinderSyntaxView____x40_Lake_Util_Binder___hyg_339__spec__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
extern lean_object* l_Lean_Parser_Term_binderIdent;
LEAN_EXPORT lean_object* l_Lake_BinderSyntaxView_mkFunBinder(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___Lean_Elab_Term_mkFreshIdent___at___Lake_expandBinderIdent_spec__0_spec__0(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_expandBinderCore_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_expandOptType___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkHoleFrom___boxed(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_expandOptIdent(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Binder_0__Lake_reprBinderSyntaxView____x40_Lake_Util_Binder___hyg_339____boxed(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getBinderIds(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isIdent(lean_object*);
LEAN_EXPORT lean_object* l_Lake_expandBinderType(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Binder_0__Lake_reprBinderSyntaxView____x40_Lake_Util_Binder___hyg_339_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_expandBinderCore_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Macro_throwErrorAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_expandBinderCore_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_binder_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_expandBinders(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Macro_throwUnsupported(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_expandOptIdent___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_mkDepArrow_spec__0(lean_object*, size_t, size_t, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkHoleFrom(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_expandBinderCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshIdent___at___Lake_expandBinderIdent_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append(lean_object*, lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instCoeTermArgument;
LEAN_EXPORT lean_object* l_Lake_getBinderIds___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instCoeBinderIdentBinder;
LEAN_EXPORT lean_object* l_Lake_instCoeEllipsisArgument;
lean_object* l_Lean_Parser_Term_bracketedBinder_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_binder;
lean_object* l_Lean_mkAtomFrom(lean_object*, lean_object*, uint8_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_mkDepArrow_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_bracketedBinder(uint8_t);
LEAN_EXPORT lean_object* l_Lake_mkDepArrow(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshIdent___at___Lake_expandBinderIdent_spec__0(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BinderSyntaxView_mkBinder(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instCoeBinderIdentBinder___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instCoeTermArgument___lam__0(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
static lean_object* _init_l_Lake_instCoeTermArgument() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instCoeTermArgument___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeTermArgument___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_instCoeTermArgument___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instCoeEllipsisArgument() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instCoeTermArgument___lam__0___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instCoeNamedArgumentArgument() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instCoeTermArgument___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_mkHoleFrom(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Term", 4, 4);
x_5 = lean_mk_string_unchecked("hole", 4, 4);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_mk_string_unchecked("_", 1, 1);
x_8 = lean_box(0);
x_9 = lean_unbox(x_8);
x_10 = l_Lean_mkAtomFrom(x_1, x_7, x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_mk_empty_array_with_capacity(x_11);
x_13 = lean_array_push(x_12, x_10);
x_14 = lean_box(2);
x_15 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_6);
lean_ctor_set(x_15, 2, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lake_mkHoleFrom___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_mkHoleFrom(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instCoeHoleTerm() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instCoeTermArgument___lam__0___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instCoeHoleBinderIdent() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instCoeTermArgument___lam__0___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instCoeIdentBinderIdent() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instCoeTermArgument___lam__0___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instCoeBinderIdentFunBinder() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instCoeTermArgument___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_binder_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_Term_binderIdent_formatter), 5, 0);
x_7 = lean_box(0);
x_8 = lean_alloc_closure((void*)(l_Lean_Parser_Term_bracketedBinder_formatter___boxed), 6, 1);
lean_closure_set(x_8, 0, x_7);
x_9 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_6, x_8, x_1, x_2, x_3, x_4, x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_binder_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_Term_binderIdent_parenthesizer), 5, 0);
x_7 = lean_box(0);
x_8 = lean_alloc_closure((void*)(l_Lean_Parser_Term_bracketedBinder_parenthesizer___boxed), 6, 1);
lean_closure_set(x_8, 0, x_7);
x_9 = l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer(x_6, x_8, x_1, x_2, x_3, x_4, x_5);
return x_9;
}
}
static lean_object* _init_l_Lake_binder() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Parser_Term_binderIdent;
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
x_4 = l_Lean_Parser_Term_bracketedBinder(x_3);
x_5 = l_Lean_Parser_orelse(x_1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeBinderIdentBinder___lam__0(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
static lean_object* _init_l_Lake_instCoeBinderIdentBinder() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instCoeBinderIdentBinder___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeBinderIdentBinder___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_instCoeBinderIdentBinder___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instCoeBracketedBinderBinder() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instCoeBinderIdentBinder___lam__0___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instCoeBinderDeclBinder() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instCoeBinderIdentBinder___lam__0___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instCoeDepArrowTerm() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instCoeBinderIdentBinder___lam__0___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instInhabitedBinderSyntaxView() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_1);
lean_ctor_set(x_4, 2, x_1);
lean_ctor_set(x_4, 3, x_3);
x_5 = lean_unbox(x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_5);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at_____private_Lake_Util_Binder_0__Lake_reprBinderSyntaxView____x40_Lake_Util_Binder___hyg_339__spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_mk_string_unchecked("none", 4, 4);
x_4 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_mk_string_unchecked("some ", 5, 5);
lean_ctor_set_tag(x_1, 3);
lean_ctor_set(x_1, 0, x_7);
x_8 = l___private_Init_Meta_0__Lean_Syntax_reprTSyntax___redArg____x40_Init_Meta___hyg_2266_(x_6);
x_9 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Repr_addAppParen(x_9, x_2);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_mk_string_unchecked("some ", 5, 5);
x_13 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = l___private_Init_Meta_0__Lean_Syntax_reprTSyntax___redArg____x40_Init_Meta___hyg_2266_(x_11);
x_15 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Repr_addAppParen(x_15, x_2);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Binder_0__Lake_reprBinderSyntaxView___redArg____x40_Lake_Util_Binder___hyg_339_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_2 = lean_mk_string_unchecked("{ ", 2, 2);
x_3 = lean_box(0);
x_4 = lean_mk_string_unchecked("ref", 3, 3);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_mk_string_unchecked(" := ", 4, 4);
x_8 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_8, 0, x_7);
lean_inc(x_8);
x_9 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(7u);
x_11 = lean_nat_to_int(x_10);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l___private_Init_Meta_0__Lean_Syntax_reprSyntax____x40_Init_Meta___hyg_2026_(x_12, x_13);
x_15 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_17, 0, x_15);
x_18 = lean_unbox(x_16);
lean_ctor_set_uint8(x_17, sizeof(void*)*1, x_18);
x_19 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_19, 0, x_9);
lean_ctor_set(x_19, 1, x_17);
x_20 = lean_mk_string_unchecked(",", 1, 1);
x_21 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_21, 0, x_20);
lean_inc(x_21);
x_22 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_box(1);
x_24 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_mk_string_unchecked("id", 2, 2);
x_26 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_26);
lean_inc(x_8);
x_28 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_8);
x_29 = lean_unsigned_to_nat(6u);
x_30 = lean_nat_to_int(x_29);
x_31 = lean_ctor_get(x_1, 1);
lean_inc(x_31);
x_32 = l___private_Init_Meta_0__Lean_Syntax_reprTSyntax___redArg____x40_Init_Meta___hyg_2266_(x_31);
x_33 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_34, 0, x_33);
x_35 = lean_unbox(x_16);
lean_ctor_set_uint8(x_34, sizeof(void*)*1, x_35);
x_36 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_36, 0, x_28);
lean_ctor_set(x_36, 1, x_34);
lean_inc(x_21);
x_37 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_21);
x_38 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_23);
x_39 = lean_mk_string_unchecked("type", 4, 4);
x_40 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_40, 0, x_39);
x_41 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set(x_41, 1, x_40);
lean_inc(x_8);
x_42 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_8);
x_43 = lean_unsigned_to_nat(8u);
x_44 = lean_nat_to_int(x_43);
x_45 = lean_ctor_get(x_1, 2);
lean_inc(x_45);
x_46 = l___private_Init_Meta_0__Lean_Syntax_reprTSyntax___redArg____x40_Init_Meta___hyg_2266_(x_45);
lean_inc(x_44);
x_47 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_47, 0, x_44);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_48, 0, x_47);
x_49 = lean_unbox(x_16);
lean_ctor_set_uint8(x_48, sizeof(void*)*1, x_49);
x_50 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_50, 0, x_42);
lean_ctor_set(x_50, 1, x_48);
lean_inc(x_21);
x_51 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_21);
x_52 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_23);
x_53 = lean_mk_string_unchecked("info", 4, 4);
x_54 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_55 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_55, 0, x_52);
lean_ctor_set(x_55, 1, x_54);
lean_inc(x_8);
x_56 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_8);
x_57 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
x_58 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_424_(x_57, x_13);
x_59 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_59, 0, x_44);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_60, 0, x_59);
x_61 = lean_unbox(x_16);
lean_ctor_set_uint8(x_60, sizeof(void*)*1, x_61);
x_62 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_62, 0, x_56);
lean_ctor_set(x_62, 1, x_60);
x_63 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_21);
x_64 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_23);
x_65 = lean_mk_string_unchecked("modifier\?", 9, 9);
x_66 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_66, 0, x_65);
x_67 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_67, 0, x_64);
lean_ctor_set(x_67, 1, x_66);
x_68 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_8);
x_69 = lean_unsigned_to_nat(13u);
x_70 = lean_nat_to_int(x_69);
x_71 = lean_ctor_get(x_1, 3);
lean_inc(x_71);
lean_dec(x_1);
x_72 = l_Option_repr___at_____private_Lake_Util_Binder_0__Lake_reprBinderSyntaxView____x40_Lake_Util_Binder___hyg_339__spec__0(x_71, x_13);
x_73 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_73, 0, x_70);
lean_ctor_set(x_73, 1, x_72);
x_74 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_74, 0, x_73);
x_75 = lean_unbox(x_16);
lean_ctor_set_uint8(x_74, sizeof(void*)*1, x_75);
x_76 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_76, 0, x_68);
lean_ctor_set(x_76, 1, x_74);
x_77 = lean_mk_string_unchecked(" }", 2, 2);
x_78 = lean_unsigned_to_nat(2u);
x_79 = lean_nat_to_int(x_78);
x_80 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_80, 0, x_2);
x_81 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_76);
x_82 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_82, 0, x_77);
x_83 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
x_84 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_84, 0, x_79);
lean_ctor_set(x_84, 1, x_83);
x_85 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_85, 0, x_84);
x_86 = lean_unbox(x_16);
lean_ctor_set_uint8(x_85, sizeof(void*)*1, x_86);
return x_85;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Binder_0__Lake_reprBinderSyntaxView____x40_Lake_Util_Binder___hyg_339_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lake_Util_Binder_0__Lake_reprBinderSyntaxView___redArg____x40_Lake_Util_Binder___hyg_339_(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at_____private_Lake_Util_Binder_0__Lake_reprBinderSyntaxView____x40_Lake_Util_Binder___hyg_339__spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Option_repr___at_____private_Lake_Util_Binder_0__Lake_reprBinderSyntaxView____x40_Lake_Util_Binder___hyg_339__spec__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Binder_0__Lake_reprBinderSyntaxView____x40_Lake_Util_Binder___hyg_339____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lake_Util_Binder_0__Lake_reprBinderSyntaxView____x40_Lake_Util_Binder___hyg_339_(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_instReprBinderSyntaxView() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lake_Util_Binder_0__Lake_reprBinderSyntaxView____x40_Lake_Util_Binder___hyg_339____boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_expandOptType(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_Syntax_isNone(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_Syntax_getArg(x_2, x_4);
x_6 = lean_unsigned_to_nat(1u);
x_7 = l_Lean_Syntax_getArg(x_5, x_6);
lean_dec(x_5);
return x_7;
}
else
{
lean_object* x_8; 
x_8 = l_Lake_mkHoleFrom(x_1);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lake_expandOptType___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_expandOptType(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lake_getBinderIds_spec__0(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_19; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_8 = lean_array_uget(x_3, x_2);
x_9 = lean_box(0);
x_10 = lean_array_uset(x_3, x_2, x_9);
lean_inc(x_8);
x_27 = l_Lean_Syntax_getKind(x_8);
x_28 = lean_mk_string_unchecked("ident", 5, 5);
x_29 = l_Lean_Name_mkStr1(x_28);
x_30 = lean_name_eq(x_27, x_29);
lean_dec(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_31 = lean_mk_string_unchecked("Lean", 4, 4);
x_32 = lean_mk_string_unchecked("Parser", 6, 6);
x_33 = lean_mk_string_unchecked("Term", 4, 4);
x_34 = lean_mk_string_unchecked("hole", 4, 4);
x_35 = l_Lean_Name_mkStr4(x_31, x_32, x_33, x_34);
x_36 = lean_name_eq(x_27, x_35);
lean_dec(x_35);
lean_dec(x_27);
x_19 = x_36;
goto block_26;
}
else
{
lean_dec(x_27);
x_19 = x_30;
goto block_26;
}
block_18:
{
lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_usize_of_nat(x_13);
x_15 = lean_usize_add(x_2, x_14);
x_16 = lean_array_uset(x_10, x_2, x_11);
x_2 = x_15;
x_3 = x_16;
x_5 = x_12;
goto _start;
}
block_26:
{
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
lean_dec(x_10);
x_20 = lean_mk_string_unchecked("identifier or `_` expected", 26, 26);
x_21 = l_Lean_Macro_throwErrorAt(lean_box(0), x_8, x_20, x_4, x_5);
lean_dec(x_8);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
return x_21;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_21);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
x_11 = x_8;
x_12 = x_5;
goto block_18;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_getBinderIds(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; size_t x_5; lean_object* x_6; size_t x_7; lean_object* x_8; 
x_4 = l_Lean_Syntax_getArgs(x_1);
x_5 = lean_array_size(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_usize_of_nat(x_6);
x_8 = l_Array_mapMUnsafe_map___at___Lake_getBinderIds_spec__0(x_5, x_7, x_4, x_2, x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lake_getBinderIds_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = l_Array_mapMUnsafe_map___at___Lake_getBinderIds_spec__0(x_6, x_7, x_3, x_4, x_5);
lean_dec(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_getBinderIds___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_getBinderIds(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___Lean_Elab_Term_mkFreshIdent___at___Lake_expandBinderIdent_spec__0_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_3 = lean_mk_string_unchecked("x", 1, 1);
x_4 = l_Lean_Name_mkStr1(x_3);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_add(x_5, x_6);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = l_Lean_addMacroScope(x_10, x_4, x_5);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshIdent___at___Lake_expandBinderIdent_spec__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Elab_Term_mkFreshBinderName___at___Lean_Elab_Term_mkFreshIdent___at___Lake_expandBinderIdent_spec__0_spec__0(x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = l_Lean_mkIdentFrom(x_1, x_7, x_2);
lean_ctor_set(x_5, 0, x_8);
return x_5;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_5, 0);
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_5);
x_11 = l_Lean_mkIdentFrom(x_1, x_9, x_2);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lake_expandBinderIdent(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Term", 4, 4);
x_7 = lean_mk_string_unchecked("hole", 4, 4);
x_8 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_7);
lean_inc(x_1);
x_9 = l_Lean_Syntax_isOfKind(x_1, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_2);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_3);
return x_10;
}
else
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_box(0);
x_12 = lean_unbox(x_11);
x_13 = l_Lean_Elab_Term_mkFreshIdent___at___Lake_expandBinderIdent_spec__0(x_1, x_12, x_2, x_3);
lean_dec(x_1);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshIdent___at___Lake_expandBinderIdent_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_Elab_Term_mkFreshIdent___at___Lake_expandBinderIdent_spec__0(x_1, x_5, x_3, x_4);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_expandOptIdent(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_Syntax_isNone(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Lean_Syntax_getArg(x_1, x_3);
return x_4;
}
else
{
lean_object* x_5; 
x_5 = l_Lake_mkHoleFrom(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lake_expandOptIdent___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_expandOptIdent(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_expandBinderType(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_Syntax_getNumArgs(x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
lean_dec(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = l_Lean_Syntax_getArg(x_2, x_6);
return x_7;
}
else
{
lean_object* x_8; 
x_8 = l_Lake_mkHoleFrom(x_1);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lake_expandBinderType___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_expandBinderType(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_expandBinderModifier(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_getOptional_x3f(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
return x_2;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_expandBinderModifier___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_expandBinderModifier(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_expandBinderCore_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_eq(x_3, x_4);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; 
x_9 = lean_array_uget(x_2, x_3);
lean_inc(x_6);
lean_inc(x_9);
x_10 = l_Lake_expandBinderIdent(x_9, x_6, x_7);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_unsigned_to_nat(2u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
x_15 = l_Lake_expandBinderType(x_9, x_14);
lean_dec(x_14);
lean_dec(x_9);
x_16 = lean_box(2);
x_17 = lean_box(0);
lean_inc(x_1);
x_18 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_11);
lean_ctor_set(x_18, 2, x_15);
lean_ctor_set(x_18, 3, x_17);
x_19 = lean_unbox(x_16);
lean_ctor_set_uint8(x_18, sizeof(void*)*4, x_19);
x_20 = lean_array_push(x_5, x_18);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_usize_of_nat(x_21);
x_23 = lean_usize_add(x_3, x_22);
x_3 = x_23;
x_5 = x_20;
x_7 = x_12;
goto _start;
}
else
{
lean_object* x_25; 
lean_dec(x_6);
lean_dec(x_1);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_5);
lean_ctor_set(x_25, 1, x_7);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_expandBinderCore_spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_eq(x_3, x_4);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; 
x_9 = lean_array_uget(x_2, x_3);
lean_inc(x_6);
lean_inc(x_9);
x_10 = l_Lake_expandBinderIdent(x_9, x_6, x_7);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_unsigned_to_nat(2u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
x_15 = l_Lake_expandBinderType(x_9, x_14);
lean_dec(x_14);
lean_dec(x_9);
x_16 = lean_box(1);
x_17 = lean_box(0);
lean_inc(x_1);
x_18 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_11);
lean_ctor_set(x_18, 2, x_15);
lean_ctor_set(x_18, 3, x_17);
x_19 = lean_unbox(x_16);
lean_ctor_set_uint8(x_18, sizeof(void*)*4, x_19);
x_20 = lean_array_push(x_5, x_18);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_usize_of_nat(x_21);
x_23 = lean_usize_add(x_3, x_22);
x_3 = x_23;
x_5 = x_20;
x_7 = x_12;
goto _start;
}
else
{
lean_object* x_25; 
lean_dec(x_6);
lean_dec(x_1);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_5);
lean_ctor_set(x_25, 1, x_7);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_expandBinderCore_spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(3u);
x_9 = lean_usize_dec_eq(x_3, x_4);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; 
x_10 = lean_array_uget(x_2, x_3);
lean_inc(x_6);
lean_inc(x_10);
x_11 = l_Lake_expandBinderIdent(x_10, x_6, x_7);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_unsigned_to_nat(2u);
x_15 = l_Lean_Syntax_getArg(x_1, x_8);
x_16 = l_Lean_Syntax_getArg(x_1, x_14);
x_17 = l_Lake_expandBinderModifier(x_15);
lean_dec(x_15);
x_18 = l_Lake_expandBinderType(x_10, x_16);
lean_dec(x_16);
lean_dec(x_10);
x_19 = lean_box(0);
lean_inc(x_1);
x_20 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_12);
lean_ctor_set(x_20, 2, x_18);
lean_ctor_set(x_20, 3, x_17);
x_21 = lean_unbox(x_19);
lean_ctor_set_uint8(x_20, sizeof(void*)*4, x_21);
x_22 = lean_array_push(x_5, x_20);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_usize_of_nat(x_23);
x_25 = lean_usize_add(x_3, x_24);
x_3 = x_25;
x_5 = x_22;
x_7 = x_13;
goto _start;
}
else
{
lean_object* x_27; 
lean_dec(x_6);
lean_dec(x_1);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_5);
lean_ctor_set(x_27, 1, x_7);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l_Lake_expandBinderCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; uint8_t x_149; 
lean_inc(x_2);
x_5 = l_Lean_Syntax_getKind(x_2);
x_149 = l_Lean_Syntax_isIdent(x_2);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; uint8_t x_155; 
x_150 = lean_mk_string_unchecked("Lean", 4, 4);
x_151 = lean_mk_string_unchecked("Parser", 6, 6);
x_152 = lean_mk_string_unchecked("Term", 4, 4);
x_153 = lean_mk_string_unchecked("hole", 4, 4);
x_154 = l_Lean_Name_mkStr4(x_150, x_151, x_152, x_153);
x_155 = lean_name_eq(x_5, x_154);
lean_dec(x_154);
x_6 = x_155;
goto block_148;
}
else
{
x_6 = x_149;
goto block_148;
}
block_148:
{
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_7 = lean_mk_string_unchecked("Lean", 4, 4);
x_8 = lean_mk_string_unchecked("Parser", 6, 6);
x_9 = lean_mk_string_unchecked("Term", 4, 4);
x_10 = lean_mk_string_unchecked("explicitBinder", 14, 14);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_11 = l_Lean_Name_mkStr4(x_7, x_8, x_9, x_10);
x_12 = lean_name_eq(x_5, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_mk_string_unchecked("implicitBinder", 14, 14);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_14 = l_Lean_Name_mkStr4(x_7, x_8, x_9, x_13);
x_15 = lean_name_eq(x_5, x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_mk_string_unchecked("strictImplicitBinder", 20, 20);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_17 = l_Lean_Name_mkStr4(x_7, x_8, x_9, x_16);
x_18 = lean_name_eq(x_5, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_mk_string_unchecked("instBinder", 10, 10);
x_20 = l_Lean_Name_mkStr4(x_7, x_8, x_9, x_19);
x_21 = lean_name_eq(x_5, x_20);
lean_dec(x_20);
lean_dec(x_5);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_2);
lean_dec(x_1);
x_22 = l_Lean_Macro_throwUnsupported(lean_box(0), x_3, x_4);
lean_dec(x_3);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_23 = lean_unsigned_to_nat(1u);
x_24 = l_Lean_Syntax_getArg(x_2, x_23);
x_25 = l_Lake_expandOptIdent(x_24);
lean_dec(x_24);
x_26 = l_Lake_expandBinderIdent(x_25, x_3, x_4);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = lean_unsigned_to_nat(2u);
x_30 = l_Lean_Syntax_getArg(x_2, x_29);
x_31 = lean_box(3);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_33, 0, x_2);
lean_ctor_set(x_33, 1, x_28);
lean_ctor_set(x_33, 2, x_30);
lean_ctor_set(x_33, 3, x_32);
x_34 = lean_unbox(x_31);
lean_ctor_set_uint8(x_33, sizeof(void*)*4, x_34);
x_35 = lean_array_push(x_1, x_33);
lean_ctor_set(x_26, 0, x_35);
return x_26;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; 
x_36 = lean_ctor_get(x_26, 0);
x_37 = lean_ctor_get(x_26, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_26);
x_38 = lean_unsigned_to_nat(2u);
x_39 = l_Lean_Syntax_getArg(x_2, x_38);
x_40 = lean_box(3);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_42, 0, x_2);
lean_ctor_set(x_42, 1, x_36);
lean_ctor_set(x_42, 2, x_39);
lean_ctor_set(x_42, 3, x_41);
x_43 = lean_unbox(x_40);
lean_ctor_set_uint8(x_42, sizeof(void*)*4, x_43);
x_44 = lean_array_push(x_1, x_42);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_37);
return x_45;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
x_46 = lean_unsigned_to_nat(1u);
x_47 = l_Lean_Syntax_getArg(x_2, x_46);
x_48 = l_Lake_getBinderIds(x_47, x_3, x_4);
lean_dec(x_47);
if (lean_obj_tag(x_48) == 0)
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_50 = lean_ctor_get(x_48, 0);
x_51 = lean_ctor_get(x_48, 1);
x_52 = lean_unsigned_to_nat(0u);
x_53 = lean_array_get_size(x_50);
x_54 = lean_nat_dec_lt(x_52, x_53);
if (x_54 == 0)
{
lean_dec(x_53);
lean_dec(x_50);
lean_dec(x_3);
lean_dec(x_2);
lean_ctor_set(x_48, 0, x_1);
return x_48;
}
else
{
uint8_t x_55; 
x_55 = lean_nat_dec_le(x_53, x_53);
if (x_55 == 0)
{
lean_dec(x_53);
lean_dec(x_50);
lean_dec(x_3);
lean_dec(x_2);
lean_ctor_set(x_48, 0, x_1);
return x_48;
}
else
{
size_t x_56; size_t x_57; lean_object* x_58; 
lean_free_object(x_48);
x_56 = lean_usize_of_nat(x_52);
x_57 = lean_usize_of_nat(x_53);
lean_dec(x_53);
x_58 = l_Array_foldlMUnsafe_fold___at___Lake_expandBinderCore_spec__0(x_2, x_50, x_56, x_57, x_1, x_3, x_51);
lean_dec(x_50);
return x_58;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_59 = lean_ctor_get(x_48, 0);
x_60 = lean_ctor_get(x_48, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_48);
x_61 = lean_unsigned_to_nat(0u);
x_62 = lean_array_get_size(x_59);
x_63 = lean_nat_dec_lt(x_61, x_62);
if (x_63 == 0)
{
lean_object* x_64; 
lean_dec(x_62);
lean_dec(x_59);
lean_dec(x_3);
lean_dec(x_2);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_1);
lean_ctor_set(x_64, 1, x_60);
return x_64;
}
else
{
uint8_t x_65; 
x_65 = lean_nat_dec_le(x_62, x_62);
if (x_65 == 0)
{
lean_object* x_66; 
lean_dec(x_62);
lean_dec(x_59);
lean_dec(x_3);
lean_dec(x_2);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_1);
lean_ctor_set(x_66, 1, x_60);
return x_66;
}
else
{
size_t x_67; size_t x_68; lean_object* x_69; 
x_67 = lean_usize_of_nat(x_61);
x_68 = lean_usize_of_nat(x_62);
lean_dec(x_62);
x_69 = l_Array_foldlMUnsafe_fold___at___Lake_expandBinderCore_spec__0(x_2, x_59, x_67, x_68, x_1, x_3, x_60);
lean_dec(x_59);
return x_69;
}
}
}
}
else
{
uint8_t x_70; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_70 = !lean_is_exclusive(x_48);
if (x_70 == 0)
{
return x_48;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_48, 0);
x_72 = lean_ctor_get(x_48, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_48);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
x_74 = lean_unsigned_to_nat(1u);
x_75 = l_Lean_Syntax_getArg(x_2, x_74);
x_76 = l_Lake_getBinderIds(x_75, x_3, x_4);
lean_dec(x_75);
if (lean_obj_tag(x_76) == 0)
{
uint8_t x_77; 
x_77 = !lean_is_exclusive(x_76);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_78 = lean_ctor_get(x_76, 0);
x_79 = lean_ctor_get(x_76, 1);
x_80 = lean_unsigned_to_nat(0u);
x_81 = lean_array_get_size(x_78);
x_82 = lean_nat_dec_lt(x_80, x_81);
if (x_82 == 0)
{
lean_dec(x_81);
lean_dec(x_78);
lean_dec(x_3);
lean_dec(x_2);
lean_ctor_set(x_76, 0, x_1);
return x_76;
}
else
{
uint8_t x_83; 
x_83 = lean_nat_dec_le(x_81, x_81);
if (x_83 == 0)
{
lean_dec(x_81);
lean_dec(x_78);
lean_dec(x_3);
lean_dec(x_2);
lean_ctor_set(x_76, 0, x_1);
return x_76;
}
else
{
size_t x_84; size_t x_85; lean_object* x_86; 
lean_free_object(x_76);
x_84 = lean_usize_of_nat(x_80);
x_85 = lean_usize_of_nat(x_81);
lean_dec(x_81);
x_86 = l_Array_foldlMUnsafe_fold___at___Lake_expandBinderCore_spec__1(x_2, x_78, x_84, x_85, x_1, x_3, x_79);
lean_dec(x_78);
return x_86;
}
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_87 = lean_ctor_get(x_76, 0);
x_88 = lean_ctor_get(x_76, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_76);
x_89 = lean_unsigned_to_nat(0u);
x_90 = lean_array_get_size(x_87);
x_91 = lean_nat_dec_lt(x_89, x_90);
if (x_91 == 0)
{
lean_object* x_92; 
lean_dec(x_90);
lean_dec(x_87);
lean_dec(x_3);
lean_dec(x_2);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_1);
lean_ctor_set(x_92, 1, x_88);
return x_92;
}
else
{
uint8_t x_93; 
x_93 = lean_nat_dec_le(x_90, x_90);
if (x_93 == 0)
{
lean_object* x_94; 
lean_dec(x_90);
lean_dec(x_87);
lean_dec(x_3);
lean_dec(x_2);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_1);
lean_ctor_set(x_94, 1, x_88);
return x_94;
}
else
{
size_t x_95; size_t x_96; lean_object* x_97; 
x_95 = lean_usize_of_nat(x_89);
x_96 = lean_usize_of_nat(x_90);
lean_dec(x_90);
x_97 = l_Array_foldlMUnsafe_fold___at___Lake_expandBinderCore_spec__1(x_2, x_87, x_95, x_96, x_1, x_3, x_88);
lean_dec(x_87);
return x_97;
}
}
}
}
else
{
uint8_t x_98; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_98 = !lean_is_exclusive(x_76);
if (x_98 == 0)
{
return x_76;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_76, 0);
x_100 = lean_ctor_get(x_76, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_76);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
x_102 = lean_unsigned_to_nat(1u);
x_103 = l_Lean_Syntax_getArg(x_2, x_102);
x_104 = l_Lake_getBinderIds(x_103, x_3, x_4);
lean_dec(x_103);
if (lean_obj_tag(x_104) == 0)
{
uint8_t x_105; 
x_105 = !lean_is_exclusive(x_104);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; 
x_106 = lean_ctor_get(x_104, 0);
x_107 = lean_ctor_get(x_104, 1);
x_108 = lean_unsigned_to_nat(0u);
x_109 = lean_array_get_size(x_106);
x_110 = lean_nat_dec_lt(x_108, x_109);
if (x_110 == 0)
{
lean_dec(x_109);
lean_dec(x_106);
lean_dec(x_3);
lean_dec(x_2);
lean_ctor_set(x_104, 0, x_1);
return x_104;
}
else
{
uint8_t x_111; 
x_111 = lean_nat_dec_le(x_109, x_109);
if (x_111 == 0)
{
lean_dec(x_109);
lean_dec(x_106);
lean_dec(x_3);
lean_dec(x_2);
lean_ctor_set(x_104, 0, x_1);
return x_104;
}
else
{
size_t x_112; size_t x_113; lean_object* x_114; 
lean_free_object(x_104);
x_112 = lean_usize_of_nat(x_108);
x_113 = lean_usize_of_nat(x_109);
lean_dec(x_109);
x_114 = l_Array_foldlMUnsafe_fold___at___Lake_expandBinderCore_spec__2(x_2, x_106, x_112, x_113, x_1, x_3, x_107);
lean_dec(x_106);
return x_114;
}
}
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; 
x_115 = lean_ctor_get(x_104, 0);
x_116 = lean_ctor_get(x_104, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_104);
x_117 = lean_unsigned_to_nat(0u);
x_118 = lean_array_get_size(x_115);
x_119 = lean_nat_dec_lt(x_117, x_118);
if (x_119 == 0)
{
lean_object* x_120; 
lean_dec(x_118);
lean_dec(x_115);
lean_dec(x_3);
lean_dec(x_2);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_1);
lean_ctor_set(x_120, 1, x_116);
return x_120;
}
else
{
uint8_t x_121; 
x_121 = lean_nat_dec_le(x_118, x_118);
if (x_121 == 0)
{
lean_object* x_122; 
lean_dec(x_118);
lean_dec(x_115);
lean_dec(x_3);
lean_dec(x_2);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_1);
lean_ctor_set(x_122, 1, x_116);
return x_122;
}
else
{
size_t x_123; size_t x_124; lean_object* x_125; 
x_123 = lean_usize_of_nat(x_117);
x_124 = lean_usize_of_nat(x_118);
lean_dec(x_118);
x_125 = l_Array_foldlMUnsafe_fold___at___Lake_expandBinderCore_spec__2(x_2, x_115, x_123, x_124, x_1, x_3, x_116);
lean_dec(x_115);
return x_125;
}
}
}
}
else
{
uint8_t x_126; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_126 = !lean_is_exclusive(x_104);
if (x_126 == 0)
{
return x_104;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_104, 0);
x_128 = lean_ctor_get(x_104, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_104);
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
return x_129;
}
}
}
}
else
{
lean_object* x_130; uint8_t x_131; 
lean_dec(x_5);
lean_inc(x_2);
x_130 = l_Lake_expandBinderIdent(x_2, x_3, x_4);
x_131 = !lean_is_exclusive(x_130);
if (x_131 == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; lean_object* x_138; 
x_132 = lean_ctor_get(x_130, 0);
x_133 = l_Lake_mkHoleFrom(x_2);
x_134 = lean_box(0);
x_135 = lean_box(0);
x_136 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_136, 0, x_2);
lean_ctor_set(x_136, 1, x_132);
lean_ctor_set(x_136, 2, x_133);
lean_ctor_set(x_136, 3, x_135);
x_137 = lean_unbox(x_134);
lean_ctor_set_uint8(x_136, sizeof(void*)*4, x_137);
x_138 = lean_array_push(x_1, x_136);
lean_ctor_set(x_130, 0, x_138);
return x_130;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; lean_object* x_146; lean_object* x_147; 
x_139 = lean_ctor_get(x_130, 0);
x_140 = lean_ctor_get(x_130, 1);
lean_inc(x_140);
lean_inc(x_139);
lean_dec(x_130);
x_141 = l_Lake_mkHoleFrom(x_2);
x_142 = lean_box(0);
x_143 = lean_box(0);
x_144 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_144, 0, x_2);
lean_ctor_set(x_144, 1, x_139);
lean_ctor_set(x_144, 2, x_141);
lean_ctor_set(x_144, 3, x_143);
x_145 = lean_unbox(x_142);
lean_ctor_set_uint8(x_144, sizeof(void*)*4, x_145);
x_146 = lean_array_push(x_1, x_144);
x_147 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_140);
return x_147;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_expandBinderCore_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l_Array_foldlMUnsafe_fold___at___Lake_expandBinderCore_spec__0(x_1, x_2, x_8, x_9, x_5, x_6, x_7);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_expandBinderCore_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l_Array_foldlMUnsafe_fold___at___Lake_expandBinderCore_spec__1(x_1, x_2, x_8, x_9, x_5, x_6, x_7);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_expandBinderCore_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l_Array_foldlMUnsafe_fold___at___Lake_expandBinderCore_spec__2(x_1, x_2, x_8, x_9, x_5, x_6, x_7);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_expandBinder(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_mk_empty_array_with_capacity(x_4);
x_6 = l_Lake_expandBinderCore(x_5, x_1, x_2, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_expandBinders_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_2, x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_array_uget(x_1, x_2);
lean_inc(x_5);
x_9 = l_Lake_expandBinderCore(x_4, x_8, x_5, x_6);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_usize_of_nat(x_12);
x_14 = lean_usize_add(x_2, x_13);
x_2 = x_14;
x_4 = x_10;
x_6 = x_11;
goto _start;
}
else
{
lean_dec(x_5);
return x_9;
}
}
else
{
lean_object* x_16; 
lean_dec(x_5);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_4);
lean_ctor_set(x_16, 1, x_6);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lake_expandBinders(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_mk_empty_array_with_capacity(x_4);
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_lt(x_4, x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_6);
lean_dec(x_2);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = lean_nat_dec_le(x_6, x_6);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_2);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_3);
return x_10;
}
else
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_usize_of_nat(x_4);
x_12 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_13 = l_Array_foldlMUnsafe_fold___at___Lake_expandBinders_spec__0(x_1, x_11, x_12, x_5, x_2, x_3);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_expandBinders_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Array_foldlMUnsafe_fold___at___Lake_expandBinders_spec__0(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_expandBinders___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_expandBinders(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_BinderSyntaxView_mkBinder(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
switch (x_2) {
case 0:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 3);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_box(0);
x_8 = lean_unbox(x_7);
x_9 = l_Lean_SourceInfo_fromRef(x_3, x_8);
lean_dec(x_3);
x_10 = lean_mk_string_unchecked("Lean", 4, 4);
x_11 = lean_mk_string_unchecked("Parser", 6, 6);
x_12 = lean_mk_string_unchecked("Term", 4, 4);
x_13 = lean_mk_string_unchecked("explicitBinder", 14, 14);
x_14 = l_Lean_Name_mkStr4(x_10, x_11, x_12, x_13);
x_15 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_9);
x_16 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_16, 0, x_9);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_mk_string_unchecked("null", 4, 4);
x_18 = l_Lean_Name_mkStr1(x_17);
lean_inc(x_18);
lean_inc(x_9);
x_19 = l_Lean_Syntax_node1(x_9, x_18, x_4);
x_20 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_9);
x_21 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_21, 0, x_9);
lean_ctor_set(x_21, 1, x_20);
lean_inc(x_18);
lean_inc(x_9);
x_22 = l_Lean_Syntax_node2(x_9, x_18, x_21, x_5);
x_23 = l_Array_mkArray0(lean_box(0));
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_31; 
x_31 = l_Array_empty(lean_box(0));
x_24 = x_31;
goto block_30;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_6, 0);
lean_inc(x_32);
lean_dec(x_6);
x_33 = l_Array_mkArray1___redArg(x_32);
x_24 = x_33;
goto block_30;
}
block_30:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = l_Array_append(lean_box(0), x_23, x_24);
lean_dec(x_24);
lean_inc(x_9);
x_26 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_26, 0, x_9);
lean_ctor_set(x_26, 1, x_18);
lean_ctor_set(x_26, 2, x_25);
x_27 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_9);
x_28 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_28, 0, x_9);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_Syntax_node5(x_9, x_14, x_16, x_19, x_22, x_26, x_28);
return x_29;
}
}
case 1:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_34 = lean_ctor_get(x_1, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_1, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_1, 2);
lean_inc(x_36);
lean_dec(x_1);
x_37 = lean_box(0);
x_38 = lean_unbox(x_37);
x_39 = l_Lean_SourceInfo_fromRef(x_34, x_38);
lean_dec(x_34);
x_40 = lean_mk_string_unchecked("Lean", 4, 4);
x_41 = lean_mk_string_unchecked("Parser", 6, 6);
x_42 = lean_mk_string_unchecked("Term", 4, 4);
x_43 = lean_mk_string_unchecked("implicitBinder", 14, 14);
x_44 = l_Lean_Name_mkStr4(x_40, x_41, x_42, x_43);
x_45 = lean_mk_string_unchecked("{", 1, 1);
lean_inc(x_39);
x_46 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_46, 0, x_39);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_mk_string_unchecked("null", 4, 4);
x_48 = l_Lean_Name_mkStr1(x_47);
lean_inc(x_48);
lean_inc(x_39);
x_49 = l_Lean_Syntax_node1(x_39, x_48, x_35);
x_50 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_39);
x_51 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_51, 0, x_39);
lean_ctor_set(x_51, 1, x_50);
lean_inc(x_39);
x_52 = l_Lean_Syntax_node2(x_39, x_48, x_51, x_36);
x_53 = lean_mk_string_unchecked("}", 1, 1);
lean_inc(x_39);
x_54 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_54, 0, x_39);
lean_ctor_set(x_54, 1, x_53);
x_55 = l_Lean_Syntax_node4(x_39, x_44, x_46, x_49, x_52, x_54);
return x_55;
}
case 2:
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_56 = lean_ctor_get(x_1, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_1, 1);
lean_inc(x_57);
x_58 = lean_ctor_get(x_1, 2);
lean_inc(x_58);
lean_dec(x_1);
x_59 = lean_box(0);
x_60 = lean_unbox(x_59);
x_61 = l_Lean_SourceInfo_fromRef(x_56, x_60);
lean_dec(x_56);
x_62 = lean_mk_string_unchecked("Lean", 4, 4);
x_63 = lean_mk_string_unchecked("Parser", 6, 6);
x_64 = lean_mk_string_unchecked("Term", 4, 4);
x_65 = lean_mk_string_unchecked("strictImplicitBinder", 20, 20);
x_66 = l_Lean_Name_mkStr4(x_62, x_63, x_64, x_65);
x_67 = lean_mk_string_unchecked("⦃", 3, 1);
lean_inc(x_61);
x_68 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_68, 0, x_61);
lean_ctor_set(x_68, 1, x_67);
x_69 = lean_mk_string_unchecked("null", 4, 4);
x_70 = l_Lean_Name_mkStr1(x_69);
lean_inc(x_70);
lean_inc(x_61);
x_71 = l_Lean_Syntax_node1(x_61, x_70, x_57);
x_72 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_61);
x_73 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_73, 0, x_61);
lean_ctor_set(x_73, 1, x_72);
lean_inc(x_61);
x_74 = l_Lean_Syntax_node2(x_61, x_70, x_73, x_58);
x_75 = lean_mk_string_unchecked("⦄", 3, 1);
lean_inc(x_61);
x_76 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_76, 0, x_61);
lean_ctor_set(x_76, 1, x_75);
x_77 = l_Lean_Syntax_node4(x_61, x_66, x_68, x_71, x_74, x_76);
return x_77;
}
default: 
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_78 = lean_ctor_get(x_1, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_1, 1);
lean_inc(x_79);
x_80 = lean_ctor_get(x_1, 2);
lean_inc(x_80);
lean_dec(x_1);
x_81 = lean_box(0);
x_82 = lean_unbox(x_81);
x_83 = l_Lean_SourceInfo_fromRef(x_78, x_82);
lean_dec(x_78);
x_84 = lean_mk_string_unchecked("Lean", 4, 4);
x_85 = lean_mk_string_unchecked("Parser", 6, 6);
x_86 = lean_mk_string_unchecked("Term", 4, 4);
x_87 = lean_mk_string_unchecked("instBinder", 10, 10);
x_88 = l_Lean_Name_mkStr4(x_84, x_85, x_86, x_87);
x_89 = lean_mk_string_unchecked("[", 1, 1);
lean_inc(x_83);
x_90 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_90, 0, x_83);
lean_ctor_set(x_90, 1, x_89);
x_91 = lean_mk_string_unchecked("null", 4, 4);
x_92 = l_Lean_Name_mkStr1(x_91);
x_93 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_83);
x_94 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_94, 0, x_83);
lean_ctor_set(x_94, 1, x_93);
lean_inc(x_83);
x_95 = l_Lean_Syntax_node2(x_83, x_92, x_79, x_94);
x_96 = lean_mk_string_unchecked("]", 1, 1);
lean_inc(x_83);
x_97 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_97, 0, x_83);
lean_ctor_set(x_97, 1, x_96);
x_98 = l_Lean_Syntax_node4(x_83, x_88, x_90, x_95, x_80, x_97);
return x_98;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BinderSyntaxView_mkDepArrow(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_box(0);
x_5 = lean_unbox(x_4);
x_6 = l_Lean_SourceInfo_fromRef(x_3, x_5);
lean_dec(x_3);
x_7 = lean_mk_string_unchecked("Lean", 4, 4);
x_8 = lean_mk_string_unchecked("Parser", 6, 6);
x_9 = lean_mk_string_unchecked("Term", 4, 4);
x_10 = lean_mk_string_unchecked("depArrow", 8, 8);
x_11 = l_Lean_Name_mkStr4(x_7, x_8, x_9, x_10);
x_12 = l_Lake_BinderSyntaxView_mkBinder(x_2);
x_13 = lean_mk_string_unchecked("→", 3, 1);
lean_inc(x_6);
x_14 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_14, 0, x_6);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Lean_Syntax_node3(x_6, x_11, x_12, x_14, x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_mkDepArrow_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Lake_BinderSyntaxView_mkDepArrow(x_4, x_6);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_usize_of_nat(x_8);
x_10 = lean_usize_add(x_2, x_9);
x_2 = x_10;
x_4 = x_7;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lake_mkDepArrow(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
lean_dec(x_4);
return x_2;
}
else
{
uint8_t x_6; 
x_6 = lean_nat_dec_le(x_4, x_4);
if (x_6 == 0)
{
lean_dec(x_4);
return x_2;
}
else
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_usize_of_nat(x_3);
x_8 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_9 = l_Array_foldlMUnsafe_fold___at___Lake_mkDepArrow_spec__0(x_1, x_7, x_8, x_2);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_mkDepArrow_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Lake_mkDepArrow_spec__0(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_mkDepArrow___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_mkDepArrow(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_BinderSyntaxView_mkFunBinder(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
x_5 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = l_Lean_replaceRef(x_2, x_6);
lean_dec(x_2);
switch (x_5) {
case 0:
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_8 = lean_box(0);
x_9 = lean_unbox(x_8);
x_10 = l_Lean_SourceInfo_fromRef(x_7, x_9);
lean_dec(x_7);
x_11 = lean_mk_string_unchecked("Lean", 4, 4);
x_12 = lean_mk_string_unchecked("Parser", 6, 6);
x_13 = lean_mk_string_unchecked("Term", 4, 4);
x_14 = lean_mk_string_unchecked("typeAscription", 14, 14);
x_15 = l_Lean_Name_mkStr4(x_11, x_12, x_13, x_14);
x_16 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_10);
x_17 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_17, 0, x_10);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_10);
x_19 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_19, 0, x_10);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_mk_string_unchecked("null", 4, 4);
x_21 = l_Lean_Name_mkStr1(x_20);
lean_inc(x_10);
x_22 = l_Lean_Syntax_node1(x_10, x_21, x_4);
x_23 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_10);
x_24 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_24, 0, x_10);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_Syntax_node5(x_10, x_15, x_17, x_3, x_19, x_22, x_24);
return x_25;
}
case 1:
{
lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_26 = lean_box(0);
x_27 = lean_unbox(x_26);
x_28 = l_Lean_SourceInfo_fromRef(x_7, x_27);
lean_dec(x_7);
x_29 = lean_mk_string_unchecked("Lean", 4, 4);
x_30 = lean_mk_string_unchecked("Parser", 6, 6);
x_31 = lean_mk_string_unchecked("Term", 4, 4);
x_32 = lean_mk_string_unchecked("implicitBinder", 14, 14);
x_33 = l_Lean_Name_mkStr4(x_29, x_30, x_31, x_32);
x_34 = lean_mk_string_unchecked("{", 1, 1);
lean_inc(x_28);
x_35 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_35, 0, x_28);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_mk_string_unchecked("null", 4, 4);
x_37 = l_Lean_Name_mkStr1(x_36);
lean_inc(x_37);
lean_inc(x_28);
x_38 = l_Lean_Syntax_node1(x_28, x_37, x_3);
x_39 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_28);
x_40 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_40, 0, x_28);
lean_ctor_set(x_40, 1, x_39);
lean_inc(x_28);
x_41 = l_Lean_Syntax_node2(x_28, x_37, x_40, x_4);
x_42 = lean_mk_string_unchecked("}", 1, 1);
lean_inc(x_28);
x_43 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_43, 0, x_28);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_Lean_Syntax_node4(x_28, x_33, x_35, x_38, x_41, x_43);
return x_44;
}
case 2:
{
lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_45 = lean_box(0);
x_46 = lean_unbox(x_45);
x_47 = l_Lean_SourceInfo_fromRef(x_7, x_46);
lean_dec(x_7);
x_48 = lean_mk_string_unchecked("Lean", 4, 4);
x_49 = lean_mk_string_unchecked("Parser", 6, 6);
x_50 = lean_mk_string_unchecked("Term", 4, 4);
x_51 = lean_mk_string_unchecked("strictImplicitBinder", 20, 20);
x_52 = l_Lean_Name_mkStr4(x_48, x_49, x_50, x_51);
x_53 = lean_mk_string_unchecked("⦃", 3, 1);
lean_inc(x_47);
x_54 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_54, 0, x_47);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_mk_string_unchecked("null", 4, 4);
x_56 = l_Lean_Name_mkStr1(x_55);
lean_inc(x_56);
lean_inc(x_47);
x_57 = l_Lean_Syntax_node1(x_47, x_56, x_3);
x_58 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_47);
x_59 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_59, 0, x_47);
lean_ctor_set(x_59, 1, x_58);
lean_inc(x_47);
x_60 = l_Lean_Syntax_node2(x_47, x_56, x_59, x_4);
x_61 = lean_mk_string_unchecked("⦄", 3, 1);
lean_inc(x_47);
x_62 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_62, 0, x_47);
lean_ctor_set(x_62, 1, x_61);
x_63 = l_Lean_Syntax_node4(x_47, x_52, x_54, x_57, x_60, x_62);
return x_63;
}
default: 
{
lean_object* x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_64 = lean_box(0);
x_65 = lean_unbox(x_64);
x_66 = l_Lean_SourceInfo_fromRef(x_7, x_65);
lean_dec(x_7);
x_67 = lean_mk_string_unchecked("Lean", 4, 4);
x_68 = lean_mk_string_unchecked("Parser", 6, 6);
x_69 = lean_mk_string_unchecked("Term", 4, 4);
x_70 = lean_mk_string_unchecked("instBinder", 10, 10);
x_71 = l_Lean_Name_mkStr4(x_67, x_68, x_69, x_70);
x_72 = lean_mk_string_unchecked("[", 1, 1);
lean_inc(x_66);
x_73 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_73, 0, x_66);
lean_ctor_set(x_73, 1, x_72);
x_74 = lean_mk_string_unchecked("null", 4, 4);
x_75 = l_Lean_Name_mkStr1(x_74);
x_76 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_66);
x_77 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_77, 0, x_66);
lean_ctor_set(x_77, 1, x_76);
lean_inc(x_66);
x_78 = l_Lean_Syntax_node2(x_66, x_75, x_3, x_77);
x_79 = lean_mk_string_unchecked("]", 1, 1);
lean_inc(x_66);
x_80 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_80, 0, x_66);
lean_ctor_set(x_80, 1, x_79);
x_81 = l_Lean_Syntax_node4(x_66, x_71, x_73, x_78, x_4, x_80);
return x_81;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BinderSyntaxView_mkArgument(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_box(0);
x_5 = l_Lean_replaceRef(x_2, x_4);
lean_dec(x_2);
x_6 = lean_box(0);
x_7 = lean_unbox(x_6);
x_8 = l_Lean_SourceInfo_fromRef(x_5, x_7);
lean_dec(x_5);
x_9 = lean_mk_string_unchecked("Lean", 4, 4);
x_10 = lean_mk_string_unchecked("Parser", 6, 6);
x_11 = lean_mk_string_unchecked("Term", 4, 4);
x_12 = lean_mk_string_unchecked("namedArgument", 13, 13);
x_13 = l_Lean_Name_mkStr4(x_9, x_10, x_11, x_12);
x_14 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_8);
x_15 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_8);
x_17 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_17, 0, x_8);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_8);
x_19 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_19, 0, x_8);
lean_ctor_set(x_19, 1, x_18);
lean_inc(x_3);
x_20 = l_Lean_Syntax_node5(x_8, x_13, x_15, x_3, x_17, x_3, x_19);
return x_20;
}
}
lean_object* initialize_Lean_Parser_Term(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Term(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Expr(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Util_Binder(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Parser_Term(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Term(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Expr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_instCoeTermArgument = _init_l_Lake_instCoeTermArgument();
lean_mark_persistent(l_Lake_instCoeTermArgument);
l_Lake_instCoeEllipsisArgument = _init_l_Lake_instCoeEllipsisArgument();
lean_mark_persistent(l_Lake_instCoeEllipsisArgument);
l_Lake_instCoeNamedArgumentArgument = _init_l_Lake_instCoeNamedArgumentArgument();
lean_mark_persistent(l_Lake_instCoeNamedArgumentArgument);
l_Lake_instCoeHoleTerm = _init_l_Lake_instCoeHoleTerm();
lean_mark_persistent(l_Lake_instCoeHoleTerm);
l_Lake_instCoeHoleBinderIdent = _init_l_Lake_instCoeHoleBinderIdent();
lean_mark_persistent(l_Lake_instCoeHoleBinderIdent);
l_Lake_instCoeIdentBinderIdent = _init_l_Lake_instCoeIdentBinderIdent();
lean_mark_persistent(l_Lake_instCoeIdentBinderIdent);
l_Lake_instCoeBinderIdentFunBinder = _init_l_Lake_instCoeBinderIdentFunBinder();
lean_mark_persistent(l_Lake_instCoeBinderIdentFunBinder);
l_Lake_binder = _init_l_Lake_binder();
lean_mark_persistent(l_Lake_binder);
l_Lake_instCoeBinderIdentBinder = _init_l_Lake_instCoeBinderIdentBinder();
lean_mark_persistent(l_Lake_instCoeBinderIdentBinder);
l_Lake_instCoeBracketedBinderBinder = _init_l_Lake_instCoeBracketedBinderBinder();
lean_mark_persistent(l_Lake_instCoeBracketedBinderBinder);
l_Lake_instCoeBinderDeclBinder = _init_l_Lake_instCoeBinderDeclBinder();
lean_mark_persistent(l_Lake_instCoeBinderDeclBinder);
l_Lake_instCoeDepArrowTerm = _init_l_Lake_instCoeDepArrowTerm();
lean_mark_persistent(l_Lake_instCoeDepArrowTerm);
l_Lake_instInhabitedBinderSyntaxView = _init_l_Lake_instInhabitedBinderSyntaxView();
lean_mark_persistent(l_Lake_instInhabitedBinderSyntaxView);
l_Lake_instReprBinderSyntaxView = _init_l_Lake_instReprBinderSyntaxView();
lean_mark_persistent(l_Lake_instReprBinderSyntaxView);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
