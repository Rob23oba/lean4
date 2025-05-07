// Lean compiler output
// Module: Lake.Util.Git
// Imports: Lake.Util.Proc Lake.Util.Lift
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
LEAN_EXPORT lean_object* l_Lake_GitRepo_getFilteredRemoteUrl_x3f(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_anyAux___at___Lake_Git_isFullObjectName_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_testGit(lean_object*, lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToStringGitRepo;
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instCoeFilePathGitRepo___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_captureGit_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Git_isFullObjectName___boxed(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRemoteRevision(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_captureProc_x3f(lean_object*, lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_anyAux___at___Lake_Git_isFullObjectName_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_System_FilePath_isDir(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instCoeFilePathGitRepo;
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
uint32_t lean_uint32_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_branchExists___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_cwd;
LEAN_EXPORT uint8_t l_Lake_GitRepo_getTags___lam__0(uint32_t);
LEAN_EXPORT lean_object* l_Lake_GitRepo_branchExists(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Git_filterUrl_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_clone(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRevision_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_dirExists(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_findRemoteRevision(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_hasNoDiff(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_dirExists___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_revisionExists(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevision(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_Git_isFullObjectName(lean_object*);
lean_object* l_Lake_testProc(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Git_defaultRemote;
lean_object* l_Substring_nextn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_fetch(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_findTag_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_checkoutDetach(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevision_x3f(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_getTags___lam__0___boxed(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_execGit(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Substring_prevn(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_proc(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_hasDiff(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_checkoutBranch(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Substring_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_getTags(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_getRemoteUrl_x3f(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_quietInit(lean_object*, lean_object*, lean_object*);
uint8_t l_instDecidableEqChar(uint32_t, uint32_t);
lean_object* l_String_split(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instCoeFilePathGitRepo___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_insideWorkTree(lean_object*, lean_object*);
uint32_t l_Char_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Git_upstreamBranch;
static lean_object* _init_l_Lake_Git_defaultRemote() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("origin", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lake_Git_upstreamBranch() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("master", 6, 6);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Git_filterUrl_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_2 = lean_mk_string_unchecked("git", 3, 3);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_string_utf8_byte_size(x_1);
lean_inc(x_4);
lean_inc(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
x_6 = lean_unsigned_to_nat(3u);
x_7 = l_Substring_nextn(x_5, x_6, x_3);
lean_inc(x_1);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_3);
lean_ctor_set(x_8, 2, x_7);
x_9 = lean_string_utf8_byte_size(x_2);
x_10 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_3);
lean_ctor_set(x_10, 2, x_9);
x_11 = l_Substring_beq(x_8, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_12 = lean_mk_string_unchecked(".git", 4, 4);
x_13 = lean_unsigned_to_nat(4u);
lean_inc(x_4);
x_14 = l_Substring_prevn(x_5, x_13, x_4);
lean_dec(x_5);
lean_inc(x_14);
lean_inc(x_1);
x_15 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set(x_15, 2, x_4);
x_16 = lean_string_utf8_byte_size(x_12);
x_17 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_17, 0, x_12);
lean_ctor_set(x_17, 1, x_3);
lean_ctor_set(x_17, 2, x_16);
x_18 = l_Substring_beq(x_15, x_17);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_14);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_1);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_string_utf8_extract(x_1, x_3, x_14);
lean_dec(x_14);
lean_dec(x_1);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
else
{
lean_object* x_22; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_22 = lean_box(0);
return x_22;
}
}
}
LEAN_EXPORT uint8_t l_String_anyAux___at___Lake_Git_isFullObjectName_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_string_length(x_1);
x_9 = lean_unsigned_to_nat(40u);
x_10 = lean_nat_dec_lt(x_4, x_3);
if (x_10 == 0)
{
lean_dec(x_8);
lean_dec(x_4);
return x_10;
}
else
{
uint8_t x_11; uint8_t x_12; uint32_t x_14; uint8_t x_15; lean_object* x_23; uint32_t x_24; uint8_t x_25; 
x_11 = lean_nat_dec_eq(x_8, x_9);
lean_dec(x_8);
x_14 = lean_string_utf8_get(x_2, x_4);
x_23 = lean_unsigned_to_nat(48u);
x_24 = lean_uint32_of_nat(x_23);
x_25 = lean_uint32_dec_le(x_24, x_14);
if (x_25 == 0)
{
x_15 = x_25;
goto block_22;
}
else
{
lean_object* x_26; uint32_t x_27; uint8_t x_28; 
x_26 = lean_unsigned_to_nat(57u);
x_27 = lean_uint32_of_nat(x_26);
x_28 = lean_uint32_dec_le(x_14, x_27);
x_15 = x_28;
goto block_22;
}
block_13:
{
if (x_12 == 0)
{
if (x_11 == 0)
{
goto block_7;
}
else
{
lean_dec(x_4);
return x_11;
}
}
else
{
goto block_7;
}
}
block_22:
{
if (x_15 == 0)
{
lean_object* x_16; uint32_t x_17; uint8_t x_18; 
x_16 = lean_unsigned_to_nat(97u);
x_17 = l_Char_ofNat(x_16);
x_18 = lean_uint32_dec_le(x_17, x_14);
if (x_18 == 0)
{
x_12 = x_18;
goto block_13;
}
else
{
lean_object* x_19; uint32_t x_20; uint8_t x_21; 
x_19 = lean_unsigned_to_nat(102u);
x_20 = l_Char_ofNat(x_19);
x_21 = lean_uint32_dec_le(x_14, x_20);
x_12 = x_21;
goto block_13;
}
}
else
{
goto block_7;
}
}
}
block_7:
{
lean_object* x_5; 
x_5 = lean_string_utf8_next(x_2, x_4);
lean_dec(x_4);
x_4 = x_5;
goto _start;
}
}
}
LEAN_EXPORT uint8_t l_Lake_Git_isFullObjectName(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_string_length(x_1);
x_3 = lean_unsigned_to_nat(40u);
x_4 = lean_nat_dec_eq(x_2, x_3);
lean_dec(x_2);
if (x_4 == 0)
{
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_string_utf8_byte_size(x_1);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_String_anyAux___at___Lake_Git_isFullObjectName_spec__0(x_1, x_1, x_5, x_6);
lean_dec(x_5);
if (x_7 == 0)
{
return x_4;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_box(0);
x_9 = lean_unbox(x_8);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_String_anyAux___at___Lake_Git_isFullObjectName_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_String_anyAux___at___Lake_Git_isFullObjectName_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_Git_isFullObjectName___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lake_Git_isFullObjectName(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeFilePathGitRepo___lam__0(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
static lean_object* _init_l_Lake_instCoeFilePathGitRepo() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instCoeFilePathGitRepo___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeFilePathGitRepo___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_instCoeFilePathGitRepo___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instToStringGitRepo() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instCoeFilePathGitRepo___lam__0___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_GitRepo_cwd() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(".", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_dirExists(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_System_FilePath_isDir(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_dirExists___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_GitRepo_dirExists(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_captureGit_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_4 = lean_box(1);
x_5 = lean_alloc_ctor(0, 0, 3);
x_6 = lean_unbox(x_4);
lean_ctor_set_uint8(x_5, 0, x_6);
x_7 = lean_unbox(x_4);
lean_ctor_set_uint8(x_5, 1, x_7);
x_8 = lean_unbox(x_4);
lean_ctor_set_uint8(x_5, 2, x_8);
x_9 = lean_mk_string_unchecked("git", 3, 3);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_2);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_mk_empty_array_with_capacity(x_11);
x_13 = lean_box(1);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_15, 0, x_5);
lean_ctor_set(x_15, 1, x_9);
lean_ctor_set(x_15, 2, x_1);
lean_ctor_set(x_15, 3, x_10);
lean_ctor_set(x_15, 4, x_12);
x_16 = lean_unbox(x_13);
lean_ctor_set_uint8(x_15, sizeof(void*)*5, x_16);
x_17 = lean_unbox(x_14);
lean_ctor_set_uint8(x_15, sizeof(void*)*5 + 1, x_17);
x_18 = l_Lake_captureProc_x3f(x_15, x_3);
lean_dec(x_15);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_execGit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; lean_object* x_20; 
x_5 = lean_box(1);
x_6 = lean_alloc_ctor(0, 0, 3);
x_7 = lean_unbox(x_5);
lean_ctor_set_uint8(x_6, 0, x_7);
x_8 = lean_unbox(x_5);
lean_ctor_set_uint8(x_6, 1, x_8);
x_9 = lean_unbox(x_5);
lean_ctor_set_uint8(x_6, 2, x_9);
x_10 = lean_mk_string_unchecked("git", 3, 3);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_2);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_mk_empty_array_with_capacity(x_12);
x_14 = lean_box(1);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_16, 0, x_6);
lean_ctor_set(x_16, 1, x_10);
lean_ctor_set(x_16, 2, x_1);
lean_ctor_set(x_16, 3, x_11);
lean_ctor_set(x_16, 4, x_13);
x_17 = lean_unbox(x_14);
lean_ctor_set_uint8(x_16, sizeof(void*)*5, x_17);
x_18 = lean_unbox(x_15);
lean_ctor_set_uint8(x_16, sizeof(void*)*5 + 1, x_18);
x_19 = lean_unbox(x_14);
x_20 = l_Lake_proc(x_16, x_19, x_3, x_4);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_testGit(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_4 = lean_box(1);
x_5 = lean_alloc_ctor(0, 0, 3);
x_6 = lean_unbox(x_4);
lean_ctor_set_uint8(x_5, 0, x_6);
x_7 = lean_unbox(x_4);
lean_ctor_set_uint8(x_5, 1, x_7);
x_8 = lean_unbox(x_4);
lean_ctor_set_uint8(x_5, 2, x_8);
x_9 = lean_mk_string_unchecked("git", 3, 3);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_2);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_mk_empty_array_with_capacity(x_11);
x_13 = lean_box(1);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_15, 0, x_5);
lean_ctor_set(x_15, 1, x_9);
lean_ctor_set(x_15, 2, x_1);
lean_ctor_set(x_15, 3, x_10);
lean_ctor_set(x_15, 4, x_12);
x_16 = lean_unbox(x_13);
lean_ctor_set_uint8(x_15, sizeof(void*)*5, x_16);
x_17 = lean_unbox(x_14);
lean_ctor_set_uint8(x_15, sizeof(void*)*5 + 1, x_17);
x_18 = l_Lake_testProc(x_15, x_3);
lean_dec(x_15);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_clone(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; lean_object* x_26; 
x_5 = lean_box(1);
x_6 = lean_alloc_ctor(0, 0, 3);
x_7 = lean_unbox(x_5);
lean_ctor_set_uint8(x_6, 0, x_7);
x_8 = lean_unbox(x_5);
lean_ctor_set_uint8(x_6, 1, x_8);
x_9 = lean_unbox(x_5);
lean_ctor_set_uint8(x_6, 2, x_9);
x_10 = lean_mk_string_unchecked("git", 3, 3);
x_11 = lean_mk_string_unchecked("clone", 5, 5);
x_12 = lean_unsigned_to_nat(3u);
x_13 = lean_mk_empty_array_with_capacity(x_12);
x_14 = lean_array_push(x_13, x_11);
x_15 = lean_array_push(x_14, x_1);
x_16 = lean_array_push(x_15, x_2);
x_17 = lean_box(0);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_mk_empty_array_with_capacity(x_18);
x_20 = lean_box(1);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_22, 0, x_6);
lean_ctor_set(x_22, 1, x_10);
lean_ctor_set(x_22, 2, x_16);
lean_ctor_set(x_22, 3, x_17);
lean_ctor_set(x_22, 4, x_19);
x_23 = lean_unbox(x_20);
lean_ctor_set_uint8(x_22, sizeof(void*)*5, x_23);
x_24 = lean_unbox(x_21);
lean_ctor_set_uint8(x_22, sizeof(void*)*5 + 1, x_24);
x_25 = lean_unbox(x_20);
x_26 = l_Lake_proc(x_22, x_25, x_3, x_4);
return x_26;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_quietInit(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; lean_object* x_25; 
x_4 = lean_mk_string_unchecked("init", 4, 4);
x_5 = lean_mk_string_unchecked("-q", 2, 2);
x_6 = lean_unsigned_to_nat(2u);
x_7 = lean_mk_empty_array_with_capacity(x_6);
x_8 = lean_array_push(x_7, x_4);
x_9 = lean_array_push(x_8, x_5);
x_10 = lean_box(1);
x_11 = lean_alloc_ctor(0, 0, 3);
x_12 = lean_unbox(x_10);
lean_ctor_set_uint8(x_11, 0, x_12);
x_13 = lean_unbox(x_10);
lean_ctor_set_uint8(x_11, 1, x_13);
x_14 = lean_unbox(x_10);
lean_ctor_set_uint8(x_11, 2, x_14);
x_15 = lean_mk_string_unchecked("git", 3, 3);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_1);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_mk_empty_array_with_capacity(x_17);
x_19 = lean_box(1);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_21, 0, x_11);
lean_ctor_set(x_21, 1, x_15);
lean_ctor_set(x_21, 2, x_9);
lean_ctor_set(x_21, 3, x_16);
lean_ctor_set(x_21, 4, x_18);
x_22 = lean_unbox(x_19);
lean_ctor_set_uint8(x_21, sizeof(void*)*5, x_22);
x_23 = lean_unbox(x_20);
lean_ctor_set_uint8(x_21, sizeof(void*)*5 + 1, x_23);
x_24 = lean_unbox(x_19);
x_25 = l_Lake_proc(x_21, x_24, x_2, x_3);
return x_25;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_insideWorkTree(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_22; lean_object* x_23; 
x_3 = lean_mk_string_unchecked("rev-parse", 9, 9);
x_4 = lean_mk_string_unchecked("--is-inside-work-tree", 21, 21);
x_5 = lean_unsigned_to_nat(2u);
x_6 = lean_mk_empty_array_with_capacity(x_5);
x_7 = lean_array_push(x_6, x_3);
x_8 = lean_array_push(x_7, x_4);
x_9 = lean_box(1);
x_10 = lean_alloc_ctor(0, 0, 3);
x_11 = lean_unbox(x_9);
lean_ctor_set_uint8(x_10, 0, x_11);
x_12 = lean_unbox(x_9);
lean_ctor_set_uint8(x_10, 1, x_12);
x_13 = lean_unbox(x_9);
lean_ctor_set_uint8(x_10, 2, x_13);
x_14 = lean_mk_string_unchecked("git", 3, 3);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_1);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_mk_empty_array_with_capacity(x_16);
x_18 = lean_box(1);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_20, 0, x_10);
lean_ctor_set(x_20, 1, x_14);
lean_ctor_set(x_20, 2, x_8);
lean_ctor_set(x_20, 3, x_15);
lean_ctor_set(x_20, 4, x_17);
x_21 = lean_unbox(x_18);
lean_ctor_set_uint8(x_20, sizeof(void*)*5, x_21);
x_22 = lean_unbox(x_19);
lean_ctor_set_uint8(x_20, sizeof(void*)*5 + 1, x_22);
x_23 = l_Lake_testProc(x_20, x_2);
lean_dec(x_20);
return x_23;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_fetch(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; lean_object* x_29; 
x_5 = lean_mk_string_unchecked("fetch", 5, 5);
x_6 = lean_mk_string_unchecked("--tags", 6, 6);
x_7 = lean_mk_string_unchecked("--force", 7, 7);
x_8 = lean_unsigned_to_nat(4u);
x_9 = lean_mk_empty_array_with_capacity(x_8);
x_10 = lean_array_push(x_9, x_5);
x_11 = lean_array_push(x_10, x_6);
x_12 = lean_array_push(x_11, x_7);
x_13 = lean_array_push(x_12, x_2);
x_14 = lean_box(1);
x_15 = lean_alloc_ctor(0, 0, 3);
x_16 = lean_unbox(x_14);
lean_ctor_set_uint8(x_15, 0, x_16);
x_17 = lean_unbox(x_14);
lean_ctor_set_uint8(x_15, 1, x_17);
x_18 = lean_unbox(x_14);
lean_ctor_set_uint8(x_15, 2, x_18);
x_19 = lean_mk_string_unchecked("git", 3, 3);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_1);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_mk_empty_array_with_capacity(x_21);
x_23 = lean_box(1);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_25, 0, x_15);
lean_ctor_set(x_25, 1, x_19);
lean_ctor_set(x_25, 2, x_13);
lean_ctor_set(x_25, 3, x_20);
lean_ctor_set(x_25, 4, x_22);
x_26 = lean_unbox(x_23);
lean_ctor_set_uint8(x_25, sizeof(void*)*5, x_26);
x_27 = lean_unbox(x_24);
lean_ctor_set_uint8(x_25, sizeof(void*)*5 + 1, x_27);
x_28 = lean_unbox(x_23);
x_29 = l_Lake_proc(x_25, x_28, x_3, x_4);
return x_29;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_checkoutBranch(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; lean_object* x_27; 
x_5 = lean_mk_string_unchecked("checkout", 8, 8);
x_6 = lean_mk_string_unchecked("-B", 2, 2);
x_7 = lean_unsigned_to_nat(3u);
x_8 = lean_mk_empty_array_with_capacity(x_7);
x_9 = lean_array_push(x_8, x_5);
x_10 = lean_array_push(x_9, x_6);
x_11 = lean_array_push(x_10, x_1);
x_12 = lean_box(1);
x_13 = lean_alloc_ctor(0, 0, 3);
x_14 = lean_unbox(x_12);
lean_ctor_set_uint8(x_13, 0, x_14);
x_15 = lean_unbox(x_12);
lean_ctor_set_uint8(x_13, 1, x_15);
x_16 = lean_unbox(x_12);
lean_ctor_set_uint8(x_13, 2, x_16);
x_17 = lean_mk_string_unchecked("git", 3, 3);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_2);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_mk_empty_array_with_capacity(x_19);
x_21 = lean_box(1);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_23, 0, x_13);
lean_ctor_set(x_23, 1, x_17);
lean_ctor_set(x_23, 2, x_11);
lean_ctor_set(x_23, 3, x_18);
lean_ctor_set(x_23, 4, x_20);
x_24 = lean_unbox(x_21);
lean_ctor_set_uint8(x_23, sizeof(void*)*5, x_24);
x_25 = lean_unbox(x_22);
lean_ctor_set_uint8(x_23, sizeof(void*)*5 + 1, x_25);
x_26 = lean_unbox(x_21);
x_27 = l_Lake_proc(x_23, x_26, x_3, x_4);
return x_27;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_checkoutDetach(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; lean_object* x_29; 
x_5 = lean_mk_string_unchecked("checkout", 8, 8);
x_6 = lean_mk_string_unchecked("--detach", 8, 8);
x_7 = lean_mk_string_unchecked("--", 2, 2);
x_8 = lean_unsigned_to_nat(4u);
x_9 = lean_mk_empty_array_with_capacity(x_8);
x_10 = lean_array_push(x_9, x_5);
x_11 = lean_array_push(x_10, x_6);
x_12 = lean_array_push(x_11, x_1);
x_13 = lean_array_push(x_12, x_7);
x_14 = lean_box(1);
x_15 = lean_alloc_ctor(0, 0, 3);
x_16 = lean_unbox(x_14);
lean_ctor_set_uint8(x_15, 0, x_16);
x_17 = lean_unbox(x_14);
lean_ctor_set_uint8(x_15, 1, x_17);
x_18 = lean_unbox(x_14);
lean_ctor_set_uint8(x_15, 2, x_18);
x_19 = lean_mk_string_unchecked("git", 3, 3);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_2);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_mk_empty_array_with_capacity(x_21);
x_23 = lean_box(1);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_25, 0, x_15);
lean_ctor_set(x_25, 1, x_19);
lean_ctor_set(x_25, 2, x_13);
lean_ctor_set(x_25, 3, x_20);
lean_ctor_set(x_25, 4, x_22);
x_26 = lean_unbox(x_23);
lean_ctor_set_uint8(x_25, sizeof(void*)*5, x_26);
x_27 = lean_unbox(x_24);
lean_ctor_set_uint8(x_25, sizeof(void*)*5 + 1, x_27);
x_28 = lean_unbox(x_23);
x_29 = l_Lake_proc(x_25, x_28, x_3, x_4);
return x_29;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRevision_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_26; lean_object* x_27; 
x_4 = lean_mk_string_unchecked("rev-parse", 9, 9);
x_5 = lean_mk_string_unchecked("--verify", 8, 8);
x_6 = lean_mk_string_unchecked("--end-of-options", 16, 16);
x_7 = lean_unsigned_to_nat(4u);
x_8 = lean_mk_empty_array_with_capacity(x_7);
x_9 = lean_array_push(x_8, x_4);
x_10 = lean_array_push(x_9, x_5);
x_11 = lean_array_push(x_10, x_6);
x_12 = lean_array_push(x_11, x_1);
x_13 = lean_box(1);
x_14 = lean_alloc_ctor(0, 0, 3);
x_15 = lean_unbox(x_13);
lean_ctor_set_uint8(x_14, 0, x_15);
x_16 = lean_unbox(x_13);
lean_ctor_set_uint8(x_14, 1, x_16);
x_17 = lean_unbox(x_13);
lean_ctor_set_uint8(x_14, 2, x_17);
x_18 = lean_mk_string_unchecked("git", 3, 3);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_2);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_mk_empty_array_with_capacity(x_20);
x_22 = lean_box(1);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_24, 0, x_14);
lean_ctor_set(x_24, 1, x_18);
lean_ctor_set(x_24, 2, x_12);
lean_ctor_set(x_24, 3, x_19);
lean_ctor_set(x_24, 4, x_21);
x_25 = lean_unbox(x_22);
lean_ctor_set_uint8(x_24, sizeof(void*)*5, x_25);
x_26 = lean_unbox(x_23);
lean_ctor_set_uint8(x_24, sizeof(void*)*5 + 1, x_26);
x_27 = l_Lake_captureProc_x3f(x_24, x_3);
lean_dec(x_24);
return x_27;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevision_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_26; lean_object* x_27; 
x_3 = lean_mk_string_unchecked("HEAD", 4, 4);
x_4 = lean_mk_string_unchecked("rev-parse", 9, 9);
x_5 = lean_mk_string_unchecked("--verify", 8, 8);
x_6 = lean_mk_string_unchecked("--end-of-options", 16, 16);
x_7 = lean_unsigned_to_nat(4u);
x_8 = lean_mk_empty_array_with_capacity(x_7);
x_9 = lean_array_push(x_8, x_4);
x_10 = lean_array_push(x_9, x_5);
x_11 = lean_array_push(x_10, x_6);
x_12 = lean_array_push(x_11, x_3);
x_13 = lean_box(1);
x_14 = lean_alloc_ctor(0, 0, 3);
x_15 = lean_unbox(x_13);
lean_ctor_set_uint8(x_14, 0, x_15);
x_16 = lean_unbox(x_13);
lean_ctor_set_uint8(x_14, 1, x_16);
x_17 = lean_unbox(x_13);
lean_ctor_set_uint8(x_14, 2, x_17);
x_18 = lean_mk_string_unchecked("git", 3, 3);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_1);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_mk_empty_array_with_capacity(x_20);
x_22 = lean_box(1);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_24, 0, x_14);
lean_ctor_set(x_24, 1, x_18);
lean_ctor_set(x_24, 2, x_12);
lean_ctor_set(x_24, 3, x_19);
lean_ctor_set(x_24, 4, x_21);
x_25 = lean_unbox(x_22);
lean_ctor_set_uint8(x_24, sizeof(void*)*5, x_25);
x_26 = lean_unbox(x_23);
lean_ctor_set_uint8(x_24, sizeof(void*)*5 + 1, x_26);
x_27 = l_Lake_captureProc_x3f(x_24, x_2);
lean_dec(x_24);
return x_27;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevision(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; 
x_4 = lean_mk_string_unchecked("HEAD", 4, 4);
x_5 = lean_mk_string_unchecked("rev-parse", 9, 9);
x_6 = lean_mk_string_unchecked("--verify", 8, 8);
x_7 = lean_mk_string_unchecked("--end-of-options", 16, 16);
x_8 = lean_unsigned_to_nat(4u);
x_9 = lean_mk_empty_array_with_capacity(x_8);
x_10 = lean_array_push(x_9, x_5);
x_11 = lean_array_push(x_10, x_6);
x_12 = lean_array_push(x_11, x_7);
x_13 = lean_array_push(x_12, x_4);
x_14 = lean_box(1);
x_15 = lean_alloc_ctor(0, 0, 3);
x_16 = lean_unbox(x_14);
lean_ctor_set_uint8(x_15, 0, x_16);
x_17 = lean_unbox(x_14);
lean_ctor_set_uint8(x_15, 1, x_17);
x_18 = lean_unbox(x_14);
lean_ctor_set_uint8(x_15, 2, x_18);
x_19 = lean_mk_string_unchecked("git", 3, 3);
lean_inc(x_1);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_1);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_mk_empty_array_with_capacity(x_21);
x_23 = lean_box(1);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_25, 0, x_15);
lean_ctor_set(x_25, 1, x_19);
lean_ctor_set(x_25, 2, x_13);
lean_ctor_set(x_25, 3, x_20);
lean_ctor_set(x_25, 4, x_22);
x_26 = lean_unbox(x_23);
lean_ctor_set_uint8(x_25, sizeof(void*)*5, x_26);
x_27 = lean_unbox(x_24);
lean_ctor_set_uint8(x_25, sizeof(void*)*5 + 1, x_27);
x_28 = l_Lake_captureProc_x3f(x_25, x_3);
lean_dec(x_25);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_28);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_31 = lean_ctor_get(x_28, 0);
lean_dec(x_31);
x_32 = lean_mk_string_unchecked(": could not resolve 'HEAD' to a commit; the repository may be corrupt, so you may need to remove it and try again", 113, 113);
x_33 = lean_string_append(x_1, x_32);
lean_dec(x_32);
x_34 = lean_box(3);
x_35 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_35, 0, x_33);
x_36 = lean_unbox(x_34);
lean_ctor_set_uint8(x_35, sizeof(void*)*1, x_36);
x_37 = lean_array_get_size(x_2);
x_38 = lean_array_push(x_2, x_35);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
lean_ctor_set(x_28, 0, x_39);
return x_28;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_40 = lean_ctor_get(x_28, 1);
lean_inc(x_40);
lean_dec(x_28);
x_41 = lean_mk_string_unchecked(": could not resolve 'HEAD' to a commit; the repository may be corrupt, so you may need to remove it and try again", 113, 113);
x_42 = lean_string_append(x_1, x_41);
lean_dec(x_41);
x_43 = lean_box(3);
x_44 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_44, 0, x_42);
x_45 = lean_unbox(x_43);
lean_ctor_set_uint8(x_44, sizeof(void*)*1, x_45);
x_46 = lean_array_get_size(x_2);
x_47 = lean_array_push(x_2, x_44);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_40);
return x_49;
}
}
else
{
uint8_t x_50; 
lean_dec(x_1);
x_50 = !lean_is_exclusive(x_28);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_28, 0);
lean_dec(x_51);
x_52 = lean_ctor_get(x_29, 0);
lean_inc(x_52);
lean_dec(x_29);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_2);
lean_ctor_set(x_28, 0, x_53);
return x_28;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_28, 1);
lean_inc(x_54);
lean_dec(x_28);
x_55 = lean_ctor_get(x_29, 0);
lean_inc(x_55);
lean_dec(x_29);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_2);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_54);
return x_57;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRemoteRevision(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = l_Lake_Git_isFullObjectName(x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; 
x_7 = lean_mk_string_unchecked("/", 1, 1);
x_8 = lean_string_append(x_2, x_7);
lean_dec(x_7);
x_9 = lean_string_append(x_8, x_1);
x_10 = lean_mk_string_unchecked("rev-parse", 9, 9);
x_11 = lean_mk_string_unchecked("--verify", 8, 8);
x_12 = lean_mk_string_unchecked("--end-of-options", 16, 16);
x_13 = lean_unsigned_to_nat(4u);
x_14 = lean_mk_empty_array_with_capacity(x_13);
x_15 = lean_array_push(x_14, x_10);
x_16 = lean_array_push(x_15, x_11);
x_17 = lean_array_push(x_16, x_12);
lean_inc(x_17);
x_18 = lean_array_push(x_17, x_9);
x_19 = lean_box(1);
x_20 = lean_alloc_ctor(0, 0, 3);
x_21 = lean_unbox(x_19);
lean_ctor_set_uint8(x_20, 0, x_21);
x_22 = lean_unbox(x_19);
lean_ctor_set_uint8(x_20, 1, x_22);
x_23 = lean_unbox(x_19);
lean_ctor_set_uint8(x_20, 2, x_23);
x_24 = lean_mk_string_unchecked("git", 3, 3);
lean_inc(x_3);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_3);
x_26 = lean_unsigned_to_nat(0u);
x_27 = lean_mk_empty_array_with_capacity(x_26);
x_28 = lean_box(1);
lean_inc(x_27);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_20);
x_29 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_29, 0, x_20);
lean_ctor_set(x_29, 1, x_24);
lean_ctor_set(x_29, 2, x_18);
lean_ctor_set(x_29, 3, x_25);
lean_ctor_set(x_29, 4, x_27);
x_30 = lean_unbox(x_28);
lean_ctor_set_uint8(x_29, sizeof(void*)*5, x_30);
lean_ctor_set_uint8(x_29, sizeof(void*)*5 + 1, x_6);
x_31 = l_Lake_captureProc_x3f(x_29, x_5);
lean_dec(x_29);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; 
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
lean_inc(x_1);
x_34 = lean_array_push(x_17, x_1);
x_35 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_35, 0, x_20);
lean_ctor_set(x_35, 1, x_24);
lean_ctor_set(x_35, 2, x_34);
lean_ctor_set(x_35, 3, x_25);
lean_ctor_set(x_35, 4, x_27);
x_36 = lean_unbox(x_28);
lean_ctor_set_uint8(x_35, sizeof(void*)*5, x_36);
lean_ctor_set_uint8(x_35, sizeof(void*)*5 + 1, x_6);
x_37 = l_Lake_captureProc_x3f(x_35, x_33);
lean_dec(x_35);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
if (lean_obj_tag(x_38) == 0)
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_37);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_40 = lean_ctor_get(x_37, 0);
lean_dec(x_40);
x_41 = lean_mk_string_unchecked(": revision not found '", 22, 22);
x_42 = lean_string_append(x_3, x_41);
lean_dec(x_41);
x_43 = lean_string_append(x_42, x_1);
lean_dec(x_1);
x_44 = lean_mk_string_unchecked("'", 1, 1);
x_45 = lean_string_append(x_43, x_44);
lean_dec(x_44);
x_46 = lean_box(3);
x_47 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_47, 0, x_45);
x_48 = lean_unbox(x_46);
lean_ctor_set_uint8(x_47, sizeof(void*)*1, x_48);
x_49 = lean_array_get_size(x_4);
x_50 = lean_array_push(x_4, x_47);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
lean_ctor_set(x_37, 0, x_51);
return x_37;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_52 = lean_ctor_get(x_37, 1);
lean_inc(x_52);
lean_dec(x_37);
x_53 = lean_mk_string_unchecked(": revision not found '", 22, 22);
x_54 = lean_string_append(x_3, x_53);
lean_dec(x_53);
x_55 = lean_string_append(x_54, x_1);
lean_dec(x_1);
x_56 = lean_mk_string_unchecked("'", 1, 1);
x_57 = lean_string_append(x_55, x_56);
lean_dec(x_56);
x_58 = lean_box(3);
x_59 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_59, 0, x_57);
x_60 = lean_unbox(x_58);
lean_ctor_set_uint8(x_59, sizeof(void*)*1, x_60);
x_61 = lean_array_get_size(x_4);
x_62 = lean_array_push(x_4, x_59);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_52);
return x_64;
}
}
else
{
uint8_t x_65; 
lean_dec(x_3);
lean_dec(x_1);
x_65 = !lean_is_exclusive(x_37);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_37, 0);
lean_dec(x_66);
x_67 = lean_ctor_get(x_38, 0);
lean_inc(x_67);
lean_dec(x_38);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_4);
lean_ctor_set(x_37, 0, x_68);
return x_37;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_69 = lean_ctor_get(x_37, 1);
lean_inc(x_69);
lean_dec(x_37);
x_70 = lean_ctor_get(x_38, 0);
lean_inc(x_70);
lean_dec(x_38);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_4);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_69);
return x_72;
}
}
}
else
{
uint8_t x_73; 
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_3);
lean_dec(x_1);
x_73 = !lean_is_exclusive(x_31);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_31, 0);
lean_dec(x_74);
x_75 = lean_ctor_get(x_32, 0);
lean_inc(x_75);
lean_dec(x_32);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_4);
lean_ctor_set(x_31, 0, x_76);
return x_31;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_77 = lean_ctor_get(x_31, 1);
lean_inc(x_77);
lean_dec(x_31);
x_78 = lean_ctor_get(x_32, 0);
lean_inc(x_78);
lean_dec(x_32);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_4);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_77);
return x_80;
}
}
}
else
{
lean_object* x_81; lean_object* x_82; 
lean_dec(x_3);
lean_dec(x_2);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_1);
lean_ctor_set(x_81, 1, x_4);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_5);
return x_82;
}
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_findRemoteRevision(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; 
x_6 = lean_mk_string_unchecked("fetch", 5, 5);
x_7 = lean_mk_string_unchecked("--tags", 6, 6);
x_8 = lean_mk_string_unchecked("--force", 7, 7);
x_9 = lean_unsigned_to_nat(4u);
x_10 = lean_mk_empty_array_with_capacity(x_9);
x_11 = lean_array_push(x_10, x_6);
x_12 = lean_array_push(x_11, x_7);
x_13 = lean_array_push(x_12, x_8);
lean_inc(x_3);
x_14 = lean_array_push(x_13, x_3);
x_15 = lean_box(1);
x_16 = lean_alloc_ctor(0, 0, 3);
x_17 = lean_unbox(x_15);
lean_ctor_set_uint8(x_16, 0, x_17);
x_18 = lean_unbox(x_15);
lean_ctor_set_uint8(x_16, 1, x_18);
x_19 = lean_unbox(x_15);
lean_ctor_set_uint8(x_16, 2, x_19);
x_20 = lean_mk_string_unchecked("git", 3, 3);
lean_inc(x_1);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_1);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_mk_empty_array_with_capacity(x_22);
x_24 = lean_box(1);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_26, 0, x_16);
lean_ctor_set(x_26, 1, x_20);
lean_ctor_set(x_26, 2, x_14);
lean_ctor_set(x_26, 3, x_21);
lean_ctor_set(x_26, 4, x_23);
x_27 = lean_unbox(x_24);
lean_ctor_set_uint8(x_26, sizeof(void*)*5, x_27);
x_28 = lean_unbox(x_25);
lean_ctor_set_uint8(x_26, sizeof(void*)*5 + 1, x_28);
x_29 = lean_unbox(x_24);
x_30 = l_Lake_proc(x_26, x_29, x_4, x_5);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_mk_string_unchecked("master", 6, 6);
x_35 = l_Lake_GitRepo_resolveRemoteRevision(x_34, x_3, x_1, x_33, x_32);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_30, 1);
lean_inc(x_36);
lean_dec(x_30);
x_37 = lean_ctor_get(x_31, 1);
lean_inc(x_37);
lean_dec(x_31);
x_38 = lean_ctor_get(x_2, 0);
lean_inc(x_38);
lean_dec(x_2);
x_39 = l_Lake_GitRepo_resolveRemoteRevision(x_38, x_3, x_1, x_37, x_36);
return x_39;
}
}
else
{
uint8_t x_40; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_30);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_30, 0);
lean_dec(x_41);
x_42 = !lean_is_exclusive(x_31);
if (x_42 == 0)
{
return x_30;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_31, 0);
x_44 = lean_ctor_get(x_31, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_31);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
lean_ctor_set(x_30, 0, x_45);
return x_30;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_46 = lean_ctor_get(x_30, 1);
lean_inc(x_46);
lean_dec(x_30);
x_47 = lean_ctor_get(x_31, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_31, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_49 = x_31;
} else {
 lean_dec_ref(x_31);
 x_49 = lean_box(0);
}
if (lean_is_scalar(x_49)) {
 x_50 = lean_alloc_ctor(1, 2, 0);
} else {
 x_50 = x_49;
}
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_48);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_46);
return x_51;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_branchExists(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_26; lean_object* x_27; 
x_4 = lean_mk_string_unchecked("show-ref", 8, 8);
x_5 = lean_mk_string_unchecked("--verify", 8, 8);
x_6 = lean_mk_string_unchecked("refs/heads/", 11, 11);
x_7 = lean_string_append(x_6, x_1);
x_8 = lean_unsigned_to_nat(3u);
x_9 = lean_mk_empty_array_with_capacity(x_8);
x_10 = lean_array_push(x_9, x_4);
x_11 = lean_array_push(x_10, x_5);
x_12 = lean_array_push(x_11, x_7);
x_13 = lean_box(1);
x_14 = lean_alloc_ctor(0, 0, 3);
x_15 = lean_unbox(x_13);
lean_ctor_set_uint8(x_14, 0, x_15);
x_16 = lean_unbox(x_13);
lean_ctor_set_uint8(x_14, 1, x_16);
x_17 = lean_unbox(x_13);
lean_ctor_set_uint8(x_14, 2, x_17);
x_18 = lean_mk_string_unchecked("git", 3, 3);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_2);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_mk_empty_array_with_capacity(x_20);
x_22 = lean_box(1);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_24, 0, x_14);
lean_ctor_set(x_24, 1, x_18);
lean_ctor_set(x_24, 2, x_12);
lean_ctor_set(x_24, 3, x_19);
lean_ctor_set(x_24, 4, x_21);
x_25 = lean_unbox(x_22);
lean_ctor_set_uint8(x_24, sizeof(void*)*5, x_25);
x_26 = lean_unbox(x_23);
lean_ctor_set_uint8(x_24, sizeof(void*)*5 + 1, x_26);
x_27 = l_Lake_testProc(x_24, x_3);
lean_dec(x_24);
return x_27;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_branchExists___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_GitRepo_branchExists(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_revisionExists(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_26; lean_object* x_27; 
x_4 = lean_mk_string_unchecked("rev-parse", 9, 9);
x_5 = lean_mk_string_unchecked("--verify", 8, 8);
x_6 = lean_mk_string_unchecked("^{commit}", 9, 9);
x_7 = lean_string_append(x_1, x_6);
lean_dec(x_6);
x_8 = lean_unsigned_to_nat(3u);
x_9 = lean_mk_empty_array_with_capacity(x_8);
x_10 = lean_array_push(x_9, x_4);
x_11 = lean_array_push(x_10, x_5);
x_12 = lean_array_push(x_11, x_7);
x_13 = lean_box(1);
x_14 = lean_alloc_ctor(0, 0, 3);
x_15 = lean_unbox(x_13);
lean_ctor_set_uint8(x_14, 0, x_15);
x_16 = lean_unbox(x_13);
lean_ctor_set_uint8(x_14, 1, x_16);
x_17 = lean_unbox(x_13);
lean_ctor_set_uint8(x_14, 2, x_17);
x_18 = lean_mk_string_unchecked("git", 3, 3);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_2);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_mk_empty_array_with_capacity(x_20);
x_22 = lean_box(1);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_24, 0, x_14);
lean_ctor_set(x_24, 1, x_18);
lean_ctor_set(x_24, 2, x_12);
lean_ctor_set(x_24, 3, x_19);
lean_ctor_set(x_24, 4, x_21);
x_25 = lean_unbox(x_22);
lean_ctor_set_uint8(x_24, sizeof(void*)*5, x_25);
x_26 = lean_unbox(x_23);
lean_ctor_set_uint8(x_24, sizeof(void*)*5 + 1, x_26);
x_27 = l_Lake_testProc(x_24, x_3);
lean_dec(x_24);
return x_27;
}
}
LEAN_EXPORT uint8_t l_Lake_GitRepo_getTags___lam__0(uint32_t x_1) {
_start:
{
lean_object* x_2; uint32_t x_3; uint8_t x_4; 
x_2 = lean_unsigned_to_nat(10u);
x_3 = l_Char_ofNat(x_2);
x_4 = l_instDecidableEqChar(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getTags(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_3 = lean_mk_string_unchecked("tag", 3, 3);
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_mk_empty_array_with_capacity(x_4);
x_6 = lean_array_push(x_5, x_3);
x_7 = lean_box(1);
x_8 = lean_alloc_ctor(0, 0, 3);
x_9 = lean_unbox(x_7);
lean_ctor_set_uint8(x_8, 0, x_9);
x_10 = lean_unbox(x_7);
lean_ctor_set_uint8(x_8, 1, x_10);
x_11 = lean_unbox(x_7);
lean_ctor_set_uint8(x_8, 2, x_11);
x_12 = lean_mk_string_unchecked("git", 3, 3);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_1);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_mk_empty_array_with_capacity(x_14);
x_16 = lean_box(1);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_18, 0, x_8);
lean_ctor_set(x_18, 1, x_12);
lean_ctor_set(x_18, 2, x_6);
lean_ctor_set(x_18, 3, x_13);
lean_ctor_set(x_18, 4, x_15);
x_19 = lean_unbox(x_16);
lean_ctor_set_uint8(x_18, sizeof(void*)*5, x_19);
x_20 = lean_unbox(x_17);
lean_ctor_set_uint8(x_18, sizeof(void*)*5 + 1, x_20);
x_21 = l_Lake_captureProc_x3f(x_18, x_2);
lean_dec(x_18);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_21, 0);
lean_dec(x_24);
x_25 = lean_box(0);
lean_ctor_set(x_21, 0, x_25);
return x_21;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_dec(x_21);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_21);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_21, 0);
lean_dec(x_30);
x_31 = lean_ctor_get(x_22, 0);
lean_inc(x_31);
lean_dec(x_22);
x_32 = lean_alloc_closure((void*)(l_Lake_GitRepo_getTags___lam__0___boxed), 1, 0);
x_33 = l_String_split(x_31, x_32);
lean_dec(x_31);
lean_ctor_set(x_21, 0, x_33);
return x_21;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_34 = lean_ctor_get(x_21, 1);
lean_inc(x_34);
lean_dec(x_21);
x_35 = lean_ctor_get(x_22, 0);
lean_inc(x_35);
lean_dec(x_22);
x_36 = lean_alloc_closure((void*)(l_Lake_GitRepo_getTags___lam__0___boxed), 1, 0);
x_37 = l_String_split(x_35, x_36);
lean_dec(x_35);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_34);
return x_38;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getTags___lam__0___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Lake_GitRepo_getTags___lam__0(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_findTag_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_26; lean_object* x_27; 
x_4 = lean_mk_string_unchecked("describe", 8, 8);
x_5 = lean_mk_string_unchecked("--tags", 6, 6);
x_6 = lean_mk_string_unchecked("--exact-match", 13, 13);
x_7 = lean_unsigned_to_nat(4u);
x_8 = lean_mk_empty_array_with_capacity(x_7);
x_9 = lean_array_push(x_8, x_4);
x_10 = lean_array_push(x_9, x_5);
x_11 = lean_array_push(x_10, x_6);
x_12 = lean_array_push(x_11, x_1);
x_13 = lean_box(1);
x_14 = lean_alloc_ctor(0, 0, 3);
x_15 = lean_unbox(x_13);
lean_ctor_set_uint8(x_14, 0, x_15);
x_16 = lean_unbox(x_13);
lean_ctor_set_uint8(x_14, 1, x_16);
x_17 = lean_unbox(x_13);
lean_ctor_set_uint8(x_14, 2, x_17);
x_18 = lean_mk_string_unchecked("git", 3, 3);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_2);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_mk_empty_array_with_capacity(x_20);
x_22 = lean_box(1);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_24, 0, x_14);
lean_ctor_set(x_24, 1, x_18);
lean_ctor_set(x_24, 2, x_12);
lean_ctor_set(x_24, 3, x_19);
lean_ctor_set(x_24, 4, x_21);
x_25 = lean_unbox(x_22);
lean_ctor_set_uint8(x_24, sizeof(void*)*5, x_25);
x_26 = lean_unbox(x_23);
lean_ctor_set_uint8(x_24, sizeof(void*)*5 + 1, x_26);
x_27 = l_Lake_captureProc_x3f(x_24, x_3);
lean_dec(x_24);
return x_27;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getRemoteUrl_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_24; lean_object* x_25; 
x_4 = lean_mk_string_unchecked("remote", 6, 6);
x_5 = lean_mk_string_unchecked("get-url", 7, 7);
x_6 = lean_unsigned_to_nat(3u);
x_7 = lean_mk_empty_array_with_capacity(x_6);
x_8 = lean_array_push(x_7, x_4);
x_9 = lean_array_push(x_8, x_5);
x_10 = lean_array_push(x_9, x_1);
x_11 = lean_box(1);
x_12 = lean_alloc_ctor(0, 0, 3);
x_13 = lean_unbox(x_11);
lean_ctor_set_uint8(x_12, 0, x_13);
x_14 = lean_unbox(x_11);
lean_ctor_set_uint8(x_12, 1, x_14);
x_15 = lean_unbox(x_11);
lean_ctor_set_uint8(x_12, 2, x_15);
x_16 = lean_mk_string_unchecked("git", 3, 3);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_2);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_mk_empty_array_with_capacity(x_18);
x_20 = lean_box(1);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_22, 0, x_12);
lean_ctor_set(x_22, 1, x_16);
lean_ctor_set(x_22, 2, x_10);
lean_ctor_set(x_22, 3, x_17);
lean_ctor_set(x_22, 4, x_19);
x_23 = lean_unbox(x_20);
lean_ctor_set_uint8(x_22, sizeof(void*)*5, x_23);
x_24 = lean_unbox(x_21);
lean_ctor_set_uint8(x_22, sizeof(void*)*5 + 1, x_24);
x_25 = l_Lake_captureProc_x3f(x_22, x_3);
lean_dec(x_22);
return x_25;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getFilteredRemoteUrl_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; 
x_4 = lean_mk_string_unchecked("remote", 6, 6);
x_5 = lean_mk_string_unchecked("get-url", 7, 7);
x_6 = lean_unsigned_to_nat(3u);
x_7 = lean_mk_empty_array_with_capacity(x_6);
x_8 = lean_array_push(x_7, x_4);
x_9 = lean_array_push(x_8, x_5);
x_10 = lean_array_push(x_9, x_1);
x_11 = lean_box(1);
x_12 = lean_alloc_ctor(0, 0, 3);
x_13 = lean_unbox(x_11);
lean_ctor_set_uint8(x_12, 0, x_13);
x_14 = lean_unbox(x_11);
lean_ctor_set_uint8(x_12, 1, x_14);
x_15 = lean_unbox(x_11);
lean_ctor_set_uint8(x_12, 2, x_15);
x_16 = lean_mk_string_unchecked("git", 3, 3);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_2);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_mk_empty_array_with_capacity(x_18);
x_20 = lean_box(1);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_22, 0, x_12);
lean_ctor_set(x_22, 1, x_16);
lean_ctor_set(x_22, 2, x_10);
lean_ctor_set(x_22, 3, x_17);
lean_ctor_set(x_22, 4, x_19);
x_23 = lean_unbox(x_20);
lean_ctor_set_uint8(x_22, sizeof(void*)*5, x_23);
x_24 = lean_unbox(x_21);
lean_ctor_set_uint8(x_22, sizeof(void*)*5 + 1, x_24);
x_25 = l_Lake_captureProc_x3f(x_22, x_3);
lean_dec(x_22);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
if (lean_obj_tag(x_26) == 0)
{
return x_25;
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_25);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_25, 0);
lean_dec(x_28);
x_29 = lean_ctor_get(x_26, 0);
lean_inc(x_29);
lean_dec(x_26);
x_30 = l_Lake_Git_filterUrl_x3f(x_29);
lean_ctor_set(x_25, 0, x_30);
return x_25;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_25, 1);
lean_inc(x_31);
lean_dec(x_25);
x_32 = lean_ctor_get(x_26, 0);
lean_inc(x_32);
lean_dec(x_26);
x_33 = l_Lake_Git_filterUrl_x3f(x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_31);
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_hasNoDiff(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_22; lean_object* x_23; 
x_3 = lean_mk_string_unchecked("diff", 4, 4);
x_4 = lean_mk_string_unchecked("--exit-code", 11, 11);
x_5 = lean_unsigned_to_nat(2u);
x_6 = lean_mk_empty_array_with_capacity(x_5);
x_7 = lean_array_push(x_6, x_3);
x_8 = lean_array_push(x_7, x_4);
x_9 = lean_box(1);
x_10 = lean_alloc_ctor(0, 0, 3);
x_11 = lean_unbox(x_9);
lean_ctor_set_uint8(x_10, 0, x_11);
x_12 = lean_unbox(x_9);
lean_ctor_set_uint8(x_10, 1, x_12);
x_13 = lean_unbox(x_9);
lean_ctor_set_uint8(x_10, 2, x_13);
x_14 = lean_mk_string_unchecked("git", 3, 3);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_1);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_mk_empty_array_with_capacity(x_16);
x_18 = lean_box(1);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_20, 0, x_10);
lean_ctor_set(x_20, 1, x_14);
lean_ctor_set(x_20, 2, x_8);
lean_ctor_set(x_20, 3, x_15);
lean_ctor_set(x_20, 4, x_17);
x_21 = lean_unbox(x_18);
lean_ctor_set_uint8(x_20, sizeof(void*)*5, x_21);
x_22 = lean_unbox(x_19);
lean_ctor_set_uint8(x_20, sizeof(void*)*5 + 1, x_22);
x_23 = l_Lake_testProc(x_20, x_2);
lean_dec(x_20);
return x_23;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_hasDiff(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_3 = lean_mk_string_unchecked("diff", 4, 4);
x_4 = lean_mk_string_unchecked("--exit-code", 11, 11);
x_5 = lean_unsigned_to_nat(2u);
x_6 = lean_mk_empty_array_with_capacity(x_5);
x_7 = lean_array_push(x_6, x_3);
x_8 = lean_array_push(x_7, x_4);
x_9 = lean_box(1);
x_10 = lean_alloc_ctor(0, 0, 3);
x_11 = lean_unbox(x_9);
lean_ctor_set_uint8(x_10, 0, x_11);
x_12 = lean_unbox(x_9);
lean_ctor_set_uint8(x_10, 1, x_12);
x_13 = lean_unbox(x_9);
lean_ctor_set_uint8(x_10, 2, x_13);
x_14 = lean_mk_string_unchecked("git", 3, 3);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_1);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_mk_empty_array_with_capacity(x_16);
x_18 = lean_box(1);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_20, 0, x_10);
lean_ctor_set(x_20, 1, x_14);
lean_ctor_set(x_20, 2, x_8);
lean_ctor_set(x_20, 3, x_15);
lean_ctor_set(x_20, 4, x_17);
x_21 = lean_unbox(x_18);
lean_ctor_set_uint8(x_20, sizeof(void*)*5, x_21);
x_22 = lean_unbox(x_19);
lean_ctor_set_uint8(x_20, sizeof(void*)*5 + 1, x_22);
x_23 = l_Lake_testProc(x_20, x_2);
lean_dec(x_20);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_unbox(x_24);
lean_dec(x_24);
if (x_25 == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_23);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_23, 0);
lean_dec(x_27);
lean_ctor_set(x_23, 0, x_18);
return x_23;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_23, 1);
lean_inc(x_28);
lean_dec(x_23);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_18);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
else
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_23);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_23, 0);
lean_dec(x_31);
lean_ctor_set(x_23, 0, x_19);
return x_23;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_23, 1);
lean_inc(x_32);
lean_dec(x_23);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_19);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
lean_object* initialize_Lake_Util_Proc(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_Lift(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Util_Git(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Util_Proc(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Lift(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_Git_defaultRemote = _init_l_Lake_Git_defaultRemote();
lean_mark_persistent(l_Lake_Git_defaultRemote);
l_Lake_Git_upstreamBranch = _init_l_Lake_Git_upstreamBranch();
lean_mark_persistent(l_Lake_Git_upstreamBranch);
l_Lake_instCoeFilePathGitRepo = _init_l_Lake_instCoeFilePathGitRepo();
lean_mark_persistent(l_Lake_instCoeFilePathGitRepo);
l_Lake_instToStringGitRepo = _init_l_Lake_instToStringGitRepo();
lean_mark_persistent(l_Lake_instToStringGitRepo);
l_Lake_GitRepo_cwd = _init_l_Lake_GitRepo_cwd();
lean_mark_persistent(l_Lake_GitRepo_cwd);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
