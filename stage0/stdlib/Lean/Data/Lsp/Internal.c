// Lean compiler output
// Module: Lean.Data.Lsp.Internal
// Imports: Lean.Expr Lean.Data.Lsp.Basic Lean.Data.JsonRpc Std.Data.TreeMap
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
lean_object* l_Lean_JsonNumber_fromNat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRefInfo___lam__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_toJson(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_398_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instOrdRefIdent;
lean_object* l_Lean_Json_getObj_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Json_getObjValAs_x3f___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2193__spec__0_spec__0_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM___at___Lean_RBNode_foldM___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2193__spec__0_spec__5_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instInhabitedRefIdent;
lean_object* l_Lean_Json_compress(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2299__spec__2_spec__2(size_t, size_t, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonModuleRefs___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapTR_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
lean_object* l_Lean_Json_getObjValAs_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanQueryModuleParams____x40_Lean_Data_Lsp_Internal___hyg_3101__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instForInModuleRefsProdRefIdentRefInfo___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2299__spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_instToJsonRefIdentJsonRepr;
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonOpenNamespace____x40_Lean_Data_Lsp_Internal___hyg_2804_(lean_object*);
lean_object* l_Except_instMonad___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRefInfo___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Json_getObjValAs_x3f___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2193__spec__0_spec__0_spec__0_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanIdentifier____x40_Lean_Data_Lsp_Internal___hyg_3432_(lean_object*);
lean_object* l_Except_pure(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanQueryModuleResponse____x40_Lean_Data_Lsp_Internal___hyg_3583__spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonOpenNamespace___lam__0____x40_Lean_Data_Lsp_Internal___hyg_2624____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonOpenNamespace;
lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanModuleQuery;
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2299_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_fromJsonRepr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instInhabitedLeanQueryModuleResponse;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanIleanInfoParams;
lean_object* l_Array_mapMUnsafe_map___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Basic_0__Lean_Lsp_fromJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1614__spec__0_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanStaleDependencyParams____x40_Lean_Data_Lsp_Internal___hyg_2481_(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanQueryModuleResponse____x40_Lean_Data_Lsp_Internal___hyg_3516__spec__0_spec__1(size_t, size_t, lean_object*);
lean_object* l_Except_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanQueryModuleParams;
uint64_t lean_string_hash(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanQueryModuleResponse____x40_Lean_Data_Lsp_Internal___hyg_3516_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonModuleRefs;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2299__spec__1___lam__0___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams___lam__0____x40_Lean_Data_Lsp_Internal___hyg_2193_(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanStaleDependencyParams;
lean_object* l_Lean_instFromJsonOption___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanIdentifier;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2299__spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonOpenNamespace____x40_Lean_Data_Lsp_Internal___hyg_2804__spec__0(size_t, size_t, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Except_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_hashRefIdent____x40_Lean_Data_Lsp_Internal___hyg_158_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRefInfo___lam__1(lean_object*);
lean_object* l_id___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2193__spec__0_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___List_mapTR_loop___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2299__spec__5_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2299__spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonRefInfo___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanQueryModuleResponse____x40_Lean_Data_Lsp_Internal___hyg_3516__spec__0_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_RefInfo_instInhabitedLocation;
LEAN_EXPORT uint8_t l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_ordRefIdent____x40_Lean_Data_Lsp_Internal___hyg_232_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanQueryModuleResponse;
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2299__spec__1___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanModuleQuery;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2193__spec__0_spec__3___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instForInModuleRefsProdRefIdentRefInfo___lam__1(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanQueryModuleParams____x40_Lean_Data_Lsp_Internal___hyg_3101__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Except_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanStaleDependencyParams;
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanQueryModuleParams____x40_Lean_Data_Lsp_Internal___hyg_3207_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonOpenNamespace___lam__0____x40_Lean_Data_Lsp_Internal___hyg_2624_(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanQueryModuleParams____x40_Lean_Data_Lsp_Internal___hyg_3207__spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonOpenNamespace____x40_Lean_Data_Lsp_Internal___hyg_2624_(lean_object*);
lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Basic_0__Lean_Lsp_fromJsonChangeAnnotation____x40_Lean_Data_Lsp_Basic___hyg_2784__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_RefInfo_instToJsonParentDecl;
lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Basic_0__Lean_Lsp_fromJsonResolveSupport____x40_Lean_Data_Lsp_Basic___hyg_7139__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonModuleRefs___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanModuleQuery____x40_Lean_Data_Lsp_Internal___hyg_2922__spec__0_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_toJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_578_(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanModuleQuery____x40_Lean_Data_Lsp_Internal___hyg_2922__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRefInfo___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonModuleRefs___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Json_getObjValAs_x3f___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2193__spec__0_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2299__spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanQueryModuleParams;
lean_object* l_Lean_Json_getObjValD(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanQueryModuleResponse____x40_Lean_Data_Lsp_Internal___hyg_3583__spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanQueryModuleParams____x40_Lean_Data_Lsp_Internal___hyg_3101_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonOpenNamespace;
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanQueryModuleResponse____x40_Lean_Data_Lsp_Internal___hyg_3516__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2193__spec__0_spec__3(size_t, size_t, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_instFromJsonArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanIleanInfoParams;
LEAN_EXPORT lean_object* l_Lean_Lsp_instForInModuleRefsProdRefIdentRefInfo___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonOpenNamespace___lam__1____x40_Lean_Data_Lsp_Internal___hyg_2624_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_getObjValAs_x3f___at___IO_FS_Stream_readMessage_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2299__spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanModuleQuery____x40_Lean_Data_Lsp_Internal___hyg_3028__spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonRefInfo;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2299__spec__5(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2193__spec__0_spec__3___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanModuleQuery____x40_Lean_Data_Lsp_Internal___hyg_3028_(lean_object*);
lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Basic_0__Lean_Lsp_fromJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1614__spec__0(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_toJsonRepr(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2193__spec__0_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanImportClosureParams____x40_Lean_Data_Lsp_Internal___hyg_2431_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_fromJson_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanQueryModuleResponse;
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanStaleDependencyParams____x40_Lean_Data_Lsp_Internal___hyg_2548_(lean_object*);
lean_object* l_Except_orElseLazy___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonOpenNamespace___lam__1____x40_Lean_Data_Lsp_Internal___hyg_2624____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_beqRefIdent____x40_Lean_Data_Lsp_Internal___hyg_45_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRefInfo___lam__2(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr___lam__1____x40_Lean_Data_Lsp_Internal___hyg_398____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instHashableRefIdent;
lean_object* l_Lean_instFromJsonJson___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2299__spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonModuleRefs;
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanModuleQuery____x40_Lean_Data_Lsp_Internal___hyg_2922_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instModuleRefsEmptyCollection;
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2193__spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRefInfo;
lean_object* l_Lean_Json_parseTagged(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonOpenNamespace____x40_Lean_Data_Lsp_Internal___hyg_2804__spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanQueryModuleResponse____x40_Lean_Data_Lsp_Internal___hyg_3516__spec__0_spec__1_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanQueryModuleParams____x40_Lean_Data_Lsp_Internal___hyg_3101__spec__0_spec__0(size_t, size_t, lean_object*);
lean_object* l___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonRange____x40_Lean_Data_Lsp_Basic___hyg_615_(lean_object*);
LEAN_EXPORT uint8_t l_Array_mapMUnsafe_map___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonOpenNamespace____x40_Lean_Data_Lsp_Internal___hyg_2804__spec__0___lam__0(lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Except_instMonad___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonOpenNamespace____x40_Lean_Data_Lsp_Internal___hyg_2804__spec__0___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanQueryModuleParams____x40_Lean_Data_Lsp_Internal___hyg_3207__spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_ordRefIdent____x40_Lean_Data_Lsp_Internal___hyg_232____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonOpenNamespace____x40_Lean_Data_Lsp_Internal___hyg_2624__spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2193__spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2193__spec__0(lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefInfo_toJsonParentDecl____x40_Lean_Data_Lsp_Internal___hyg_851_(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanQueryModuleResponse____x40_Lean_Data_Lsp_Internal___hyg_3516__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___Lean_Json_opt___at_____private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1558__spec__0_spec__0(size_t, size_t, lean_object*);
lean_object* l_Except_instMonad___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanIdentifier;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonRefInfo___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_beqRefIdent____x40_Lean_Data_Lsp_Internal___hyg_45____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIdentifier____x40_Lean_Data_Lsp_Internal___hyg_3287__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr___lam__1____x40_Lean_Data_Lsp_Internal___hyg_398_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr___lam__0____x40_Lean_Data_Lsp_Internal___hyg_398____boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2299__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2193__spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_String_toName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonModuleRefs___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instBEqRefIdent;
lean_object* l_Std_DTreeMap_Internal_Impl_insert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanQueryModuleResponse____x40_Lean_Data_Lsp_Internal___hyg_3583_(lean_object*);
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams___lam__0____x40_Lean_Data_Lsp_Internal___hyg_2193____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr___lam__0____x40_Lean_Data_Lsp_Internal___hyg_398_(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonOpenNamespace____x40_Lean_Data_Lsp_Internal___hyg_2624__spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_getNat_x3f(lean_object*);
lean_object* l_List_flatMapTR_go___at_____private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonPosition____x40_Lean_Data_Lsp_Basic___hyg_221__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanQueryModuleResponse____x40_Lean_Data_Lsp_Internal___hyg_3583__spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_foldM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRefInfo___lam__0(lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIdentifier____x40_Lean_Data_Lsp_Internal___hyg_3287__spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIdentifier____x40_Lean_Data_Lsp_Internal___hyg_3287_(lean_object*);
lean_object* lean_array_mk(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanQueryModuleResponse____x40_Lean_Data_Lsp_Internal___hyg_3516__spec__0_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_instFromJson;
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Json_getObjValAs_x3f___at___IO_FS_Stream_readMessage_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanModuleQuery____x40_Lean_Data_Lsp_Internal___hyg_3028__spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_List_appendTR(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanQueryModuleResponse____x40_Lean_Data_Lsp_Internal___hyg_3583__spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2193_(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanQueryModuleResponse____x40_Lean_Data_Lsp_Internal___hyg_3583__spec__1_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2193__spec__0_spec__0(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonResolveSupport____x40_Lean_Data_Lsp_Basic___hyg_7206__spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanQueryModuleResponse____x40_Lean_Data_Lsp_Internal___hyg_3516__spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Json_getObjValAs_x3f___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2193__spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonModuleRefs___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanModuleQuery____x40_Lean_Data_Lsp_Internal___hyg_2922__spec__0(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanQueryModuleResponse____x40_Lean_Data_Lsp_Internal___hyg_3516__spec__0___boxed(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanQueryModuleResponse____x40_Lean_Data_Lsp_Internal___hyg_3583__spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_parse(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2193__spec__0_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanImportClosureParams;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanImportClosureParams____x40_Lean_Data_Lsp_Internal___hyg_2364_(lean_object*);
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_instToJson;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2299__spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonRefInfo___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instForInModuleRefsProdRefIdentRefInfo(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanModuleQuery____x40_Lean_Data_Lsp_Internal___hyg_2922__spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanQueryModuleParams____x40_Lean_Data_Lsp_Internal___hyg_3101__spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanImportClosureParams;
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_hashRefIdent____x40_Lean_Data_Lsp_Internal___hyg_158____boxed(lean_object*);
lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Basic_0__Lean_Lsp_fromJsonPosition____x40_Lean_Data_Lsp_Basic___hyg_273__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonRefInfo___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_beqRefIdent____x40_Lean_Data_Lsp_Internal___hyg_45_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
x_3 = x_10;
x_4 = x_11;
x_5 = x_12;
x_6 = x_13;
goto block_9;
}
else
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_box(0);
x_15 = lean_unbox(x_14);
return x_15;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_box(0);
x_17 = lean_unbox(x_16);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_1, 0);
x_19 = lean_ctor_get(x_1, 1);
x_20 = lean_ctor_get(x_2, 0);
x_21 = lean_ctor_get(x_2, 1);
x_3 = x_18;
x_4 = x_19;
x_5 = x_20;
x_6 = x_21;
goto block_9;
}
}
block_9:
{
uint8_t x_7; 
x_7 = lean_string_dec_eq(x_3, x_5);
if (x_7 == 0)
{
return x_7;
}
else
{
uint8_t x_8; 
x_8 = lean_string_dec_eq(x_4, x_6);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_beqRefIdent____x40_Lean_Data_Lsp_Internal___hyg_45____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_beqRefIdent____x40_Lean_Data_Lsp_Internal___hyg_45_(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Lsp_instBEqRefIdent() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_beqRefIdent____x40_Lean_Data_Lsp_Internal___hyg_45____boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT uint64_t l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_hashRefIdent____x40_Lean_Data_Lsp_Internal___hyg_158_(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint64_t x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_uint64_of_nat(x_4);
x_6 = lean_string_hash(x_2);
x_7 = lean_uint64_mix_hash(x_5, x_6);
x_8 = lean_string_hash(x_3);
x_9 = lean_uint64_mix_hash(x_7, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_uint64_of_nat(x_12);
x_14 = lean_string_hash(x_10);
x_15 = lean_uint64_mix_hash(x_13, x_14);
x_16 = lean_string_hash(x_11);
x_17 = lean_uint64_mix_hash(x_15, x_16);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_hashRefIdent____x40_Lean_Data_Lsp_Internal___hyg_158____boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_hashRefIdent____x40_Lean_Data_Lsp_Internal___hyg_158_(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instHashableRefIdent() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_hashRefIdent____x40_Lean_Data_Lsp_Internal___hyg_158____boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_instInhabitedRefIdent() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_mk_string_unchecked("", 0, 0);
lean_inc(x_1);
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_ordRefIdent____x40_Lean_Data_Lsp_Internal___hyg_232_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_1, 0);
x_23 = lean_ctor_get(x_1, 1);
x_24 = lean_ctor_get(x_2, 0);
x_25 = lean_ctor_get(x_2, 1);
x_3 = x_22;
x_4 = x_23;
x_5 = x_24;
x_6 = x_25;
goto block_21;
}
else
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_box(0);
x_27 = lean_unbox(x_26);
return x_27;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_box(2);
x_29 = lean_unbox(x_28);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_1, 0);
x_31 = lean_ctor_get(x_1, 1);
x_32 = lean_ctor_get(x_2, 0);
x_33 = lean_ctor_get(x_2, 1);
x_3 = x_30;
x_4 = x_31;
x_5 = x_32;
x_6 = x_33;
goto block_21;
}
}
block_21:
{
uint8_t x_7; 
x_7 = lean_string_dec_lt(x_3, x_5);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = lean_string_dec_eq(x_3, x_5);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_box(2);
x_10 = lean_unbox(x_9);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = lean_string_dec_lt(x_4, x_6);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = lean_string_dec_eq(x_4, x_6);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_box(2);
x_14 = lean_unbox(x_13);
return x_14;
}
else
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_box(1);
x_16 = lean_unbox(x_15);
return x_16;
}
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_box(0);
x_18 = lean_unbox(x_17);
return x_18;
}
}
}
else
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_box(0);
x_20 = lean_unbox(x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_ordRefIdent____x40_Lean_Data_Lsp_Internal___hyg_232____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_ordRefIdent____x40_Lean_Data_Lsp_Internal___hyg_232_(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Lsp_instOrdRefIdent() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_ordRefIdent____x40_Lean_Data_Lsp_Internal___hyg_232____boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr___lam__0____x40_Lean_Data_Lsp_Internal___hyg_398_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_mk_string_unchecked("no inductive constructor matched", 32, 32);
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr___lam__1____x40_Lean_Data_Lsp_Internal___hyg_398_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_7 = lean_mk_string_unchecked("c", 1, 1);
x_8 = lean_mk_string_unchecked("n", 1, 1);
x_9 = l_Lean_Name_mkStr1(x_8);
x_10 = lean_mk_empty_array_with_capacity(x_1);
x_11 = lean_array_push(x_10, x_2);
x_12 = lean_array_push(x_11, x_9);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = l_Lean_Json_parseTagged(x_3, x_7, x_1, x_13);
lean_dec(x_13);
lean_dec(x_7);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
lean_dec(x_5);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = l_Except_orElseLazy___redArg(x_14, x_4);
lean_dec(x_14);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = l_Except_orElseLazy___redArg(x_18, x_4);
lean_dec(x_18);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_14, 0);
lean_inc(x_20);
lean_dec(x_14);
x_21 = lean_unsigned_to_nat(0u);
lean_inc(x_5);
x_22 = lean_array_get(x_5, x_20, x_21);
x_23 = l_Lean_Json_getStr_x3f(x_22);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
lean_dec(x_20);
lean_dec(x_5);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = l_Except_orElseLazy___redArg(x_23, x_4);
lean_dec(x_23);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_23, 0);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = l_Except_orElseLazy___redArg(x_27, x_4);
lean_dec(x_27);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_23, 0);
lean_inc(x_29);
lean_dec(x_23);
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_array_get(x_5, x_20, x_30);
lean_dec(x_20);
x_32 = l_Lean_Json_getStr_x3f(x_31);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
lean_dec(x_29);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = l_Except_orElseLazy___redArg(x_32, x_4);
lean_dec(x_32);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_32, 0);
lean_inc(x_35);
lean_dec(x_32);
x_36 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_36, 0, x_35);
x_37 = l_Except_orElseLazy___redArg(x_36, x_4);
lean_dec(x_36);
return x_37;
}
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_32);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_32, 0);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_29);
lean_ctor_set(x_40, 1, x_39);
lean_ctor_set(x_32, 0, x_40);
x_41 = l_Except_orElseLazy___redArg(x_32, x_4);
lean_dec(x_32);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_32, 0);
lean_inc(x_42);
lean_dec(x_32);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_29);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
x_45 = l_Except_orElseLazy___redArg(x_44, x_4);
lean_dec(x_44);
return x_45;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_398_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr___lam__0____x40_Lean_Data_Lsp_Internal___hyg_398____boxed), 1, 0);
x_3 = lean_box(0);
x_4 = lean_mk_string_unchecked("f", 1, 1);
x_5 = lean_unsigned_to_nat(2u);
x_6 = lean_mk_string_unchecked("m", 1, 1);
x_7 = l_Lean_Name_mkStr1(x_6);
lean_inc(x_1);
lean_inc(x_7);
x_8 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr___lam__1____x40_Lean_Data_Lsp_Internal___hyg_398____boxed), 6, 5);
lean_closure_set(x_8, 0, x_5);
lean_closure_set(x_8, 1, x_7);
lean_closure_set(x_8, 2, x_1);
lean_closure_set(x_8, 3, x_2);
lean_closure_set(x_8, 4, x_3);
x_9 = lean_mk_string_unchecked("i", 1, 1);
x_10 = l_Lean_Name_mkStr1(x_9);
x_11 = lean_mk_empty_array_with_capacity(x_5);
x_12 = lean_array_push(x_11, x_7);
x_13 = lean_array_push(x_12, x_10);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = l_Lean_Json_parseTagged(x_1, x_4, x_5, x_14);
lean_dec(x_14);
lean_dec(x_4);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = l_Except_orElseLazy___redArg(x_15, x_8);
lean_dec(x_15);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = l_Except_orElseLazy___redArg(x_19, x_8);
lean_dec(x_19);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_15, 0);
lean_inc(x_21);
lean_dec(x_15);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_array_get(x_3, x_21, x_22);
x_24 = l_Lean_Json_getStr_x3f(x_23);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
lean_dec(x_21);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = l_Except_orElseLazy___redArg(x_24, x_8);
lean_dec(x_24);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_24, 0);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = l_Except_orElseLazy___redArg(x_28, x_8);
lean_dec(x_28);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_24, 0);
lean_inc(x_30);
lean_dec(x_24);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_array_get(x_3, x_21, x_31);
lean_dec(x_21);
x_33 = l_Lean_Json_getStr_x3f(x_32);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
lean_dec(x_30);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = l_Except_orElseLazy___redArg(x_33, x_8);
lean_dec(x_33);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_33, 0);
lean_inc(x_36);
lean_dec(x_33);
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = l_Except_orElseLazy___redArg(x_37, x_8);
lean_dec(x_37);
return x_38;
}
}
else
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_33);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_33, 0);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_30);
lean_ctor_set(x_41, 1, x_40);
lean_ctor_set(x_33, 0, x_41);
x_42 = l_Except_orElseLazy___redArg(x_33, x_8);
lean_dec(x_33);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_33, 0);
lean_inc(x_43);
lean_dec(x_33);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_30);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_44);
x_46 = l_Except_orElseLazy___redArg(x_45, x_8);
lean_dec(x_45);
return x_46;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr___lam__0____x40_Lean_Data_Lsp_Internal___hyg_398____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr___lam__0____x40_Lean_Data_Lsp_Internal___hyg_398_(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr___lam__1____x40_Lean_Data_Lsp_Internal___hyg_398____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr___lam__1____x40_Lean_Data_Lsp_Internal___hyg_398_(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_398_), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_toJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_578_(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_mk_string_unchecked("c", 1, 1);
x_6 = lean_mk_string_unchecked("m", 1, 1);
x_7 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_1, 1, x_7);
lean_ctor_set(x_1, 0, x_6);
x_8 = lean_mk_string_unchecked("n", 1, 1);
x_9 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_9, 0, x_4);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Lean_Json_mkObj(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_5);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_11);
x_17 = l_Lean_Json_mkObj(x_16);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_18 = lean_ctor_get(x_1, 0);
x_19 = lean_ctor_get(x_1, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_1);
x_20 = lean_mk_string_unchecked("c", 1, 1);
x_21 = lean_mk_string_unchecked("m", 1, 1);
x_22 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_22, 0, x_18);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_mk_string_unchecked("n", 1, 1);
x_25 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_25, 0, x_19);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_23);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Lean_Json_mkObj(x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_20);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_27);
x_33 = l_Lean_Json_mkObj(x_32);
return x_33;
}
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_1);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_35 = lean_ctor_get(x_1, 0);
x_36 = lean_ctor_get(x_1, 1);
x_37 = lean_mk_string_unchecked("f", 1, 1);
x_38 = lean_mk_string_unchecked("m", 1, 1);
x_39 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_39, 0, x_35);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_39);
lean_ctor_set(x_1, 0, x_38);
x_40 = lean_mk_string_unchecked("i", 1, 1);
x_41 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_41, 0, x_36);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_1);
lean_ctor_set(x_45, 1, x_44);
x_46 = l_Lean_Json_mkObj(x_45);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_37);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_43);
x_49 = l_Lean_Json_mkObj(x_48);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_50 = lean_ctor_get(x_1, 0);
x_51 = lean_ctor_get(x_1, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_1);
x_52 = lean_mk_string_unchecked("f", 1, 1);
x_53 = lean_mk_string_unchecked("m", 1, 1);
x_54 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_54, 0, x_50);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_mk_string_unchecked("i", 1, 1);
x_57 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_57, 0, x_51);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
x_59 = lean_box(0);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_55);
lean_ctor_set(x_61, 1, x_60);
x_62 = l_Lean_Json_mkObj(x_61);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_52);
lean_ctor_set(x_63, 1, x_62);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_59);
x_65 = l_Lean_Json_mkObj(x_64);
return x_65;
}
}
}
}
static lean_object* _init_l_Lean_Lsp_RefIdent_instToJsonRefIdentJsonRepr() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_toJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_578_), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_toJsonRepr(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_1);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
return x_1;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_1);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_fromJsonRepr(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_1);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
return x_1;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_1);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_fromJson_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_398_(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_2);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = l_Lean_Lsp_RefIdent_fromJsonRepr(x_7);
lean_ctor_set(x_2, 0, x_8);
return x_2;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec(x_2);
x_10 = l_Lean_Lsp_RefIdent_fromJsonRepr(x_9);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_toJson(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Lsp_RefIdent_toJsonRepr(x_1);
x_3 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_toJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_578_(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_RefIdent_instFromJson() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Lsp_RefIdent_fromJson_x3f), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_RefIdent_instToJson() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Lsp_RefIdent_toJson), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefInfo_toJsonParentDecl____x40_Lean_Data_Lsp_Internal___hyg_851_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_2 = lean_mk_string_unchecked("name", 4, 4);
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_4, 0, x_3);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_4);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_mk_string_unchecked("range", 5, 5);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = l___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonRange____x40_Lean_Data_Lsp_Basic___hyg_615_(x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_6);
x_13 = lean_mk_string_unchecked("selectionRange", 14, 14);
x_14 = lean_ctor_get(x_1, 2);
lean_inc(x_14);
lean_dec(x_1);
x_15 = l___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonRange____x40_Lean_Data_Lsp_Basic___hyg_615_(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_6);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_12);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_7);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_mk_empty_array_with_capacity(x_22);
x_24 = l_List_flatMapTR_go___at_____private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonPosition____x40_Lean_Data_Lsp_Basic___hyg_221__spec__0(x_21, x_23);
x_25 = l_Lean_Json_mkObj(x_24);
return x_25;
}
}
static lean_object* _init_l_Lean_Lsp_RefInfo_instToJsonParentDecl() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefInfo_toJsonParentDecl____x40_Lean_Data_Lsp_Internal___hyg_851_), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_RefInfo_instInhabitedLocation() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
lean_inc(x_2);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRefInfo___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_5, 0);
x_7 = lean_ctor_get(x_5, 1);
x_8 = lean_box(0);
lean_inc(x_7);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
lean_inc(x_6);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_9);
lean_inc(x_4);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_10);
lean_inc(x_3);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRefInfo___lam__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_JsonNumber_fromNat(x_1);
x_3 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRefInfo___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_inc(x_1);
x_6 = lean_apply_1(x_1, x_5);
x_7 = lean_box(0);
x_8 = l_List_mapTR_loop(lean_box(0), lean_box(0), x_2, x_6, x_7);
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
lean_dec(x_4);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
lean_dec(x_3);
lean_dec(x_1);
x_10 = l_List_appendTR(lean_box(0), x_8, x_7);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_12 = lean_ctor_get(x_9, 0);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_ctor_set_tag(x_9, 3);
lean_ctor_set(x_9, 0, x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_inc(x_1);
x_15 = lean_apply_1(x_1, x_14);
lean_inc(x_3);
x_16 = l_List_mapTR_loop(lean_box(0), lean_box(0), x_3, x_15, x_7);
x_17 = lean_ctor_get(x_12, 2);
lean_inc(x_17);
lean_dec(x_12);
x_18 = lean_apply_1(x_1, x_17);
x_19 = l_List_mapTR_loop(lean_box(0), lean_box(0), x_3, x_18, x_7);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_9);
lean_ctor_set(x_20, 1, x_7);
x_21 = l_List_appendTR(lean_box(0), x_20, x_16);
x_22 = l_List_appendTR(lean_box(0), x_21, x_19);
x_23 = l_List_appendTR(lean_box(0), x_8, x_22);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_24 = lean_ctor_get(x_9, 0);
lean_inc(x_24);
lean_dec(x_9);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_inc(x_1);
x_28 = lean_apply_1(x_1, x_27);
lean_inc(x_3);
x_29 = l_List_mapTR_loop(lean_box(0), lean_box(0), x_3, x_28, x_7);
x_30 = lean_ctor_get(x_24, 2);
lean_inc(x_30);
lean_dec(x_24);
x_31 = lean_apply_1(x_1, x_30);
x_32 = l_List_mapTR_loop(lean_box(0), lean_box(0), x_3, x_31, x_7);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_26);
lean_ctor_set(x_33, 1, x_7);
x_34 = l_List_appendTR(lean_box(0), x_33, x_29);
x_35 = l_List_appendTR(lean_box(0), x_34, x_32);
x_36 = l_List_appendTR(lean_box(0), x_8, x_35);
return x_36;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRefInfo___lam__2(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; lean_object* x_15; size_t x_16; lean_object* x_17; lean_object* x_18; 
x_2 = lean_array_mk(x_1);
x_3 = lean_alloc_closure((void*)(l_id___boxed), 2, 1);
lean_closure_set(x_3, 0, lean_box(0));
x_4 = lean_alloc_closure((void*)(l_Id_instMonad___lam__0), 4, 0);
x_5 = lean_alloc_closure((void*)(l_Id_instMonad___lam__1___boxed), 4, 0);
x_6 = lean_alloc_closure((void*)(l_Id_instMonad___lam__2___boxed), 2, 0);
x_7 = lean_alloc_closure((void*)(l_Id_instMonad___lam__3), 4, 0);
x_8 = lean_alloc_closure((void*)(l_Id_instMonad___lam__4___boxed), 4, 0);
x_9 = lean_alloc_closure((void*)(l_Id_instMonad___lam__5___boxed), 4, 0);
x_10 = lean_alloc_closure((void*)(l_Id_instMonad___lam__6), 4, 0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_5);
x_12 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_6);
lean_ctor_set(x_12, 2, x_7);
lean_ctor_set(x_12, 3, x_8);
lean_ctor_set(x_12, 4, x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
x_14 = lean_array_size(x_2);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_usize_of_nat(x_15);
x_17 = l_Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), x_13, x_3, x_14, x_16, x_2);
x_18 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRefInfo___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_32; 
x_4 = lean_mk_string_unchecked("definition", 10, 10);
x_32 = lean_ctor_get(x_3, 0);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; 
x_33 = lean_box(0);
x_5 = x_33;
goto block_31;
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_32);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; size_t x_49; lean_object* x_50; size_t x_51; lean_object* x_52; 
x_35 = lean_ctor_get(x_32, 0);
lean_inc(x_1);
x_36 = lean_apply_1(x_1, x_35);
x_37 = lean_array_mk(x_36);
x_38 = lean_alloc_closure((void*)(l_id___boxed), 2, 1);
lean_closure_set(x_38, 0, lean_box(0));
x_39 = lean_alloc_closure((void*)(l_Id_instMonad___lam__0), 4, 0);
x_40 = lean_alloc_closure((void*)(l_Id_instMonad___lam__1___boxed), 4, 0);
x_41 = lean_alloc_closure((void*)(l_Id_instMonad___lam__2___boxed), 2, 0);
x_42 = lean_alloc_closure((void*)(l_Id_instMonad___lam__3), 4, 0);
x_43 = lean_alloc_closure((void*)(l_Id_instMonad___lam__4___boxed), 4, 0);
x_44 = lean_alloc_closure((void*)(l_Id_instMonad___lam__5___boxed), 4, 0);
x_45 = lean_alloc_closure((void*)(l_Id_instMonad___lam__6), 4, 0);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_39);
lean_ctor_set(x_46, 1, x_40);
x_47 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_41);
lean_ctor_set(x_47, 2, x_42);
lean_ctor_set(x_47, 3, x_43);
lean_ctor_set(x_47, 4, x_44);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_45);
x_49 = lean_array_size(x_37);
x_50 = lean_unsigned_to_nat(0u);
x_51 = lean_usize_of_nat(x_50);
x_52 = l_Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), x_48, x_38, x_49, x_51, x_37);
lean_ctor_set_tag(x_32, 4);
lean_ctor_set(x_32, 0, x_52);
x_5 = x_32;
goto block_31;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; size_t x_67; lean_object* x_68; size_t x_69; lean_object* x_70; lean_object* x_71; 
x_53 = lean_ctor_get(x_32, 0);
lean_inc(x_53);
lean_dec(x_32);
lean_inc(x_1);
x_54 = lean_apply_1(x_1, x_53);
x_55 = lean_array_mk(x_54);
x_56 = lean_alloc_closure((void*)(l_id___boxed), 2, 1);
lean_closure_set(x_56, 0, lean_box(0));
x_57 = lean_alloc_closure((void*)(l_Id_instMonad___lam__0), 4, 0);
x_58 = lean_alloc_closure((void*)(l_Id_instMonad___lam__1___boxed), 4, 0);
x_59 = lean_alloc_closure((void*)(l_Id_instMonad___lam__2___boxed), 2, 0);
x_60 = lean_alloc_closure((void*)(l_Id_instMonad___lam__3), 4, 0);
x_61 = lean_alloc_closure((void*)(l_Id_instMonad___lam__4___boxed), 4, 0);
x_62 = lean_alloc_closure((void*)(l_Id_instMonad___lam__5___boxed), 4, 0);
x_63 = lean_alloc_closure((void*)(l_Id_instMonad___lam__6), 4, 0);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_57);
lean_ctor_set(x_64, 1, x_58);
x_65 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_59);
lean_ctor_set(x_65, 2, x_60);
lean_ctor_set(x_65, 3, x_61);
lean_ctor_set(x_65, 4, x_62);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_63);
x_67 = lean_array_size(x_55);
x_68 = lean_unsigned_to_nat(0u);
x_69 = lean_usize_of_nat(x_68);
x_70 = l_Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), x_66, x_56, x_67, x_69, x_55);
x_71 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_71, 0, x_70);
x_5 = x_71;
goto block_31;
}
}
block_31:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; lean_object* x_20; size_t x_21; lean_object* x_22; size_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_mk_string_unchecked("usages", 6, 6);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_dec(x_3);
x_9 = lean_alloc_closure((void*)(l_Id_instMonad___lam__0), 4, 0);
x_10 = lean_alloc_closure((void*)(l_Id_instMonad___lam__1___boxed), 4, 0);
x_11 = lean_alloc_closure((void*)(l_Id_instMonad___lam__2___boxed), 2, 0);
x_12 = lean_alloc_closure((void*)(l_Id_instMonad___lam__3), 4, 0);
x_13 = lean_alloc_closure((void*)(l_Id_instMonad___lam__4___boxed), 4, 0);
x_14 = lean_alloc_closure((void*)(l_Id_instMonad___lam__5___boxed), 4, 0);
x_15 = lean_alloc_closure((void*)(l_Id_instMonad___lam__6), 4, 0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_9);
lean_ctor_set(x_16, 1, x_10);
x_17 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_11);
lean_ctor_set(x_17, 2, x_12);
lean_ctor_set(x_17, 3, x_13);
lean_ctor_set(x_17, 4, x_14);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_15);
x_19 = lean_array_size(x_8);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_usize_of_nat(x_20);
lean_inc(x_18);
x_22 = l_Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), x_18, x_1, x_19, x_21, x_8);
x_23 = lean_array_size(x_22);
x_24 = l_Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), x_18, x_2, x_23, x_21, x_22);
x_25 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_7);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_6);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Lean_Json_mkObj(x_29);
return x_30;
}
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonRefInfo() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_alloc_closure((void*)(l_Lean_Lsp_instToJsonRefInfo___lam__0___boxed), 1, 0);
x_2 = lean_alloc_closure((void*)(l_Lean_Lsp_instToJsonRefInfo___lam__1), 1, 0);
lean_inc(x_2);
x_3 = lean_alloc_closure((void*)(l_Lean_Lsp_instToJsonRefInfo___lam__3), 4, 3);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
lean_closure_set(x_3, 2, x_2);
x_4 = lean_alloc_closure((void*)(l_Lean_Lsp_instToJsonRefInfo___lam__2), 1, 0);
x_5 = lean_alloc_closure((void*)(l_Lean_Lsp_instToJsonRefInfo___lam__4), 3, 2);
lean_closure_set(x_5, 0, x_3);
lean_closure_set(x_5, 1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRefInfo___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_instToJsonRefInfo___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonRefInfo___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_unsigned_to_nat(4u);
x_5 = lean_nat_add(x_2, x_4);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_7 = lean_array_fget(x_1, x_2);
x_8 = l_Lean_Json_getNat_x3f(x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
return x_8;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_2, x_13);
x_15 = lean_array_fget(x_1, x_14);
lean_dec(x_14);
x_16 = l_Lean_Json_getNat_x3f(x_15);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
lean_dec(x_12);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
return x_16;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_16, 0);
lean_inc(x_20);
lean_dec(x_16);
x_21 = lean_unsigned_to_nat(2u);
x_22 = lean_nat_add(x_2, x_21);
x_23 = lean_array_fget(x_1, x_22);
lean_dec(x_22);
x_24 = l_Lean_Json_getNat_x3f(x_23);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
lean_dec(x_20);
lean_dec(x_12);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
return x_24;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_24, 0);
lean_inc(x_28);
lean_dec(x_24);
x_29 = lean_unsigned_to_nat(3u);
x_30 = lean_nat_add(x_2, x_29);
x_31 = lean_array_fget(x_1, x_30);
lean_dec(x_30);
x_32 = l_Lean_Json_getNat_x3f(x_31);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
lean_dec(x_28);
lean_dec(x_20);
lean_dec(x_12);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
return x_32;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
}
else
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_32);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_32, 0);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_12);
lean_ctor_set(x_38, 1, x_20);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_28);
lean_ctor_set(x_39, 1, x_37);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
lean_ctor_set(x_32, 0, x_40);
return x_32;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_41 = lean_ctor_get(x_32, 0);
lean_inc(x_41);
lean_dec(x_32);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_12);
lean_ctor_set(x_42, 1, x_20);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_28);
lean_ctor_set(x_43, 1, x_41);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_44);
return x_45;
}
}
}
}
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_46 = lean_mk_string_unchecked("Expected list of length 4, not ", 31, 31);
x_47 = l___private_Init_Data_Repr_0__Nat_reprFast(x_3);
x_48 = lean_string_append(x_46, x_47);
lean_dec(x_47);
x_49 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_49, 0, x_48);
return x_49;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonRefInfo___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_76 = lean_array_get_size(x_3);
x_77 = lean_unsigned_to_nat(4u);
x_78 = lean_nat_dec_eq(x_76, x_77);
if (x_78 == 0)
{
lean_object* x_79; uint8_t x_80; 
x_79 = lean_unsigned_to_nat(13u);
x_80 = lean_nat_dec_eq(x_76, x_79);
lean_dec(x_76);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_81 = lean_mk_string_unchecked("Expected list of length 4 or 13, not {l.size}", 45, 45);
x_82 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_82, 0, x_81);
return x_82;
}
else
{
goto block_75;
}
}
else
{
lean_dec(x_76);
goto block_75;
}
block_75:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(0u);
lean_inc(x_1);
lean_inc(x_3);
x_5 = lean_apply_2(x_1, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_5);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_5, 0);
x_11 = lean_array_get_size(x_3);
x_12 = lean_unsigned_to_nat(13u);
x_13 = lean_nat_dec_eq(x_11, x_12);
lean_dec(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set(x_5, 0, x_15);
return x_5;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_free_object(x_5);
x_16 = lean_unsigned_to_nat(4u);
x_17 = lean_array_get(x_2, x_3, x_16);
x_18 = l_Lean_Json_getStr_x3f(x_17);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
return x_18;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_18, 0);
lean_inc(x_22);
lean_dec(x_18);
x_23 = lean_unsigned_to_nat(5u);
lean_inc(x_1);
lean_inc(x_3);
x_24 = lean_apply_2(x_1, x_3, x_23);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
lean_dec(x_22);
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
return x_24;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_24, 0);
lean_inc(x_28);
lean_dec(x_24);
x_29 = lean_unsigned_to_nat(9u);
x_30 = lean_apply_2(x_1, x_3, x_29);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
lean_dec(x_28);
lean_dec(x_22);
lean_dec(x_10);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
return x_30;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_30);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_30, 0);
x_36 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_36, 0, x_22);
lean_ctor_set(x_36, 1, x_28);
lean_ctor_set(x_36, 2, x_35);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_10);
lean_ctor_set(x_38, 1, x_37);
lean_ctor_set(x_30, 0, x_38);
return x_30;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_30, 0);
lean_inc(x_39);
lean_dec(x_30);
x_40 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_40, 0, x_22);
lean_ctor_set(x_40, 1, x_28);
lean_ctor_set(x_40, 2, x_39);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_10);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
return x_43;
}
}
}
}
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_44 = lean_ctor_get(x_5, 0);
lean_inc(x_44);
lean_dec(x_5);
x_45 = lean_array_get_size(x_3);
x_46 = lean_unsigned_to_nat(13u);
x_47 = lean_nat_dec_eq(x_45, x_46);
lean_dec(x_45);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_48 = lean_box(0);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_44);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_49);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_unsigned_to_nat(4u);
x_52 = lean_array_get(x_2, x_3, x_51);
x_53 = l_Lean_Json_getStr_x3f(x_52);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_44);
lean_dec(x_3);
lean_dec(x_1);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 x_55 = x_53;
} else {
 lean_dec_ref(x_53);
 x_55 = lean_box(0);
}
if (lean_is_scalar(x_55)) {
 x_56 = lean_alloc_ctor(0, 1, 0);
} else {
 x_56 = x_55;
}
lean_ctor_set(x_56, 0, x_54);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_53, 0);
lean_inc(x_57);
lean_dec(x_53);
x_58 = lean_unsigned_to_nat(5u);
lean_inc(x_1);
lean_inc(x_3);
x_59 = lean_apply_2(x_1, x_3, x_58);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_57);
lean_dec(x_44);
lean_dec(x_3);
lean_dec(x_1);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 x_61 = x_59;
} else {
 lean_dec_ref(x_59);
 x_61 = lean_box(0);
}
if (lean_is_scalar(x_61)) {
 x_62 = lean_alloc_ctor(0, 1, 0);
} else {
 x_62 = x_61;
}
lean_ctor_set(x_62, 0, x_60);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_59, 0);
lean_inc(x_63);
lean_dec(x_59);
x_64 = lean_unsigned_to_nat(9u);
x_65 = lean_apply_2(x_1, x_3, x_64);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_63);
lean_dec(x_57);
lean_dec(x_44);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 x_67 = x_65;
} else {
 lean_dec_ref(x_65);
 x_67 = lean_box(0);
}
if (lean_is_scalar(x_67)) {
 x_68 = lean_alloc_ctor(0, 1, 0);
} else {
 x_68 = x_67;
}
lean_ctor_set(x_68, 0, x_66);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_69 = lean_ctor_get(x_65, 0);
lean_inc(x_69);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 x_70 = x_65;
} else {
 lean_dec_ref(x_65);
 x_70 = lean_box(0);
}
x_71 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_71, 0, x_57);
lean_ctor_set(x_71, 1, x_63);
lean_ctor_set(x_71, 2, x_69);
x_72 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_72, 0, x_71);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_44);
lean_ctor_set(x_73, 1, x_72);
if (lean_is_scalar(x_70)) {
 x_74 = lean_alloc_ctor(1, 1, 0);
} else {
 x_74 = x_70;
}
lean_ctor_set(x_74, 0, x_73);
return x_74;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonRefInfo___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_27; lean_object* x_28; 
x_27 = lean_mk_string_unchecked("definition", 10, 10);
lean_inc(x_5);
x_28 = l_Lean_Json_getObjValAs_x3f___redArg(x_5, x_1, x_27);
lean_dec(x_27);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
return x_28;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
}
else
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_28, 0);
lean_inc(x_32);
lean_dec(x_28);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; 
x_33 = lean_box(0);
x_6 = x_33;
goto block_26;
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_32);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_32, 0);
lean_inc(x_4);
x_36 = lean_apply_1(x_4, x_35);
if (lean_obj_tag(x_36) == 0)
{
uint8_t x_37; 
lean_free_object(x_32);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
return x_36;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_36, 0);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_38);
return x_39;
}
}
else
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_36, 0);
lean_inc(x_40);
lean_dec(x_36);
lean_ctor_set(x_32, 0, x_40);
x_6 = x_32;
goto block_26;
}
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_32, 0);
lean_inc(x_41);
lean_dec(x_32);
lean_inc(x_4);
x_42 = lean_apply_1(x_4, x_41);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 x_44 = x_42;
} else {
 lean_dec_ref(x_42);
 x_44 = lean_box(0);
}
if (lean_is_scalar(x_44)) {
 x_45 = lean_alloc_ctor(0, 1, 0);
} else {
 x_45 = x_44;
}
lean_ctor_set(x_45, 0, x_43);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_42, 0);
lean_inc(x_46);
lean_dec(x_42);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
x_6 = x_47;
goto block_26;
}
}
}
}
block_26:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_mk_string_unchecked("usages", 6, 6);
x_8 = l_Lean_Json_getObjValAs_x3f___redArg(x_5, x_2, x_7);
lean_dec(x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
return x_8;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
else
{
lean_object* x_12; size_t x_13; lean_object* x_14; size_t x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
x_13 = lean_array_size(x_12);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_usize_of_nat(x_14);
x_16 = l_Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), x_3, x_4, x_13, x_15, x_12);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
lean_dec(x_6);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
return x_16;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_16);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_16, 0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_6);
lean_ctor_set(x_22, 1, x_21);
lean_ctor_set(x_16, 0, x_22);
return x_16;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_16, 0);
lean_inc(x_23);
lean_dec(x_16);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_6);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRefInfo() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_1 = lean_alloc_closure((void*)(l_Lean_Lsp_instFromJsonRefInfo___lam__0___boxed), 2, 0);
x_2 = lean_alloc_closure((void*)(l_Except_instMonad___lam__0), 4, 0);
x_3 = lean_alloc_closure((void*)(l_Except_instMonad___lam__1), 4, 0);
x_4 = lean_alloc_closure((void*)(l_Except_instMonad___lam__2___boxed), 4, 0);
x_5 = lean_alloc_closure((void*)(l_Except_instMonad___lam__3___boxed), 4, 0);
x_6 = lean_alloc_closure((void*)(l_Except_map), 5, 1);
lean_closure_set(x_6, 0, lean_box(0));
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_2);
x_8 = lean_alloc_closure((void*)(l_Except_pure), 3, 1);
lean_closure_set(x_8, 0, lean_box(0));
x_9 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set(x_9, 2, x_3);
lean_ctor_set(x_9, 3, x_4);
lean_ctor_set(x_9, 4, x_5);
x_10 = lean_alloc_closure((void*)(l_Except_bind), 5, 1);
lean_closure_set(x_10, 0, lean_box(0));
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_box(0);
x_13 = lean_alloc_closure((void*)(l_Lean_Lsp_instFromJsonRefInfo___lam__1), 3, 2);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_12);
x_14 = lean_alloc_closure((void*)(l_Lean_instFromJsonJson___lam__0), 1, 0);
x_15 = l_Lean_instFromJsonArray(lean_box(0), x_14);
lean_inc(x_15);
x_16 = lean_alloc_closure((void*)(l_Lean_instFromJsonOption___redArg___lam__0), 2, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = l_Lean_instFromJsonArray(lean_box(0), x_15);
x_18 = lean_alloc_closure((void*)(l_Lean_Lsp_instFromJsonRefInfo___lam__2), 5, 4);
lean_closure_set(x_18, 0, x_16);
lean_closure_set(x_18, 1, x_17);
lean_closure_set(x_18, 2, x_11);
lean_closure_set(x_18, 3, x_13);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonRefInfo___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Lsp_instFromJsonRefInfo___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instModuleRefsEmptyCollection() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instForInModuleRefsProdRefIdentRefInfo___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
x_6 = lean_apply_2(x_1, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instForInModuleRefsProdRefIdentRefInfo___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_apply_2(x_1, lean_box(0), x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instForInModuleRefsProdRefIdentRefInfo___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_alloc_closure((void*)(l_Lean_Lsp_instForInModuleRefsProdRefIdentRefInfo___lam__0), 4, 1);
lean_closure_set(x_6, 0, x_5);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_inc(x_2);
x_8 = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(x_2, x_6, x_4, x_3);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec(x_2);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Lsp_instForInModuleRefsProdRefIdentRefInfo___lam__1), 2, 1);
lean_closure_set(x_11, 0, x_10);
x_12 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_8, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instForInModuleRefsProdRefIdentRefInfo(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Lsp_instForInModuleRefsProdRefIdentRefInfo___lam__2), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonModuleRefs___lam__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_40; lean_object* x_59; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_8 = x_5;
} else {
 lean_dec_ref(x_5);
 x_8 = lean_box(0);
}
x_9 = l_Lean_Lsp_RefIdent_toJson(x_6);
x_10 = l_Lean_Json_compress(x_9);
x_11 = lean_mk_string_unchecked("definition", 10, 10);
x_59 = lean_ctor_get(x_7, 0);
lean_inc(x_59);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; 
lean_dec(x_4);
lean_dec(x_3);
x_60 = lean_box(0);
x_12 = x_60;
goto block_39;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_61 = lean_ctor_get(x_59, 0);
lean_inc(x_61);
lean_dec(x_59);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = lean_ctor_get(x_62, 1);
lean_inc(x_66);
lean_dec(x_62);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = lean_box(0);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_67);
lean_ctor_set(x_71, 1, x_70);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_65);
lean_ctor_set(x_72, 1, x_71);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_64);
lean_ctor_set(x_73, 1, x_72);
x_74 = lean_box(0);
x_75 = l_List_mapTR_loop(lean_box(0), lean_box(0), x_3, x_73, x_74);
x_76 = lean_ctor_get(x_61, 1);
lean_inc(x_76);
lean_dec(x_61);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; 
lean_dec(x_4);
x_77 = l_List_appendTR(lean_box(0), x_75, x_74);
x_40 = x_77;
goto block_58;
}
else
{
uint8_t x_78; 
x_78 = !lean_is_exclusive(x_76);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_79 = lean_ctor_get(x_76, 0);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
lean_ctor_set_tag(x_76, 3);
lean_ctor_set(x_76, 0, x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_85 = lean_ctor_get(x_81, 1);
lean_inc(x_85);
lean_dec(x_81);
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_69);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_86);
lean_ctor_set(x_89, 1, x_88);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_84);
lean_ctor_set(x_90, 1, x_89);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_83);
lean_ctor_set(x_91, 1, x_90);
lean_inc(x_4);
x_92 = l_List_mapTR_loop(lean_box(0), lean_box(0), x_4, x_91, x_74);
x_93 = lean_ctor_get(x_79, 2);
lean_inc(x_93);
lean_dec(x_79);
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec(x_94);
x_97 = lean_ctor_get(x_93, 1);
lean_inc(x_97);
lean_dec(x_93);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
lean_dec(x_97);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_69);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_98);
lean_ctor_set(x_101, 1, x_100);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_96);
lean_ctor_set(x_102, 1, x_101);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_95);
lean_ctor_set(x_103, 1, x_102);
x_104 = l_List_mapTR_loop(lean_box(0), lean_box(0), x_4, x_103, x_74);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_76);
lean_ctor_set(x_105, 1, x_74);
x_106 = l_List_appendTR(lean_box(0), x_105, x_92);
x_107 = l_List_appendTR(lean_box(0), x_106, x_104);
x_108 = l_List_appendTR(lean_box(0), x_75, x_107);
x_40 = x_108;
goto block_58;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_109 = lean_ctor_get(x_76, 0);
lean_inc(x_109);
lean_dec(x_76);
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_111, 0, x_110);
x_112 = lean_ctor_get(x_109, 1);
lean_inc(x_112);
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
lean_dec(x_113);
x_116 = lean_ctor_get(x_112, 1);
lean_inc(x_116);
lean_dec(x_112);
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
lean_dec(x_116);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_69);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_117);
lean_ctor_set(x_120, 1, x_119);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_115);
lean_ctor_set(x_121, 1, x_120);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_114);
lean_ctor_set(x_122, 1, x_121);
lean_inc(x_4);
x_123 = l_List_mapTR_loop(lean_box(0), lean_box(0), x_4, x_122, x_74);
x_124 = lean_ctor_get(x_109, 2);
lean_inc(x_124);
lean_dec(x_109);
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
lean_dec(x_125);
x_128 = lean_ctor_get(x_124, 1);
lean_inc(x_128);
lean_dec(x_124);
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_128, 1);
lean_inc(x_130);
lean_dec(x_128);
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_69);
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_129);
lean_ctor_set(x_132, 1, x_131);
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_127);
lean_ctor_set(x_133, 1, x_132);
x_134 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_134, 0, x_126);
lean_ctor_set(x_134, 1, x_133);
x_135 = l_List_mapTR_loop(lean_box(0), lean_box(0), x_4, x_134, x_74);
x_136 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_136, 0, x_111);
lean_ctor_set(x_136, 1, x_74);
x_137 = l_List_appendTR(lean_box(0), x_136, x_123);
x_138 = l_List_appendTR(lean_box(0), x_137, x_135);
x_139 = l_List_appendTR(lean_box(0), x_75, x_138);
x_40 = x_139;
goto block_58;
}
}
}
block_39:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; size_t x_26; lean_object* x_27; size_t x_28; lean_object* x_29; size_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
if (lean_is_scalar(x_8)) {
 x_13 = lean_alloc_ctor(0, 2, 0);
} else {
 x_13 = x_8;
}
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_mk_string_unchecked("usages", 6, 6);
x_15 = lean_ctor_get(x_7, 1);
lean_inc(x_15);
lean_dec(x_7);
x_16 = lean_alloc_closure((void*)(l_Id_instMonad___lam__0), 4, 0);
x_17 = lean_alloc_closure((void*)(l_Id_instMonad___lam__1___boxed), 4, 0);
x_18 = lean_alloc_closure((void*)(l_Id_instMonad___lam__2___boxed), 2, 0);
x_19 = lean_alloc_closure((void*)(l_Id_instMonad___lam__3), 4, 0);
x_20 = lean_alloc_closure((void*)(l_Id_instMonad___lam__4___boxed), 4, 0);
x_21 = lean_alloc_closure((void*)(l_Id_instMonad___lam__5___boxed), 4, 0);
x_22 = lean_alloc_closure((void*)(l_Id_instMonad___lam__6), 4, 0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_16);
lean_ctor_set(x_23, 1, x_17);
x_24 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_18);
lean_ctor_set(x_24, 2, x_19);
lean_ctor_set(x_24, 3, x_20);
lean_ctor_set(x_24, 4, x_21);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_22);
x_26 = lean_array_size(x_15);
x_27 = lean_unsigned_to_nat(0u);
x_28 = lean_usize_of_nat(x_27);
lean_inc(x_25);
x_29 = l_Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), x_25, x_1, x_26, x_28, x_15);
x_30 = lean_array_size(x_29);
x_31 = l_Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), x_25, x_2, x_30, x_28, x_29);
x_32 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_14);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_13);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_Lean_Json_mkObj(x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_10);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
block_58:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; size_t x_53; lean_object* x_54; size_t x_55; lean_object* x_56; lean_object* x_57; 
x_41 = lean_array_mk(x_40);
x_42 = lean_alloc_closure((void*)(l_id___boxed), 2, 1);
lean_closure_set(x_42, 0, lean_box(0));
x_43 = lean_alloc_closure((void*)(l_Id_instMonad___lam__0), 4, 0);
x_44 = lean_alloc_closure((void*)(l_Id_instMonad___lam__1___boxed), 4, 0);
x_45 = lean_alloc_closure((void*)(l_Id_instMonad___lam__2___boxed), 2, 0);
x_46 = lean_alloc_closure((void*)(l_Id_instMonad___lam__3), 4, 0);
x_47 = lean_alloc_closure((void*)(l_Id_instMonad___lam__4___boxed), 4, 0);
x_48 = lean_alloc_closure((void*)(l_Id_instMonad___lam__5___boxed), 4, 0);
x_49 = lean_alloc_closure((void*)(l_Id_instMonad___lam__6), 4, 0);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_43);
lean_ctor_set(x_50, 1, x_44);
x_51 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_45);
lean_ctor_set(x_51, 2, x_46);
lean_ctor_set(x_51, 3, x_47);
lean_ctor_set(x_51, 4, x_48);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_49);
x_53 = lean_array_size(x_41);
x_54 = lean_unsigned_to_nat(0u);
x_55 = lean_usize_of_nat(x_54);
x_56 = l_Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), x_52, x_42, x_53, x_55, x_41);
x_57 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_57, 0, x_56);
x_12 = x_57;
goto block_39;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonModuleRefs___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonModuleRefs___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_4 = lean_box(0);
x_5 = lean_alloc_closure((void*)(l_Id_instMonad___lam__0), 4, 0);
x_6 = lean_alloc_closure((void*)(l_Id_instMonad___lam__1___boxed), 4, 0);
x_7 = lean_alloc_closure((void*)(l_Id_instMonad___lam__2___boxed), 2, 0);
x_8 = lean_alloc_closure((void*)(l_Id_instMonad___lam__3), 4, 0);
x_9 = lean_alloc_closure((void*)(l_Id_instMonad___lam__4___boxed), 4, 0);
x_10 = lean_alloc_closure((void*)(l_Id_instMonad___lam__5___boxed), 4, 0);
x_11 = lean_alloc_closure((void*)(l_Id_instMonad___lam__6), 4, 0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_6);
x_13 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_7);
lean_ctor_set(x_13, 2, x_8);
lean_ctor_set(x_13, 3, x_9);
lean_ctor_set(x_13, 4, x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
x_15 = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(x_14, x_1, x_4, x_3);
x_16 = lean_box(0);
x_17 = l_List_mapTR_loop(lean_box(0), lean_box(0), x_2, x_15, x_16);
x_18 = l_Lean_Json_mkObj(x_17);
return x_18;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonModuleRefs() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = lean_alloc_closure((void*)(l_Lean_Lsp_instToJsonRefInfo___lam__0___boxed), 1, 0);
x_2 = lean_alloc_closure((void*)(l_Lean_Lsp_instToJsonRefInfo___lam__1), 1, 0);
lean_inc_n(x_2, 2);
x_3 = lean_alloc_closure((void*)(l_Lean_Lsp_instToJsonRefInfo___lam__3), 4, 3);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
lean_closure_set(x_3, 2, x_2);
x_4 = lean_alloc_closure((void*)(l_Lean_Lsp_instToJsonRefInfo___lam__2), 1, 0);
lean_inc(x_2);
x_5 = lean_alloc_closure((void*)(l_Lean_Lsp_instToJsonModuleRefs___lam__5), 5, 4);
lean_closure_set(x_5, 0, x_3);
lean_closure_set(x_5, 1, x_4);
lean_closure_set(x_5, 2, x_2);
lean_closure_set(x_5, 3, x_2);
x_6 = lean_alloc_closure((void*)(l_Lean_Lsp_instToJsonModuleRefs___lam__0), 3, 0);
x_7 = lean_alloc_closure((void*)(l_Lean_Lsp_instToJsonModuleRefs___lam__1), 3, 2);
lean_closure_set(x_7, 0, x_6);
lean_closure_set(x_7, 1, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonModuleRefs___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Json_parse(x_3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_5, 0);
lean_inc(x_9);
lean_dec(x_5);
x_10 = l_Lean_Lsp_RefIdent_fromJson_x3f(x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
return x_10;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_10);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_15 = lean_ctor_get(x_10, 0);
x_16 = lean_alloc_closure((void*)(l_Except_instMonad___lam__0), 4, 0);
x_17 = lean_alloc_closure((void*)(l_Except_instMonad___lam__1), 4, 0);
x_18 = lean_alloc_closure((void*)(l_Except_instMonad___lam__2___boxed), 4, 0);
x_19 = lean_alloc_closure((void*)(l_Except_instMonad___lam__3___boxed), 4, 0);
x_20 = lean_alloc_closure((void*)(l_Except_map), 5, 1);
lean_closure_set(x_20, 0, lean_box(0));
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_16);
x_22 = lean_alloc_closure((void*)(l_Except_pure), 3, 1);
lean_closure_set(x_22, 0, lean_box(0));
x_23 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set(x_23, 2, x_17);
lean_ctor_set(x_23, 3, x_18);
lean_ctor_set(x_23, 4, x_19);
x_24 = lean_alloc_closure((void*)(l_Except_bind), 5, 1);
lean_closure_set(x_24, 0, lean_box(0));
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_closure((void*)(l_Lean_instFromJsonJson___lam__0), 1, 0);
x_27 = l_Lean_instFromJsonArray(lean_box(0), x_26);
lean_inc(x_27);
x_28 = lean_alloc_closure((void*)(l_Lean_instFromJsonOption___redArg___lam__0), 2, 1);
lean_closure_set(x_28, 0, x_27);
x_29 = lean_mk_string_unchecked("definition", 10, 10);
lean_inc(x_4);
x_30 = l_Lean_Json_getObjValAs_x3f___redArg(x_4, x_28, x_29);
lean_dec(x_29);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
lean_dec(x_27);
lean_dec(x_25);
lean_free_object(x_10);
lean_dec(x_15);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
return x_30;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_64; 
x_34 = lean_ctor_get(x_30, 0);
lean_inc(x_34);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 x_35 = x_30;
} else {
 lean_dec_ref(x_30);
 x_35 = lean_box(0);
}
x_36 = lean_box(0);
x_37 = lean_alloc_closure((void*)(l_Lean_Lsp_instFromJsonRefInfo___lam__1), 3, 2);
lean_closure_set(x_37, 0, x_1);
lean_closure_set(x_37, 1, x_36);
x_38 = l_Lean_instFromJsonArray(lean_box(0), x_27);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_67; 
lean_dec(x_35);
lean_free_object(x_10);
x_67 = lean_box(0);
x_39 = x_67;
goto block_63;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_313; lean_object* x_314; uint8_t x_315; 
x_68 = lean_ctor_get(x_34, 0);
lean_inc(x_68);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 x_69 = x_34;
} else {
 lean_dec_ref(x_34);
 x_69 = lean_box(0);
}
x_313 = lean_array_get_size(x_68);
x_314 = lean_unsigned_to_nat(4u);
x_315 = lean_nat_dec_eq(x_313, x_314);
if (x_315 == 0)
{
lean_object* x_316; uint8_t x_317; 
x_316 = lean_unsigned_to_nat(13u);
x_317 = lean_nat_dec_eq(x_313, x_316);
lean_dec(x_313);
if (x_317 == 0)
{
lean_object* x_318; 
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_35);
lean_dec(x_25);
lean_dec(x_15);
lean_dec(x_4);
lean_dec(x_2);
x_318 = lean_mk_string_unchecked("Expected list of length 4 or 13, not {l.size}", 45, 45);
lean_ctor_set_tag(x_10, 0);
lean_ctor_set(x_10, 0, x_318);
return x_10;
}
else
{
lean_free_object(x_10);
goto block_312;
}
}
else
{
lean_dec(x_313);
lean_free_object(x_10);
goto block_312;
}
block_312:
{
lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_70 = lean_array_get_size(x_68);
x_71 = lean_unsigned_to_nat(4u);
x_72 = lean_nat_dec_lt(x_70, x_71);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_35);
x_73 = lean_unsigned_to_nat(0u);
x_74 = lean_array_fget(x_68, x_73);
x_75 = l_Lean_Json_getNat_x3f(x_74);
if (lean_obj_tag(x_75) == 0)
{
uint8_t x_76; 
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_25);
lean_dec(x_15);
lean_dec(x_4);
lean_dec(x_2);
x_76 = !lean_is_exclusive(x_75);
if (x_76 == 0)
{
return x_75;
}
else
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_75, 0);
lean_inc(x_77);
lean_dec(x_75);
x_78 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_78, 0, x_77);
return x_78;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_79 = lean_ctor_get(x_75, 0);
lean_inc(x_79);
lean_dec(x_75);
x_80 = lean_unsigned_to_nat(1u);
x_81 = lean_array_fget(x_68, x_80);
x_82 = l_Lean_Json_getNat_x3f(x_81);
if (lean_obj_tag(x_82) == 0)
{
uint8_t x_83; 
lean_dec(x_79);
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_25);
lean_dec(x_15);
lean_dec(x_4);
lean_dec(x_2);
x_83 = !lean_is_exclusive(x_82);
if (x_83 == 0)
{
return x_82;
}
else
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_82, 0);
lean_inc(x_84);
lean_dec(x_82);
x_85 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_85, 0, x_84);
return x_85;
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_86 = lean_ctor_get(x_82, 0);
lean_inc(x_86);
lean_dec(x_82);
x_87 = lean_unsigned_to_nat(2u);
x_88 = lean_array_fget(x_68, x_87);
x_89 = l_Lean_Json_getNat_x3f(x_88);
if (lean_obj_tag(x_89) == 0)
{
uint8_t x_90; 
lean_dec(x_86);
lean_dec(x_79);
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_25);
lean_dec(x_15);
lean_dec(x_4);
lean_dec(x_2);
x_90 = !lean_is_exclusive(x_89);
if (x_90 == 0)
{
return x_89;
}
else
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_89, 0);
lean_inc(x_91);
lean_dec(x_89);
x_92 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_92, 0, x_91);
return x_92;
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_93 = lean_ctor_get(x_89, 0);
lean_inc(x_93);
lean_dec(x_89);
x_94 = lean_unsigned_to_nat(3u);
x_95 = lean_array_fget(x_68, x_94);
x_96 = l_Lean_Json_getNat_x3f(x_95);
if (lean_obj_tag(x_96) == 0)
{
uint8_t x_97; 
lean_dec(x_93);
lean_dec(x_86);
lean_dec(x_79);
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_25);
lean_dec(x_15);
lean_dec(x_4);
lean_dec(x_2);
x_97 = !lean_is_exclusive(x_96);
if (x_97 == 0)
{
return x_96;
}
else
{
lean_object* x_98; lean_object* x_99; 
x_98 = lean_ctor_get(x_96, 0);
lean_inc(x_98);
lean_dec(x_96);
x_99 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_99, 0, x_98);
return x_99;
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; 
x_100 = lean_ctor_get(x_96, 0);
lean_inc(x_100);
lean_dec(x_96);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_79);
lean_ctor_set(x_101, 1, x_86);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_93);
lean_ctor_set(x_102, 1, x_100);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
x_104 = lean_unsigned_to_nat(13u);
x_105 = lean_nat_dec_eq(x_70, x_104);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; 
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_68);
x_106 = lean_box(0);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_103);
lean_ctor_set(x_107, 1, x_106);
x_64 = x_107;
goto block_66;
}
else
{
lean_object* x_108; lean_object* x_109; 
x_108 = lean_array_get(x_36, x_68, x_71);
x_109 = l_Lean_Json_getStr_x3f(x_108);
if (lean_obj_tag(x_109) == 0)
{
uint8_t x_110; 
lean_dec(x_103);
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_25);
lean_dec(x_15);
lean_dec(x_4);
lean_dec(x_2);
x_110 = !lean_is_exclusive(x_109);
if (x_110 == 0)
{
return x_109;
}
else
{
lean_object* x_111; lean_object* x_112; 
x_111 = lean_ctor_get(x_109, 0);
lean_inc(x_111);
lean_dec(x_109);
x_112 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_112, 0, x_111);
return x_112;
}
}
else
{
uint8_t x_113; 
x_113 = !lean_is_exclusive(x_109);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; uint8_t x_116; 
x_114 = lean_ctor_get(x_109, 0);
x_115 = lean_unsigned_to_nat(9u);
x_116 = lean_nat_dec_lt(x_70, x_115);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_free_object(x_109);
x_117 = lean_unsigned_to_nat(5u);
x_118 = lean_array_fget(x_68, x_117);
x_119 = l_Lean_Json_getNat_x3f(x_118);
if (lean_obj_tag(x_119) == 0)
{
uint8_t x_120; 
lean_dec(x_114);
lean_dec(x_103);
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_25);
lean_dec(x_15);
lean_dec(x_4);
lean_dec(x_2);
x_120 = !lean_is_exclusive(x_119);
if (x_120 == 0)
{
return x_119;
}
else
{
lean_object* x_121; lean_object* x_122; 
x_121 = lean_ctor_get(x_119, 0);
lean_inc(x_121);
lean_dec(x_119);
x_122 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_122, 0, x_121);
return x_122;
}
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_123 = lean_ctor_get(x_119, 0);
lean_inc(x_123);
lean_dec(x_119);
x_124 = lean_unsigned_to_nat(6u);
x_125 = lean_array_fget(x_68, x_124);
x_126 = l_Lean_Json_getNat_x3f(x_125);
if (lean_obj_tag(x_126) == 0)
{
uint8_t x_127; 
lean_dec(x_123);
lean_dec(x_114);
lean_dec(x_103);
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_25);
lean_dec(x_15);
lean_dec(x_4);
lean_dec(x_2);
x_127 = !lean_is_exclusive(x_126);
if (x_127 == 0)
{
return x_126;
}
else
{
lean_object* x_128; lean_object* x_129; 
x_128 = lean_ctor_get(x_126, 0);
lean_inc(x_128);
lean_dec(x_126);
x_129 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_129, 0, x_128);
return x_129;
}
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_130 = lean_ctor_get(x_126, 0);
lean_inc(x_130);
lean_dec(x_126);
x_131 = lean_unsigned_to_nat(7u);
x_132 = lean_array_fget(x_68, x_131);
x_133 = l_Lean_Json_getNat_x3f(x_132);
if (lean_obj_tag(x_133) == 0)
{
uint8_t x_134; 
lean_dec(x_130);
lean_dec(x_123);
lean_dec(x_114);
lean_dec(x_103);
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_25);
lean_dec(x_15);
lean_dec(x_4);
lean_dec(x_2);
x_134 = !lean_is_exclusive(x_133);
if (x_134 == 0)
{
return x_133;
}
else
{
lean_object* x_135; lean_object* x_136; 
x_135 = lean_ctor_get(x_133, 0);
lean_inc(x_135);
lean_dec(x_133);
x_136 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_136, 0, x_135);
return x_136;
}
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_137 = lean_ctor_get(x_133, 0);
lean_inc(x_137);
lean_dec(x_133);
x_138 = lean_unsigned_to_nat(8u);
x_139 = lean_array_fget(x_68, x_138);
x_140 = l_Lean_Json_getNat_x3f(x_139);
if (lean_obj_tag(x_140) == 0)
{
uint8_t x_141; 
lean_dec(x_137);
lean_dec(x_130);
lean_dec(x_123);
lean_dec(x_114);
lean_dec(x_103);
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_25);
lean_dec(x_15);
lean_dec(x_4);
lean_dec(x_2);
x_141 = !lean_is_exclusive(x_140);
if (x_141 == 0)
{
return x_140;
}
else
{
lean_object* x_142; lean_object* x_143; 
x_142 = lean_ctor_get(x_140, 0);
lean_inc(x_142);
lean_dec(x_140);
x_143 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_143, 0, x_142);
return x_143;
}
}
else
{
uint8_t x_144; 
x_144 = !lean_is_exclusive(x_140);
if (x_144 == 0)
{
lean_object* x_145; uint8_t x_146; 
x_145 = lean_ctor_get(x_140, 0);
x_146 = lean_nat_dec_lt(x_70, x_104);
if (x_146 == 0)
{
lean_object* x_147; lean_object* x_148; 
lean_free_object(x_140);
lean_dec(x_70);
x_147 = lean_array_fget(x_68, x_115);
x_148 = l_Lean_Json_getNat_x3f(x_147);
if (lean_obj_tag(x_148) == 0)
{
uint8_t x_149; 
lean_dec(x_145);
lean_dec(x_137);
lean_dec(x_130);
lean_dec(x_123);
lean_dec(x_114);
lean_dec(x_103);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_25);
lean_dec(x_15);
lean_dec(x_4);
lean_dec(x_2);
x_149 = !lean_is_exclusive(x_148);
if (x_149 == 0)
{
return x_148;
}
else
{
lean_object* x_150; lean_object* x_151; 
x_150 = lean_ctor_get(x_148, 0);
lean_inc(x_150);
lean_dec(x_148);
x_151 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_151, 0, x_150);
return x_151;
}
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_152 = lean_ctor_get(x_148, 0);
lean_inc(x_152);
lean_dec(x_148);
x_153 = lean_unsigned_to_nat(10u);
x_154 = lean_array_fget(x_68, x_153);
x_155 = l_Lean_Json_getNat_x3f(x_154);
if (lean_obj_tag(x_155) == 0)
{
uint8_t x_156; 
lean_dec(x_152);
lean_dec(x_145);
lean_dec(x_137);
lean_dec(x_130);
lean_dec(x_123);
lean_dec(x_114);
lean_dec(x_103);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_25);
lean_dec(x_15);
lean_dec(x_4);
lean_dec(x_2);
x_156 = !lean_is_exclusive(x_155);
if (x_156 == 0)
{
return x_155;
}
else
{
lean_object* x_157; lean_object* x_158; 
x_157 = lean_ctor_get(x_155, 0);
lean_inc(x_157);
lean_dec(x_155);
x_158 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_158, 0, x_157);
return x_158;
}
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_159 = lean_ctor_get(x_155, 0);
lean_inc(x_159);
lean_dec(x_155);
x_160 = lean_unsigned_to_nat(11u);
x_161 = lean_array_fget(x_68, x_160);
x_162 = l_Lean_Json_getNat_x3f(x_161);
if (lean_obj_tag(x_162) == 0)
{
uint8_t x_163; 
lean_dec(x_159);
lean_dec(x_152);
lean_dec(x_145);
lean_dec(x_137);
lean_dec(x_130);
lean_dec(x_123);
lean_dec(x_114);
lean_dec(x_103);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_25);
lean_dec(x_15);
lean_dec(x_4);
lean_dec(x_2);
x_163 = !lean_is_exclusive(x_162);
if (x_163 == 0)
{
return x_162;
}
else
{
lean_object* x_164; lean_object* x_165; 
x_164 = lean_ctor_get(x_162, 0);
lean_inc(x_164);
lean_dec(x_162);
x_165 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_165, 0, x_164);
return x_165;
}
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_166 = lean_ctor_get(x_162, 0);
lean_inc(x_166);
lean_dec(x_162);
x_167 = lean_unsigned_to_nat(12u);
x_168 = lean_array_fget(x_68, x_167);
lean_dec(x_68);
x_169 = l_Lean_Json_getNat_x3f(x_168);
if (lean_obj_tag(x_169) == 0)
{
uint8_t x_170; 
lean_dec(x_166);
lean_dec(x_159);
lean_dec(x_152);
lean_dec(x_145);
lean_dec(x_137);
lean_dec(x_130);
lean_dec(x_123);
lean_dec(x_114);
lean_dec(x_103);
lean_dec(x_69);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_25);
lean_dec(x_15);
lean_dec(x_4);
lean_dec(x_2);
x_170 = !lean_is_exclusive(x_169);
if (x_170 == 0)
{
return x_169;
}
else
{
lean_object* x_171; lean_object* x_172; 
x_171 = lean_ctor_get(x_169, 0);
lean_inc(x_171);
lean_dec(x_169);
x_172 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_172, 0, x_171);
return x_172;
}
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_173 = lean_ctor_get(x_169, 0);
lean_inc(x_173);
lean_dec(x_169);
x_174 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_174, 0, x_123);
lean_ctor_set(x_174, 1, x_130);
x_175 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_175, 0, x_137);
lean_ctor_set(x_175, 1, x_145);
x_176 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_176, 0, x_174);
lean_ctor_set(x_176, 1, x_175);
x_177 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_177, 0, x_152);
lean_ctor_set(x_177, 1, x_159);
x_178 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_178, 0, x_166);
lean_ctor_set(x_178, 1, x_173);
x_179 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_179, 0, x_177);
lean_ctor_set(x_179, 1, x_178);
x_180 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_180, 0, x_114);
lean_ctor_set(x_180, 1, x_176);
lean_ctor_set(x_180, 2, x_179);
if (lean_is_scalar(x_69)) {
 x_181 = lean_alloc_ctor(1, 1, 0);
} else {
 x_181 = x_69;
}
lean_ctor_set(x_181, 0, x_180);
x_182 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_182, 0, x_103);
lean_ctor_set(x_182, 1, x_181);
x_64 = x_182;
goto block_66;
}
}
}
}
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; 
lean_dec(x_145);
lean_dec(x_137);
lean_dec(x_130);
lean_dec(x_123);
lean_dec(x_114);
lean_dec(x_103);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_25);
lean_dec(x_15);
lean_dec(x_4);
lean_dec(x_2);
x_183 = lean_mk_string_unchecked("Expected list of length 4, not ", 31, 31);
x_184 = l___private_Init_Data_Repr_0__Nat_reprFast(x_70);
x_185 = lean_string_append(x_183, x_184);
lean_dec(x_184);
lean_ctor_set_tag(x_140, 0);
lean_ctor_set(x_140, 0, x_185);
return x_140;
}
}
else
{
lean_object* x_186; uint8_t x_187; 
x_186 = lean_ctor_get(x_140, 0);
lean_inc(x_186);
lean_dec(x_140);
x_187 = lean_nat_dec_lt(x_70, x_104);
if (x_187 == 0)
{
lean_object* x_188; lean_object* x_189; 
lean_dec(x_70);
x_188 = lean_array_fget(x_68, x_115);
x_189 = l_Lean_Json_getNat_x3f(x_188);
if (lean_obj_tag(x_189) == 0)
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; 
lean_dec(x_186);
lean_dec(x_137);
lean_dec(x_130);
lean_dec(x_123);
lean_dec(x_114);
lean_dec(x_103);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_25);
lean_dec(x_15);
lean_dec(x_4);
lean_dec(x_2);
x_190 = lean_ctor_get(x_189, 0);
lean_inc(x_190);
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 x_191 = x_189;
} else {
 lean_dec_ref(x_189);
 x_191 = lean_box(0);
}
if (lean_is_scalar(x_191)) {
 x_192 = lean_alloc_ctor(0, 1, 0);
} else {
 x_192 = x_191;
}
lean_ctor_set(x_192, 0, x_190);
return x_192;
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_193 = lean_ctor_get(x_189, 0);
lean_inc(x_193);
lean_dec(x_189);
x_194 = lean_unsigned_to_nat(10u);
x_195 = lean_array_fget(x_68, x_194);
x_196 = l_Lean_Json_getNat_x3f(x_195);
if (lean_obj_tag(x_196) == 0)
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; 
lean_dec(x_193);
lean_dec(x_186);
lean_dec(x_137);
lean_dec(x_130);
lean_dec(x_123);
lean_dec(x_114);
lean_dec(x_103);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_25);
lean_dec(x_15);
lean_dec(x_4);
lean_dec(x_2);
x_197 = lean_ctor_get(x_196, 0);
lean_inc(x_197);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 x_198 = x_196;
} else {
 lean_dec_ref(x_196);
 x_198 = lean_box(0);
}
if (lean_is_scalar(x_198)) {
 x_199 = lean_alloc_ctor(0, 1, 0);
} else {
 x_199 = x_198;
}
lean_ctor_set(x_199, 0, x_197);
return x_199;
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_200 = lean_ctor_get(x_196, 0);
lean_inc(x_200);
lean_dec(x_196);
x_201 = lean_unsigned_to_nat(11u);
x_202 = lean_array_fget(x_68, x_201);
x_203 = l_Lean_Json_getNat_x3f(x_202);
if (lean_obj_tag(x_203) == 0)
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; 
lean_dec(x_200);
lean_dec(x_193);
lean_dec(x_186);
lean_dec(x_137);
lean_dec(x_130);
lean_dec(x_123);
lean_dec(x_114);
lean_dec(x_103);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_25);
lean_dec(x_15);
lean_dec(x_4);
lean_dec(x_2);
x_204 = lean_ctor_get(x_203, 0);
lean_inc(x_204);
if (lean_is_exclusive(x_203)) {
 lean_ctor_release(x_203, 0);
 x_205 = x_203;
} else {
 lean_dec_ref(x_203);
 x_205 = lean_box(0);
}
if (lean_is_scalar(x_205)) {
 x_206 = lean_alloc_ctor(0, 1, 0);
} else {
 x_206 = x_205;
}
lean_ctor_set(x_206, 0, x_204);
return x_206;
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_207 = lean_ctor_get(x_203, 0);
lean_inc(x_207);
lean_dec(x_203);
x_208 = lean_unsigned_to_nat(12u);
x_209 = lean_array_fget(x_68, x_208);
lean_dec(x_68);
x_210 = l_Lean_Json_getNat_x3f(x_209);
if (lean_obj_tag(x_210) == 0)
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; 
lean_dec(x_207);
lean_dec(x_200);
lean_dec(x_193);
lean_dec(x_186);
lean_dec(x_137);
lean_dec(x_130);
lean_dec(x_123);
lean_dec(x_114);
lean_dec(x_103);
lean_dec(x_69);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_25);
lean_dec(x_15);
lean_dec(x_4);
lean_dec(x_2);
x_211 = lean_ctor_get(x_210, 0);
lean_inc(x_211);
if (lean_is_exclusive(x_210)) {
 lean_ctor_release(x_210, 0);
 x_212 = x_210;
} else {
 lean_dec_ref(x_210);
 x_212 = lean_box(0);
}
if (lean_is_scalar(x_212)) {
 x_213 = lean_alloc_ctor(0, 1, 0);
} else {
 x_213 = x_212;
}
lean_ctor_set(x_213, 0, x_211);
return x_213;
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_214 = lean_ctor_get(x_210, 0);
lean_inc(x_214);
lean_dec(x_210);
x_215 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_215, 0, x_123);
lean_ctor_set(x_215, 1, x_130);
x_216 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_216, 0, x_137);
lean_ctor_set(x_216, 1, x_186);
x_217 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_217, 0, x_215);
lean_ctor_set(x_217, 1, x_216);
x_218 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_218, 0, x_193);
lean_ctor_set(x_218, 1, x_200);
x_219 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_219, 0, x_207);
lean_ctor_set(x_219, 1, x_214);
x_220 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_220, 0, x_218);
lean_ctor_set(x_220, 1, x_219);
x_221 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_221, 0, x_114);
lean_ctor_set(x_221, 1, x_217);
lean_ctor_set(x_221, 2, x_220);
if (lean_is_scalar(x_69)) {
 x_222 = lean_alloc_ctor(1, 1, 0);
} else {
 x_222 = x_69;
}
lean_ctor_set(x_222, 0, x_221);
x_223 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_223, 0, x_103);
lean_ctor_set(x_223, 1, x_222);
x_64 = x_223;
goto block_66;
}
}
}
}
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
lean_dec(x_186);
lean_dec(x_137);
lean_dec(x_130);
lean_dec(x_123);
lean_dec(x_114);
lean_dec(x_103);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_25);
lean_dec(x_15);
lean_dec(x_4);
lean_dec(x_2);
x_224 = lean_mk_string_unchecked("Expected list of length 4, not ", 31, 31);
x_225 = l___private_Init_Data_Repr_0__Nat_reprFast(x_70);
x_226 = lean_string_append(x_224, x_225);
lean_dec(x_225);
x_227 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_227, 0, x_226);
return x_227;
}
}
}
}
}
}
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; 
lean_dec(x_114);
lean_dec(x_103);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_25);
lean_dec(x_15);
lean_dec(x_4);
lean_dec(x_2);
x_228 = lean_mk_string_unchecked("Expected list of length 4, not ", 31, 31);
x_229 = l___private_Init_Data_Repr_0__Nat_reprFast(x_70);
x_230 = lean_string_append(x_228, x_229);
lean_dec(x_229);
lean_ctor_set_tag(x_109, 0);
lean_ctor_set(x_109, 0, x_230);
return x_109;
}
}
else
{
lean_object* x_231; lean_object* x_232; uint8_t x_233; 
x_231 = lean_ctor_get(x_109, 0);
lean_inc(x_231);
lean_dec(x_109);
x_232 = lean_unsigned_to_nat(9u);
x_233 = lean_nat_dec_lt(x_70, x_232);
if (x_233 == 0)
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_234 = lean_unsigned_to_nat(5u);
x_235 = lean_array_fget(x_68, x_234);
x_236 = l_Lean_Json_getNat_x3f(x_235);
if (lean_obj_tag(x_236) == 0)
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; 
lean_dec(x_231);
lean_dec(x_103);
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_25);
lean_dec(x_15);
lean_dec(x_4);
lean_dec(x_2);
x_237 = lean_ctor_get(x_236, 0);
lean_inc(x_237);
if (lean_is_exclusive(x_236)) {
 lean_ctor_release(x_236, 0);
 x_238 = x_236;
} else {
 lean_dec_ref(x_236);
 x_238 = lean_box(0);
}
if (lean_is_scalar(x_238)) {
 x_239 = lean_alloc_ctor(0, 1, 0);
} else {
 x_239 = x_238;
}
lean_ctor_set(x_239, 0, x_237);
return x_239;
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; 
x_240 = lean_ctor_get(x_236, 0);
lean_inc(x_240);
lean_dec(x_236);
x_241 = lean_unsigned_to_nat(6u);
x_242 = lean_array_fget(x_68, x_241);
x_243 = l_Lean_Json_getNat_x3f(x_242);
if (lean_obj_tag(x_243) == 0)
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; 
lean_dec(x_240);
lean_dec(x_231);
lean_dec(x_103);
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_25);
lean_dec(x_15);
lean_dec(x_4);
lean_dec(x_2);
x_244 = lean_ctor_get(x_243, 0);
lean_inc(x_244);
if (lean_is_exclusive(x_243)) {
 lean_ctor_release(x_243, 0);
 x_245 = x_243;
} else {
 lean_dec_ref(x_243);
 x_245 = lean_box(0);
}
if (lean_is_scalar(x_245)) {
 x_246 = lean_alloc_ctor(0, 1, 0);
} else {
 x_246 = x_245;
}
lean_ctor_set(x_246, 0, x_244);
return x_246;
}
else
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_247 = lean_ctor_get(x_243, 0);
lean_inc(x_247);
lean_dec(x_243);
x_248 = lean_unsigned_to_nat(7u);
x_249 = lean_array_fget(x_68, x_248);
x_250 = l_Lean_Json_getNat_x3f(x_249);
if (lean_obj_tag(x_250) == 0)
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; 
lean_dec(x_247);
lean_dec(x_240);
lean_dec(x_231);
lean_dec(x_103);
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_25);
lean_dec(x_15);
lean_dec(x_4);
lean_dec(x_2);
x_251 = lean_ctor_get(x_250, 0);
lean_inc(x_251);
if (lean_is_exclusive(x_250)) {
 lean_ctor_release(x_250, 0);
 x_252 = x_250;
} else {
 lean_dec_ref(x_250);
 x_252 = lean_box(0);
}
if (lean_is_scalar(x_252)) {
 x_253 = lean_alloc_ctor(0, 1, 0);
} else {
 x_253 = x_252;
}
lean_ctor_set(x_253, 0, x_251);
return x_253;
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; 
x_254 = lean_ctor_get(x_250, 0);
lean_inc(x_254);
lean_dec(x_250);
x_255 = lean_unsigned_to_nat(8u);
x_256 = lean_array_fget(x_68, x_255);
x_257 = l_Lean_Json_getNat_x3f(x_256);
if (lean_obj_tag(x_257) == 0)
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; 
lean_dec(x_254);
lean_dec(x_247);
lean_dec(x_240);
lean_dec(x_231);
lean_dec(x_103);
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_25);
lean_dec(x_15);
lean_dec(x_4);
lean_dec(x_2);
x_258 = lean_ctor_get(x_257, 0);
lean_inc(x_258);
if (lean_is_exclusive(x_257)) {
 lean_ctor_release(x_257, 0);
 x_259 = x_257;
} else {
 lean_dec_ref(x_257);
 x_259 = lean_box(0);
}
if (lean_is_scalar(x_259)) {
 x_260 = lean_alloc_ctor(0, 1, 0);
} else {
 x_260 = x_259;
}
lean_ctor_set(x_260, 0, x_258);
return x_260;
}
else
{
lean_object* x_261; lean_object* x_262; uint8_t x_263; 
x_261 = lean_ctor_get(x_257, 0);
lean_inc(x_261);
if (lean_is_exclusive(x_257)) {
 lean_ctor_release(x_257, 0);
 x_262 = x_257;
} else {
 lean_dec_ref(x_257);
 x_262 = lean_box(0);
}
x_263 = lean_nat_dec_lt(x_70, x_104);
if (x_263 == 0)
{
lean_object* x_264; lean_object* x_265; 
lean_dec(x_262);
lean_dec(x_70);
x_264 = lean_array_fget(x_68, x_232);
x_265 = l_Lean_Json_getNat_x3f(x_264);
if (lean_obj_tag(x_265) == 0)
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; 
lean_dec(x_261);
lean_dec(x_254);
lean_dec(x_247);
lean_dec(x_240);
lean_dec(x_231);
lean_dec(x_103);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_25);
lean_dec(x_15);
lean_dec(x_4);
lean_dec(x_2);
x_266 = lean_ctor_get(x_265, 0);
lean_inc(x_266);
if (lean_is_exclusive(x_265)) {
 lean_ctor_release(x_265, 0);
 x_267 = x_265;
} else {
 lean_dec_ref(x_265);
 x_267 = lean_box(0);
}
if (lean_is_scalar(x_267)) {
 x_268 = lean_alloc_ctor(0, 1, 0);
} else {
 x_268 = x_267;
}
lean_ctor_set(x_268, 0, x_266);
return x_268;
}
else
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; 
x_269 = lean_ctor_get(x_265, 0);
lean_inc(x_269);
lean_dec(x_265);
x_270 = lean_unsigned_to_nat(10u);
x_271 = lean_array_fget(x_68, x_270);
x_272 = l_Lean_Json_getNat_x3f(x_271);
if (lean_obj_tag(x_272) == 0)
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; 
lean_dec(x_269);
lean_dec(x_261);
lean_dec(x_254);
lean_dec(x_247);
lean_dec(x_240);
lean_dec(x_231);
lean_dec(x_103);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_25);
lean_dec(x_15);
lean_dec(x_4);
lean_dec(x_2);
x_273 = lean_ctor_get(x_272, 0);
lean_inc(x_273);
if (lean_is_exclusive(x_272)) {
 lean_ctor_release(x_272, 0);
 x_274 = x_272;
} else {
 lean_dec_ref(x_272);
 x_274 = lean_box(0);
}
if (lean_is_scalar(x_274)) {
 x_275 = lean_alloc_ctor(0, 1, 0);
} else {
 x_275 = x_274;
}
lean_ctor_set(x_275, 0, x_273);
return x_275;
}
else
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; 
x_276 = lean_ctor_get(x_272, 0);
lean_inc(x_276);
lean_dec(x_272);
x_277 = lean_unsigned_to_nat(11u);
x_278 = lean_array_fget(x_68, x_277);
x_279 = l_Lean_Json_getNat_x3f(x_278);
if (lean_obj_tag(x_279) == 0)
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; 
lean_dec(x_276);
lean_dec(x_269);
lean_dec(x_261);
lean_dec(x_254);
lean_dec(x_247);
lean_dec(x_240);
lean_dec(x_231);
lean_dec(x_103);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_25);
lean_dec(x_15);
lean_dec(x_4);
lean_dec(x_2);
x_280 = lean_ctor_get(x_279, 0);
lean_inc(x_280);
if (lean_is_exclusive(x_279)) {
 lean_ctor_release(x_279, 0);
 x_281 = x_279;
} else {
 lean_dec_ref(x_279);
 x_281 = lean_box(0);
}
if (lean_is_scalar(x_281)) {
 x_282 = lean_alloc_ctor(0, 1, 0);
} else {
 x_282 = x_281;
}
lean_ctor_set(x_282, 0, x_280);
return x_282;
}
else
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; 
x_283 = lean_ctor_get(x_279, 0);
lean_inc(x_283);
lean_dec(x_279);
x_284 = lean_unsigned_to_nat(12u);
x_285 = lean_array_fget(x_68, x_284);
lean_dec(x_68);
x_286 = l_Lean_Json_getNat_x3f(x_285);
if (lean_obj_tag(x_286) == 0)
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; 
lean_dec(x_283);
lean_dec(x_276);
lean_dec(x_269);
lean_dec(x_261);
lean_dec(x_254);
lean_dec(x_247);
lean_dec(x_240);
lean_dec(x_231);
lean_dec(x_103);
lean_dec(x_69);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_25);
lean_dec(x_15);
lean_dec(x_4);
lean_dec(x_2);
x_287 = lean_ctor_get(x_286, 0);
lean_inc(x_287);
if (lean_is_exclusive(x_286)) {
 lean_ctor_release(x_286, 0);
 x_288 = x_286;
} else {
 lean_dec_ref(x_286);
 x_288 = lean_box(0);
}
if (lean_is_scalar(x_288)) {
 x_289 = lean_alloc_ctor(0, 1, 0);
} else {
 x_289 = x_288;
}
lean_ctor_set(x_289, 0, x_287);
return x_289;
}
else
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; 
x_290 = lean_ctor_get(x_286, 0);
lean_inc(x_290);
lean_dec(x_286);
x_291 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_291, 0, x_240);
lean_ctor_set(x_291, 1, x_247);
x_292 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_292, 0, x_254);
lean_ctor_set(x_292, 1, x_261);
x_293 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_293, 0, x_291);
lean_ctor_set(x_293, 1, x_292);
x_294 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_294, 0, x_269);
lean_ctor_set(x_294, 1, x_276);
x_295 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_295, 0, x_283);
lean_ctor_set(x_295, 1, x_290);
x_296 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_296, 0, x_294);
lean_ctor_set(x_296, 1, x_295);
x_297 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_297, 0, x_231);
lean_ctor_set(x_297, 1, x_293);
lean_ctor_set(x_297, 2, x_296);
if (lean_is_scalar(x_69)) {
 x_298 = lean_alloc_ctor(1, 1, 0);
} else {
 x_298 = x_69;
}
lean_ctor_set(x_298, 0, x_297);
x_299 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_299, 0, x_103);
lean_ctor_set(x_299, 1, x_298);
x_64 = x_299;
goto block_66;
}
}
}
}
}
else
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; 
lean_dec(x_261);
lean_dec(x_254);
lean_dec(x_247);
lean_dec(x_240);
lean_dec(x_231);
lean_dec(x_103);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_25);
lean_dec(x_15);
lean_dec(x_4);
lean_dec(x_2);
x_300 = lean_mk_string_unchecked("Expected list of length 4, not ", 31, 31);
x_301 = l___private_Init_Data_Repr_0__Nat_reprFast(x_70);
x_302 = lean_string_append(x_300, x_301);
lean_dec(x_301);
if (lean_is_scalar(x_262)) {
 x_303 = lean_alloc_ctor(0, 1, 0);
} else {
 x_303 = x_262;
 lean_ctor_set_tag(x_303, 0);
}
lean_ctor_set(x_303, 0, x_302);
return x_303;
}
}
}
}
}
}
else
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; 
lean_dec(x_231);
lean_dec(x_103);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_25);
lean_dec(x_15);
lean_dec(x_4);
lean_dec(x_2);
x_304 = lean_mk_string_unchecked("Expected list of length 4, not ", 31, 31);
x_305 = l___private_Init_Data_Repr_0__Nat_reprFast(x_70);
x_306 = lean_string_append(x_304, x_305);
lean_dec(x_305);
x_307 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_307, 0, x_306);
return x_307;
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
lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; 
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_25);
lean_dec(x_15);
lean_dec(x_4);
lean_dec(x_2);
x_308 = lean_mk_string_unchecked("Expected list of length 4, not ", 31, 31);
x_309 = l___private_Init_Data_Repr_0__Nat_reprFast(x_70);
x_310 = lean_string_append(x_308, x_309);
lean_dec(x_309);
if (lean_is_scalar(x_35)) {
 x_311 = lean_alloc_ctor(0, 1, 0);
} else {
 x_311 = x_35;
 lean_ctor_set_tag(x_311, 0);
}
lean_ctor_set(x_311, 0, x_310);
return x_311;
}
}
}
block_63:
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_mk_string_unchecked("usages", 6, 6);
x_41 = l_Lean_Json_getObjValAs_x3f___redArg(x_4, x_38, x_40);
lean_dec(x_40);
if (lean_obj_tag(x_41) == 0)
{
uint8_t x_42; 
lean_dec(x_39);
lean_dec(x_37);
lean_dec(x_25);
lean_dec(x_15);
lean_dec(x_2);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
return x_41;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_41, 0);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_43);
return x_44;
}
}
else
{
lean_object* x_45; size_t x_46; lean_object* x_47; size_t x_48; lean_object* x_49; 
x_45 = lean_ctor_get(x_41, 0);
lean_inc(x_45);
lean_dec(x_41);
x_46 = lean_array_size(x_45);
x_47 = lean_unsigned_to_nat(0u);
x_48 = lean_usize_of_nat(x_47);
x_49 = l_Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), x_25, x_37, x_46, x_48, x_45);
if (lean_obj_tag(x_49) == 0)
{
uint8_t x_50; 
lean_dec(x_39);
lean_dec(x_15);
lean_dec(x_2);
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
return x_49;
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_49, 0);
lean_inc(x_51);
lean_dec(x_49);
x_52 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_52, 0, x_51);
return x_52;
}
}
else
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_49);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_49, 0);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_39);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_ordRefIdent____x40_Lean_Data_Lsp_Internal___hyg_232____boxed), 2, 0);
x_57 = l_Std_DTreeMap_Internal_Impl_insert(lean_box(0), lean_box(0), x_56, x_15, x_55, x_2, lean_box(0));
lean_ctor_set(x_49, 0, x_57);
return x_49;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_58 = lean_ctor_get(x_49, 0);
lean_inc(x_58);
lean_dec(x_49);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_39);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_ordRefIdent____x40_Lean_Data_Lsp_Internal___hyg_232____boxed), 2, 0);
x_61 = l_Std_DTreeMap_Internal_Impl_insert(lean_box(0), lean_box(0), x_60, x_15, x_59, x_2, lean_box(0));
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_61);
return x_62;
}
}
}
}
block_66:
{
lean_object* x_65; 
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_64);
x_39 = x_65;
goto block_63;
}
}
}
else
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; 
x_319 = lean_ctor_get(x_10, 0);
lean_inc(x_319);
lean_dec(x_10);
x_320 = lean_alloc_closure((void*)(l_Except_instMonad___lam__0), 4, 0);
x_321 = lean_alloc_closure((void*)(l_Except_instMonad___lam__1), 4, 0);
x_322 = lean_alloc_closure((void*)(l_Except_instMonad___lam__2___boxed), 4, 0);
x_323 = lean_alloc_closure((void*)(l_Except_instMonad___lam__3___boxed), 4, 0);
x_324 = lean_alloc_closure((void*)(l_Except_map), 5, 1);
lean_closure_set(x_324, 0, lean_box(0));
x_325 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_325, 0, x_324);
lean_ctor_set(x_325, 1, x_320);
x_326 = lean_alloc_closure((void*)(l_Except_pure), 3, 1);
lean_closure_set(x_326, 0, lean_box(0));
x_327 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_327, 0, x_325);
lean_ctor_set(x_327, 1, x_326);
lean_ctor_set(x_327, 2, x_321);
lean_ctor_set(x_327, 3, x_322);
lean_ctor_set(x_327, 4, x_323);
x_328 = lean_alloc_closure((void*)(l_Except_bind), 5, 1);
lean_closure_set(x_328, 0, lean_box(0));
x_329 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_329, 0, x_327);
lean_ctor_set(x_329, 1, x_328);
x_330 = lean_alloc_closure((void*)(l_Lean_instFromJsonJson___lam__0), 1, 0);
x_331 = l_Lean_instFromJsonArray(lean_box(0), x_330);
lean_inc(x_331);
x_332 = lean_alloc_closure((void*)(l_Lean_instFromJsonOption___redArg___lam__0), 2, 1);
lean_closure_set(x_332, 0, x_331);
x_333 = lean_mk_string_unchecked("definition", 10, 10);
lean_inc(x_4);
x_334 = l_Lean_Json_getObjValAs_x3f___redArg(x_4, x_332, x_333);
lean_dec(x_333);
if (lean_obj_tag(x_334) == 0)
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; 
lean_dec(x_331);
lean_dec(x_329);
lean_dec(x_319);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_335 = lean_ctor_get(x_334, 0);
lean_inc(x_335);
if (lean_is_exclusive(x_334)) {
 lean_ctor_release(x_334, 0);
 x_336 = x_334;
} else {
 lean_dec_ref(x_334);
 x_336 = lean_box(0);
}
if (lean_is_scalar(x_336)) {
 x_337 = lean_alloc_ctor(0, 1, 0);
} else {
 x_337 = x_336;
}
lean_ctor_set(x_337, 0, x_335);
return x_337;
}
else
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_364; 
x_338 = lean_ctor_get(x_334, 0);
lean_inc(x_338);
if (lean_is_exclusive(x_334)) {
 lean_ctor_release(x_334, 0);
 x_339 = x_334;
} else {
 lean_dec_ref(x_334);
 x_339 = lean_box(0);
}
x_340 = lean_box(0);
x_341 = lean_alloc_closure((void*)(l_Lean_Lsp_instFromJsonRefInfo___lam__1), 3, 2);
lean_closure_set(x_341, 0, x_1);
lean_closure_set(x_341, 1, x_340);
x_342 = l_Lean_instFromJsonArray(lean_box(0), x_331);
if (lean_obj_tag(x_338) == 0)
{
lean_object* x_367; 
lean_dec(x_339);
x_367 = lean_box(0);
x_343 = x_367;
goto block_363;
}
else
{
lean_object* x_368; lean_object* x_369; lean_object* x_496; lean_object* x_497; uint8_t x_498; 
x_368 = lean_ctor_get(x_338, 0);
lean_inc(x_368);
if (lean_is_exclusive(x_338)) {
 lean_ctor_release(x_338, 0);
 x_369 = x_338;
} else {
 lean_dec_ref(x_338);
 x_369 = lean_box(0);
}
x_496 = lean_array_get_size(x_368);
x_497 = lean_unsigned_to_nat(4u);
x_498 = lean_nat_dec_eq(x_496, x_497);
if (x_498 == 0)
{
lean_object* x_499; uint8_t x_500; 
x_499 = lean_unsigned_to_nat(13u);
x_500 = lean_nat_dec_eq(x_496, x_499);
lean_dec(x_496);
if (x_500 == 0)
{
lean_object* x_501; lean_object* x_502; 
lean_dec(x_369);
lean_dec(x_368);
lean_dec(x_342);
lean_dec(x_341);
lean_dec(x_339);
lean_dec(x_329);
lean_dec(x_319);
lean_dec(x_4);
lean_dec(x_2);
x_501 = lean_mk_string_unchecked("Expected list of length 4 or 13, not {l.size}", 45, 45);
x_502 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_502, 0, x_501);
return x_502;
}
else
{
goto block_495;
}
}
else
{
lean_dec(x_496);
goto block_495;
}
block_495:
{
lean_object* x_370; lean_object* x_371; uint8_t x_372; 
x_370 = lean_array_get_size(x_368);
x_371 = lean_unsigned_to_nat(4u);
x_372 = lean_nat_dec_lt(x_370, x_371);
if (x_372 == 0)
{
lean_object* x_373; lean_object* x_374; lean_object* x_375; 
lean_dec(x_339);
x_373 = lean_unsigned_to_nat(0u);
x_374 = lean_array_fget(x_368, x_373);
x_375 = l_Lean_Json_getNat_x3f(x_374);
if (lean_obj_tag(x_375) == 0)
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; 
lean_dec(x_370);
lean_dec(x_369);
lean_dec(x_368);
lean_dec(x_342);
lean_dec(x_341);
lean_dec(x_329);
lean_dec(x_319);
lean_dec(x_4);
lean_dec(x_2);
x_376 = lean_ctor_get(x_375, 0);
lean_inc(x_376);
if (lean_is_exclusive(x_375)) {
 lean_ctor_release(x_375, 0);
 x_377 = x_375;
} else {
 lean_dec_ref(x_375);
 x_377 = lean_box(0);
}
if (lean_is_scalar(x_377)) {
 x_378 = lean_alloc_ctor(0, 1, 0);
} else {
 x_378 = x_377;
}
lean_ctor_set(x_378, 0, x_376);
return x_378;
}
else
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; 
x_379 = lean_ctor_get(x_375, 0);
lean_inc(x_379);
lean_dec(x_375);
x_380 = lean_unsigned_to_nat(1u);
x_381 = lean_array_fget(x_368, x_380);
x_382 = l_Lean_Json_getNat_x3f(x_381);
if (lean_obj_tag(x_382) == 0)
{
lean_object* x_383; lean_object* x_384; lean_object* x_385; 
lean_dec(x_379);
lean_dec(x_370);
lean_dec(x_369);
lean_dec(x_368);
lean_dec(x_342);
lean_dec(x_341);
lean_dec(x_329);
lean_dec(x_319);
lean_dec(x_4);
lean_dec(x_2);
x_383 = lean_ctor_get(x_382, 0);
lean_inc(x_383);
if (lean_is_exclusive(x_382)) {
 lean_ctor_release(x_382, 0);
 x_384 = x_382;
} else {
 lean_dec_ref(x_382);
 x_384 = lean_box(0);
}
if (lean_is_scalar(x_384)) {
 x_385 = lean_alloc_ctor(0, 1, 0);
} else {
 x_385 = x_384;
}
lean_ctor_set(x_385, 0, x_383);
return x_385;
}
else
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; 
x_386 = lean_ctor_get(x_382, 0);
lean_inc(x_386);
lean_dec(x_382);
x_387 = lean_unsigned_to_nat(2u);
x_388 = lean_array_fget(x_368, x_387);
x_389 = l_Lean_Json_getNat_x3f(x_388);
if (lean_obj_tag(x_389) == 0)
{
lean_object* x_390; lean_object* x_391; lean_object* x_392; 
lean_dec(x_386);
lean_dec(x_379);
lean_dec(x_370);
lean_dec(x_369);
lean_dec(x_368);
lean_dec(x_342);
lean_dec(x_341);
lean_dec(x_329);
lean_dec(x_319);
lean_dec(x_4);
lean_dec(x_2);
x_390 = lean_ctor_get(x_389, 0);
lean_inc(x_390);
if (lean_is_exclusive(x_389)) {
 lean_ctor_release(x_389, 0);
 x_391 = x_389;
} else {
 lean_dec_ref(x_389);
 x_391 = lean_box(0);
}
if (lean_is_scalar(x_391)) {
 x_392 = lean_alloc_ctor(0, 1, 0);
} else {
 x_392 = x_391;
}
lean_ctor_set(x_392, 0, x_390);
return x_392;
}
else
{
lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; 
x_393 = lean_ctor_get(x_389, 0);
lean_inc(x_393);
lean_dec(x_389);
x_394 = lean_unsigned_to_nat(3u);
x_395 = lean_array_fget(x_368, x_394);
x_396 = l_Lean_Json_getNat_x3f(x_395);
if (lean_obj_tag(x_396) == 0)
{
lean_object* x_397; lean_object* x_398; lean_object* x_399; 
lean_dec(x_393);
lean_dec(x_386);
lean_dec(x_379);
lean_dec(x_370);
lean_dec(x_369);
lean_dec(x_368);
lean_dec(x_342);
lean_dec(x_341);
lean_dec(x_329);
lean_dec(x_319);
lean_dec(x_4);
lean_dec(x_2);
x_397 = lean_ctor_get(x_396, 0);
lean_inc(x_397);
if (lean_is_exclusive(x_396)) {
 lean_ctor_release(x_396, 0);
 x_398 = x_396;
} else {
 lean_dec_ref(x_396);
 x_398 = lean_box(0);
}
if (lean_is_scalar(x_398)) {
 x_399 = lean_alloc_ctor(0, 1, 0);
} else {
 x_399 = x_398;
}
lean_ctor_set(x_399, 0, x_397);
return x_399;
}
else
{
lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; uint8_t x_405; 
x_400 = lean_ctor_get(x_396, 0);
lean_inc(x_400);
lean_dec(x_396);
x_401 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_401, 0, x_379);
lean_ctor_set(x_401, 1, x_386);
x_402 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_402, 0, x_393);
lean_ctor_set(x_402, 1, x_400);
x_403 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_403, 0, x_401);
lean_ctor_set(x_403, 1, x_402);
x_404 = lean_unsigned_to_nat(13u);
x_405 = lean_nat_dec_eq(x_370, x_404);
if (x_405 == 0)
{
lean_object* x_406; lean_object* x_407; 
lean_dec(x_370);
lean_dec(x_369);
lean_dec(x_368);
x_406 = lean_box(0);
x_407 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_407, 0, x_403);
lean_ctor_set(x_407, 1, x_406);
x_364 = x_407;
goto block_366;
}
else
{
lean_object* x_408; lean_object* x_409; 
x_408 = lean_array_get(x_340, x_368, x_371);
x_409 = l_Lean_Json_getStr_x3f(x_408);
if (lean_obj_tag(x_409) == 0)
{
lean_object* x_410; lean_object* x_411; lean_object* x_412; 
lean_dec(x_403);
lean_dec(x_370);
lean_dec(x_369);
lean_dec(x_368);
lean_dec(x_342);
lean_dec(x_341);
lean_dec(x_329);
lean_dec(x_319);
lean_dec(x_4);
lean_dec(x_2);
x_410 = lean_ctor_get(x_409, 0);
lean_inc(x_410);
if (lean_is_exclusive(x_409)) {
 lean_ctor_release(x_409, 0);
 x_411 = x_409;
} else {
 lean_dec_ref(x_409);
 x_411 = lean_box(0);
}
if (lean_is_scalar(x_411)) {
 x_412 = lean_alloc_ctor(0, 1, 0);
} else {
 x_412 = x_411;
}
lean_ctor_set(x_412, 0, x_410);
return x_412;
}
else
{
lean_object* x_413; lean_object* x_414; lean_object* x_415; uint8_t x_416; 
x_413 = lean_ctor_get(x_409, 0);
lean_inc(x_413);
if (lean_is_exclusive(x_409)) {
 lean_ctor_release(x_409, 0);
 x_414 = x_409;
} else {
 lean_dec_ref(x_409);
 x_414 = lean_box(0);
}
x_415 = lean_unsigned_to_nat(9u);
x_416 = lean_nat_dec_lt(x_370, x_415);
if (x_416 == 0)
{
lean_object* x_417; lean_object* x_418; lean_object* x_419; 
lean_dec(x_414);
x_417 = lean_unsigned_to_nat(5u);
x_418 = lean_array_fget(x_368, x_417);
x_419 = l_Lean_Json_getNat_x3f(x_418);
if (lean_obj_tag(x_419) == 0)
{
lean_object* x_420; lean_object* x_421; lean_object* x_422; 
lean_dec(x_413);
lean_dec(x_403);
lean_dec(x_370);
lean_dec(x_369);
lean_dec(x_368);
lean_dec(x_342);
lean_dec(x_341);
lean_dec(x_329);
lean_dec(x_319);
lean_dec(x_4);
lean_dec(x_2);
x_420 = lean_ctor_get(x_419, 0);
lean_inc(x_420);
if (lean_is_exclusive(x_419)) {
 lean_ctor_release(x_419, 0);
 x_421 = x_419;
} else {
 lean_dec_ref(x_419);
 x_421 = lean_box(0);
}
if (lean_is_scalar(x_421)) {
 x_422 = lean_alloc_ctor(0, 1, 0);
} else {
 x_422 = x_421;
}
lean_ctor_set(x_422, 0, x_420);
return x_422;
}
else
{
lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; 
x_423 = lean_ctor_get(x_419, 0);
lean_inc(x_423);
lean_dec(x_419);
x_424 = lean_unsigned_to_nat(6u);
x_425 = lean_array_fget(x_368, x_424);
x_426 = l_Lean_Json_getNat_x3f(x_425);
if (lean_obj_tag(x_426) == 0)
{
lean_object* x_427; lean_object* x_428; lean_object* x_429; 
lean_dec(x_423);
lean_dec(x_413);
lean_dec(x_403);
lean_dec(x_370);
lean_dec(x_369);
lean_dec(x_368);
lean_dec(x_342);
lean_dec(x_341);
lean_dec(x_329);
lean_dec(x_319);
lean_dec(x_4);
lean_dec(x_2);
x_427 = lean_ctor_get(x_426, 0);
lean_inc(x_427);
if (lean_is_exclusive(x_426)) {
 lean_ctor_release(x_426, 0);
 x_428 = x_426;
} else {
 lean_dec_ref(x_426);
 x_428 = lean_box(0);
}
if (lean_is_scalar(x_428)) {
 x_429 = lean_alloc_ctor(0, 1, 0);
} else {
 x_429 = x_428;
}
lean_ctor_set(x_429, 0, x_427);
return x_429;
}
else
{
lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; 
x_430 = lean_ctor_get(x_426, 0);
lean_inc(x_430);
lean_dec(x_426);
x_431 = lean_unsigned_to_nat(7u);
x_432 = lean_array_fget(x_368, x_431);
x_433 = l_Lean_Json_getNat_x3f(x_432);
if (lean_obj_tag(x_433) == 0)
{
lean_object* x_434; lean_object* x_435; lean_object* x_436; 
lean_dec(x_430);
lean_dec(x_423);
lean_dec(x_413);
lean_dec(x_403);
lean_dec(x_370);
lean_dec(x_369);
lean_dec(x_368);
lean_dec(x_342);
lean_dec(x_341);
lean_dec(x_329);
lean_dec(x_319);
lean_dec(x_4);
lean_dec(x_2);
x_434 = lean_ctor_get(x_433, 0);
lean_inc(x_434);
if (lean_is_exclusive(x_433)) {
 lean_ctor_release(x_433, 0);
 x_435 = x_433;
} else {
 lean_dec_ref(x_433);
 x_435 = lean_box(0);
}
if (lean_is_scalar(x_435)) {
 x_436 = lean_alloc_ctor(0, 1, 0);
} else {
 x_436 = x_435;
}
lean_ctor_set(x_436, 0, x_434);
return x_436;
}
else
{
lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; 
x_437 = lean_ctor_get(x_433, 0);
lean_inc(x_437);
lean_dec(x_433);
x_438 = lean_unsigned_to_nat(8u);
x_439 = lean_array_fget(x_368, x_438);
x_440 = l_Lean_Json_getNat_x3f(x_439);
if (lean_obj_tag(x_440) == 0)
{
lean_object* x_441; lean_object* x_442; lean_object* x_443; 
lean_dec(x_437);
lean_dec(x_430);
lean_dec(x_423);
lean_dec(x_413);
lean_dec(x_403);
lean_dec(x_370);
lean_dec(x_369);
lean_dec(x_368);
lean_dec(x_342);
lean_dec(x_341);
lean_dec(x_329);
lean_dec(x_319);
lean_dec(x_4);
lean_dec(x_2);
x_441 = lean_ctor_get(x_440, 0);
lean_inc(x_441);
if (lean_is_exclusive(x_440)) {
 lean_ctor_release(x_440, 0);
 x_442 = x_440;
} else {
 lean_dec_ref(x_440);
 x_442 = lean_box(0);
}
if (lean_is_scalar(x_442)) {
 x_443 = lean_alloc_ctor(0, 1, 0);
} else {
 x_443 = x_442;
}
lean_ctor_set(x_443, 0, x_441);
return x_443;
}
else
{
lean_object* x_444; lean_object* x_445; uint8_t x_446; 
x_444 = lean_ctor_get(x_440, 0);
lean_inc(x_444);
if (lean_is_exclusive(x_440)) {
 lean_ctor_release(x_440, 0);
 x_445 = x_440;
} else {
 lean_dec_ref(x_440);
 x_445 = lean_box(0);
}
x_446 = lean_nat_dec_lt(x_370, x_404);
if (x_446 == 0)
{
lean_object* x_447; lean_object* x_448; 
lean_dec(x_445);
lean_dec(x_370);
x_447 = lean_array_fget(x_368, x_415);
x_448 = l_Lean_Json_getNat_x3f(x_447);
if (lean_obj_tag(x_448) == 0)
{
lean_object* x_449; lean_object* x_450; lean_object* x_451; 
lean_dec(x_444);
lean_dec(x_437);
lean_dec(x_430);
lean_dec(x_423);
lean_dec(x_413);
lean_dec(x_403);
lean_dec(x_369);
lean_dec(x_368);
lean_dec(x_342);
lean_dec(x_341);
lean_dec(x_329);
lean_dec(x_319);
lean_dec(x_4);
lean_dec(x_2);
x_449 = lean_ctor_get(x_448, 0);
lean_inc(x_449);
if (lean_is_exclusive(x_448)) {
 lean_ctor_release(x_448, 0);
 x_450 = x_448;
} else {
 lean_dec_ref(x_448);
 x_450 = lean_box(0);
}
if (lean_is_scalar(x_450)) {
 x_451 = lean_alloc_ctor(0, 1, 0);
} else {
 x_451 = x_450;
}
lean_ctor_set(x_451, 0, x_449);
return x_451;
}
else
{
lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; 
x_452 = lean_ctor_get(x_448, 0);
lean_inc(x_452);
lean_dec(x_448);
x_453 = lean_unsigned_to_nat(10u);
x_454 = lean_array_fget(x_368, x_453);
x_455 = l_Lean_Json_getNat_x3f(x_454);
if (lean_obj_tag(x_455) == 0)
{
lean_object* x_456; lean_object* x_457; lean_object* x_458; 
lean_dec(x_452);
lean_dec(x_444);
lean_dec(x_437);
lean_dec(x_430);
lean_dec(x_423);
lean_dec(x_413);
lean_dec(x_403);
lean_dec(x_369);
lean_dec(x_368);
lean_dec(x_342);
lean_dec(x_341);
lean_dec(x_329);
lean_dec(x_319);
lean_dec(x_4);
lean_dec(x_2);
x_456 = lean_ctor_get(x_455, 0);
lean_inc(x_456);
if (lean_is_exclusive(x_455)) {
 lean_ctor_release(x_455, 0);
 x_457 = x_455;
} else {
 lean_dec_ref(x_455);
 x_457 = lean_box(0);
}
if (lean_is_scalar(x_457)) {
 x_458 = lean_alloc_ctor(0, 1, 0);
} else {
 x_458 = x_457;
}
lean_ctor_set(x_458, 0, x_456);
return x_458;
}
else
{
lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; 
x_459 = lean_ctor_get(x_455, 0);
lean_inc(x_459);
lean_dec(x_455);
x_460 = lean_unsigned_to_nat(11u);
x_461 = lean_array_fget(x_368, x_460);
x_462 = l_Lean_Json_getNat_x3f(x_461);
if (lean_obj_tag(x_462) == 0)
{
lean_object* x_463; lean_object* x_464; lean_object* x_465; 
lean_dec(x_459);
lean_dec(x_452);
lean_dec(x_444);
lean_dec(x_437);
lean_dec(x_430);
lean_dec(x_423);
lean_dec(x_413);
lean_dec(x_403);
lean_dec(x_369);
lean_dec(x_368);
lean_dec(x_342);
lean_dec(x_341);
lean_dec(x_329);
lean_dec(x_319);
lean_dec(x_4);
lean_dec(x_2);
x_463 = lean_ctor_get(x_462, 0);
lean_inc(x_463);
if (lean_is_exclusive(x_462)) {
 lean_ctor_release(x_462, 0);
 x_464 = x_462;
} else {
 lean_dec_ref(x_462);
 x_464 = lean_box(0);
}
if (lean_is_scalar(x_464)) {
 x_465 = lean_alloc_ctor(0, 1, 0);
} else {
 x_465 = x_464;
}
lean_ctor_set(x_465, 0, x_463);
return x_465;
}
else
{
lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; 
x_466 = lean_ctor_get(x_462, 0);
lean_inc(x_466);
lean_dec(x_462);
x_467 = lean_unsigned_to_nat(12u);
x_468 = lean_array_fget(x_368, x_467);
lean_dec(x_368);
x_469 = l_Lean_Json_getNat_x3f(x_468);
if (lean_obj_tag(x_469) == 0)
{
lean_object* x_470; lean_object* x_471; lean_object* x_472; 
lean_dec(x_466);
lean_dec(x_459);
lean_dec(x_452);
lean_dec(x_444);
lean_dec(x_437);
lean_dec(x_430);
lean_dec(x_423);
lean_dec(x_413);
lean_dec(x_403);
lean_dec(x_369);
lean_dec(x_342);
lean_dec(x_341);
lean_dec(x_329);
lean_dec(x_319);
lean_dec(x_4);
lean_dec(x_2);
x_470 = lean_ctor_get(x_469, 0);
lean_inc(x_470);
if (lean_is_exclusive(x_469)) {
 lean_ctor_release(x_469, 0);
 x_471 = x_469;
} else {
 lean_dec_ref(x_469);
 x_471 = lean_box(0);
}
if (lean_is_scalar(x_471)) {
 x_472 = lean_alloc_ctor(0, 1, 0);
} else {
 x_472 = x_471;
}
lean_ctor_set(x_472, 0, x_470);
return x_472;
}
else
{
lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; 
x_473 = lean_ctor_get(x_469, 0);
lean_inc(x_473);
lean_dec(x_469);
x_474 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_474, 0, x_423);
lean_ctor_set(x_474, 1, x_430);
x_475 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_475, 0, x_437);
lean_ctor_set(x_475, 1, x_444);
x_476 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_476, 0, x_474);
lean_ctor_set(x_476, 1, x_475);
x_477 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_477, 0, x_452);
lean_ctor_set(x_477, 1, x_459);
x_478 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_478, 0, x_466);
lean_ctor_set(x_478, 1, x_473);
x_479 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_479, 0, x_477);
lean_ctor_set(x_479, 1, x_478);
x_480 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_480, 0, x_413);
lean_ctor_set(x_480, 1, x_476);
lean_ctor_set(x_480, 2, x_479);
if (lean_is_scalar(x_369)) {
 x_481 = lean_alloc_ctor(1, 1, 0);
} else {
 x_481 = x_369;
}
lean_ctor_set(x_481, 0, x_480);
x_482 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_482, 0, x_403);
lean_ctor_set(x_482, 1, x_481);
x_364 = x_482;
goto block_366;
}
}
}
}
}
else
{
lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; 
lean_dec(x_444);
lean_dec(x_437);
lean_dec(x_430);
lean_dec(x_423);
lean_dec(x_413);
lean_dec(x_403);
lean_dec(x_369);
lean_dec(x_368);
lean_dec(x_342);
lean_dec(x_341);
lean_dec(x_329);
lean_dec(x_319);
lean_dec(x_4);
lean_dec(x_2);
x_483 = lean_mk_string_unchecked("Expected list of length 4, not ", 31, 31);
x_484 = l___private_Init_Data_Repr_0__Nat_reprFast(x_370);
x_485 = lean_string_append(x_483, x_484);
lean_dec(x_484);
if (lean_is_scalar(x_445)) {
 x_486 = lean_alloc_ctor(0, 1, 0);
} else {
 x_486 = x_445;
 lean_ctor_set_tag(x_486, 0);
}
lean_ctor_set(x_486, 0, x_485);
return x_486;
}
}
}
}
}
}
else
{
lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; 
lean_dec(x_413);
lean_dec(x_403);
lean_dec(x_369);
lean_dec(x_368);
lean_dec(x_342);
lean_dec(x_341);
lean_dec(x_329);
lean_dec(x_319);
lean_dec(x_4);
lean_dec(x_2);
x_487 = lean_mk_string_unchecked("Expected list of length 4, not ", 31, 31);
x_488 = l___private_Init_Data_Repr_0__Nat_reprFast(x_370);
x_489 = lean_string_append(x_487, x_488);
lean_dec(x_488);
if (lean_is_scalar(x_414)) {
 x_490 = lean_alloc_ctor(0, 1, 0);
} else {
 x_490 = x_414;
 lean_ctor_set_tag(x_490, 0);
}
lean_ctor_set(x_490, 0, x_489);
return x_490;
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
lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; 
lean_dec(x_369);
lean_dec(x_368);
lean_dec(x_342);
lean_dec(x_341);
lean_dec(x_329);
lean_dec(x_319);
lean_dec(x_4);
lean_dec(x_2);
x_491 = lean_mk_string_unchecked("Expected list of length 4, not ", 31, 31);
x_492 = l___private_Init_Data_Repr_0__Nat_reprFast(x_370);
x_493 = lean_string_append(x_491, x_492);
lean_dec(x_492);
if (lean_is_scalar(x_339)) {
 x_494 = lean_alloc_ctor(0, 1, 0);
} else {
 x_494 = x_339;
 lean_ctor_set_tag(x_494, 0);
}
lean_ctor_set(x_494, 0, x_493);
return x_494;
}
}
}
block_363:
{
lean_object* x_344; lean_object* x_345; 
x_344 = lean_mk_string_unchecked("usages", 6, 6);
x_345 = l_Lean_Json_getObjValAs_x3f___redArg(x_4, x_342, x_344);
lean_dec(x_344);
if (lean_obj_tag(x_345) == 0)
{
lean_object* x_346; lean_object* x_347; lean_object* x_348; 
lean_dec(x_343);
lean_dec(x_341);
lean_dec(x_329);
lean_dec(x_319);
lean_dec(x_2);
x_346 = lean_ctor_get(x_345, 0);
lean_inc(x_346);
if (lean_is_exclusive(x_345)) {
 lean_ctor_release(x_345, 0);
 x_347 = x_345;
} else {
 lean_dec_ref(x_345);
 x_347 = lean_box(0);
}
if (lean_is_scalar(x_347)) {
 x_348 = lean_alloc_ctor(0, 1, 0);
} else {
 x_348 = x_347;
}
lean_ctor_set(x_348, 0, x_346);
return x_348;
}
else
{
lean_object* x_349; size_t x_350; lean_object* x_351; size_t x_352; lean_object* x_353; 
x_349 = lean_ctor_get(x_345, 0);
lean_inc(x_349);
lean_dec(x_345);
x_350 = lean_array_size(x_349);
x_351 = lean_unsigned_to_nat(0u);
x_352 = lean_usize_of_nat(x_351);
x_353 = l_Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), x_329, x_341, x_350, x_352, x_349);
if (lean_obj_tag(x_353) == 0)
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; 
lean_dec(x_343);
lean_dec(x_319);
lean_dec(x_2);
x_354 = lean_ctor_get(x_353, 0);
lean_inc(x_354);
if (lean_is_exclusive(x_353)) {
 lean_ctor_release(x_353, 0);
 x_355 = x_353;
} else {
 lean_dec_ref(x_353);
 x_355 = lean_box(0);
}
if (lean_is_scalar(x_355)) {
 x_356 = lean_alloc_ctor(0, 1, 0);
} else {
 x_356 = x_355;
}
lean_ctor_set(x_356, 0, x_354);
return x_356;
}
else
{
lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; 
x_357 = lean_ctor_get(x_353, 0);
lean_inc(x_357);
if (lean_is_exclusive(x_353)) {
 lean_ctor_release(x_353, 0);
 x_358 = x_353;
} else {
 lean_dec_ref(x_353);
 x_358 = lean_box(0);
}
x_359 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_359, 0, x_343);
lean_ctor_set(x_359, 1, x_357);
x_360 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_ordRefIdent____x40_Lean_Data_Lsp_Internal___hyg_232____boxed), 2, 0);
x_361 = l_Std_DTreeMap_Internal_Impl_insert(lean_box(0), lean_box(0), x_360, x_319, x_359, x_2, lean_box(0));
if (lean_is_scalar(x_358)) {
 x_362 = lean_alloc_ctor(1, 1, 0);
} else {
 x_362 = x_358;
}
lean_ctor_set(x_362, 0, x_361);
return x_362;
}
}
}
block_366:
{
lean_object* x_365; 
x_365 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_365, 0, x_364);
x_343 = x_365;
goto block_363;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonModuleRefs___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Json_getObj_x3f(x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
lean_dec(x_2);
lean_dec(x_1);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
lean_dec(x_4);
x_9 = lean_box(1);
x_10 = l_Lean_RBNode_foldM___redArg(x_1, x_2, x_9, x_8);
return x_10;
}
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonModuleRefs() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_1 = lean_alloc_closure((void*)(l_Lean_Lsp_instFromJsonRefInfo___lam__0___boxed), 2, 0);
x_2 = lean_alloc_closure((void*)(l_Lean_Lsp_instFromJsonModuleRefs___lam__2), 4, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = lean_alloc_closure((void*)(l_Except_instMonad___lam__0), 4, 0);
x_4 = lean_alloc_closure((void*)(l_Except_instMonad___lam__1), 4, 0);
x_5 = lean_alloc_closure((void*)(l_Except_instMonad___lam__2___boxed), 4, 0);
x_6 = lean_alloc_closure((void*)(l_Except_instMonad___lam__3___boxed), 4, 0);
x_7 = lean_alloc_closure((void*)(l_Except_map), 5, 1);
lean_closure_set(x_7, 0, lean_box(0));
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
x_9 = lean_alloc_closure((void*)(l_Except_pure), 3, 1);
lean_closure_set(x_9, 0, lean_box(0));
x_10 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
lean_ctor_set(x_10, 2, x_4);
lean_ctor_set(x_10, 3, x_5);
lean_ctor_set(x_10, 4, x_6);
x_11 = lean_alloc_closure((void*)(l_Except_bind), 5, 1);
lean_closure_set(x_11, 0, lean_box(0));
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_closure((void*)(l_Lean_Lsp_instFromJsonModuleRefs___lam__0), 3, 2);
lean_closure_set(x_13, 0, x_12);
lean_closure_set(x_13, 1, x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Json_getObjValAs_x3f___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2193__spec__0_spec__0_spec__0_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_3);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = lean_array_uget(x_3, x_2);
if (lean_obj_tag(x_6) == 4)
{
lean_object* x_7; size_t x_8; lean_object* x_9; size_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_array_size(x_7);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_usize_of_nat(x_9);
x_11 = l_Array_mapMUnsafe_map___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Basic_0__Lean_Lsp_fromJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1614__spec__0_spec__0(x_8, x_10, x_7);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_box(0);
x_14 = lean_array_uset(x_3, x_2, x_13);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_usize_of_nat(x_15);
x_17 = lean_usize_add(x_2, x_16);
x_18 = lean_array_uset(x_14, x_2, x_12);
x_2 = x_17;
x_3 = x_18;
goto _start;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_3);
x_20 = lean_mk_string_unchecked("expected JSON array, got '", 26, 26);
x_21 = lean_unsigned_to_nat(80u);
x_22 = l_Lean_Json_pretty(x_6, x_21);
x_23 = lean_string_append(x_20, x_22);
lean_dec(x_22);
x_24 = lean_mk_string_unchecked("'", 1, 1);
x_25 = lean_string_append(x_23, x_24);
lean_dec(x_24);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Json_getObjValAs_x3f___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2193__spec__0_spec__0_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_3);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = lean_array_uget(x_3, x_2);
if (lean_obj_tag(x_6) == 4)
{
lean_object* x_7; size_t x_8; lean_object* x_9; size_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_array_size(x_7);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_usize_of_nat(x_9);
x_11 = l_Array_mapMUnsafe_map___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Basic_0__Lean_Lsp_fromJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1614__spec__0_spec__0(x_8, x_10, x_7);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_box(0);
x_14 = lean_array_uset(x_3, x_2, x_13);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_usize_of_nat(x_15);
x_17 = lean_usize_add(x_2, x_16);
x_18 = lean_array_uset(x_14, x_2, x_12);
x_19 = l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Json_getObjValAs_x3f___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2193__spec__0_spec__0_spec__0_spec__0(x_1, x_17, x_18);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_3);
x_20 = lean_mk_string_unchecked("expected JSON array, got '", 26, 26);
x_21 = lean_unsigned_to_nat(80u);
x_22 = l_Lean_Json_pretty(x_6, x_21);
x_23 = lean_string_append(x_20, x_22);
lean_dec(x_22);
x_24 = lean_mk_string_unchecked("'", 1, 1);
x_25 = lean_string_append(x_23, x_24);
lean_dec(x_24);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2193__spec__0_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
if (lean_obj_tag(x_3) == 4)
{
lean_object* x_4; size_t x_5; lean_object* x_6; size_t x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_array_size(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_usize_of_nat(x_6);
x_8 = l_Array_mapMUnsafe_map___at___Lean_Json_getObjValAs_x3f___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2193__spec__0_spec__0_spec__0(x_5, x_7, x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_mk_string_unchecked("expected JSON array, got '", 26, 26);
x_10 = lean_unsigned_to_nat(80u);
x_11 = l_Lean_Json_pretty(x_3, x_10);
x_12 = lean_string_append(x_9, x_11);
lean_dec(x_11);
x_13 = lean_mk_string_unchecked("'", 1, 1);
x_14 = lean_string_append(x_12, x_13);
lean_dec(x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2193__spec__0_spec__3___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_unsigned_to_nat(4u);
x_5 = lean_nat_add(x_2, x_4);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_7 = lean_array_fget(x_1, x_2);
x_8 = l_Lean_Json_getNat_x3f(x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
return x_8;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_2, x_13);
x_15 = lean_array_fget(x_1, x_14);
lean_dec(x_14);
x_16 = l_Lean_Json_getNat_x3f(x_15);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
lean_dec(x_12);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
return x_16;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_16, 0);
lean_inc(x_20);
lean_dec(x_16);
x_21 = lean_unsigned_to_nat(2u);
x_22 = lean_nat_add(x_2, x_21);
x_23 = lean_array_fget(x_1, x_22);
lean_dec(x_22);
x_24 = l_Lean_Json_getNat_x3f(x_23);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
lean_dec(x_20);
lean_dec(x_12);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
return x_24;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_24, 0);
lean_inc(x_28);
lean_dec(x_24);
x_29 = lean_unsigned_to_nat(3u);
x_30 = lean_nat_add(x_2, x_29);
x_31 = lean_array_fget(x_1, x_30);
lean_dec(x_30);
x_32 = l_Lean_Json_getNat_x3f(x_31);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
lean_dec(x_28);
lean_dec(x_20);
lean_dec(x_12);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
return x_32;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
}
else
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_32);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_32, 0);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_12);
lean_ctor_set(x_38, 1, x_20);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_28);
lean_ctor_set(x_39, 1, x_37);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
lean_ctor_set(x_32, 0, x_40);
return x_32;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_41 = lean_ctor_get(x_32, 0);
lean_inc(x_41);
lean_dec(x_32);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_12);
lean_ctor_set(x_42, 1, x_20);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_28);
lean_ctor_set(x_43, 1, x_41);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_44);
return x_45;
}
}
}
}
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_46 = lean_mk_string_unchecked("Expected list of length 4, not ", 31, 31);
x_47 = l___private_Init_Data_Repr_0__Nat_reprFast(x_3);
x_48 = lean_string_append(x_46, x_47);
lean_dec(x_47);
x_49 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_49, 0, x_48);
return x_49;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2193__spec__0_spec__3(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_6 = lean_box(0);
x_7 = lean_array_uget(x_3, x_2);
x_8 = lean_box(0);
x_9 = lean_array_uset(x_3, x_2, x_8);
x_51 = lean_array_get_size(x_7);
x_52 = lean_unsigned_to_nat(4u);
x_53 = lean_nat_dec_eq(x_51, x_52);
if (x_53 == 0)
{
lean_object* x_54; uint8_t x_55; 
x_54 = lean_unsigned_to_nat(13u);
x_55 = lean_nat_dec_eq(x_51, x_54);
lean_dec(x_51);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
lean_dec(x_9);
lean_dec(x_7);
x_56 = lean_mk_string_unchecked("Expected list of length 4 or 13, not {l.size}", 45, 45);
x_57 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_57, 0, x_56);
return x_57;
}
else
{
goto block_50;
}
}
else
{
lean_dec(x_51);
goto block_50;
}
block_16:
{
lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_usize_of_nat(x_11);
x_13 = lean_usize_add(x_2, x_12);
x_14 = lean_array_uset(x_9, x_2, x_10);
x_2 = x_13;
x_3 = x_14;
goto _start;
}
block_50:
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_unsigned_to_nat(0u);
x_18 = l_Array_mapMUnsafe_map___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2193__spec__0_spec__3___lam__0(x_7, x_17);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
lean_dec(x_9);
lean_dec(x_7);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
return x_18;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_18, 0);
lean_inc(x_22);
lean_dec(x_18);
x_23 = lean_array_get_size(x_7);
x_24 = lean_unsigned_to_nat(13u);
x_25 = lean_nat_dec_eq(x_23, x_24);
lean_dec(x_23);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_7);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_22);
lean_ctor_set(x_27, 1, x_26);
x_10 = x_27;
goto block_16;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_unsigned_to_nat(4u);
x_29 = lean_array_get(x_6, x_7, x_28);
x_30 = l_Lean_Json_getStr_x3f(x_29);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_7);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
return x_30;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_30, 0);
lean_inc(x_34);
lean_dec(x_30);
x_35 = lean_unsigned_to_nat(5u);
x_36 = l_Array_mapMUnsafe_map___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2193__spec__0_spec__3___lam__0(x_7, x_35);
if (lean_obj_tag(x_36) == 0)
{
uint8_t x_37; 
lean_dec(x_34);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_7);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
return x_36;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_36, 0);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_38);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_36, 0);
lean_inc(x_40);
lean_dec(x_36);
x_41 = lean_unsigned_to_nat(9u);
x_42 = l_Array_mapMUnsafe_map___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2193__spec__0_spec__3___lam__0(x_7, x_41);
lean_dec(x_7);
if (lean_obj_tag(x_42) == 0)
{
uint8_t x_43; 
lean_dec(x_40);
lean_dec(x_34);
lean_dec(x_22);
lean_dec(x_9);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
return x_42;
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_42, 0);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_45, 0, x_44);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_46 = lean_ctor_get(x_42, 0);
lean_inc(x_46);
lean_dec(x_42);
x_47 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_47, 0, x_34);
lean_ctor_set(x_47, 1, x_40);
lean_ctor_set(x_47, 2, x_46);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_22);
lean_ctor_set(x_49, 1, x_48);
x_10 = x_49;
goto block_16;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2193__spec__0_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 3);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 4);
lean_inc(x_8);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 lean_ctor_release(x_3, 4);
 x_9 = x_3;
} else {
 lean_dec_ref(x_3);
 x_9 = lean_box(0);
}
x_10 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_ordRefIdent____x40_Lean_Data_Lsp_Internal___hyg_232_(x_1, x_5);
switch (x_10) {
case 0:
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_4);
x_11 = l_Std_DTreeMap_Internal_Impl_insert___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2193__spec__0_spec__4___redArg(x_1, x_2, x_7);
x_12 = lean_unsigned_to_nat(1u);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_13 = lean_ctor_get(x_8, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_11, 2);
lean_inc(x_16);
x_17 = lean_ctor_get(x_11, 3);
lean_inc(x_17);
x_18 = lean_ctor_get(x_11, 4);
lean_inc(x_18);
x_19 = lean_unsigned_to_nat(3u);
x_20 = lean_nat_mul(x_19, x_13);
x_21 = lean_nat_dec_lt(x_20, x_14);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
x_22 = lean_nat_add(x_12, x_14);
lean_dec(x_14);
x_23 = lean_nat_add(x_22, x_13);
lean_dec(x_13);
lean_dec(x_22);
if (lean_is_scalar(x_9)) {
 x_24 = lean_alloc_ctor(0, 5, 0);
} else {
 x_24 = x_9;
}
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_5);
lean_ctor_set(x_24, 2, x_6);
lean_ctor_set(x_24, 3, x_11);
lean_ctor_set(x_24, 4, x_8);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 lean_ctor_release(x_11, 2);
 lean_ctor_release(x_11, 3);
 lean_ctor_release(x_11, 4);
 x_25 = x_11;
} else {
 lean_dec_ref(x_11);
 x_25 = lean_box(0);
}
x_26 = lean_ctor_get(x_17, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_18, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_18, 1);
lean_inc(x_28);
x_29 = lean_ctor_get(x_18, 2);
lean_inc(x_29);
x_30 = lean_ctor_get(x_18, 3);
lean_inc(x_30);
x_31 = lean_ctor_get(x_18, 4);
lean_inc(x_31);
x_32 = lean_nat_shiftl(x_26, x_12);
x_33 = lean_nat_dec_lt(x_27, x_32);
lean_dec(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_44; lean_object* x_45; 
lean_dec(x_27);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 lean_ctor_release(x_18, 2);
 lean_ctor_release(x_18, 3);
 lean_ctor_release(x_18, 4);
 x_34 = x_18;
} else {
 lean_dec_ref(x_18);
 x_34 = lean_box(0);
}
x_35 = lean_nat_add(x_12, x_14);
lean_dec(x_14);
x_36 = lean_nat_add(x_35, x_13);
lean_dec(x_35);
x_44 = lean_nat_add(x_12, x_26);
lean_dec(x_26);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_30, 0);
lean_inc(x_52);
x_45 = x_52;
goto block_51;
}
else
{
lean_object* x_53; 
x_53 = lean_unsigned_to_nat(0u);
x_45 = x_53;
goto block_51;
}
block_43:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_nat_add(x_37, x_39);
lean_dec(x_39);
lean_dec(x_37);
if (lean_is_scalar(x_34)) {
 x_41 = lean_alloc_ctor(0, 5, 0);
} else {
 x_41 = x_34;
}
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_5);
lean_ctor_set(x_41, 2, x_6);
lean_ctor_set(x_41, 3, x_31);
lean_ctor_set(x_41, 4, x_8);
if (lean_is_scalar(x_25)) {
 x_42 = lean_alloc_ctor(0, 5, 0);
} else {
 x_42 = x_25;
}
lean_ctor_set(x_42, 0, x_36);
lean_ctor_set(x_42, 1, x_28);
lean_ctor_set(x_42, 2, x_29);
lean_ctor_set(x_42, 3, x_38);
lean_ctor_set(x_42, 4, x_41);
return x_42;
}
block_51:
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_nat_add(x_44, x_45);
lean_dec(x_45);
lean_dec(x_44);
if (lean_is_scalar(x_9)) {
 x_47 = lean_alloc_ctor(0, 5, 0);
} else {
 x_47 = x_9;
}
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_15);
lean_ctor_set(x_47, 2, x_16);
lean_ctor_set(x_47, 3, x_17);
lean_ctor_set(x_47, 4, x_30);
x_48 = lean_nat_add(x_12, x_13);
lean_dec(x_13);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_31, 0);
lean_inc(x_49);
x_37 = x_48;
x_38 = x_47;
x_39 = x_49;
goto block_43;
}
else
{
lean_object* x_50; 
x_50 = lean_unsigned_to_nat(0u);
x_37 = x_48;
x_38 = x_47;
x_39 = x_50;
goto block_43;
}
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_9);
x_54 = lean_nat_add(x_12, x_14);
lean_dec(x_14);
x_55 = lean_nat_add(x_54, x_13);
lean_dec(x_54);
x_56 = lean_nat_add(x_12, x_13);
lean_dec(x_13);
x_57 = lean_nat_add(x_56, x_27);
lean_dec(x_27);
lean_dec(x_56);
lean_inc(x_8);
if (lean_is_scalar(x_25)) {
 x_58 = lean_alloc_ctor(0, 5, 0);
} else {
 x_58 = x_25;
}
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_5);
lean_ctor_set(x_58, 2, x_6);
lean_ctor_set(x_58, 3, x_18);
lean_ctor_set(x_58, 4, x_8);
x_59 = !lean_is_exclusive(x_8);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_60 = lean_ctor_get(x_8, 4);
lean_dec(x_60);
x_61 = lean_ctor_get(x_8, 3);
lean_dec(x_61);
x_62 = lean_ctor_get(x_8, 2);
lean_dec(x_62);
x_63 = lean_ctor_get(x_8, 1);
lean_dec(x_63);
x_64 = lean_ctor_get(x_8, 0);
lean_dec(x_64);
lean_ctor_set(x_8, 4, x_58);
lean_ctor_set(x_8, 3, x_17);
lean_ctor_set(x_8, 2, x_16);
lean_ctor_set(x_8, 1, x_15);
lean_ctor_set(x_8, 0, x_55);
return x_8;
}
else
{
lean_object* x_65; 
lean_dec(x_8);
x_65 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_65, 0, x_55);
lean_ctor_set(x_65, 1, x_15);
lean_ctor_set(x_65, 2, x_16);
lean_ctor_set(x_65, 3, x_17);
lean_ctor_set(x_65, 4, x_58);
return x_65;
}
}
}
}
else
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_11, 3);
lean_inc(x_66);
if (lean_obj_tag(x_66) == 0)
{
uint8_t x_67; 
x_67 = !lean_is_exclusive(x_11);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_68 = lean_ctor_get(x_11, 4);
x_69 = lean_ctor_get(x_11, 1);
x_70 = lean_ctor_get(x_11, 2);
x_71 = lean_ctor_get(x_11, 3);
lean_dec(x_71);
x_72 = lean_ctor_get(x_11, 0);
lean_dec(x_72);
x_73 = lean_unsigned_to_nat(3u);
lean_inc(x_68);
lean_ctor_set(x_11, 3, x_68);
lean_ctor_set(x_11, 2, x_6);
lean_ctor_set(x_11, 1, x_5);
lean_ctor_set(x_11, 0, x_12);
if (lean_is_scalar(x_9)) {
 x_74 = lean_alloc_ctor(0, 5, 0);
} else {
 x_74 = x_9;
}
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_69);
lean_ctor_set(x_74, 2, x_70);
lean_ctor_set(x_74, 3, x_66);
lean_ctor_set(x_74, 4, x_11);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_75 = lean_ctor_get(x_11, 4);
x_76 = lean_ctor_get(x_11, 1);
x_77 = lean_ctor_get(x_11, 2);
lean_inc(x_75);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_11);
x_78 = lean_unsigned_to_nat(3u);
lean_inc(x_75);
x_79 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_79, 0, x_12);
lean_ctor_set(x_79, 1, x_5);
lean_ctor_set(x_79, 2, x_6);
lean_ctor_set(x_79, 3, x_75);
lean_ctor_set(x_79, 4, x_75);
if (lean_is_scalar(x_9)) {
 x_80 = lean_alloc_ctor(0, 5, 0);
} else {
 x_80 = x_9;
}
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_76);
lean_ctor_set(x_80, 2, x_77);
lean_ctor_set(x_80, 3, x_66);
lean_ctor_set(x_80, 4, x_79);
return x_80;
}
}
else
{
lean_object* x_81; 
x_81 = lean_ctor_get(x_11, 4);
lean_inc(x_81);
if (lean_obj_tag(x_81) == 0)
{
uint8_t x_82; 
x_82 = !lean_is_exclusive(x_11);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_83 = lean_ctor_get(x_11, 1);
x_84 = lean_ctor_get(x_11, 2);
x_85 = lean_ctor_get(x_11, 4);
lean_dec(x_85);
x_86 = lean_ctor_get(x_11, 3);
lean_dec(x_86);
x_87 = lean_ctor_get(x_11, 0);
lean_dec(x_87);
x_88 = !lean_is_exclusive(x_81);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_89 = lean_ctor_get(x_81, 1);
x_90 = lean_ctor_get(x_81, 2);
x_91 = lean_ctor_get(x_81, 4);
lean_dec(x_91);
x_92 = lean_ctor_get(x_81, 3);
lean_dec(x_92);
x_93 = lean_ctor_get(x_81, 0);
lean_dec(x_93);
x_94 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_81, 4, x_66);
lean_ctor_set(x_81, 3, x_66);
lean_ctor_set(x_81, 2, x_84);
lean_ctor_set(x_81, 1, x_83);
lean_ctor_set(x_81, 0, x_12);
lean_ctor_set(x_11, 4, x_66);
lean_ctor_set(x_11, 2, x_6);
lean_ctor_set(x_11, 1, x_5);
lean_ctor_set(x_11, 0, x_12);
if (lean_is_scalar(x_9)) {
 x_95 = lean_alloc_ctor(0, 5, 0);
} else {
 x_95 = x_9;
}
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_89);
lean_ctor_set(x_95, 2, x_90);
lean_ctor_set(x_95, 3, x_81);
lean_ctor_set(x_95, 4, x_11);
return x_95;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_96 = lean_ctor_get(x_81, 1);
x_97 = lean_ctor_get(x_81, 2);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_81);
x_98 = lean_unsigned_to_nat(3u);
x_99 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_99, 0, x_12);
lean_ctor_set(x_99, 1, x_83);
lean_ctor_set(x_99, 2, x_84);
lean_ctor_set(x_99, 3, x_66);
lean_ctor_set(x_99, 4, x_66);
lean_ctor_set(x_11, 4, x_66);
lean_ctor_set(x_11, 2, x_6);
lean_ctor_set(x_11, 1, x_5);
lean_ctor_set(x_11, 0, x_12);
if (lean_is_scalar(x_9)) {
 x_100 = lean_alloc_ctor(0, 5, 0);
} else {
 x_100 = x_9;
}
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_96);
lean_ctor_set(x_100, 2, x_97);
lean_ctor_set(x_100, 3, x_99);
lean_ctor_set(x_100, 4, x_11);
return x_100;
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_101 = lean_ctor_get(x_11, 1);
x_102 = lean_ctor_get(x_11, 2);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_11);
x_103 = lean_ctor_get(x_81, 1);
lean_inc(x_103);
x_104 = lean_ctor_get(x_81, 2);
lean_inc(x_104);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 lean_ctor_release(x_81, 2);
 lean_ctor_release(x_81, 3);
 lean_ctor_release(x_81, 4);
 x_105 = x_81;
} else {
 lean_dec_ref(x_81);
 x_105 = lean_box(0);
}
x_106 = lean_unsigned_to_nat(3u);
if (lean_is_scalar(x_105)) {
 x_107 = lean_alloc_ctor(0, 5, 0);
} else {
 x_107 = x_105;
}
lean_ctor_set(x_107, 0, x_12);
lean_ctor_set(x_107, 1, x_101);
lean_ctor_set(x_107, 2, x_102);
lean_ctor_set(x_107, 3, x_66);
lean_ctor_set(x_107, 4, x_66);
x_108 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_108, 0, x_12);
lean_ctor_set(x_108, 1, x_5);
lean_ctor_set(x_108, 2, x_6);
lean_ctor_set(x_108, 3, x_66);
lean_ctor_set(x_108, 4, x_66);
if (lean_is_scalar(x_9)) {
 x_109 = lean_alloc_ctor(0, 5, 0);
} else {
 x_109 = x_9;
}
lean_ctor_set(x_109, 0, x_106);
lean_ctor_set(x_109, 1, x_103);
lean_ctor_set(x_109, 2, x_104);
lean_ctor_set(x_109, 3, x_107);
lean_ctor_set(x_109, 4, x_108);
return x_109;
}
}
else
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_unsigned_to_nat(2u);
if (lean_is_scalar(x_9)) {
 x_111 = lean_alloc_ctor(0, 5, 0);
} else {
 x_111 = x_9;
}
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_5);
lean_ctor_set(x_111, 2, x_6);
lean_ctor_set(x_111, 3, x_11);
lean_ctor_set(x_111, 4, x_81);
return x_111;
}
}
}
}
case 1:
{
lean_object* x_112; 
lean_dec(x_6);
lean_dec(x_5);
if (lean_is_scalar(x_9)) {
 x_112 = lean_alloc_ctor(0, 5, 0);
} else {
 x_112 = x_9;
}
lean_ctor_set(x_112, 0, x_4);
lean_ctor_set(x_112, 1, x_1);
lean_ctor_set(x_112, 2, x_2);
lean_ctor_set(x_112, 3, x_7);
lean_ctor_set(x_112, 4, x_8);
return x_112;
}
default: 
{
lean_object* x_113; lean_object* x_114; 
lean_dec(x_4);
x_113 = l_Std_DTreeMap_Internal_Impl_insert___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2193__spec__0_spec__4___redArg(x_1, x_2, x_8);
x_114 = lean_unsigned_to_nat(1u);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; 
x_115 = lean_ctor_get(x_7, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_113, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_113, 1);
lean_inc(x_117);
x_118 = lean_ctor_get(x_113, 2);
lean_inc(x_118);
x_119 = lean_ctor_get(x_113, 3);
lean_inc(x_119);
x_120 = lean_ctor_get(x_113, 4);
lean_inc(x_120);
x_121 = lean_unsigned_to_nat(3u);
x_122 = lean_nat_mul(x_121, x_115);
x_123 = lean_nat_dec_lt(x_122, x_116);
lean_dec(x_122);
if (x_123 == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
lean_dec(x_120);
lean_dec(x_119);
lean_dec(x_118);
lean_dec(x_117);
x_124 = lean_nat_add(x_114, x_115);
lean_dec(x_115);
x_125 = lean_nat_add(x_124, x_116);
lean_dec(x_116);
lean_dec(x_124);
if (lean_is_scalar(x_9)) {
 x_126 = lean_alloc_ctor(0, 5, 0);
} else {
 x_126 = x_9;
}
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_5);
lean_ctor_set(x_126, 2, x_6);
lean_ctor_set(x_126, 3, x_7);
lean_ctor_set(x_126, 4, x_113);
return x_126;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; 
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 lean_ctor_release(x_113, 2);
 lean_ctor_release(x_113, 3);
 lean_ctor_release(x_113, 4);
 x_127 = x_113;
} else {
 lean_dec_ref(x_113);
 x_127 = lean_box(0);
}
x_128 = lean_ctor_get(x_119, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_119, 1);
lean_inc(x_129);
x_130 = lean_ctor_get(x_119, 2);
lean_inc(x_130);
x_131 = lean_ctor_get(x_119, 3);
lean_inc(x_131);
x_132 = lean_ctor_get(x_119, 4);
lean_inc(x_132);
x_133 = lean_ctor_get(x_120, 0);
lean_inc(x_133);
x_134 = lean_nat_shiftl(x_133, x_114);
x_135 = lean_nat_dec_lt(x_128, x_134);
lean_dec(x_134);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_146; 
lean_dec(x_128);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 lean_ctor_release(x_119, 2);
 lean_ctor_release(x_119, 3);
 lean_ctor_release(x_119, 4);
 x_136 = x_119;
} else {
 lean_dec_ref(x_119);
 x_136 = lean_box(0);
}
x_137 = lean_nat_add(x_114, x_115);
lean_dec(x_115);
x_138 = lean_nat_add(x_137, x_116);
lean_dec(x_116);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_153; 
x_153 = lean_ctor_get(x_131, 0);
lean_inc(x_153);
x_146 = x_153;
goto block_152;
}
else
{
lean_object* x_154; 
x_154 = lean_unsigned_to_nat(0u);
x_146 = x_154;
goto block_152;
}
block_145:
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_142 = lean_nat_add(x_139, x_141);
lean_dec(x_141);
lean_dec(x_139);
if (lean_is_scalar(x_136)) {
 x_143 = lean_alloc_ctor(0, 5, 0);
} else {
 x_143 = x_136;
}
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_117);
lean_ctor_set(x_143, 2, x_118);
lean_ctor_set(x_143, 3, x_132);
lean_ctor_set(x_143, 4, x_120);
if (lean_is_scalar(x_127)) {
 x_144 = lean_alloc_ctor(0, 5, 0);
} else {
 x_144 = x_127;
}
lean_ctor_set(x_144, 0, x_138);
lean_ctor_set(x_144, 1, x_129);
lean_ctor_set(x_144, 2, x_130);
lean_ctor_set(x_144, 3, x_140);
lean_ctor_set(x_144, 4, x_143);
return x_144;
}
block_152:
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_147 = lean_nat_add(x_137, x_146);
lean_dec(x_146);
lean_dec(x_137);
if (lean_is_scalar(x_9)) {
 x_148 = lean_alloc_ctor(0, 5, 0);
} else {
 x_148 = x_9;
}
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_5);
lean_ctor_set(x_148, 2, x_6);
lean_ctor_set(x_148, 3, x_7);
lean_ctor_set(x_148, 4, x_131);
x_149 = lean_nat_add(x_114, x_133);
lean_dec(x_133);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_150; 
x_150 = lean_ctor_get(x_132, 0);
lean_inc(x_150);
x_139 = x_149;
x_140 = x_148;
x_141 = x_150;
goto block_145;
}
else
{
lean_object* x_151; 
x_151 = lean_unsigned_to_nat(0u);
x_139 = x_149;
x_140 = x_148;
x_141 = x_151;
goto block_145;
}
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; 
lean_dec(x_133);
lean_dec(x_132);
lean_dec(x_131);
lean_dec(x_130);
lean_dec(x_129);
lean_dec(x_9);
x_155 = lean_nat_add(x_114, x_115);
lean_dec(x_115);
x_156 = lean_nat_add(x_155, x_116);
lean_dec(x_116);
x_157 = lean_nat_add(x_155, x_128);
lean_dec(x_128);
lean_dec(x_155);
lean_inc(x_7);
if (lean_is_scalar(x_127)) {
 x_158 = lean_alloc_ctor(0, 5, 0);
} else {
 x_158 = x_127;
}
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_5);
lean_ctor_set(x_158, 2, x_6);
lean_ctor_set(x_158, 3, x_7);
lean_ctor_set(x_158, 4, x_119);
x_159 = !lean_is_exclusive(x_7);
if (x_159 == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_160 = lean_ctor_get(x_7, 4);
lean_dec(x_160);
x_161 = lean_ctor_get(x_7, 3);
lean_dec(x_161);
x_162 = lean_ctor_get(x_7, 2);
lean_dec(x_162);
x_163 = lean_ctor_get(x_7, 1);
lean_dec(x_163);
x_164 = lean_ctor_get(x_7, 0);
lean_dec(x_164);
lean_ctor_set(x_7, 4, x_120);
lean_ctor_set(x_7, 3, x_158);
lean_ctor_set(x_7, 2, x_118);
lean_ctor_set(x_7, 1, x_117);
lean_ctor_set(x_7, 0, x_156);
return x_7;
}
else
{
lean_object* x_165; 
lean_dec(x_7);
x_165 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_165, 0, x_156);
lean_ctor_set(x_165, 1, x_117);
lean_ctor_set(x_165, 2, x_118);
lean_ctor_set(x_165, 3, x_158);
lean_ctor_set(x_165, 4, x_120);
return x_165;
}
}
}
}
else
{
lean_object* x_166; 
x_166 = lean_ctor_get(x_113, 3);
lean_inc(x_166);
if (lean_obj_tag(x_166) == 0)
{
uint8_t x_167; 
x_167 = !lean_is_exclusive(x_113);
if (x_167 == 0)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; uint8_t x_171; 
x_168 = lean_ctor_get(x_113, 4);
x_169 = lean_ctor_get(x_113, 3);
lean_dec(x_169);
x_170 = lean_ctor_get(x_113, 0);
lean_dec(x_170);
x_171 = !lean_is_exclusive(x_166);
if (x_171 == 0)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_172 = lean_ctor_get(x_166, 1);
x_173 = lean_ctor_get(x_166, 2);
x_174 = lean_ctor_get(x_166, 4);
lean_dec(x_174);
x_175 = lean_ctor_get(x_166, 3);
lean_dec(x_175);
x_176 = lean_ctor_get(x_166, 0);
lean_dec(x_176);
x_177 = lean_unsigned_to_nat(3u);
lean_inc_n(x_168, 2);
lean_ctor_set(x_166, 4, x_168);
lean_ctor_set(x_166, 3, x_168);
lean_ctor_set(x_166, 2, x_6);
lean_ctor_set(x_166, 1, x_5);
lean_ctor_set(x_166, 0, x_114);
lean_inc(x_168);
lean_ctor_set(x_113, 3, x_168);
lean_ctor_set(x_113, 0, x_114);
if (lean_is_scalar(x_9)) {
 x_178 = lean_alloc_ctor(0, 5, 0);
} else {
 x_178 = x_9;
}
lean_ctor_set(x_178, 0, x_177);
lean_ctor_set(x_178, 1, x_172);
lean_ctor_set(x_178, 2, x_173);
lean_ctor_set(x_178, 3, x_166);
lean_ctor_set(x_178, 4, x_113);
return x_178;
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_179 = lean_ctor_get(x_166, 1);
x_180 = lean_ctor_get(x_166, 2);
lean_inc(x_180);
lean_inc(x_179);
lean_dec(x_166);
x_181 = lean_unsigned_to_nat(3u);
lean_inc_n(x_168, 2);
x_182 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_182, 0, x_114);
lean_ctor_set(x_182, 1, x_5);
lean_ctor_set(x_182, 2, x_6);
lean_ctor_set(x_182, 3, x_168);
lean_ctor_set(x_182, 4, x_168);
lean_inc(x_168);
lean_ctor_set(x_113, 3, x_168);
lean_ctor_set(x_113, 0, x_114);
if (lean_is_scalar(x_9)) {
 x_183 = lean_alloc_ctor(0, 5, 0);
} else {
 x_183 = x_9;
}
lean_ctor_set(x_183, 0, x_181);
lean_ctor_set(x_183, 1, x_179);
lean_ctor_set(x_183, 2, x_180);
lean_ctor_set(x_183, 3, x_182);
lean_ctor_set(x_183, 4, x_113);
return x_183;
}
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_184 = lean_ctor_get(x_113, 4);
x_185 = lean_ctor_get(x_113, 1);
x_186 = lean_ctor_get(x_113, 2);
lean_inc(x_184);
lean_inc(x_186);
lean_inc(x_185);
lean_dec(x_113);
x_187 = lean_ctor_get(x_166, 1);
lean_inc(x_187);
x_188 = lean_ctor_get(x_166, 2);
lean_inc(x_188);
if (lean_is_exclusive(x_166)) {
 lean_ctor_release(x_166, 0);
 lean_ctor_release(x_166, 1);
 lean_ctor_release(x_166, 2);
 lean_ctor_release(x_166, 3);
 lean_ctor_release(x_166, 4);
 x_189 = x_166;
} else {
 lean_dec_ref(x_166);
 x_189 = lean_box(0);
}
x_190 = lean_unsigned_to_nat(3u);
lean_inc_n(x_184, 2);
if (lean_is_scalar(x_189)) {
 x_191 = lean_alloc_ctor(0, 5, 0);
} else {
 x_191 = x_189;
}
lean_ctor_set(x_191, 0, x_114);
lean_ctor_set(x_191, 1, x_5);
lean_ctor_set(x_191, 2, x_6);
lean_ctor_set(x_191, 3, x_184);
lean_ctor_set(x_191, 4, x_184);
lean_inc(x_184);
x_192 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_192, 0, x_114);
lean_ctor_set(x_192, 1, x_185);
lean_ctor_set(x_192, 2, x_186);
lean_ctor_set(x_192, 3, x_184);
lean_ctor_set(x_192, 4, x_184);
if (lean_is_scalar(x_9)) {
 x_193 = lean_alloc_ctor(0, 5, 0);
} else {
 x_193 = x_9;
}
lean_ctor_set(x_193, 0, x_190);
lean_ctor_set(x_193, 1, x_187);
lean_ctor_set(x_193, 2, x_188);
lean_ctor_set(x_193, 3, x_191);
lean_ctor_set(x_193, 4, x_192);
return x_193;
}
}
else
{
lean_object* x_194; 
x_194 = lean_ctor_get(x_113, 4);
lean_inc(x_194);
if (lean_obj_tag(x_194) == 0)
{
uint8_t x_195; 
x_195 = !lean_is_exclusive(x_113);
if (x_195 == 0)
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_196 = lean_ctor_get(x_113, 1);
x_197 = lean_ctor_get(x_113, 2);
x_198 = lean_ctor_get(x_113, 4);
lean_dec(x_198);
x_199 = lean_ctor_get(x_113, 3);
lean_dec(x_199);
x_200 = lean_ctor_get(x_113, 0);
lean_dec(x_200);
x_201 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_113, 4, x_166);
lean_ctor_set(x_113, 2, x_6);
lean_ctor_set(x_113, 1, x_5);
lean_ctor_set(x_113, 0, x_114);
if (lean_is_scalar(x_9)) {
 x_202 = lean_alloc_ctor(0, 5, 0);
} else {
 x_202 = x_9;
}
lean_ctor_set(x_202, 0, x_201);
lean_ctor_set(x_202, 1, x_196);
lean_ctor_set(x_202, 2, x_197);
lean_ctor_set(x_202, 3, x_113);
lean_ctor_set(x_202, 4, x_194);
return x_202;
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_203 = lean_ctor_get(x_113, 1);
x_204 = lean_ctor_get(x_113, 2);
lean_inc(x_204);
lean_inc(x_203);
lean_dec(x_113);
x_205 = lean_unsigned_to_nat(3u);
x_206 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_206, 0, x_114);
lean_ctor_set(x_206, 1, x_5);
lean_ctor_set(x_206, 2, x_6);
lean_ctor_set(x_206, 3, x_166);
lean_ctor_set(x_206, 4, x_166);
if (lean_is_scalar(x_9)) {
 x_207 = lean_alloc_ctor(0, 5, 0);
} else {
 x_207 = x_9;
}
lean_ctor_set(x_207, 0, x_205);
lean_ctor_set(x_207, 1, x_203);
lean_ctor_set(x_207, 2, x_204);
lean_ctor_set(x_207, 3, x_206);
lean_ctor_set(x_207, 4, x_194);
return x_207;
}
}
else
{
lean_object* x_208; lean_object* x_209; 
x_208 = lean_unsigned_to_nat(2u);
if (lean_is_scalar(x_9)) {
 x_209 = lean_alloc_ctor(0, 5, 0);
} else {
 x_209 = x_9;
}
lean_ctor_set(x_209, 0, x_208);
lean_ctor_set(x_209, 1, x_5);
lean_ctor_set(x_209, 2, x_6);
lean_ctor_set(x_209, 3, x_194);
lean_ctor_set(x_209, 4, x_113);
return x_209;
}
}
}
}
}
}
else
{
lean_object* x_210; lean_object* x_211; 
x_210 = lean_unsigned_to_nat(1u);
x_211 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_211, 0, x_210);
lean_ctor_set(x_211, 1, x_1);
lean_ctor_set(x_211, 2, x_2);
lean_ctor_set(x_211, 3, x_3);
lean_ctor_set(x_211, 4, x_3);
return x_211;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2193__spec__0_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_DTreeMap_Internal_Impl_insert___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2193__spec__0_spec__4___redArg(x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM___at___Lean_RBNode_foldM___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2193__spec__0_spec__5_spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 3);
lean_inc(x_7);
lean_dec(x_2);
x_8 = l_Lean_RBNode_foldM___at___Lean_RBNode_foldM___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2193__spec__0_spec__5_spec__5(x_1, x_4);
if (lean_obj_tag(x_8) == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 x_10 = x_8;
} else {
 lean_dec_ref(x_8);
 x_10 = lean_box(0);
}
x_11 = l_Lean_Json_parse(x_5);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
return x_11;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_11, 0);
lean_inc(x_15);
lean_dec(x_11);
x_16 = l_Lean_Lsp_RefIdent_fromJson_x3f(x_15);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
return x_16;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_16);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_41; lean_object* x_44; lean_object* x_45; 
x_21 = lean_ctor_get(x_16, 0);
x_44 = lean_mk_string_unchecked("definition", 10, 10);
lean_inc(x_6);
x_45 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Basic_0__Lean_Lsp_fromJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1614__spec__0(x_6, x_44);
lean_dec(x_44);
if (lean_obj_tag(x_45) == 0)
{
uint8_t x_46; 
lean_free_object(x_16);
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
return x_45;
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_45, 0);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_47);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_45, 0);
lean_inc(x_49);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 x_50 = x_45;
} else {
 lean_dec_ref(x_45);
 x_50 = lean_box(0);
}
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_51; 
lean_dec(x_50);
lean_free_object(x_16);
lean_dec(x_10);
x_51 = lean_box(0);
x_22 = x_51;
goto block_40;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_298; lean_object* x_299; uint8_t x_300; 
x_52 = lean_ctor_get(x_49, 0);
lean_inc(x_52);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 x_53 = x_49;
} else {
 lean_dec_ref(x_49);
 x_53 = lean_box(0);
}
x_54 = lean_box(0);
x_298 = lean_array_get_size(x_52);
x_299 = lean_unsigned_to_nat(4u);
x_300 = lean_nat_dec_eq(x_298, x_299);
if (x_300 == 0)
{
lean_object* x_301; uint8_t x_302; 
x_301 = lean_unsigned_to_nat(13u);
x_302 = lean_nat_dec_eq(x_298, x_301);
lean_dec(x_298);
if (x_302 == 0)
{
lean_object* x_303; 
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_50);
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_303 = lean_mk_string_unchecked("Expected list of length 4 or 13, not {l.size}", 45, 45);
lean_ctor_set_tag(x_16, 0);
lean_ctor_set(x_16, 0, x_303);
return x_16;
}
else
{
lean_free_object(x_16);
goto block_297;
}
}
else
{
lean_dec(x_298);
lean_free_object(x_16);
goto block_297;
}
block_297:
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_55 = lean_array_get_size(x_52);
x_56 = lean_unsigned_to_nat(4u);
x_57 = lean_nat_dec_lt(x_55, x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_50);
x_58 = lean_unsigned_to_nat(0u);
x_59 = lean_array_fget(x_52, x_58);
x_60 = l_Lean_Json_getNat_x3f(x_59);
if (lean_obj_tag(x_60) == 0)
{
uint8_t x_61; 
lean_dec(x_55);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_61 = !lean_is_exclusive(x_60);
if (x_61 == 0)
{
return x_60;
}
else
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_60, 0);
lean_inc(x_62);
lean_dec(x_60);
x_63 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_63, 0, x_62);
return x_63;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_64 = lean_ctor_get(x_60, 0);
lean_inc(x_64);
lean_dec(x_60);
x_65 = lean_unsigned_to_nat(1u);
x_66 = lean_array_fget(x_52, x_65);
x_67 = l_Lean_Json_getNat_x3f(x_66);
if (lean_obj_tag(x_67) == 0)
{
uint8_t x_68; 
lean_dec(x_64);
lean_dec(x_55);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_68 = !lean_is_exclusive(x_67);
if (x_68 == 0)
{
return x_67;
}
else
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_67, 0);
lean_inc(x_69);
lean_dec(x_67);
x_70 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_70, 0, x_69);
return x_70;
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_71 = lean_ctor_get(x_67, 0);
lean_inc(x_71);
lean_dec(x_67);
x_72 = lean_unsigned_to_nat(2u);
x_73 = lean_array_fget(x_52, x_72);
x_74 = l_Lean_Json_getNat_x3f(x_73);
if (lean_obj_tag(x_74) == 0)
{
uint8_t x_75; 
lean_dec(x_71);
lean_dec(x_64);
lean_dec(x_55);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_75 = !lean_is_exclusive(x_74);
if (x_75 == 0)
{
return x_74;
}
else
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_74, 0);
lean_inc(x_76);
lean_dec(x_74);
x_77 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_77, 0, x_76);
return x_77;
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_78 = lean_ctor_get(x_74, 0);
lean_inc(x_78);
lean_dec(x_74);
x_79 = lean_unsigned_to_nat(3u);
x_80 = lean_array_fget(x_52, x_79);
x_81 = l_Lean_Json_getNat_x3f(x_80);
if (lean_obj_tag(x_81) == 0)
{
uint8_t x_82; 
lean_dec(x_78);
lean_dec(x_71);
lean_dec(x_64);
lean_dec(x_55);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_82 = !lean_is_exclusive(x_81);
if (x_82 == 0)
{
return x_81;
}
else
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_81, 0);
lean_inc(x_83);
lean_dec(x_81);
x_84 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_84, 0, x_83);
return x_84;
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_85 = lean_ctor_get(x_81, 0);
lean_inc(x_85);
lean_dec(x_81);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_64);
lean_ctor_set(x_86, 1, x_71);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_78);
lean_ctor_set(x_87, 1, x_85);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
x_89 = lean_unsigned_to_nat(13u);
x_90 = lean_nat_dec_eq(x_55, x_89);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; 
lean_dec(x_55);
lean_dec(x_53);
lean_dec(x_52);
x_91 = lean_box(0);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_88);
lean_ctor_set(x_92, 1, x_91);
x_41 = x_92;
goto block_43;
}
else
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_array_get(x_54, x_52, x_56);
x_94 = l_Lean_Json_getStr_x3f(x_93);
if (lean_obj_tag(x_94) == 0)
{
uint8_t x_95; 
lean_dec(x_88);
lean_dec(x_55);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_95 = !lean_is_exclusive(x_94);
if (x_95 == 0)
{
return x_94;
}
else
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_94, 0);
lean_inc(x_96);
lean_dec(x_94);
x_97 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_97, 0, x_96);
return x_97;
}
}
else
{
uint8_t x_98; 
x_98 = !lean_is_exclusive(x_94);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_99 = lean_ctor_get(x_94, 0);
x_100 = lean_unsigned_to_nat(9u);
x_101 = lean_nat_dec_lt(x_55, x_100);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_free_object(x_94);
x_102 = lean_unsigned_to_nat(5u);
x_103 = lean_array_fget(x_52, x_102);
x_104 = l_Lean_Json_getNat_x3f(x_103);
if (lean_obj_tag(x_104) == 0)
{
uint8_t x_105; 
lean_dec(x_99);
lean_dec(x_88);
lean_dec(x_55);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_105 = !lean_is_exclusive(x_104);
if (x_105 == 0)
{
return x_104;
}
else
{
lean_object* x_106; lean_object* x_107; 
x_106 = lean_ctor_get(x_104, 0);
lean_inc(x_106);
lean_dec(x_104);
x_107 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_107, 0, x_106);
return x_107;
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_108 = lean_ctor_get(x_104, 0);
lean_inc(x_108);
lean_dec(x_104);
x_109 = lean_unsigned_to_nat(6u);
x_110 = lean_array_fget(x_52, x_109);
x_111 = l_Lean_Json_getNat_x3f(x_110);
if (lean_obj_tag(x_111) == 0)
{
uint8_t x_112; 
lean_dec(x_108);
lean_dec(x_99);
lean_dec(x_88);
lean_dec(x_55);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_112 = !lean_is_exclusive(x_111);
if (x_112 == 0)
{
return x_111;
}
else
{
lean_object* x_113; lean_object* x_114; 
x_113 = lean_ctor_get(x_111, 0);
lean_inc(x_113);
lean_dec(x_111);
x_114 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_114, 0, x_113);
return x_114;
}
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_115 = lean_ctor_get(x_111, 0);
lean_inc(x_115);
lean_dec(x_111);
x_116 = lean_unsigned_to_nat(7u);
x_117 = lean_array_fget(x_52, x_116);
x_118 = l_Lean_Json_getNat_x3f(x_117);
if (lean_obj_tag(x_118) == 0)
{
uint8_t x_119; 
lean_dec(x_115);
lean_dec(x_108);
lean_dec(x_99);
lean_dec(x_88);
lean_dec(x_55);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_119 = !lean_is_exclusive(x_118);
if (x_119 == 0)
{
return x_118;
}
else
{
lean_object* x_120; lean_object* x_121; 
x_120 = lean_ctor_get(x_118, 0);
lean_inc(x_120);
lean_dec(x_118);
x_121 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_121, 0, x_120);
return x_121;
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_122 = lean_ctor_get(x_118, 0);
lean_inc(x_122);
lean_dec(x_118);
x_123 = lean_unsigned_to_nat(8u);
x_124 = lean_array_fget(x_52, x_123);
x_125 = l_Lean_Json_getNat_x3f(x_124);
if (lean_obj_tag(x_125) == 0)
{
uint8_t x_126; 
lean_dec(x_122);
lean_dec(x_115);
lean_dec(x_108);
lean_dec(x_99);
lean_dec(x_88);
lean_dec(x_55);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_126 = !lean_is_exclusive(x_125);
if (x_126 == 0)
{
return x_125;
}
else
{
lean_object* x_127; lean_object* x_128; 
x_127 = lean_ctor_get(x_125, 0);
lean_inc(x_127);
lean_dec(x_125);
x_128 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_128, 0, x_127);
return x_128;
}
}
else
{
uint8_t x_129; 
x_129 = !lean_is_exclusive(x_125);
if (x_129 == 0)
{
lean_object* x_130; uint8_t x_131; 
x_130 = lean_ctor_get(x_125, 0);
x_131 = lean_nat_dec_lt(x_55, x_89);
if (x_131 == 0)
{
lean_object* x_132; lean_object* x_133; 
lean_free_object(x_125);
lean_dec(x_55);
x_132 = lean_array_fget(x_52, x_100);
x_133 = l_Lean_Json_getNat_x3f(x_132);
if (lean_obj_tag(x_133) == 0)
{
uint8_t x_134; 
lean_dec(x_130);
lean_dec(x_122);
lean_dec(x_115);
lean_dec(x_108);
lean_dec(x_99);
lean_dec(x_88);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_134 = !lean_is_exclusive(x_133);
if (x_134 == 0)
{
return x_133;
}
else
{
lean_object* x_135; lean_object* x_136; 
x_135 = lean_ctor_get(x_133, 0);
lean_inc(x_135);
lean_dec(x_133);
x_136 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_136, 0, x_135);
return x_136;
}
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_137 = lean_ctor_get(x_133, 0);
lean_inc(x_137);
lean_dec(x_133);
x_138 = lean_unsigned_to_nat(10u);
x_139 = lean_array_fget(x_52, x_138);
x_140 = l_Lean_Json_getNat_x3f(x_139);
if (lean_obj_tag(x_140) == 0)
{
uint8_t x_141; 
lean_dec(x_137);
lean_dec(x_130);
lean_dec(x_122);
lean_dec(x_115);
lean_dec(x_108);
lean_dec(x_99);
lean_dec(x_88);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_141 = !lean_is_exclusive(x_140);
if (x_141 == 0)
{
return x_140;
}
else
{
lean_object* x_142; lean_object* x_143; 
x_142 = lean_ctor_get(x_140, 0);
lean_inc(x_142);
lean_dec(x_140);
x_143 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_143, 0, x_142);
return x_143;
}
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_144 = lean_ctor_get(x_140, 0);
lean_inc(x_144);
lean_dec(x_140);
x_145 = lean_unsigned_to_nat(11u);
x_146 = lean_array_fget(x_52, x_145);
x_147 = l_Lean_Json_getNat_x3f(x_146);
if (lean_obj_tag(x_147) == 0)
{
uint8_t x_148; 
lean_dec(x_144);
lean_dec(x_137);
lean_dec(x_130);
lean_dec(x_122);
lean_dec(x_115);
lean_dec(x_108);
lean_dec(x_99);
lean_dec(x_88);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_148 = !lean_is_exclusive(x_147);
if (x_148 == 0)
{
return x_147;
}
else
{
lean_object* x_149; lean_object* x_150; 
x_149 = lean_ctor_get(x_147, 0);
lean_inc(x_149);
lean_dec(x_147);
x_150 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_150, 0, x_149);
return x_150;
}
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_151 = lean_ctor_get(x_147, 0);
lean_inc(x_151);
lean_dec(x_147);
x_152 = lean_unsigned_to_nat(12u);
x_153 = lean_array_fget(x_52, x_152);
lean_dec(x_52);
x_154 = l_Lean_Json_getNat_x3f(x_153);
if (lean_obj_tag(x_154) == 0)
{
uint8_t x_155; 
lean_dec(x_151);
lean_dec(x_144);
lean_dec(x_137);
lean_dec(x_130);
lean_dec(x_122);
lean_dec(x_115);
lean_dec(x_108);
lean_dec(x_99);
lean_dec(x_88);
lean_dec(x_53);
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_155 = !lean_is_exclusive(x_154);
if (x_155 == 0)
{
return x_154;
}
else
{
lean_object* x_156; lean_object* x_157; 
x_156 = lean_ctor_get(x_154, 0);
lean_inc(x_156);
lean_dec(x_154);
x_157 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_157, 0, x_156);
return x_157;
}
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_158 = lean_ctor_get(x_154, 0);
lean_inc(x_158);
lean_dec(x_154);
x_159 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_159, 0, x_108);
lean_ctor_set(x_159, 1, x_115);
x_160 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_160, 0, x_122);
lean_ctor_set(x_160, 1, x_130);
x_161 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_161, 0, x_159);
lean_ctor_set(x_161, 1, x_160);
x_162 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_162, 0, x_137);
lean_ctor_set(x_162, 1, x_144);
x_163 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_163, 0, x_151);
lean_ctor_set(x_163, 1, x_158);
x_164 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_164, 0, x_162);
lean_ctor_set(x_164, 1, x_163);
x_165 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_165, 0, x_99);
lean_ctor_set(x_165, 1, x_161);
lean_ctor_set(x_165, 2, x_164);
if (lean_is_scalar(x_53)) {
 x_166 = lean_alloc_ctor(1, 1, 0);
} else {
 x_166 = x_53;
}
lean_ctor_set(x_166, 0, x_165);
x_167 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_167, 0, x_88);
lean_ctor_set(x_167, 1, x_166);
x_41 = x_167;
goto block_43;
}
}
}
}
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; 
lean_dec(x_130);
lean_dec(x_122);
lean_dec(x_115);
lean_dec(x_108);
lean_dec(x_99);
lean_dec(x_88);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_168 = lean_mk_string_unchecked("Expected list of length 4, not ", 31, 31);
x_169 = l___private_Init_Data_Repr_0__Nat_reprFast(x_55);
x_170 = lean_string_append(x_168, x_169);
lean_dec(x_169);
lean_ctor_set_tag(x_125, 0);
lean_ctor_set(x_125, 0, x_170);
return x_125;
}
}
else
{
lean_object* x_171; uint8_t x_172; 
x_171 = lean_ctor_get(x_125, 0);
lean_inc(x_171);
lean_dec(x_125);
x_172 = lean_nat_dec_lt(x_55, x_89);
if (x_172 == 0)
{
lean_object* x_173; lean_object* x_174; 
lean_dec(x_55);
x_173 = lean_array_fget(x_52, x_100);
x_174 = l_Lean_Json_getNat_x3f(x_173);
if (lean_obj_tag(x_174) == 0)
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; 
lean_dec(x_171);
lean_dec(x_122);
lean_dec(x_115);
lean_dec(x_108);
lean_dec(x_99);
lean_dec(x_88);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_175 = lean_ctor_get(x_174, 0);
lean_inc(x_175);
if (lean_is_exclusive(x_174)) {
 lean_ctor_release(x_174, 0);
 x_176 = x_174;
} else {
 lean_dec_ref(x_174);
 x_176 = lean_box(0);
}
if (lean_is_scalar(x_176)) {
 x_177 = lean_alloc_ctor(0, 1, 0);
} else {
 x_177 = x_176;
}
lean_ctor_set(x_177, 0, x_175);
return x_177;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_178 = lean_ctor_get(x_174, 0);
lean_inc(x_178);
lean_dec(x_174);
x_179 = lean_unsigned_to_nat(10u);
x_180 = lean_array_fget(x_52, x_179);
x_181 = l_Lean_Json_getNat_x3f(x_180);
if (lean_obj_tag(x_181) == 0)
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; 
lean_dec(x_178);
lean_dec(x_171);
lean_dec(x_122);
lean_dec(x_115);
lean_dec(x_108);
lean_dec(x_99);
lean_dec(x_88);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_182 = lean_ctor_get(x_181, 0);
lean_inc(x_182);
if (lean_is_exclusive(x_181)) {
 lean_ctor_release(x_181, 0);
 x_183 = x_181;
} else {
 lean_dec_ref(x_181);
 x_183 = lean_box(0);
}
if (lean_is_scalar(x_183)) {
 x_184 = lean_alloc_ctor(0, 1, 0);
} else {
 x_184 = x_183;
}
lean_ctor_set(x_184, 0, x_182);
return x_184;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_185 = lean_ctor_get(x_181, 0);
lean_inc(x_185);
lean_dec(x_181);
x_186 = lean_unsigned_to_nat(11u);
x_187 = lean_array_fget(x_52, x_186);
x_188 = l_Lean_Json_getNat_x3f(x_187);
if (lean_obj_tag(x_188) == 0)
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; 
lean_dec(x_185);
lean_dec(x_178);
lean_dec(x_171);
lean_dec(x_122);
lean_dec(x_115);
lean_dec(x_108);
lean_dec(x_99);
lean_dec(x_88);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 x_190 = x_188;
} else {
 lean_dec_ref(x_188);
 x_190 = lean_box(0);
}
if (lean_is_scalar(x_190)) {
 x_191 = lean_alloc_ctor(0, 1, 0);
} else {
 x_191 = x_190;
}
lean_ctor_set(x_191, 0, x_189);
return x_191;
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_192 = lean_ctor_get(x_188, 0);
lean_inc(x_192);
lean_dec(x_188);
x_193 = lean_unsigned_to_nat(12u);
x_194 = lean_array_fget(x_52, x_193);
lean_dec(x_52);
x_195 = l_Lean_Json_getNat_x3f(x_194);
if (lean_obj_tag(x_195) == 0)
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; 
lean_dec(x_192);
lean_dec(x_185);
lean_dec(x_178);
lean_dec(x_171);
lean_dec(x_122);
lean_dec(x_115);
lean_dec(x_108);
lean_dec(x_99);
lean_dec(x_88);
lean_dec(x_53);
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_196 = lean_ctor_get(x_195, 0);
lean_inc(x_196);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 x_197 = x_195;
} else {
 lean_dec_ref(x_195);
 x_197 = lean_box(0);
}
if (lean_is_scalar(x_197)) {
 x_198 = lean_alloc_ctor(0, 1, 0);
} else {
 x_198 = x_197;
}
lean_ctor_set(x_198, 0, x_196);
return x_198;
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_199 = lean_ctor_get(x_195, 0);
lean_inc(x_199);
lean_dec(x_195);
x_200 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_200, 0, x_108);
lean_ctor_set(x_200, 1, x_115);
x_201 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_201, 0, x_122);
lean_ctor_set(x_201, 1, x_171);
x_202 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_202, 0, x_200);
lean_ctor_set(x_202, 1, x_201);
x_203 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_203, 0, x_178);
lean_ctor_set(x_203, 1, x_185);
x_204 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_204, 0, x_192);
lean_ctor_set(x_204, 1, x_199);
x_205 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_205, 0, x_203);
lean_ctor_set(x_205, 1, x_204);
x_206 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_206, 0, x_99);
lean_ctor_set(x_206, 1, x_202);
lean_ctor_set(x_206, 2, x_205);
if (lean_is_scalar(x_53)) {
 x_207 = lean_alloc_ctor(1, 1, 0);
} else {
 x_207 = x_53;
}
lean_ctor_set(x_207, 0, x_206);
x_208 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_208, 0, x_88);
lean_ctor_set(x_208, 1, x_207);
x_41 = x_208;
goto block_43;
}
}
}
}
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
lean_dec(x_171);
lean_dec(x_122);
lean_dec(x_115);
lean_dec(x_108);
lean_dec(x_99);
lean_dec(x_88);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_209 = lean_mk_string_unchecked("Expected list of length 4, not ", 31, 31);
x_210 = l___private_Init_Data_Repr_0__Nat_reprFast(x_55);
x_211 = lean_string_append(x_209, x_210);
lean_dec(x_210);
x_212 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_212, 0, x_211);
return x_212;
}
}
}
}
}
}
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; 
lean_dec(x_99);
lean_dec(x_88);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_213 = lean_mk_string_unchecked("Expected list of length 4, not ", 31, 31);
x_214 = l___private_Init_Data_Repr_0__Nat_reprFast(x_55);
x_215 = lean_string_append(x_213, x_214);
lean_dec(x_214);
lean_ctor_set_tag(x_94, 0);
lean_ctor_set(x_94, 0, x_215);
return x_94;
}
}
else
{
lean_object* x_216; lean_object* x_217; uint8_t x_218; 
x_216 = lean_ctor_get(x_94, 0);
lean_inc(x_216);
lean_dec(x_94);
x_217 = lean_unsigned_to_nat(9u);
x_218 = lean_nat_dec_lt(x_55, x_217);
if (x_218 == 0)
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_219 = lean_unsigned_to_nat(5u);
x_220 = lean_array_fget(x_52, x_219);
x_221 = l_Lean_Json_getNat_x3f(x_220);
if (lean_obj_tag(x_221) == 0)
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; 
lean_dec(x_216);
lean_dec(x_88);
lean_dec(x_55);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_222 = lean_ctor_get(x_221, 0);
lean_inc(x_222);
if (lean_is_exclusive(x_221)) {
 lean_ctor_release(x_221, 0);
 x_223 = x_221;
} else {
 lean_dec_ref(x_221);
 x_223 = lean_box(0);
}
if (lean_is_scalar(x_223)) {
 x_224 = lean_alloc_ctor(0, 1, 0);
} else {
 x_224 = x_223;
}
lean_ctor_set(x_224, 0, x_222);
return x_224;
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_225 = lean_ctor_get(x_221, 0);
lean_inc(x_225);
lean_dec(x_221);
x_226 = lean_unsigned_to_nat(6u);
x_227 = lean_array_fget(x_52, x_226);
x_228 = l_Lean_Json_getNat_x3f(x_227);
if (lean_obj_tag(x_228) == 0)
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; 
lean_dec(x_225);
lean_dec(x_216);
lean_dec(x_88);
lean_dec(x_55);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_229 = lean_ctor_get(x_228, 0);
lean_inc(x_229);
if (lean_is_exclusive(x_228)) {
 lean_ctor_release(x_228, 0);
 x_230 = x_228;
} else {
 lean_dec_ref(x_228);
 x_230 = lean_box(0);
}
if (lean_is_scalar(x_230)) {
 x_231 = lean_alloc_ctor(0, 1, 0);
} else {
 x_231 = x_230;
}
lean_ctor_set(x_231, 0, x_229);
return x_231;
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_232 = lean_ctor_get(x_228, 0);
lean_inc(x_232);
lean_dec(x_228);
x_233 = lean_unsigned_to_nat(7u);
x_234 = lean_array_fget(x_52, x_233);
x_235 = l_Lean_Json_getNat_x3f(x_234);
if (lean_obj_tag(x_235) == 0)
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; 
lean_dec(x_232);
lean_dec(x_225);
lean_dec(x_216);
lean_dec(x_88);
lean_dec(x_55);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_236 = lean_ctor_get(x_235, 0);
lean_inc(x_236);
if (lean_is_exclusive(x_235)) {
 lean_ctor_release(x_235, 0);
 x_237 = x_235;
} else {
 lean_dec_ref(x_235);
 x_237 = lean_box(0);
}
if (lean_is_scalar(x_237)) {
 x_238 = lean_alloc_ctor(0, 1, 0);
} else {
 x_238 = x_237;
}
lean_ctor_set(x_238, 0, x_236);
return x_238;
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; 
x_239 = lean_ctor_get(x_235, 0);
lean_inc(x_239);
lean_dec(x_235);
x_240 = lean_unsigned_to_nat(8u);
x_241 = lean_array_fget(x_52, x_240);
x_242 = l_Lean_Json_getNat_x3f(x_241);
if (lean_obj_tag(x_242) == 0)
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; 
lean_dec(x_239);
lean_dec(x_232);
lean_dec(x_225);
lean_dec(x_216);
lean_dec(x_88);
lean_dec(x_55);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_243 = lean_ctor_get(x_242, 0);
lean_inc(x_243);
if (lean_is_exclusive(x_242)) {
 lean_ctor_release(x_242, 0);
 x_244 = x_242;
} else {
 lean_dec_ref(x_242);
 x_244 = lean_box(0);
}
if (lean_is_scalar(x_244)) {
 x_245 = lean_alloc_ctor(0, 1, 0);
} else {
 x_245 = x_244;
}
lean_ctor_set(x_245, 0, x_243);
return x_245;
}
else
{
lean_object* x_246; lean_object* x_247; uint8_t x_248; 
x_246 = lean_ctor_get(x_242, 0);
lean_inc(x_246);
if (lean_is_exclusive(x_242)) {
 lean_ctor_release(x_242, 0);
 x_247 = x_242;
} else {
 lean_dec_ref(x_242);
 x_247 = lean_box(0);
}
x_248 = lean_nat_dec_lt(x_55, x_89);
if (x_248 == 0)
{
lean_object* x_249; lean_object* x_250; 
lean_dec(x_247);
lean_dec(x_55);
x_249 = lean_array_fget(x_52, x_217);
x_250 = l_Lean_Json_getNat_x3f(x_249);
if (lean_obj_tag(x_250) == 0)
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; 
lean_dec(x_246);
lean_dec(x_239);
lean_dec(x_232);
lean_dec(x_225);
lean_dec(x_216);
lean_dec(x_88);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_251 = lean_ctor_get(x_250, 0);
lean_inc(x_251);
if (lean_is_exclusive(x_250)) {
 lean_ctor_release(x_250, 0);
 x_252 = x_250;
} else {
 lean_dec_ref(x_250);
 x_252 = lean_box(0);
}
if (lean_is_scalar(x_252)) {
 x_253 = lean_alloc_ctor(0, 1, 0);
} else {
 x_253 = x_252;
}
lean_ctor_set(x_253, 0, x_251);
return x_253;
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; 
x_254 = lean_ctor_get(x_250, 0);
lean_inc(x_254);
lean_dec(x_250);
x_255 = lean_unsigned_to_nat(10u);
x_256 = lean_array_fget(x_52, x_255);
x_257 = l_Lean_Json_getNat_x3f(x_256);
if (lean_obj_tag(x_257) == 0)
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; 
lean_dec(x_254);
lean_dec(x_246);
lean_dec(x_239);
lean_dec(x_232);
lean_dec(x_225);
lean_dec(x_216);
lean_dec(x_88);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_258 = lean_ctor_get(x_257, 0);
lean_inc(x_258);
if (lean_is_exclusive(x_257)) {
 lean_ctor_release(x_257, 0);
 x_259 = x_257;
} else {
 lean_dec_ref(x_257);
 x_259 = lean_box(0);
}
if (lean_is_scalar(x_259)) {
 x_260 = lean_alloc_ctor(0, 1, 0);
} else {
 x_260 = x_259;
}
lean_ctor_set(x_260, 0, x_258);
return x_260;
}
else
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_261 = lean_ctor_get(x_257, 0);
lean_inc(x_261);
lean_dec(x_257);
x_262 = lean_unsigned_to_nat(11u);
x_263 = lean_array_fget(x_52, x_262);
x_264 = l_Lean_Json_getNat_x3f(x_263);
if (lean_obj_tag(x_264) == 0)
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; 
lean_dec(x_261);
lean_dec(x_254);
lean_dec(x_246);
lean_dec(x_239);
lean_dec(x_232);
lean_dec(x_225);
lean_dec(x_216);
lean_dec(x_88);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_265 = lean_ctor_get(x_264, 0);
lean_inc(x_265);
if (lean_is_exclusive(x_264)) {
 lean_ctor_release(x_264, 0);
 x_266 = x_264;
} else {
 lean_dec_ref(x_264);
 x_266 = lean_box(0);
}
if (lean_is_scalar(x_266)) {
 x_267 = lean_alloc_ctor(0, 1, 0);
} else {
 x_267 = x_266;
}
lean_ctor_set(x_267, 0, x_265);
return x_267;
}
else
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; 
x_268 = lean_ctor_get(x_264, 0);
lean_inc(x_268);
lean_dec(x_264);
x_269 = lean_unsigned_to_nat(12u);
x_270 = lean_array_fget(x_52, x_269);
lean_dec(x_52);
x_271 = l_Lean_Json_getNat_x3f(x_270);
if (lean_obj_tag(x_271) == 0)
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; 
lean_dec(x_268);
lean_dec(x_261);
lean_dec(x_254);
lean_dec(x_246);
lean_dec(x_239);
lean_dec(x_232);
lean_dec(x_225);
lean_dec(x_216);
lean_dec(x_88);
lean_dec(x_53);
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_272 = lean_ctor_get(x_271, 0);
lean_inc(x_272);
if (lean_is_exclusive(x_271)) {
 lean_ctor_release(x_271, 0);
 x_273 = x_271;
} else {
 lean_dec_ref(x_271);
 x_273 = lean_box(0);
}
if (lean_is_scalar(x_273)) {
 x_274 = lean_alloc_ctor(0, 1, 0);
} else {
 x_274 = x_273;
}
lean_ctor_set(x_274, 0, x_272);
return x_274;
}
else
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; 
x_275 = lean_ctor_get(x_271, 0);
lean_inc(x_275);
lean_dec(x_271);
x_276 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_276, 0, x_225);
lean_ctor_set(x_276, 1, x_232);
x_277 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_277, 0, x_239);
lean_ctor_set(x_277, 1, x_246);
x_278 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_278, 0, x_276);
lean_ctor_set(x_278, 1, x_277);
x_279 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_279, 0, x_254);
lean_ctor_set(x_279, 1, x_261);
x_280 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_280, 0, x_268);
lean_ctor_set(x_280, 1, x_275);
x_281 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_281, 0, x_279);
lean_ctor_set(x_281, 1, x_280);
x_282 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_282, 0, x_216);
lean_ctor_set(x_282, 1, x_278);
lean_ctor_set(x_282, 2, x_281);
if (lean_is_scalar(x_53)) {
 x_283 = lean_alloc_ctor(1, 1, 0);
} else {
 x_283 = x_53;
}
lean_ctor_set(x_283, 0, x_282);
x_284 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_284, 0, x_88);
lean_ctor_set(x_284, 1, x_283);
x_41 = x_284;
goto block_43;
}
}
}
}
}
else
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; 
lean_dec(x_246);
lean_dec(x_239);
lean_dec(x_232);
lean_dec(x_225);
lean_dec(x_216);
lean_dec(x_88);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_285 = lean_mk_string_unchecked("Expected list of length 4, not ", 31, 31);
x_286 = l___private_Init_Data_Repr_0__Nat_reprFast(x_55);
x_287 = lean_string_append(x_285, x_286);
lean_dec(x_286);
if (lean_is_scalar(x_247)) {
 x_288 = lean_alloc_ctor(0, 1, 0);
} else {
 x_288 = x_247;
 lean_ctor_set_tag(x_288, 0);
}
lean_ctor_set(x_288, 0, x_287);
return x_288;
}
}
}
}
}
}
else
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; 
lean_dec(x_216);
lean_dec(x_88);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_289 = lean_mk_string_unchecked("Expected list of length 4, not ", 31, 31);
x_290 = l___private_Init_Data_Repr_0__Nat_reprFast(x_55);
x_291 = lean_string_append(x_289, x_290);
lean_dec(x_290);
x_292 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_292, 0, x_291);
return x_292;
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
lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; 
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_293 = lean_mk_string_unchecked("Expected list of length 4, not ", 31, 31);
x_294 = l___private_Init_Data_Repr_0__Nat_reprFast(x_55);
x_295 = lean_string_append(x_293, x_294);
lean_dec(x_294);
if (lean_is_scalar(x_50)) {
 x_296 = lean_alloc_ctor(0, 1, 0);
} else {
 x_296 = x_50;
 lean_ctor_set_tag(x_296, 0);
}
lean_ctor_set(x_296, 0, x_295);
return x_296;
}
}
}
}
block_40:
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_mk_string_unchecked("usages", 6, 6);
x_24 = l_Lean_Json_getObjValAs_x3f___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2193__spec__0_spec__0(x_6, x_23);
lean_dec(x_23);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_9);
lean_dec(x_7);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
return x_24;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
else
{
lean_object* x_28; size_t x_29; lean_object* x_30; size_t x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_24, 0);
lean_inc(x_28);
lean_dec(x_24);
x_29 = lean_array_size(x_28);
x_30 = lean_unsigned_to_nat(0u);
x_31 = lean_usize_of_nat(x_30);
x_32 = l_Array_mapMUnsafe_map___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2193__spec__0_spec__3(x_29, x_31, x_28);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_9);
lean_dec(x_7);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
return x_32;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_32, 0);
lean_inc(x_36);
lean_dec(x_32);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_22);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_Std_DTreeMap_Internal_Impl_insert___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2193__spec__0_spec__4___redArg(x_21, x_37, x_9);
x_1 = x_38;
x_2 = x_7;
goto _start;
}
}
}
block_43:
{
lean_object* x_42; 
if (lean_is_scalar(x_10)) {
 x_42 = lean_alloc_ctor(1, 1, 0);
} else {
 x_42 = x_10;
}
lean_ctor_set(x_42, 0, x_41);
x_22 = x_42;
goto block_40;
}
}
else
{
lean_object* x_304; lean_object* x_305; lean_object* x_324; lean_object* x_327; lean_object* x_328; 
x_304 = lean_ctor_get(x_16, 0);
lean_inc(x_304);
lean_dec(x_16);
x_327 = lean_mk_string_unchecked("definition", 10, 10);
lean_inc(x_6);
x_328 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Basic_0__Lean_Lsp_fromJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1614__spec__0(x_6, x_327);
lean_dec(x_327);
if (lean_obj_tag(x_328) == 0)
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; 
lean_dec(x_304);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_329 = lean_ctor_get(x_328, 0);
lean_inc(x_329);
if (lean_is_exclusive(x_328)) {
 lean_ctor_release(x_328, 0);
 x_330 = x_328;
} else {
 lean_dec_ref(x_328);
 x_330 = lean_box(0);
}
if (lean_is_scalar(x_330)) {
 x_331 = lean_alloc_ctor(0, 1, 0);
} else {
 x_331 = x_330;
}
lean_ctor_set(x_331, 0, x_329);
return x_331;
}
else
{
lean_object* x_332; lean_object* x_333; 
x_332 = lean_ctor_get(x_328, 0);
lean_inc(x_332);
if (lean_is_exclusive(x_328)) {
 lean_ctor_release(x_328, 0);
 x_333 = x_328;
} else {
 lean_dec_ref(x_328);
 x_333 = lean_box(0);
}
if (lean_obj_tag(x_332) == 0)
{
lean_object* x_334; 
lean_dec(x_333);
lean_dec(x_10);
x_334 = lean_box(0);
x_305 = x_334;
goto block_323;
}
else
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_464; lean_object* x_465; uint8_t x_466; 
x_335 = lean_ctor_get(x_332, 0);
lean_inc(x_335);
if (lean_is_exclusive(x_332)) {
 lean_ctor_release(x_332, 0);
 x_336 = x_332;
} else {
 lean_dec_ref(x_332);
 x_336 = lean_box(0);
}
x_337 = lean_box(0);
x_464 = lean_array_get_size(x_335);
x_465 = lean_unsigned_to_nat(4u);
x_466 = lean_nat_dec_eq(x_464, x_465);
if (x_466 == 0)
{
lean_object* x_467; uint8_t x_468; 
x_467 = lean_unsigned_to_nat(13u);
x_468 = lean_nat_dec_eq(x_464, x_467);
lean_dec(x_464);
if (x_468 == 0)
{
lean_object* x_469; lean_object* x_470; 
lean_dec(x_336);
lean_dec(x_335);
lean_dec(x_333);
lean_dec(x_304);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_469 = lean_mk_string_unchecked("Expected list of length 4 or 13, not {l.size}", 45, 45);
x_470 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_470, 0, x_469);
return x_470;
}
else
{
goto block_463;
}
}
else
{
lean_dec(x_464);
goto block_463;
}
block_463:
{
lean_object* x_338; lean_object* x_339; uint8_t x_340; 
x_338 = lean_array_get_size(x_335);
x_339 = lean_unsigned_to_nat(4u);
x_340 = lean_nat_dec_lt(x_338, x_339);
if (x_340 == 0)
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; 
lean_dec(x_333);
x_341 = lean_unsigned_to_nat(0u);
x_342 = lean_array_fget(x_335, x_341);
x_343 = l_Lean_Json_getNat_x3f(x_342);
if (lean_obj_tag(x_343) == 0)
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; 
lean_dec(x_338);
lean_dec(x_336);
lean_dec(x_335);
lean_dec(x_304);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_344 = lean_ctor_get(x_343, 0);
lean_inc(x_344);
if (lean_is_exclusive(x_343)) {
 lean_ctor_release(x_343, 0);
 x_345 = x_343;
} else {
 lean_dec_ref(x_343);
 x_345 = lean_box(0);
}
if (lean_is_scalar(x_345)) {
 x_346 = lean_alloc_ctor(0, 1, 0);
} else {
 x_346 = x_345;
}
lean_ctor_set(x_346, 0, x_344);
return x_346;
}
else
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; 
x_347 = lean_ctor_get(x_343, 0);
lean_inc(x_347);
lean_dec(x_343);
x_348 = lean_unsigned_to_nat(1u);
x_349 = lean_array_fget(x_335, x_348);
x_350 = l_Lean_Json_getNat_x3f(x_349);
if (lean_obj_tag(x_350) == 0)
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; 
lean_dec(x_347);
lean_dec(x_338);
lean_dec(x_336);
lean_dec(x_335);
lean_dec(x_304);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_351 = lean_ctor_get(x_350, 0);
lean_inc(x_351);
if (lean_is_exclusive(x_350)) {
 lean_ctor_release(x_350, 0);
 x_352 = x_350;
} else {
 lean_dec_ref(x_350);
 x_352 = lean_box(0);
}
if (lean_is_scalar(x_352)) {
 x_353 = lean_alloc_ctor(0, 1, 0);
} else {
 x_353 = x_352;
}
lean_ctor_set(x_353, 0, x_351);
return x_353;
}
else
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; 
x_354 = lean_ctor_get(x_350, 0);
lean_inc(x_354);
lean_dec(x_350);
x_355 = lean_unsigned_to_nat(2u);
x_356 = lean_array_fget(x_335, x_355);
x_357 = l_Lean_Json_getNat_x3f(x_356);
if (lean_obj_tag(x_357) == 0)
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; 
lean_dec(x_354);
lean_dec(x_347);
lean_dec(x_338);
lean_dec(x_336);
lean_dec(x_335);
lean_dec(x_304);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_358 = lean_ctor_get(x_357, 0);
lean_inc(x_358);
if (lean_is_exclusive(x_357)) {
 lean_ctor_release(x_357, 0);
 x_359 = x_357;
} else {
 lean_dec_ref(x_357);
 x_359 = lean_box(0);
}
if (lean_is_scalar(x_359)) {
 x_360 = lean_alloc_ctor(0, 1, 0);
} else {
 x_360 = x_359;
}
lean_ctor_set(x_360, 0, x_358);
return x_360;
}
else
{
lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; 
x_361 = lean_ctor_get(x_357, 0);
lean_inc(x_361);
lean_dec(x_357);
x_362 = lean_unsigned_to_nat(3u);
x_363 = lean_array_fget(x_335, x_362);
x_364 = l_Lean_Json_getNat_x3f(x_363);
if (lean_obj_tag(x_364) == 0)
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; 
lean_dec(x_361);
lean_dec(x_354);
lean_dec(x_347);
lean_dec(x_338);
lean_dec(x_336);
lean_dec(x_335);
lean_dec(x_304);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_365 = lean_ctor_get(x_364, 0);
lean_inc(x_365);
if (lean_is_exclusive(x_364)) {
 lean_ctor_release(x_364, 0);
 x_366 = x_364;
} else {
 lean_dec_ref(x_364);
 x_366 = lean_box(0);
}
if (lean_is_scalar(x_366)) {
 x_367 = lean_alloc_ctor(0, 1, 0);
} else {
 x_367 = x_366;
}
lean_ctor_set(x_367, 0, x_365);
return x_367;
}
else
{
lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; uint8_t x_373; 
x_368 = lean_ctor_get(x_364, 0);
lean_inc(x_368);
lean_dec(x_364);
x_369 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_369, 0, x_347);
lean_ctor_set(x_369, 1, x_354);
x_370 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_370, 0, x_361);
lean_ctor_set(x_370, 1, x_368);
x_371 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_371, 0, x_369);
lean_ctor_set(x_371, 1, x_370);
x_372 = lean_unsigned_to_nat(13u);
x_373 = lean_nat_dec_eq(x_338, x_372);
if (x_373 == 0)
{
lean_object* x_374; lean_object* x_375; 
lean_dec(x_338);
lean_dec(x_336);
lean_dec(x_335);
x_374 = lean_box(0);
x_375 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_375, 0, x_371);
lean_ctor_set(x_375, 1, x_374);
x_324 = x_375;
goto block_326;
}
else
{
lean_object* x_376; lean_object* x_377; 
x_376 = lean_array_get(x_337, x_335, x_339);
x_377 = l_Lean_Json_getStr_x3f(x_376);
if (lean_obj_tag(x_377) == 0)
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; 
lean_dec(x_371);
lean_dec(x_338);
lean_dec(x_336);
lean_dec(x_335);
lean_dec(x_304);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_378 = lean_ctor_get(x_377, 0);
lean_inc(x_378);
if (lean_is_exclusive(x_377)) {
 lean_ctor_release(x_377, 0);
 x_379 = x_377;
} else {
 lean_dec_ref(x_377);
 x_379 = lean_box(0);
}
if (lean_is_scalar(x_379)) {
 x_380 = lean_alloc_ctor(0, 1, 0);
} else {
 x_380 = x_379;
}
lean_ctor_set(x_380, 0, x_378);
return x_380;
}
else
{
lean_object* x_381; lean_object* x_382; lean_object* x_383; uint8_t x_384; 
x_381 = lean_ctor_get(x_377, 0);
lean_inc(x_381);
if (lean_is_exclusive(x_377)) {
 lean_ctor_release(x_377, 0);
 x_382 = x_377;
} else {
 lean_dec_ref(x_377);
 x_382 = lean_box(0);
}
x_383 = lean_unsigned_to_nat(9u);
x_384 = lean_nat_dec_lt(x_338, x_383);
if (x_384 == 0)
{
lean_object* x_385; lean_object* x_386; lean_object* x_387; 
lean_dec(x_382);
x_385 = lean_unsigned_to_nat(5u);
x_386 = lean_array_fget(x_335, x_385);
x_387 = l_Lean_Json_getNat_x3f(x_386);
if (lean_obj_tag(x_387) == 0)
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; 
lean_dec(x_381);
lean_dec(x_371);
lean_dec(x_338);
lean_dec(x_336);
lean_dec(x_335);
lean_dec(x_304);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_388 = lean_ctor_get(x_387, 0);
lean_inc(x_388);
if (lean_is_exclusive(x_387)) {
 lean_ctor_release(x_387, 0);
 x_389 = x_387;
} else {
 lean_dec_ref(x_387);
 x_389 = lean_box(0);
}
if (lean_is_scalar(x_389)) {
 x_390 = lean_alloc_ctor(0, 1, 0);
} else {
 x_390 = x_389;
}
lean_ctor_set(x_390, 0, x_388);
return x_390;
}
else
{
lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; 
x_391 = lean_ctor_get(x_387, 0);
lean_inc(x_391);
lean_dec(x_387);
x_392 = lean_unsigned_to_nat(6u);
x_393 = lean_array_fget(x_335, x_392);
x_394 = l_Lean_Json_getNat_x3f(x_393);
if (lean_obj_tag(x_394) == 0)
{
lean_object* x_395; lean_object* x_396; lean_object* x_397; 
lean_dec(x_391);
lean_dec(x_381);
lean_dec(x_371);
lean_dec(x_338);
lean_dec(x_336);
lean_dec(x_335);
lean_dec(x_304);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_395 = lean_ctor_get(x_394, 0);
lean_inc(x_395);
if (lean_is_exclusive(x_394)) {
 lean_ctor_release(x_394, 0);
 x_396 = x_394;
} else {
 lean_dec_ref(x_394);
 x_396 = lean_box(0);
}
if (lean_is_scalar(x_396)) {
 x_397 = lean_alloc_ctor(0, 1, 0);
} else {
 x_397 = x_396;
}
lean_ctor_set(x_397, 0, x_395);
return x_397;
}
else
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; 
x_398 = lean_ctor_get(x_394, 0);
lean_inc(x_398);
lean_dec(x_394);
x_399 = lean_unsigned_to_nat(7u);
x_400 = lean_array_fget(x_335, x_399);
x_401 = l_Lean_Json_getNat_x3f(x_400);
if (lean_obj_tag(x_401) == 0)
{
lean_object* x_402; lean_object* x_403; lean_object* x_404; 
lean_dec(x_398);
lean_dec(x_391);
lean_dec(x_381);
lean_dec(x_371);
lean_dec(x_338);
lean_dec(x_336);
lean_dec(x_335);
lean_dec(x_304);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_402 = lean_ctor_get(x_401, 0);
lean_inc(x_402);
if (lean_is_exclusive(x_401)) {
 lean_ctor_release(x_401, 0);
 x_403 = x_401;
} else {
 lean_dec_ref(x_401);
 x_403 = lean_box(0);
}
if (lean_is_scalar(x_403)) {
 x_404 = lean_alloc_ctor(0, 1, 0);
} else {
 x_404 = x_403;
}
lean_ctor_set(x_404, 0, x_402);
return x_404;
}
else
{
lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; 
x_405 = lean_ctor_get(x_401, 0);
lean_inc(x_405);
lean_dec(x_401);
x_406 = lean_unsigned_to_nat(8u);
x_407 = lean_array_fget(x_335, x_406);
x_408 = l_Lean_Json_getNat_x3f(x_407);
if (lean_obj_tag(x_408) == 0)
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; 
lean_dec(x_405);
lean_dec(x_398);
lean_dec(x_391);
lean_dec(x_381);
lean_dec(x_371);
lean_dec(x_338);
lean_dec(x_336);
lean_dec(x_335);
lean_dec(x_304);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_409 = lean_ctor_get(x_408, 0);
lean_inc(x_409);
if (lean_is_exclusive(x_408)) {
 lean_ctor_release(x_408, 0);
 x_410 = x_408;
} else {
 lean_dec_ref(x_408);
 x_410 = lean_box(0);
}
if (lean_is_scalar(x_410)) {
 x_411 = lean_alloc_ctor(0, 1, 0);
} else {
 x_411 = x_410;
}
lean_ctor_set(x_411, 0, x_409);
return x_411;
}
else
{
lean_object* x_412; lean_object* x_413; uint8_t x_414; 
x_412 = lean_ctor_get(x_408, 0);
lean_inc(x_412);
if (lean_is_exclusive(x_408)) {
 lean_ctor_release(x_408, 0);
 x_413 = x_408;
} else {
 lean_dec_ref(x_408);
 x_413 = lean_box(0);
}
x_414 = lean_nat_dec_lt(x_338, x_372);
if (x_414 == 0)
{
lean_object* x_415; lean_object* x_416; 
lean_dec(x_413);
lean_dec(x_338);
x_415 = lean_array_fget(x_335, x_383);
x_416 = l_Lean_Json_getNat_x3f(x_415);
if (lean_obj_tag(x_416) == 0)
{
lean_object* x_417; lean_object* x_418; lean_object* x_419; 
lean_dec(x_412);
lean_dec(x_405);
lean_dec(x_398);
lean_dec(x_391);
lean_dec(x_381);
lean_dec(x_371);
lean_dec(x_336);
lean_dec(x_335);
lean_dec(x_304);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_417 = lean_ctor_get(x_416, 0);
lean_inc(x_417);
if (lean_is_exclusive(x_416)) {
 lean_ctor_release(x_416, 0);
 x_418 = x_416;
} else {
 lean_dec_ref(x_416);
 x_418 = lean_box(0);
}
if (lean_is_scalar(x_418)) {
 x_419 = lean_alloc_ctor(0, 1, 0);
} else {
 x_419 = x_418;
}
lean_ctor_set(x_419, 0, x_417);
return x_419;
}
else
{
lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; 
x_420 = lean_ctor_get(x_416, 0);
lean_inc(x_420);
lean_dec(x_416);
x_421 = lean_unsigned_to_nat(10u);
x_422 = lean_array_fget(x_335, x_421);
x_423 = l_Lean_Json_getNat_x3f(x_422);
if (lean_obj_tag(x_423) == 0)
{
lean_object* x_424; lean_object* x_425; lean_object* x_426; 
lean_dec(x_420);
lean_dec(x_412);
lean_dec(x_405);
lean_dec(x_398);
lean_dec(x_391);
lean_dec(x_381);
lean_dec(x_371);
lean_dec(x_336);
lean_dec(x_335);
lean_dec(x_304);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_424 = lean_ctor_get(x_423, 0);
lean_inc(x_424);
if (lean_is_exclusive(x_423)) {
 lean_ctor_release(x_423, 0);
 x_425 = x_423;
} else {
 lean_dec_ref(x_423);
 x_425 = lean_box(0);
}
if (lean_is_scalar(x_425)) {
 x_426 = lean_alloc_ctor(0, 1, 0);
} else {
 x_426 = x_425;
}
lean_ctor_set(x_426, 0, x_424);
return x_426;
}
else
{
lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; 
x_427 = lean_ctor_get(x_423, 0);
lean_inc(x_427);
lean_dec(x_423);
x_428 = lean_unsigned_to_nat(11u);
x_429 = lean_array_fget(x_335, x_428);
x_430 = l_Lean_Json_getNat_x3f(x_429);
if (lean_obj_tag(x_430) == 0)
{
lean_object* x_431; lean_object* x_432; lean_object* x_433; 
lean_dec(x_427);
lean_dec(x_420);
lean_dec(x_412);
lean_dec(x_405);
lean_dec(x_398);
lean_dec(x_391);
lean_dec(x_381);
lean_dec(x_371);
lean_dec(x_336);
lean_dec(x_335);
lean_dec(x_304);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_431 = lean_ctor_get(x_430, 0);
lean_inc(x_431);
if (lean_is_exclusive(x_430)) {
 lean_ctor_release(x_430, 0);
 x_432 = x_430;
} else {
 lean_dec_ref(x_430);
 x_432 = lean_box(0);
}
if (lean_is_scalar(x_432)) {
 x_433 = lean_alloc_ctor(0, 1, 0);
} else {
 x_433 = x_432;
}
lean_ctor_set(x_433, 0, x_431);
return x_433;
}
else
{
lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; 
x_434 = lean_ctor_get(x_430, 0);
lean_inc(x_434);
lean_dec(x_430);
x_435 = lean_unsigned_to_nat(12u);
x_436 = lean_array_fget(x_335, x_435);
lean_dec(x_335);
x_437 = l_Lean_Json_getNat_x3f(x_436);
if (lean_obj_tag(x_437) == 0)
{
lean_object* x_438; lean_object* x_439; lean_object* x_440; 
lean_dec(x_434);
lean_dec(x_427);
lean_dec(x_420);
lean_dec(x_412);
lean_dec(x_405);
lean_dec(x_398);
lean_dec(x_391);
lean_dec(x_381);
lean_dec(x_371);
lean_dec(x_336);
lean_dec(x_304);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_438 = lean_ctor_get(x_437, 0);
lean_inc(x_438);
if (lean_is_exclusive(x_437)) {
 lean_ctor_release(x_437, 0);
 x_439 = x_437;
} else {
 lean_dec_ref(x_437);
 x_439 = lean_box(0);
}
if (lean_is_scalar(x_439)) {
 x_440 = lean_alloc_ctor(0, 1, 0);
} else {
 x_440 = x_439;
}
lean_ctor_set(x_440, 0, x_438);
return x_440;
}
else
{
lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; 
x_441 = lean_ctor_get(x_437, 0);
lean_inc(x_441);
lean_dec(x_437);
x_442 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_442, 0, x_391);
lean_ctor_set(x_442, 1, x_398);
x_443 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_443, 0, x_405);
lean_ctor_set(x_443, 1, x_412);
x_444 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_444, 0, x_442);
lean_ctor_set(x_444, 1, x_443);
x_445 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_445, 0, x_420);
lean_ctor_set(x_445, 1, x_427);
x_446 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_446, 0, x_434);
lean_ctor_set(x_446, 1, x_441);
x_447 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_447, 0, x_445);
lean_ctor_set(x_447, 1, x_446);
x_448 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_448, 0, x_381);
lean_ctor_set(x_448, 1, x_444);
lean_ctor_set(x_448, 2, x_447);
if (lean_is_scalar(x_336)) {
 x_449 = lean_alloc_ctor(1, 1, 0);
} else {
 x_449 = x_336;
}
lean_ctor_set(x_449, 0, x_448);
x_450 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_450, 0, x_371);
lean_ctor_set(x_450, 1, x_449);
x_324 = x_450;
goto block_326;
}
}
}
}
}
else
{
lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; 
lean_dec(x_412);
lean_dec(x_405);
lean_dec(x_398);
lean_dec(x_391);
lean_dec(x_381);
lean_dec(x_371);
lean_dec(x_336);
lean_dec(x_335);
lean_dec(x_304);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_451 = lean_mk_string_unchecked("Expected list of length 4, not ", 31, 31);
x_452 = l___private_Init_Data_Repr_0__Nat_reprFast(x_338);
x_453 = lean_string_append(x_451, x_452);
lean_dec(x_452);
if (lean_is_scalar(x_413)) {
 x_454 = lean_alloc_ctor(0, 1, 0);
} else {
 x_454 = x_413;
 lean_ctor_set_tag(x_454, 0);
}
lean_ctor_set(x_454, 0, x_453);
return x_454;
}
}
}
}
}
}
else
{
lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; 
lean_dec(x_381);
lean_dec(x_371);
lean_dec(x_336);
lean_dec(x_335);
lean_dec(x_304);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_455 = lean_mk_string_unchecked("Expected list of length 4, not ", 31, 31);
x_456 = l___private_Init_Data_Repr_0__Nat_reprFast(x_338);
x_457 = lean_string_append(x_455, x_456);
lean_dec(x_456);
if (lean_is_scalar(x_382)) {
 x_458 = lean_alloc_ctor(0, 1, 0);
} else {
 x_458 = x_382;
 lean_ctor_set_tag(x_458, 0);
}
lean_ctor_set(x_458, 0, x_457);
return x_458;
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
lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; 
lean_dec(x_336);
lean_dec(x_335);
lean_dec(x_304);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_459 = lean_mk_string_unchecked("Expected list of length 4, not ", 31, 31);
x_460 = l___private_Init_Data_Repr_0__Nat_reprFast(x_338);
x_461 = lean_string_append(x_459, x_460);
lean_dec(x_460);
if (lean_is_scalar(x_333)) {
 x_462 = lean_alloc_ctor(0, 1, 0);
} else {
 x_462 = x_333;
 lean_ctor_set_tag(x_462, 0);
}
lean_ctor_set(x_462, 0, x_461);
return x_462;
}
}
}
}
block_323:
{
lean_object* x_306; lean_object* x_307; 
x_306 = lean_mk_string_unchecked("usages", 6, 6);
x_307 = l_Lean_Json_getObjValAs_x3f___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2193__spec__0_spec__0(x_6, x_306);
lean_dec(x_306);
if (lean_obj_tag(x_307) == 0)
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; 
lean_dec(x_305);
lean_dec(x_304);
lean_dec(x_9);
lean_dec(x_7);
x_308 = lean_ctor_get(x_307, 0);
lean_inc(x_308);
if (lean_is_exclusive(x_307)) {
 lean_ctor_release(x_307, 0);
 x_309 = x_307;
} else {
 lean_dec_ref(x_307);
 x_309 = lean_box(0);
}
if (lean_is_scalar(x_309)) {
 x_310 = lean_alloc_ctor(0, 1, 0);
} else {
 x_310 = x_309;
}
lean_ctor_set(x_310, 0, x_308);
return x_310;
}
else
{
lean_object* x_311; size_t x_312; lean_object* x_313; size_t x_314; lean_object* x_315; 
x_311 = lean_ctor_get(x_307, 0);
lean_inc(x_311);
lean_dec(x_307);
x_312 = lean_array_size(x_311);
x_313 = lean_unsigned_to_nat(0u);
x_314 = lean_usize_of_nat(x_313);
x_315 = l_Array_mapMUnsafe_map___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2193__spec__0_spec__3(x_312, x_314, x_311);
if (lean_obj_tag(x_315) == 0)
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; 
lean_dec(x_305);
lean_dec(x_304);
lean_dec(x_9);
lean_dec(x_7);
x_316 = lean_ctor_get(x_315, 0);
lean_inc(x_316);
if (lean_is_exclusive(x_315)) {
 lean_ctor_release(x_315, 0);
 x_317 = x_315;
} else {
 lean_dec_ref(x_315);
 x_317 = lean_box(0);
}
if (lean_is_scalar(x_317)) {
 x_318 = lean_alloc_ctor(0, 1, 0);
} else {
 x_318 = x_317;
}
lean_ctor_set(x_318, 0, x_316);
return x_318;
}
else
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; 
x_319 = lean_ctor_get(x_315, 0);
lean_inc(x_319);
lean_dec(x_315);
x_320 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_320, 0, x_305);
lean_ctor_set(x_320, 1, x_319);
x_321 = l_Std_DTreeMap_Internal_Impl_insert___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2193__spec__0_spec__4___redArg(x_304, x_320, x_9);
x_1 = x_321;
x_2 = x_7;
goto _start;
}
}
}
block_326:
{
lean_object* x_325; 
if (lean_is_scalar(x_10)) {
 x_325 = lean_alloc_ctor(1, 1, 0);
} else {
 x_325 = x_10;
}
lean_ctor_set(x_325, 0, x_324);
x_305 = x_325;
goto block_323;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2193__spec__0_spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 3);
lean_inc(x_7);
lean_dec(x_2);
x_8 = l_Lean_RBNode_foldM___at___Lean_RBNode_foldM___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2193__spec__0_spec__5_spec__5(x_1, x_4);
if (lean_obj_tag(x_8) == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 x_10 = x_8;
} else {
 lean_dec_ref(x_8);
 x_10 = lean_box(0);
}
x_11 = l_Lean_Json_parse(x_5);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
return x_11;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_11, 0);
lean_inc(x_15);
lean_dec(x_11);
x_16 = l_Lean_Lsp_RefIdent_fromJson_x3f(x_15);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
return x_16;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_16);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_41; lean_object* x_44; lean_object* x_45; 
x_21 = lean_ctor_get(x_16, 0);
x_44 = lean_mk_string_unchecked("definition", 10, 10);
lean_inc(x_6);
x_45 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Basic_0__Lean_Lsp_fromJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1614__spec__0(x_6, x_44);
lean_dec(x_44);
if (lean_obj_tag(x_45) == 0)
{
uint8_t x_46; 
lean_free_object(x_16);
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
return x_45;
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_45, 0);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_47);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_45, 0);
lean_inc(x_49);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 x_50 = x_45;
} else {
 lean_dec_ref(x_45);
 x_50 = lean_box(0);
}
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_51; 
lean_dec(x_50);
lean_free_object(x_16);
lean_dec(x_10);
x_51 = lean_box(0);
x_22 = x_51;
goto block_40;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_298; lean_object* x_299; uint8_t x_300; 
x_52 = lean_ctor_get(x_49, 0);
lean_inc(x_52);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 x_53 = x_49;
} else {
 lean_dec_ref(x_49);
 x_53 = lean_box(0);
}
x_54 = lean_box(0);
x_298 = lean_array_get_size(x_52);
x_299 = lean_unsigned_to_nat(4u);
x_300 = lean_nat_dec_eq(x_298, x_299);
if (x_300 == 0)
{
lean_object* x_301; uint8_t x_302; 
x_301 = lean_unsigned_to_nat(13u);
x_302 = lean_nat_dec_eq(x_298, x_301);
lean_dec(x_298);
if (x_302 == 0)
{
lean_object* x_303; 
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_50);
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_303 = lean_mk_string_unchecked("Expected list of length 4 or 13, not {l.size}", 45, 45);
lean_ctor_set_tag(x_16, 0);
lean_ctor_set(x_16, 0, x_303);
return x_16;
}
else
{
lean_free_object(x_16);
goto block_297;
}
}
else
{
lean_dec(x_298);
lean_free_object(x_16);
goto block_297;
}
block_297:
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_55 = lean_array_get_size(x_52);
x_56 = lean_unsigned_to_nat(4u);
x_57 = lean_nat_dec_lt(x_55, x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_50);
x_58 = lean_unsigned_to_nat(0u);
x_59 = lean_array_fget(x_52, x_58);
x_60 = l_Lean_Json_getNat_x3f(x_59);
if (lean_obj_tag(x_60) == 0)
{
uint8_t x_61; 
lean_dec(x_55);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_61 = !lean_is_exclusive(x_60);
if (x_61 == 0)
{
return x_60;
}
else
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_60, 0);
lean_inc(x_62);
lean_dec(x_60);
x_63 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_63, 0, x_62);
return x_63;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_64 = lean_ctor_get(x_60, 0);
lean_inc(x_64);
lean_dec(x_60);
x_65 = lean_unsigned_to_nat(1u);
x_66 = lean_array_fget(x_52, x_65);
x_67 = l_Lean_Json_getNat_x3f(x_66);
if (lean_obj_tag(x_67) == 0)
{
uint8_t x_68; 
lean_dec(x_64);
lean_dec(x_55);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_68 = !lean_is_exclusive(x_67);
if (x_68 == 0)
{
return x_67;
}
else
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_67, 0);
lean_inc(x_69);
lean_dec(x_67);
x_70 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_70, 0, x_69);
return x_70;
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_71 = lean_ctor_get(x_67, 0);
lean_inc(x_71);
lean_dec(x_67);
x_72 = lean_unsigned_to_nat(2u);
x_73 = lean_array_fget(x_52, x_72);
x_74 = l_Lean_Json_getNat_x3f(x_73);
if (lean_obj_tag(x_74) == 0)
{
uint8_t x_75; 
lean_dec(x_71);
lean_dec(x_64);
lean_dec(x_55);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_75 = !lean_is_exclusive(x_74);
if (x_75 == 0)
{
return x_74;
}
else
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_74, 0);
lean_inc(x_76);
lean_dec(x_74);
x_77 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_77, 0, x_76);
return x_77;
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_78 = lean_ctor_get(x_74, 0);
lean_inc(x_78);
lean_dec(x_74);
x_79 = lean_unsigned_to_nat(3u);
x_80 = lean_array_fget(x_52, x_79);
x_81 = l_Lean_Json_getNat_x3f(x_80);
if (lean_obj_tag(x_81) == 0)
{
uint8_t x_82; 
lean_dec(x_78);
lean_dec(x_71);
lean_dec(x_64);
lean_dec(x_55);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_82 = !lean_is_exclusive(x_81);
if (x_82 == 0)
{
return x_81;
}
else
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_81, 0);
lean_inc(x_83);
lean_dec(x_81);
x_84 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_84, 0, x_83);
return x_84;
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_85 = lean_ctor_get(x_81, 0);
lean_inc(x_85);
lean_dec(x_81);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_64);
lean_ctor_set(x_86, 1, x_71);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_78);
lean_ctor_set(x_87, 1, x_85);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
x_89 = lean_unsigned_to_nat(13u);
x_90 = lean_nat_dec_eq(x_55, x_89);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; 
lean_dec(x_55);
lean_dec(x_53);
lean_dec(x_52);
x_91 = lean_box(0);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_88);
lean_ctor_set(x_92, 1, x_91);
x_41 = x_92;
goto block_43;
}
else
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_array_get(x_54, x_52, x_56);
x_94 = l_Lean_Json_getStr_x3f(x_93);
if (lean_obj_tag(x_94) == 0)
{
uint8_t x_95; 
lean_dec(x_88);
lean_dec(x_55);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_95 = !lean_is_exclusive(x_94);
if (x_95 == 0)
{
return x_94;
}
else
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_94, 0);
lean_inc(x_96);
lean_dec(x_94);
x_97 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_97, 0, x_96);
return x_97;
}
}
else
{
uint8_t x_98; 
x_98 = !lean_is_exclusive(x_94);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_99 = lean_ctor_get(x_94, 0);
x_100 = lean_unsigned_to_nat(9u);
x_101 = lean_nat_dec_lt(x_55, x_100);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_free_object(x_94);
x_102 = lean_unsigned_to_nat(5u);
x_103 = lean_array_fget(x_52, x_102);
x_104 = l_Lean_Json_getNat_x3f(x_103);
if (lean_obj_tag(x_104) == 0)
{
uint8_t x_105; 
lean_dec(x_99);
lean_dec(x_88);
lean_dec(x_55);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_105 = !lean_is_exclusive(x_104);
if (x_105 == 0)
{
return x_104;
}
else
{
lean_object* x_106; lean_object* x_107; 
x_106 = lean_ctor_get(x_104, 0);
lean_inc(x_106);
lean_dec(x_104);
x_107 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_107, 0, x_106);
return x_107;
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_108 = lean_ctor_get(x_104, 0);
lean_inc(x_108);
lean_dec(x_104);
x_109 = lean_unsigned_to_nat(6u);
x_110 = lean_array_fget(x_52, x_109);
x_111 = l_Lean_Json_getNat_x3f(x_110);
if (lean_obj_tag(x_111) == 0)
{
uint8_t x_112; 
lean_dec(x_108);
lean_dec(x_99);
lean_dec(x_88);
lean_dec(x_55);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_112 = !lean_is_exclusive(x_111);
if (x_112 == 0)
{
return x_111;
}
else
{
lean_object* x_113; lean_object* x_114; 
x_113 = lean_ctor_get(x_111, 0);
lean_inc(x_113);
lean_dec(x_111);
x_114 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_114, 0, x_113);
return x_114;
}
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_115 = lean_ctor_get(x_111, 0);
lean_inc(x_115);
lean_dec(x_111);
x_116 = lean_unsigned_to_nat(7u);
x_117 = lean_array_fget(x_52, x_116);
x_118 = l_Lean_Json_getNat_x3f(x_117);
if (lean_obj_tag(x_118) == 0)
{
uint8_t x_119; 
lean_dec(x_115);
lean_dec(x_108);
lean_dec(x_99);
lean_dec(x_88);
lean_dec(x_55);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_119 = !lean_is_exclusive(x_118);
if (x_119 == 0)
{
return x_118;
}
else
{
lean_object* x_120; lean_object* x_121; 
x_120 = lean_ctor_get(x_118, 0);
lean_inc(x_120);
lean_dec(x_118);
x_121 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_121, 0, x_120);
return x_121;
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_122 = lean_ctor_get(x_118, 0);
lean_inc(x_122);
lean_dec(x_118);
x_123 = lean_unsigned_to_nat(8u);
x_124 = lean_array_fget(x_52, x_123);
x_125 = l_Lean_Json_getNat_x3f(x_124);
if (lean_obj_tag(x_125) == 0)
{
uint8_t x_126; 
lean_dec(x_122);
lean_dec(x_115);
lean_dec(x_108);
lean_dec(x_99);
lean_dec(x_88);
lean_dec(x_55);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_126 = !lean_is_exclusive(x_125);
if (x_126 == 0)
{
return x_125;
}
else
{
lean_object* x_127; lean_object* x_128; 
x_127 = lean_ctor_get(x_125, 0);
lean_inc(x_127);
lean_dec(x_125);
x_128 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_128, 0, x_127);
return x_128;
}
}
else
{
uint8_t x_129; 
x_129 = !lean_is_exclusive(x_125);
if (x_129 == 0)
{
lean_object* x_130; uint8_t x_131; 
x_130 = lean_ctor_get(x_125, 0);
x_131 = lean_nat_dec_lt(x_55, x_89);
if (x_131 == 0)
{
lean_object* x_132; lean_object* x_133; 
lean_free_object(x_125);
lean_dec(x_55);
x_132 = lean_array_fget(x_52, x_100);
x_133 = l_Lean_Json_getNat_x3f(x_132);
if (lean_obj_tag(x_133) == 0)
{
uint8_t x_134; 
lean_dec(x_130);
lean_dec(x_122);
lean_dec(x_115);
lean_dec(x_108);
lean_dec(x_99);
lean_dec(x_88);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_134 = !lean_is_exclusive(x_133);
if (x_134 == 0)
{
return x_133;
}
else
{
lean_object* x_135; lean_object* x_136; 
x_135 = lean_ctor_get(x_133, 0);
lean_inc(x_135);
lean_dec(x_133);
x_136 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_136, 0, x_135);
return x_136;
}
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_137 = lean_ctor_get(x_133, 0);
lean_inc(x_137);
lean_dec(x_133);
x_138 = lean_unsigned_to_nat(10u);
x_139 = lean_array_fget(x_52, x_138);
x_140 = l_Lean_Json_getNat_x3f(x_139);
if (lean_obj_tag(x_140) == 0)
{
uint8_t x_141; 
lean_dec(x_137);
lean_dec(x_130);
lean_dec(x_122);
lean_dec(x_115);
lean_dec(x_108);
lean_dec(x_99);
lean_dec(x_88);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_141 = !lean_is_exclusive(x_140);
if (x_141 == 0)
{
return x_140;
}
else
{
lean_object* x_142; lean_object* x_143; 
x_142 = lean_ctor_get(x_140, 0);
lean_inc(x_142);
lean_dec(x_140);
x_143 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_143, 0, x_142);
return x_143;
}
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_144 = lean_ctor_get(x_140, 0);
lean_inc(x_144);
lean_dec(x_140);
x_145 = lean_unsigned_to_nat(11u);
x_146 = lean_array_fget(x_52, x_145);
x_147 = l_Lean_Json_getNat_x3f(x_146);
if (lean_obj_tag(x_147) == 0)
{
uint8_t x_148; 
lean_dec(x_144);
lean_dec(x_137);
lean_dec(x_130);
lean_dec(x_122);
lean_dec(x_115);
lean_dec(x_108);
lean_dec(x_99);
lean_dec(x_88);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_148 = !lean_is_exclusive(x_147);
if (x_148 == 0)
{
return x_147;
}
else
{
lean_object* x_149; lean_object* x_150; 
x_149 = lean_ctor_get(x_147, 0);
lean_inc(x_149);
lean_dec(x_147);
x_150 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_150, 0, x_149);
return x_150;
}
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_151 = lean_ctor_get(x_147, 0);
lean_inc(x_151);
lean_dec(x_147);
x_152 = lean_unsigned_to_nat(12u);
x_153 = lean_array_fget(x_52, x_152);
lean_dec(x_52);
x_154 = l_Lean_Json_getNat_x3f(x_153);
if (lean_obj_tag(x_154) == 0)
{
uint8_t x_155; 
lean_dec(x_151);
lean_dec(x_144);
lean_dec(x_137);
lean_dec(x_130);
lean_dec(x_122);
lean_dec(x_115);
lean_dec(x_108);
lean_dec(x_99);
lean_dec(x_88);
lean_dec(x_53);
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_155 = !lean_is_exclusive(x_154);
if (x_155 == 0)
{
return x_154;
}
else
{
lean_object* x_156; lean_object* x_157; 
x_156 = lean_ctor_get(x_154, 0);
lean_inc(x_156);
lean_dec(x_154);
x_157 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_157, 0, x_156);
return x_157;
}
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_158 = lean_ctor_get(x_154, 0);
lean_inc(x_158);
lean_dec(x_154);
x_159 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_159, 0, x_108);
lean_ctor_set(x_159, 1, x_115);
x_160 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_160, 0, x_122);
lean_ctor_set(x_160, 1, x_130);
x_161 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_161, 0, x_159);
lean_ctor_set(x_161, 1, x_160);
x_162 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_162, 0, x_137);
lean_ctor_set(x_162, 1, x_144);
x_163 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_163, 0, x_151);
lean_ctor_set(x_163, 1, x_158);
x_164 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_164, 0, x_162);
lean_ctor_set(x_164, 1, x_163);
x_165 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_165, 0, x_99);
lean_ctor_set(x_165, 1, x_161);
lean_ctor_set(x_165, 2, x_164);
if (lean_is_scalar(x_53)) {
 x_166 = lean_alloc_ctor(1, 1, 0);
} else {
 x_166 = x_53;
}
lean_ctor_set(x_166, 0, x_165);
x_167 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_167, 0, x_88);
lean_ctor_set(x_167, 1, x_166);
x_41 = x_167;
goto block_43;
}
}
}
}
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; 
lean_dec(x_130);
lean_dec(x_122);
lean_dec(x_115);
lean_dec(x_108);
lean_dec(x_99);
lean_dec(x_88);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_168 = lean_mk_string_unchecked("Expected list of length 4, not ", 31, 31);
x_169 = l___private_Init_Data_Repr_0__Nat_reprFast(x_55);
x_170 = lean_string_append(x_168, x_169);
lean_dec(x_169);
lean_ctor_set_tag(x_125, 0);
lean_ctor_set(x_125, 0, x_170);
return x_125;
}
}
else
{
lean_object* x_171; uint8_t x_172; 
x_171 = lean_ctor_get(x_125, 0);
lean_inc(x_171);
lean_dec(x_125);
x_172 = lean_nat_dec_lt(x_55, x_89);
if (x_172 == 0)
{
lean_object* x_173; lean_object* x_174; 
lean_dec(x_55);
x_173 = lean_array_fget(x_52, x_100);
x_174 = l_Lean_Json_getNat_x3f(x_173);
if (lean_obj_tag(x_174) == 0)
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; 
lean_dec(x_171);
lean_dec(x_122);
lean_dec(x_115);
lean_dec(x_108);
lean_dec(x_99);
lean_dec(x_88);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_175 = lean_ctor_get(x_174, 0);
lean_inc(x_175);
if (lean_is_exclusive(x_174)) {
 lean_ctor_release(x_174, 0);
 x_176 = x_174;
} else {
 lean_dec_ref(x_174);
 x_176 = lean_box(0);
}
if (lean_is_scalar(x_176)) {
 x_177 = lean_alloc_ctor(0, 1, 0);
} else {
 x_177 = x_176;
}
lean_ctor_set(x_177, 0, x_175);
return x_177;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_178 = lean_ctor_get(x_174, 0);
lean_inc(x_178);
lean_dec(x_174);
x_179 = lean_unsigned_to_nat(10u);
x_180 = lean_array_fget(x_52, x_179);
x_181 = l_Lean_Json_getNat_x3f(x_180);
if (lean_obj_tag(x_181) == 0)
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; 
lean_dec(x_178);
lean_dec(x_171);
lean_dec(x_122);
lean_dec(x_115);
lean_dec(x_108);
lean_dec(x_99);
lean_dec(x_88);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_182 = lean_ctor_get(x_181, 0);
lean_inc(x_182);
if (lean_is_exclusive(x_181)) {
 lean_ctor_release(x_181, 0);
 x_183 = x_181;
} else {
 lean_dec_ref(x_181);
 x_183 = lean_box(0);
}
if (lean_is_scalar(x_183)) {
 x_184 = lean_alloc_ctor(0, 1, 0);
} else {
 x_184 = x_183;
}
lean_ctor_set(x_184, 0, x_182);
return x_184;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_185 = lean_ctor_get(x_181, 0);
lean_inc(x_185);
lean_dec(x_181);
x_186 = lean_unsigned_to_nat(11u);
x_187 = lean_array_fget(x_52, x_186);
x_188 = l_Lean_Json_getNat_x3f(x_187);
if (lean_obj_tag(x_188) == 0)
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; 
lean_dec(x_185);
lean_dec(x_178);
lean_dec(x_171);
lean_dec(x_122);
lean_dec(x_115);
lean_dec(x_108);
lean_dec(x_99);
lean_dec(x_88);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 x_190 = x_188;
} else {
 lean_dec_ref(x_188);
 x_190 = lean_box(0);
}
if (lean_is_scalar(x_190)) {
 x_191 = lean_alloc_ctor(0, 1, 0);
} else {
 x_191 = x_190;
}
lean_ctor_set(x_191, 0, x_189);
return x_191;
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_192 = lean_ctor_get(x_188, 0);
lean_inc(x_192);
lean_dec(x_188);
x_193 = lean_unsigned_to_nat(12u);
x_194 = lean_array_fget(x_52, x_193);
lean_dec(x_52);
x_195 = l_Lean_Json_getNat_x3f(x_194);
if (lean_obj_tag(x_195) == 0)
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; 
lean_dec(x_192);
lean_dec(x_185);
lean_dec(x_178);
lean_dec(x_171);
lean_dec(x_122);
lean_dec(x_115);
lean_dec(x_108);
lean_dec(x_99);
lean_dec(x_88);
lean_dec(x_53);
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_196 = lean_ctor_get(x_195, 0);
lean_inc(x_196);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 x_197 = x_195;
} else {
 lean_dec_ref(x_195);
 x_197 = lean_box(0);
}
if (lean_is_scalar(x_197)) {
 x_198 = lean_alloc_ctor(0, 1, 0);
} else {
 x_198 = x_197;
}
lean_ctor_set(x_198, 0, x_196);
return x_198;
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_199 = lean_ctor_get(x_195, 0);
lean_inc(x_199);
lean_dec(x_195);
x_200 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_200, 0, x_108);
lean_ctor_set(x_200, 1, x_115);
x_201 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_201, 0, x_122);
lean_ctor_set(x_201, 1, x_171);
x_202 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_202, 0, x_200);
lean_ctor_set(x_202, 1, x_201);
x_203 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_203, 0, x_178);
lean_ctor_set(x_203, 1, x_185);
x_204 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_204, 0, x_192);
lean_ctor_set(x_204, 1, x_199);
x_205 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_205, 0, x_203);
lean_ctor_set(x_205, 1, x_204);
x_206 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_206, 0, x_99);
lean_ctor_set(x_206, 1, x_202);
lean_ctor_set(x_206, 2, x_205);
if (lean_is_scalar(x_53)) {
 x_207 = lean_alloc_ctor(1, 1, 0);
} else {
 x_207 = x_53;
}
lean_ctor_set(x_207, 0, x_206);
x_208 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_208, 0, x_88);
lean_ctor_set(x_208, 1, x_207);
x_41 = x_208;
goto block_43;
}
}
}
}
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
lean_dec(x_171);
lean_dec(x_122);
lean_dec(x_115);
lean_dec(x_108);
lean_dec(x_99);
lean_dec(x_88);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_209 = lean_mk_string_unchecked("Expected list of length 4, not ", 31, 31);
x_210 = l___private_Init_Data_Repr_0__Nat_reprFast(x_55);
x_211 = lean_string_append(x_209, x_210);
lean_dec(x_210);
x_212 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_212, 0, x_211);
return x_212;
}
}
}
}
}
}
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; 
lean_dec(x_99);
lean_dec(x_88);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_213 = lean_mk_string_unchecked("Expected list of length 4, not ", 31, 31);
x_214 = l___private_Init_Data_Repr_0__Nat_reprFast(x_55);
x_215 = lean_string_append(x_213, x_214);
lean_dec(x_214);
lean_ctor_set_tag(x_94, 0);
lean_ctor_set(x_94, 0, x_215);
return x_94;
}
}
else
{
lean_object* x_216; lean_object* x_217; uint8_t x_218; 
x_216 = lean_ctor_get(x_94, 0);
lean_inc(x_216);
lean_dec(x_94);
x_217 = lean_unsigned_to_nat(9u);
x_218 = lean_nat_dec_lt(x_55, x_217);
if (x_218 == 0)
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_219 = lean_unsigned_to_nat(5u);
x_220 = lean_array_fget(x_52, x_219);
x_221 = l_Lean_Json_getNat_x3f(x_220);
if (lean_obj_tag(x_221) == 0)
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; 
lean_dec(x_216);
lean_dec(x_88);
lean_dec(x_55);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_222 = lean_ctor_get(x_221, 0);
lean_inc(x_222);
if (lean_is_exclusive(x_221)) {
 lean_ctor_release(x_221, 0);
 x_223 = x_221;
} else {
 lean_dec_ref(x_221);
 x_223 = lean_box(0);
}
if (lean_is_scalar(x_223)) {
 x_224 = lean_alloc_ctor(0, 1, 0);
} else {
 x_224 = x_223;
}
lean_ctor_set(x_224, 0, x_222);
return x_224;
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_225 = lean_ctor_get(x_221, 0);
lean_inc(x_225);
lean_dec(x_221);
x_226 = lean_unsigned_to_nat(6u);
x_227 = lean_array_fget(x_52, x_226);
x_228 = l_Lean_Json_getNat_x3f(x_227);
if (lean_obj_tag(x_228) == 0)
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; 
lean_dec(x_225);
lean_dec(x_216);
lean_dec(x_88);
lean_dec(x_55);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_229 = lean_ctor_get(x_228, 0);
lean_inc(x_229);
if (lean_is_exclusive(x_228)) {
 lean_ctor_release(x_228, 0);
 x_230 = x_228;
} else {
 lean_dec_ref(x_228);
 x_230 = lean_box(0);
}
if (lean_is_scalar(x_230)) {
 x_231 = lean_alloc_ctor(0, 1, 0);
} else {
 x_231 = x_230;
}
lean_ctor_set(x_231, 0, x_229);
return x_231;
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_232 = lean_ctor_get(x_228, 0);
lean_inc(x_232);
lean_dec(x_228);
x_233 = lean_unsigned_to_nat(7u);
x_234 = lean_array_fget(x_52, x_233);
x_235 = l_Lean_Json_getNat_x3f(x_234);
if (lean_obj_tag(x_235) == 0)
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; 
lean_dec(x_232);
lean_dec(x_225);
lean_dec(x_216);
lean_dec(x_88);
lean_dec(x_55);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_236 = lean_ctor_get(x_235, 0);
lean_inc(x_236);
if (lean_is_exclusive(x_235)) {
 lean_ctor_release(x_235, 0);
 x_237 = x_235;
} else {
 lean_dec_ref(x_235);
 x_237 = lean_box(0);
}
if (lean_is_scalar(x_237)) {
 x_238 = lean_alloc_ctor(0, 1, 0);
} else {
 x_238 = x_237;
}
lean_ctor_set(x_238, 0, x_236);
return x_238;
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; 
x_239 = lean_ctor_get(x_235, 0);
lean_inc(x_239);
lean_dec(x_235);
x_240 = lean_unsigned_to_nat(8u);
x_241 = lean_array_fget(x_52, x_240);
x_242 = l_Lean_Json_getNat_x3f(x_241);
if (lean_obj_tag(x_242) == 0)
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; 
lean_dec(x_239);
lean_dec(x_232);
lean_dec(x_225);
lean_dec(x_216);
lean_dec(x_88);
lean_dec(x_55);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_243 = lean_ctor_get(x_242, 0);
lean_inc(x_243);
if (lean_is_exclusive(x_242)) {
 lean_ctor_release(x_242, 0);
 x_244 = x_242;
} else {
 lean_dec_ref(x_242);
 x_244 = lean_box(0);
}
if (lean_is_scalar(x_244)) {
 x_245 = lean_alloc_ctor(0, 1, 0);
} else {
 x_245 = x_244;
}
lean_ctor_set(x_245, 0, x_243);
return x_245;
}
else
{
lean_object* x_246; lean_object* x_247; uint8_t x_248; 
x_246 = lean_ctor_get(x_242, 0);
lean_inc(x_246);
if (lean_is_exclusive(x_242)) {
 lean_ctor_release(x_242, 0);
 x_247 = x_242;
} else {
 lean_dec_ref(x_242);
 x_247 = lean_box(0);
}
x_248 = lean_nat_dec_lt(x_55, x_89);
if (x_248 == 0)
{
lean_object* x_249; lean_object* x_250; 
lean_dec(x_247);
lean_dec(x_55);
x_249 = lean_array_fget(x_52, x_217);
x_250 = l_Lean_Json_getNat_x3f(x_249);
if (lean_obj_tag(x_250) == 0)
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; 
lean_dec(x_246);
lean_dec(x_239);
lean_dec(x_232);
lean_dec(x_225);
lean_dec(x_216);
lean_dec(x_88);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_251 = lean_ctor_get(x_250, 0);
lean_inc(x_251);
if (lean_is_exclusive(x_250)) {
 lean_ctor_release(x_250, 0);
 x_252 = x_250;
} else {
 lean_dec_ref(x_250);
 x_252 = lean_box(0);
}
if (lean_is_scalar(x_252)) {
 x_253 = lean_alloc_ctor(0, 1, 0);
} else {
 x_253 = x_252;
}
lean_ctor_set(x_253, 0, x_251);
return x_253;
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; 
x_254 = lean_ctor_get(x_250, 0);
lean_inc(x_254);
lean_dec(x_250);
x_255 = lean_unsigned_to_nat(10u);
x_256 = lean_array_fget(x_52, x_255);
x_257 = l_Lean_Json_getNat_x3f(x_256);
if (lean_obj_tag(x_257) == 0)
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; 
lean_dec(x_254);
lean_dec(x_246);
lean_dec(x_239);
lean_dec(x_232);
lean_dec(x_225);
lean_dec(x_216);
lean_dec(x_88);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_258 = lean_ctor_get(x_257, 0);
lean_inc(x_258);
if (lean_is_exclusive(x_257)) {
 lean_ctor_release(x_257, 0);
 x_259 = x_257;
} else {
 lean_dec_ref(x_257);
 x_259 = lean_box(0);
}
if (lean_is_scalar(x_259)) {
 x_260 = lean_alloc_ctor(0, 1, 0);
} else {
 x_260 = x_259;
}
lean_ctor_set(x_260, 0, x_258);
return x_260;
}
else
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_261 = lean_ctor_get(x_257, 0);
lean_inc(x_261);
lean_dec(x_257);
x_262 = lean_unsigned_to_nat(11u);
x_263 = lean_array_fget(x_52, x_262);
x_264 = l_Lean_Json_getNat_x3f(x_263);
if (lean_obj_tag(x_264) == 0)
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; 
lean_dec(x_261);
lean_dec(x_254);
lean_dec(x_246);
lean_dec(x_239);
lean_dec(x_232);
lean_dec(x_225);
lean_dec(x_216);
lean_dec(x_88);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_265 = lean_ctor_get(x_264, 0);
lean_inc(x_265);
if (lean_is_exclusive(x_264)) {
 lean_ctor_release(x_264, 0);
 x_266 = x_264;
} else {
 lean_dec_ref(x_264);
 x_266 = lean_box(0);
}
if (lean_is_scalar(x_266)) {
 x_267 = lean_alloc_ctor(0, 1, 0);
} else {
 x_267 = x_266;
}
lean_ctor_set(x_267, 0, x_265);
return x_267;
}
else
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; 
x_268 = lean_ctor_get(x_264, 0);
lean_inc(x_268);
lean_dec(x_264);
x_269 = lean_unsigned_to_nat(12u);
x_270 = lean_array_fget(x_52, x_269);
lean_dec(x_52);
x_271 = l_Lean_Json_getNat_x3f(x_270);
if (lean_obj_tag(x_271) == 0)
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; 
lean_dec(x_268);
lean_dec(x_261);
lean_dec(x_254);
lean_dec(x_246);
lean_dec(x_239);
lean_dec(x_232);
lean_dec(x_225);
lean_dec(x_216);
lean_dec(x_88);
lean_dec(x_53);
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_272 = lean_ctor_get(x_271, 0);
lean_inc(x_272);
if (lean_is_exclusive(x_271)) {
 lean_ctor_release(x_271, 0);
 x_273 = x_271;
} else {
 lean_dec_ref(x_271);
 x_273 = lean_box(0);
}
if (lean_is_scalar(x_273)) {
 x_274 = lean_alloc_ctor(0, 1, 0);
} else {
 x_274 = x_273;
}
lean_ctor_set(x_274, 0, x_272);
return x_274;
}
else
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; 
x_275 = lean_ctor_get(x_271, 0);
lean_inc(x_275);
lean_dec(x_271);
x_276 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_276, 0, x_225);
lean_ctor_set(x_276, 1, x_232);
x_277 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_277, 0, x_239);
lean_ctor_set(x_277, 1, x_246);
x_278 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_278, 0, x_276);
lean_ctor_set(x_278, 1, x_277);
x_279 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_279, 0, x_254);
lean_ctor_set(x_279, 1, x_261);
x_280 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_280, 0, x_268);
lean_ctor_set(x_280, 1, x_275);
x_281 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_281, 0, x_279);
lean_ctor_set(x_281, 1, x_280);
x_282 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_282, 0, x_216);
lean_ctor_set(x_282, 1, x_278);
lean_ctor_set(x_282, 2, x_281);
if (lean_is_scalar(x_53)) {
 x_283 = lean_alloc_ctor(1, 1, 0);
} else {
 x_283 = x_53;
}
lean_ctor_set(x_283, 0, x_282);
x_284 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_284, 0, x_88);
lean_ctor_set(x_284, 1, x_283);
x_41 = x_284;
goto block_43;
}
}
}
}
}
else
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; 
lean_dec(x_246);
lean_dec(x_239);
lean_dec(x_232);
lean_dec(x_225);
lean_dec(x_216);
lean_dec(x_88);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_285 = lean_mk_string_unchecked("Expected list of length 4, not ", 31, 31);
x_286 = l___private_Init_Data_Repr_0__Nat_reprFast(x_55);
x_287 = lean_string_append(x_285, x_286);
lean_dec(x_286);
if (lean_is_scalar(x_247)) {
 x_288 = lean_alloc_ctor(0, 1, 0);
} else {
 x_288 = x_247;
 lean_ctor_set_tag(x_288, 0);
}
lean_ctor_set(x_288, 0, x_287);
return x_288;
}
}
}
}
}
}
else
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; 
lean_dec(x_216);
lean_dec(x_88);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_289 = lean_mk_string_unchecked("Expected list of length 4, not ", 31, 31);
x_290 = l___private_Init_Data_Repr_0__Nat_reprFast(x_55);
x_291 = lean_string_append(x_289, x_290);
lean_dec(x_290);
x_292 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_292, 0, x_291);
return x_292;
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
lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; 
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_293 = lean_mk_string_unchecked("Expected list of length 4, not ", 31, 31);
x_294 = l___private_Init_Data_Repr_0__Nat_reprFast(x_55);
x_295 = lean_string_append(x_293, x_294);
lean_dec(x_294);
if (lean_is_scalar(x_50)) {
 x_296 = lean_alloc_ctor(0, 1, 0);
} else {
 x_296 = x_50;
 lean_ctor_set_tag(x_296, 0);
}
lean_ctor_set(x_296, 0, x_295);
return x_296;
}
}
}
}
block_40:
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_mk_string_unchecked("usages", 6, 6);
x_24 = l_Lean_Json_getObjValAs_x3f___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2193__spec__0_spec__0(x_6, x_23);
lean_dec(x_23);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_9);
lean_dec(x_7);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
return x_24;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
else
{
lean_object* x_28; size_t x_29; lean_object* x_30; size_t x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_24, 0);
lean_inc(x_28);
lean_dec(x_24);
x_29 = lean_array_size(x_28);
x_30 = lean_unsigned_to_nat(0u);
x_31 = lean_usize_of_nat(x_30);
x_32 = l_Array_mapMUnsafe_map___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2193__spec__0_spec__3(x_29, x_31, x_28);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_9);
lean_dec(x_7);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
return x_32;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_32, 0);
lean_inc(x_36);
lean_dec(x_32);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_22);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_Std_DTreeMap_Internal_Impl_insert___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2193__spec__0_spec__4___redArg(x_21, x_37, x_9);
x_39 = l_Lean_RBNode_foldM___at___Lean_RBNode_foldM___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2193__spec__0_spec__5_spec__5(x_38, x_7);
return x_39;
}
}
}
block_43:
{
lean_object* x_42; 
if (lean_is_scalar(x_10)) {
 x_42 = lean_alloc_ctor(1, 1, 0);
} else {
 x_42 = x_10;
}
lean_ctor_set(x_42, 0, x_41);
x_22 = x_42;
goto block_40;
}
}
else
{
lean_object* x_304; lean_object* x_305; lean_object* x_324; lean_object* x_327; lean_object* x_328; 
x_304 = lean_ctor_get(x_16, 0);
lean_inc(x_304);
lean_dec(x_16);
x_327 = lean_mk_string_unchecked("definition", 10, 10);
lean_inc(x_6);
x_328 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Basic_0__Lean_Lsp_fromJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1614__spec__0(x_6, x_327);
lean_dec(x_327);
if (lean_obj_tag(x_328) == 0)
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; 
lean_dec(x_304);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_329 = lean_ctor_get(x_328, 0);
lean_inc(x_329);
if (lean_is_exclusive(x_328)) {
 lean_ctor_release(x_328, 0);
 x_330 = x_328;
} else {
 lean_dec_ref(x_328);
 x_330 = lean_box(0);
}
if (lean_is_scalar(x_330)) {
 x_331 = lean_alloc_ctor(0, 1, 0);
} else {
 x_331 = x_330;
}
lean_ctor_set(x_331, 0, x_329);
return x_331;
}
else
{
lean_object* x_332; lean_object* x_333; 
x_332 = lean_ctor_get(x_328, 0);
lean_inc(x_332);
if (lean_is_exclusive(x_328)) {
 lean_ctor_release(x_328, 0);
 x_333 = x_328;
} else {
 lean_dec_ref(x_328);
 x_333 = lean_box(0);
}
if (lean_obj_tag(x_332) == 0)
{
lean_object* x_334; 
lean_dec(x_333);
lean_dec(x_10);
x_334 = lean_box(0);
x_305 = x_334;
goto block_323;
}
else
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_464; lean_object* x_465; uint8_t x_466; 
x_335 = lean_ctor_get(x_332, 0);
lean_inc(x_335);
if (lean_is_exclusive(x_332)) {
 lean_ctor_release(x_332, 0);
 x_336 = x_332;
} else {
 lean_dec_ref(x_332);
 x_336 = lean_box(0);
}
x_337 = lean_box(0);
x_464 = lean_array_get_size(x_335);
x_465 = lean_unsigned_to_nat(4u);
x_466 = lean_nat_dec_eq(x_464, x_465);
if (x_466 == 0)
{
lean_object* x_467; uint8_t x_468; 
x_467 = lean_unsigned_to_nat(13u);
x_468 = lean_nat_dec_eq(x_464, x_467);
lean_dec(x_464);
if (x_468 == 0)
{
lean_object* x_469; lean_object* x_470; 
lean_dec(x_336);
lean_dec(x_335);
lean_dec(x_333);
lean_dec(x_304);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_469 = lean_mk_string_unchecked("Expected list of length 4 or 13, not {l.size}", 45, 45);
x_470 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_470, 0, x_469);
return x_470;
}
else
{
goto block_463;
}
}
else
{
lean_dec(x_464);
goto block_463;
}
block_463:
{
lean_object* x_338; lean_object* x_339; uint8_t x_340; 
x_338 = lean_array_get_size(x_335);
x_339 = lean_unsigned_to_nat(4u);
x_340 = lean_nat_dec_lt(x_338, x_339);
if (x_340 == 0)
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; 
lean_dec(x_333);
x_341 = lean_unsigned_to_nat(0u);
x_342 = lean_array_fget(x_335, x_341);
x_343 = l_Lean_Json_getNat_x3f(x_342);
if (lean_obj_tag(x_343) == 0)
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; 
lean_dec(x_338);
lean_dec(x_336);
lean_dec(x_335);
lean_dec(x_304);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_344 = lean_ctor_get(x_343, 0);
lean_inc(x_344);
if (lean_is_exclusive(x_343)) {
 lean_ctor_release(x_343, 0);
 x_345 = x_343;
} else {
 lean_dec_ref(x_343);
 x_345 = lean_box(0);
}
if (lean_is_scalar(x_345)) {
 x_346 = lean_alloc_ctor(0, 1, 0);
} else {
 x_346 = x_345;
}
lean_ctor_set(x_346, 0, x_344);
return x_346;
}
else
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; 
x_347 = lean_ctor_get(x_343, 0);
lean_inc(x_347);
lean_dec(x_343);
x_348 = lean_unsigned_to_nat(1u);
x_349 = lean_array_fget(x_335, x_348);
x_350 = l_Lean_Json_getNat_x3f(x_349);
if (lean_obj_tag(x_350) == 0)
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; 
lean_dec(x_347);
lean_dec(x_338);
lean_dec(x_336);
lean_dec(x_335);
lean_dec(x_304);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_351 = lean_ctor_get(x_350, 0);
lean_inc(x_351);
if (lean_is_exclusive(x_350)) {
 lean_ctor_release(x_350, 0);
 x_352 = x_350;
} else {
 lean_dec_ref(x_350);
 x_352 = lean_box(0);
}
if (lean_is_scalar(x_352)) {
 x_353 = lean_alloc_ctor(0, 1, 0);
} else {
 x_353 = x_352;
}
lean_ctor_set(x_353, 0, x_351);
return x_353;
}
else
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; 
x_354 = lean_ctor_get(x_350, 0);
lean_inc(x_354);
lean_dec(x_350);
x_355 = lean_unsigned_to_nat(2u);
x_356 = lean_array_fget(x_335, x_355);
x_357 = l_Lean_Json_getNat_x3f(x_356);
if (lean_obj_tag(x_357) == 0)
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; 
lean_dec(x_354);
lean_dec(x_347);
lean_dec(x_338);
lean_dec(x_336);
lean_dec(x_335);
lean_dec(x_304);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_358 = lean_ctor_get(x_357, 0);
lean_inc(x_358);
if (lean_is_exclusive(x_357)) {
 lean_ctor_release(x_357, 0);
 x_359 = x_357;
} else {
 lean_dec_ref(x_357);
 x_359 = lean_box(0);
}
if (lean_is_scalar(x_359)) {
 x_360 = lean_alloc_ctor(0, 1, 0);
} else {
 x_360 = x_359;
}
lean_ctor_set(x_360, 0, x_358);
return x_360;
}
else
{
lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; 
x_361 = lean_ctor_get(x_357, 0);
lean_inc(x_361);
lean_dec(x_357);
x_362 = lean_unsigned_to_nat(3u);
x_363 = lean_array_fget(x_335, x_362);
x_364 = l_Lean_Json_getNat_x3f(x_363);
if (lean_obj_tag(x_364) == 0)
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; 
lean_dec(x_361);
lean_dec(x_354);
lean_dec(x_347);
lean_dec(x_338);
lean_dec(x_336);
lean_dec(x_335);
lean_dec(x_304);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_365 = lean_ctor_get(x_364, 0);
lean_inc(x_365);
if (lean_is_exclusive(x_364)) {
 lean_ctor_release(x_364, 0);
 x_366 = x_364;
} else {
 lean_dec_ref(x_364);
 x_366 = lean_box(0);
}
if (lean_is_scalar(x_366)) {
 x_367 = lean_alloc_ctor(0, 1, 0);
} else {
 x_367 = x_366;
}
lean_ctor_set(x_367, 0, x_365);
return x_367;
}
else
{
lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; uint8_t x_373; 
x_368 = lean_ctor_get(x_364, 0);
lean_inc(x_368);
lean_dec(x_364);
x_369 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_369, 0, x_347);
lean_ctor_set(x_369, 1, x_354);
x_370 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_370, 0, x_361);
lean_ctor_set(x_370, 1, x_368);
x_371 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_371, 0, x_369);
lean_ctor_set(x_371, 1, x_370);
x_372 = lean_unsigned_to_nat(13u);
x_373 = lean_nat_dec_eq(x_338, x_372);
if (x_373 == 0)
{
lean_object* x_374; lean_object* x_375; 
lean_dec(x_338);
lean_dec(x_336);
lean_dec(x_335);
x_374 = lean_box(0);
x_375 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_375, 0, x_371);
lean_ctor_set(x_375, 1, x_374);
x_324 = x_375;
goto block_326;
}
else
{
lean_object* x_376; lean_object* x_377; 
x_376 = lean_array_get(x_337, x_335, x_339);
x_377 = l_Lean_Json_getStr_x3f(x_376);
if (lean_obj_tag(x_377) == 0)
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; 
lean_dec(x_371);
lean_dec(x_338);
lean_dec(x_336);
lean_dec(x_335);
lean_dec(x_304);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_378 = lean_ctor_get(x_377, 0);
lean_inc(x_378);
if (lean_is_exclusive(x_377)) {
 lean_ctor_release(x_377, 0);
 x_379 = x_377;
} else {
 lean_dec_ref(x_377);
 x_379 = lean_box(0);
}
if (lean_is_scalar(x_379)) {
 x_380 = lean_alloc_ctor(0, 1, 0);
} else {
 x_380 = x_379;
}
lean_ctor_set(x_380, 0, x_378);
return x_380;
}
else
{
lean_object* x_381; lean_object* x_382; lean_object* x_383; uint8_t x_384; 
x_381 = lean_ctor_get(x_377, 0);
lean_inc(x_381);
if (lean_is_exclusive(x_377)) {
 lean_ctor_release(x_377, 0);
 x_382 = x_377;
} else {
 lean_dec_ref(x_377);
 x_382 = lean_box(0);
}
x_383 = lean_unsigned_to_nat(9u);
x_384 = lean_nat_dec_lt(x_338, x_383);
if (x_384 == 0)
{
lean_object* x_385; lean_object* x_386; lean_object* x_387; 
lean_dec(x_382);
x_385 = lean_unsigned_to_nat(5u);
x_386 = lean_array_fget(x_335, x_385);
x_387 = l_Lean_Json_getNat_x3f(x_386);
if (lean_obj_tag(x_387) == 0)
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; 
lean_dec(x_381);
lean_dec(x_371);
lean_dec(x_338);
lean_dec(x_336);
lean_dec(x_335);
lean_dec(x_304);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_388 = lean_ctor_get(x_387, 0);
lean_inc(x_388);
if (lean_is_exclusive(x_387)) {
 lean_ctor_release(x_387, 0);
 x_389 = x_387;
} else {
 lean_dec_ref(x_387);
 x_389 = lean_box(0);
}
if (lean_is_scalar(x_389)) {
 x_390 = lean_alloc_ctor(0, 1, 0);
} else {
 x_390 = x_389;
}
lean_ctor_set(x_390, 0, x_388);
return x_390;
}
else
{
lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; 
x_391 = lean_ctor_get(x_387, 0);
lean_inc(x_391);
lean_dec(x_387);
x_392 = lean_unsigned_to_nat(6u);
x_393 = lean_array_fget(x_335, x_392);
x_394 = l_Lean_Json_getNat_x3f(x_393);
if (lean_obj_tag(x_394) == 0)
{
lean_object* x_395; lean_object* x_396; lean_object* x_397; 
lean_dec(x_391);
lean_dec(x_381);
lean_dec(x_371);
lean_dec(x_338);
lean_dec(x_336);
lean_dec(x_335);
lean_dec(x_304);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_395 = lean_ctor_get(x_394, 0);
lean_inc(x_395);
if (lean_is_exclusive(x_394)) {
 lean_ctor_release(x_394, 0);
 x_396 = x_394;
} else {
 lean_dec_ref(x_394);
 x_396 = lean_box(0);
}
if (lean_is_scalar(x_396)) {
 x_397 = lean_alloc_ctor(0, 1, 0);
} else {
 x_397 = x_396;
}
lean_ctor_set(x_397, 0, x_395);
return x_397;
}
else
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; 
x_398 = lean_ctor_get(x_394, 0);
lean_inc(x_398);
lean_dec(x_394);
x_399 = lean_unsigned_to_nat(7u);
x_400 = lean_array_fget(x_335, x_399);
x_401 = l_Lean_Json_getNat_x3f(x_400);
if (lean_obj_tag(x_401) == 0)
{
lean_object* x_402; lean_object* x_403; lean_object* x_404; 
lean_dec(x_398);
lean_dec(x_391);
lean_dec(x_381);
lean_dec(x_371);
lean_dec(x_338);
lean_dec(x_336);
lean_dec(x_335);
lean_dec(x_304);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_402 = lean_ctor_get(x_401, 0);
lean_inc(x_402);
if (lean_is_exclusive(x_401)) {
 lean_ctor_release(x_401, 0);
 x_403 = x_401;
} else {
 lean_dec_ref(x_401);
 x_403 = lean_box(0);
}
if (lean_is_scalar(x_403)) {
 x_404 = lean_alloc_ctor(0, 1, 0);
} else {
 x_404 = x_403;
}
lean_ctor_set(x_404, 0, x_402);
return x_404;
}
else
{
lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; 
x_405 = lean_ctor_get(x_401, 0);
lean_inc(x_405);
lean_dec(x_401);
x_406 = lean_unsigned_to_nat(8u);
x_407 = lean_array_fget(x_335, x_406);
x_408 = l_Lean_Json_getNat_x3f(x_407);
if (lean_obj_tag(x_408) == 0)
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; 
lean_dec(x_405);
lean_dec(x_398);
lean_dec(x_391);
lean_dec(x_381);
lean_dec(x_371);
lean_dec(x_338);
lean_dec(x_336);
lean_dec(x_335);
lean_dec(x_304);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_409 = lean_ctor_get(x_408, 0);
lean_inc(x_409);
if (lean_is_exclusive(x_408)) {
 lean_ctor_release(x_408, 0);
 x_410 = x_408;
} else {
 lean_dec_ref(x_408);
 x_410 = lean_box(0);
}
if (lean_is_scalar(x_410)) {
 x_411 = lean_alloc_ctor(0, 1, 0);
} else {
 x_411 = x_410;
}
lean_ctor_set(x_411, 0, x_409);
return x_411;
}
else
{
lean_object* x_412; lean_object* x_413; uint8_t x_414; 
x_412 = lean_ctor_get(x_408, 0);
lean_inc(x_412);
if (lean_is_exclusive(x_408)) {
 lean_ctor_release(x_408, 0);
 x_413 = x_408;
} else {
 lean_dec_ref(x_408);
 x_413 = lean_box(0);
}
x_414 = lean_nat_dec_lt(x_338, x_372);
if (x_414 == 0)
{
lean_object* x_415; lean_object* x_416; 
lean_dec(x_413);
lean_dec(x_338);
x_415 = lean_array_fget(x_335, x_383);
x_416 = l_Lean_Json_getNat_x3f(x_415);
if (lean_obj_tag(x_416) == 0)
{
lean_object* x_417; lean_object* x_418; lean_object* x_419; 
lean_dec(x_412);
lean_dec(x_405);
lean_dec(x_398);
lean_dec(x_391);
lean_dec(x_381);
lean_dec(x_371);
lean_dec(x_336);
lean_dec(x_335);
lean_dec(x_304);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_417 = lean_ctor_get(x_416, 0);
lean_inc(x_417);
if (lean_is_exclusive(x_416)) {
 lean_ctor_release(x_416, 0);
 x_418 = x_416;
} else {
 lean_dec_ref(x_416);
 x_418 = lean_box(0);
}
if (lean_is_scalar(x_418)) {
 x_419 = lean_alloc_ctor(0, 1, 0);
} else {
 x_419 = x_418;
}
lean_ctor_set(x_419, 0, x_417);
return x_419;
}
else
{
lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; 
x_420 = lean_ctor_get(x_416, 0);
lean_inc(x_420);
lean_dec(x_416);
x_421 = lean_unsigned_to_nat(10u);
x_422 = lean_array_fget(x_335, x_421);
x_423 = l_Lean_Json_getNat_x3f(x_422);
if (lean_obj_tag(x_423) == 0)
{
lean_object* x_424; lean_object* x_425; lean_object* x_426; 
lean_dec(x_420);
lean_dec(x_412);
lean_dec(x_405);
lean_dec(x_398);
lean_dec(x_391);
lean_dec(x_381);
lean_dec(x_371);
lean_dec(x_336);
lean_dec(x_335);
lean_dec(x_304);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_424 = lean_ctor_get(x_423, 0);
lean_inc(x_424);
if (lean_is_exclusive(x_423)) {
 lean_ctor_release(x_423, 0);
 x_425 = x_423;
} else {
 lean_dec_ref(x_423);
 x_425 = lean_box(0);
}
if (lean_is_scalar(x_425)) {
 x_426 = lean_alloc_ctor(0, 1, 0);
} else {
 x_426 = x_425;
}
lean_ctor_set(x_426, 0, x_424);
return x_426;
}
else
{
lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; 
x_427 = lean_ctor_get(x_423, 0);
lean_inc(x_427);
lean_dec(x_423);
x_428 = lean_unsigned_to_nat(11u);
x_429 = lean_array_fget(x_335, x_428);
x_430 = l_Lean_Json_getNat_x3f(x_429);
if (lean_obj_tag(x_430) == 0)
{
lean_object* x_431; lean_object* x_432; lean_object* x_433; 
lean_dec(x_427);
lean_dec(x_420);
lean_dec(x_412);
lean_dec(x_405);
lean_dec(x_398);
lean_dec(x_391);
lean_dec(x_381);
lean_dec(x_371);
lean_dec(x_336);
lean_dec(x_335);
lean_dec(x_304);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_431 = lean_ctor_get(x_430, 0);
lean_inc(x_431);
if (lean_is_exclusive(x_430)) {
 lean_ctor_release(x_430, 0);
 x_432 = x_430;
} else {
 lean_dec_ref(x_430);
 x_432 = lean_box(0);
}
if (lean_is_scalar(x_432)) {
 x_433 = lean_alloc_ctor(0, 1, 0);
} else {
 x_433 = x_432;
}
lean_ctor_set(x_433, 0, x_431);
return x_433;
}
else
{
lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; 
x_434 = lean_ctor_get(x_430, 0);
lean_inc(x_434);
lean_dec(x_430);
x_435 = lean_unsigned_to_nat(12u);
x_436 = lean_array_fget(x_335, x_435);
lean_dec(x_335);
x_437 = l_Lean_Json_getNat_x3f(x_436);
if (lean_obj_tag(x_437) == 0)
{
lean_object* x_438; lean_object* x_439; lean_object* x_440; 
lean_dec(x_434);
lean_dec(x_427);
lean_dec(x_420);
lean_dec(x_412);
lean_dec(x_405);
lean_dec(x_398);
lean_dec(x_391);
lean_dec(x_381);
lean_dec(x_371);
lean_dec(x_336);
lean_dec(x_304);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_438 = lean_ctor_get(x_437, 0);
lean_inc(x_438);
if (lean_is_exclusive(x_437)) {
 lean_ctor_release(x_437, 0);
 x_439 = x_437;
} else {
 lean_dec_ref(x_437);
 x_439 = lean_box(0);
}
if (lean_is_scalar(x_439)) {
 x_440 = lean_alloc_ctor(0, 1, 0);
} else {
 x_440 = x_439;
}
lean_ctor_set(x_440, 0, x_438);
return x_440;
}
else
{
lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; 
x_441 = lean_ctor_get(x_437, 0);
lean_inc(x_441);
lean_dec(x_437);
x_442 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_442, 0, x_391);
lean_ctor_set(x_442, 1, x_398);
x_443 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_443, 0, x_405);
lean_ctor_set(x_443, 1, x_412);
x_444 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_444, 0, x_442);
lean_ctor_set(x_444, 1, x_443);
x_445 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_445, 0, x_420);
lean_ctor_set(x_445, 1, x_427);
x_446 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_446, 0, x_434);
lean_ctor_set(x_446, 1, x_441);
x_447 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_447, 0, x_445);
lean_ctor_set(x_447, 1, x_446);
x_448 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_448, 0, x_381);
lean_ctor_set(x_448, 1, x_444);
lean_ctor_set(x_448, 2, x_447);
if (lean_is_scalar(x_336)) {
 x_449 = lean_alloc_ctor(1, 1, 0);
} else {
 x_449 = x_336;
}
lean_ctor_set(x_449, 0, x_448);
x_450 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_450, 0, x_371);
lean_ctor_set(x_450, 1, x_449);
x_324 = x_450;
goto block_326;
}
}
}
}
}
else
{
lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; 
lean_dec(x_412);
lean_dec(x_405);
lean_dec(x_398);
lean_dec(x_391);
lean_dec(x_381);
lean_dec(x_371);
lean_dec(x_336);
lean_dec(x_335);
lean_dec(x_304);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_451 = lean_mk_string_unchecked("Expected list of length 4, not ", 31, 31);
x_452 = l___private_Init_Data_Repr_0__Nat_reprFast(x_338);
x_453 = lean_string_append(x_451, x_452);
lean_dec(x_452);
if (lean_is_scalar(x_413)) {
 x_454 = lean_alloc_ctor(0, 1, 0);
} else {
 x_454 = x_413;
 lean_ctor_set_tag(x_454, 0);
}
lean_ctor_set(x_454, 0, x_453);
return x_454;
}
}
}
}
}
}
else
{
lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; 
lean_dec(x_381);
lean_dec(x_371);
lean_dec(x_336);
lean_dec(x_335);
lean_dec(x_304);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_455 = lean_mk_string_unchecked("Expected list of length 4, not ", 31, 31);
x_456 = l___private_Init_Data_Repr_0__Nat_reprFast(x_338);
x_457 = lean_string_append(x_455, x_456);
lean_dec(x_456);
if (lean_is_scalar(x_382)) {
 x_458 = lean_alloc_ctor(0, 1, 0);
} else {
 x_458 = x_382;
 lean_ctor_set_tag(x_458, 0);
}
lean_ctor_set(x_458, 0, x_457);
return x_458;
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
lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; 
lean_dec(x_336);
lean_dec(x_335);
lean_dec(x_304);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_459 = lean_mk_string_unchecked("Expected list of length 4, not ", 31, 31);
x_460 = l___private_Init_Data_Repr_0__Nat_reprFast(x_338);
x_461 = lean_string_append(x_459, x_460);
lean_dec(x_460);
if (lean_is_scalar(x_333)) {
 x_462 = lean_alloc_ctor(0, 1, 0);
} else {
 x_462 = x_333;
 lean_ctor_set_tag(x_462, 0);
}
lean_ctor_set(x_462, 0, x_461);
return x_462;
}
}
}
}
block_323:
{
lean_object* x_306; lean_object* x_307; 
x_306 = lean_mk_string_unchecked("usages", 6, 6);
x_307 = l_Lean_Json_getObjValAs_x3f___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2193__spec__0_spec__0(x_6, x_306);
lean_dec(x_306);
if (lean_obj_tag(x_307) == 0)
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; 
lean_dec(x_305);
lean_dec(x_304);
lean_dec(x_9);
lean_dec(x_7);
x_308 = lean_ctor_get(x_307, 0);
lean_inc(x_308);
if (lean_is_exclusive(x_307)) {
 lean_ctor_release(x_307, 0);
 x_309 = x_307;
} else {
 lean_dec_ref(x_307);
 x_309 = lean_box(0);
}
if (lean_is_scalar(x_309)) {
 x_310 = lean_alloc_ctor(0, 1, 0);
} else {
 x_310 = x_309;
}
lean_ctor_set(x_310, 0, x_308);
return x_310;
}
else
{
lean_object* x_311; size_t x_312; lean_object* x_313; size_t x_314; lean_object* x_315; 
x_311 = lean_ctor_get(x_307, 0);
lean_inc(x_311);
lean_dec(x_307);
x_312 = lean_array_size(x_311);
x_313 = lean_unsigned_to_nat(0u);
x_314 = lean_usize_of_nat(x_313);
x_315 = l_Array_mapMUnsafe_map___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2193__spec__0_spec__3(x_312, x_314, x_311);
if (lean_obj_tag(x_315) == 0)
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; 
lean_dec(x_305);
lean_dec(x_304);
lean_dec(x_9);
lean_dec(x_7);
x_316 = lean_ctor_get(x_315, 0);
lean_inc(x_316);
if (lean_is_exclusive(x_315)) {
 lean_ctor_release(x_315, 0);
 x_317 = x_315;
} else {
 lean_dec_ref(x_315);
 x_317 = lean_box(0);
}
if (lean_is_scalar(x_317)) {
 x_318 = lean_alloc_ctor(0, 1, 0);
} else {
 x_318 = x_317;
}
lean_ctor_set(x_318, 0, x_316);
return x_318;
}
else
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; 
x_319 = lean_ctor_get(x_315, 0);
lean_inc(x_319);
lean_dec(x_315);
x_320 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_320, 0, x_305);
lean_ctor_set(x_320, 1, x_319);
x_321 = l_Std_DTreeMap_Internal_Impl_insert___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2193__spec__0_spec__4___redArg(x_304, x_320, x_9);
x_322 = l_Lean_RBNode_foldM___at___Lean_RBNode_foldM___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2193__spec__0_spec__5_spec__5(x_321, x_7);
return x_322;
}
}
}
block_326:
{
lean_object* x_325; 
if (lean_is_scalar(x_10)) {
 x_325 = lean_alloc_ctor(1, 1, 0);
} else {
 x_325 = x_10;
}
lean_ctor_set(x_325, 0, x_324);
x_305 = x_325;
goto block_323;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2193__spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
x_4 = l_Lean_Json_getObj_x3f(x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
lean_dec(x_4);
x_9 = lean_box(1);
x_10 = l_Lean_RBNode_foldM___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2193__spec__0_spec__5(x_9, x_8);
return x_10;
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams___lam__0____x40_Lean_Data_Lsp_Internal___hyg_2193_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2193_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_mk_string_unchecked("version", 7, 7);
lean_inc(x_1);
x_3 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Basic_0__Lean_Lsp_fromJsonPosition____x40_Lean_Data_Lsp_Basic___hyg_273__spec__0(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
lean_dec(x_1);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams___lam__0____x40_Lean_Data_Lsp_Internal___hyg_2193____boxed), 1, 0);
x_7 = lean_mk_string_unchecked("Lean", 4, 4);
x_8 = lean_mk_string_unchecked("Lsp", 3, 3);
x_9 = lean_mk_string_unchecked("LeanIleanInfoParams", 19, 19);
x_10 = l_Lean_Name_mkStr3(x_7, x_8, x_9);
x_11 = lean_box(1);
x_12 = lean_unbox(x_11);
lean_inc(x_6);
x_13 = l_Lean_Name_toString(x_10, x_12, x_6);
x_14 = lean_mk_string_unchecked(".", 1, 1);
x_15 = lean_string_append(x_13, x_14);
lean_dec(x_14);
x_16 = l_Lean_Name_mkStr1(x_2);
x_17 = lean_unbox(x_11);
x_18 = l_Lean_Name_toString(x_16, x_17, x_6);
x_19 = lean_string_append(x_15, x_18);
lean_dec(x_18);
x_20 = lean_mk_string_unchecked(": ", 2, 2);
x_21 = lean_string_append(x_19, x_20);
lean_dec(x_20);
x_22 = lean_string_append(x_21, x_5);
lean_dec(x_5);
lean_ctor_set(x_3, 0, x_22);
return x_3;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_23 = lean_ctor_get(x_3, 0);
lean_inc(x_23);
lean_dec(x_3);
x_24 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams___lam__0____x40_Lean_Data_Lsp_Internal___hyg_2193____boxed), 1, 0);
x_25 = lean_mk_string_unchecked("Lean", 4, 4);
x_26 = lean_mk_string_unchecked("Lsp", 3, 3);
x_27 = lean_mk_string_unchecked("LeanIleanInfoParams", 19, 19);
x_28 = l_Lean_Name_mkStr3(x_25, x_26, x_27);
x_29 = lean_box(1);
x_30 = lean_unbox(x_29);
lean_inc(x_24);
x_31 = l_Lean_Name_toString(x_28, x_30, x_24);
x_32 = lean_mk_string_unchecked(".", 1, 1);
x_33 = lean_string_append(x_31, x_32);
lean_dec(x_32);
x_34 = l_Lean_Name_mkStr1(x_2);
x_35 = lean_unbox(x_29);
x_36 = l_Lean_Name_toString(x_34, x_35, x_24);
x_37 = lean_string_append(x_33, x_36);
lean_dec(x_36);
x_38 = lean_mk_string_unchecked(": ", 2, 2);
x_39 = lean_string_append(x_37, x_38);
lean_dec(x_38);
x_40 = lean_string_append(x_39, x_23);
lean_dec(x_23);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_40);
return x_41;
}
}
else
{
lean_dec(x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_42; 
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_3);
if (x_42 == 0)
{
lean_ctor_set_tag(x_3, 0);
return x_3;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_3, 0);
lean_inc(x_43);
lean_dec(x_3);
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_43);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_3, 0);
lean_inc(x_45);
lean_dec(x_3);
x_46 = lean_mk_string_unchecked("references", 10, 10);
x_47 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2193__spec__0(x_1, x_46);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; 
lean_dec(x_45);
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_49 = lean_ctor_get(x_47, 0);
x_50 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams___lam__0____x40_Lean_Data_Lsp_Internal___hyg_2193____boxed), 1, 0);
x_51 = lean_mk_string_unchecked("Lean", 4, 4);
x_52 = lean_mk_string_unchecked("Lsp", 3, 3);
x_53 = lean_mk_string_unchecked("LeanIleanInfoParams", 19, 19);
x_54 = l_Lean_Name_mkStr3(x_51, x_52, x_53);
x_55 = lean_box(1);
x_56 = lean_unbox(x_55);
lean_inc(x_50);
x_57 = l_Lean_Name_toString(x_54, x_56, x_50);
x_58 = lean_mk_string_unchecked(".", 1, 1);
x_59 = lean_string_append(x_57, x_58);
lean_dec(x_58);
x_60 = l_Lean_Name_mkStr1(x_46);
x_61 = lean_unbox(x_55);
x_62 = l_Lean_Name_toString(x_60, x_61, x_50);
x_63 = lean_string_append(x_59, x_62);
lean_dec(x_62);
x_64 = lean_mk_string_unchecked(": ", 2, 2);
x_65 = lean_string_append(x_63, x_64);
lean_dec(x_64);
x_66 = lean_string_append(x_65, x_49);
lean_dec(x_49);
lean_ctor_set(x_47, 0, x_66);
return x_47;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_67 = lean_ctor_get(x_47, 0);
lean_inc(x_67);
lean_dec(x_47);
x_68 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams___lam__0____x40_Lean_Data_Lsp_Internal___hyg_2193____boxed), 1, 0);
x_69 = lean_mk_string_unchecked("Lean", 4, 4);
x_70 = lean_mk_string_unchecked("Lsp", 3, 3);
x_71 = lean_mk_string_unchecked("LeanIleanInfoParams", 19, 19);
x_72 = l_Lean_Name_mkStr3(x_69, x_70, x_71);
x_73 = lean_box(1);
x_74 = lean_unbox(x_73);
lean_inc(x_68);
x_75 = l_Lean_Name_toString(x_72, x_74, x_68);
x_76 = lean_mk_string_unchecked(".", 1, 1);
x_77 = lean_string_append(x_75, x_76);
lean_dec(x_76);
x_78 = l_Lean_Name_mkStr1(x_46);
x_79 = lean_unbox(x_73);
x_80 = l_Lean_Name_toString(x_78, x_79, x_68);
x_81 = lean_string_append(x_77, x_80);
lean_dec(x_80);
x_82 = lean_mk_string_unchecked(": ", 2, 2);
x_83 = lean_string_append(x_81, x_82);
lean_dec(x_82);
x_84 = lean_string_append(x_83, x_67);
lean_dec(x_67);
x_85 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_85, 0, x_84);
return x_85;
}
}
else
{
lean_dec(x_46);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_86; 
lean_dec(x_45);
x_86 = !lean_is_exclusive(x_47);
if (x_86 == 0)
{
lean_ctor_set_tag(x_47, 0);
return x_47;
}
else
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_47, 0);
lean_inc(x_87);
lean_dec(x_47);
x_88 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_88, 0, x_87);
return x_88;
}
}
else
{
uint8_t x_89; 
x_89 = !lean_is_exclusive(x_47);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_47, 0);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_45);
lean_ctor_set(x_91, 1, x_90);
lean_ctor_set(x_47, 0, x_91);
return x_47;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_47, 0);
lean_inc(x_92);
lean_dec(x_47);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_45);
lean_ctor_set(x_93, 1, x_92);
x_94 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_94, 0, x_93);
return x_94;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Json_getObjValAs_x3f___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2193__spec__0_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Json_getObjValAs_x3f___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2193__spec__0_spec__0_spec__0_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Json_getObjValAs_x3f___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2193__spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Lean_Json_getObjValAs_x3f___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2193__spec__0_spec__0_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2193__spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2193__spec__0_spec__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2193__spec__0_spec__3___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_mapMUnsafe_map___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2193__spec__0_spec__3___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2193__spec__0_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2193__spec__0_spec__3(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2193__spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2193__spec__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams___lam__0____x40_Lean_Data_Lsp_Internal___hyg_2193____boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams___lam__0____x40_Lean_Data_Lsp_Internal___hyg_2193_(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2193_), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2299__spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___redArg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Lean_JsonNumber_fromNat(x_5);
x_8 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_8);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_1);
x_12 = l_Lean_JsonNumber_fromNat(x_10);
x_13 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_2);
x_1 = x_11;
x_2 = x_14;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2299__spec__1___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_5, 0);
x_7 = lean_ctor_get(x_5, 1);
x_8 = lean_box(0);
lean_inc(x_7);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
lean_inc(x_6);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_9);
lean_inc(x_4);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_10);
lean_inc(x_3);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2299__spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_box(0);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_15 = lean_ctor_get(x_5, 0);
lean_inc(x_15);
x_16 = l_Array_mapMUnsafe_map___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2299__spec__1___lam__0(x_15);
lean_dec(x_15);
x_17 = lean_box(0);
x_18 = l_List_mapTR_loop___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2299__spec__0(x_16, x_17);
x_19 = lean_ctor_get(x_5, 1);
lean_inc(x_19);
lean_dec(x_5);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = l_List_appendTR(lean_box(0), x_18, x_17);
x_8 = x_20;
goto block_14;
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_22 = lean_ctor_get(x_19, 0);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_ctor_set_tag(x_19, 3);
lean_ctor_set(x_19, 0, x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
x_25 = l_Array_mapMUnsafe_map___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2299__spec__1___lam__0(x_24);
lean_dec(x_24);
x_26 = l_List_mapTR_loop___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2299__spec__0(x_25, x_17);
x_27 = lean_ctor_get(x_22, 2);
lean_inc(x_27);
lean_dec(x_22);
x_28 = l_Array_mapMUnsafe_map___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2299__spec__1___lam__0(x_27);
lean_dec(x_27);
x_29 = l_List_mapTR_loop___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2299__spec__0(x_28, x_17);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_19);
lean_ctor_set(x_30, 1, x_17);
x_31 = l_List_appendTR(lean_box(0), x_30, x_26);
x_32 = l_List_appendTR(lean_box(0), x_31, x_29);
x_33 = l_List_appendTR(lean_box(0), x_18, x_32);
x_8 = x_33;
goto block_14;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_34 = lean_ctor_get(x_19, 0);
lean_inc(x_34);
lean_dec(x_19);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_36, 0, x_35);
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
x_38 = l_Array_mapMUnsafe_map___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2299__spec__1___lam__0(x_37);
lean_dec(x_37);
x_39 = l_List_mapTR_loop___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2299__spec__0(x_38, x_17);
x_40 = lean_ctor_get(x_34, 2);
lean_inc(x_40);
lean_dec(x_34);
x_41 = l_Array_mapMUnsafe_map___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2299__spec__1___lam__0(x_40);
lean_dec(x_40);
x_42 = l_List_mapTR_loop___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2299__spec__0(x_41, x_17);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_36);
lean_ctor_set(x_43, 1, x_17);
x_44 = l_List_appendTR(lean_box(0), x_43, x_39);
x_45 = l_List_appendTR(lean_box(0), x_44, x_42);
x_46 = l_List_appendTR(lean_box(0), x_18, x_45);
x_8 = x_46;
goto block_14;
}
}
block_14:
{
lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_usize_of_nat(x_9);
x_11 = lean_usize_add(x_2, x_10);
x_12 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_11;
x_3 = x_12;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2299__spec__2_spec__2(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; lean_object* x_10; size_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_box(0);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = lean_array_mk(x_5);
x_9 = lean_array_size(x_8);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_usize_of_nat(x_10);
x_12 = l_Array_mapMUnsafe_map___at___Lean_Json_opt___at_____private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1558__spec__0_spec__0(x_9, x_11, x_8);
x_13 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_usize_of_nat(x_14);
x_16 = lean_usize_add(x_2, x_15);
x_17 = lean_array_uset(x_7, x_2, x_13);
x_2 = x_16;
x_3 = x_17;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2299__spec__2(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; lean_object* x_10; size_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_box(0);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = lean_array_mk(x_5);
x_9 = lean_array_size(x_8);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_usize_of_nat(x_10);
x_12 = l_Array_mapMUnsafe_map___at___Lean_Json_opt___at_____private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1558__spec__0_spec__0(x_9, x_11, x_8);
x_13 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_usize_of_nat(x_14);
x_16 = lean_usize_add(x_2, x_15);
x_17 = lean_array_uset(x_7, x_2, x_13);
x_18 = l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2299__spec__2_spec__2(x_1, x_16, x_17);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2299__spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_ctor_get(x_2, 3);
x_6 = lean_ctor_get(x_2, 4);
x_7 = l_Std_DTreeMap_Internal_Impl_foldrM___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2299__spec__4(x_1, x_6);
lean_inc(x_4);
lean_inc(x_3);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_4);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
x_1 = x_9;
x_2 = x_5;
goto _start;
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___List_mapTR_loop___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2299__spec__5_spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___redArg(x_2);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_33; lean_object* x_41; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_6 = x_1;
} else {
 lean_dec_ref(x_1);
 x_6 = lean_box(0);
}
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_9 = x_4;
} else {
 lean_dec_ref(x_4);
 x_9 = lean_box(0);
}
x_10 = l_Lean_Lsp_RefIdent_toJson(x_7);
x_11 = l_Lean_Json_compress(x_10);
x_12 = lean_mk_string_unchecked("definition", 10, 10);
x_41 = lean_ctor_get(x_8, 0);
lean_inc(x_41);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; 
x_42 = lean_box(0);
x_13 = x_42;
goto block_32;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_43 = lean_ctor_get(x_41, 0);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_ctor_get(x_44, 1);
lean_inc(x_48);
lean_dec(x_44);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_box(0);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_49);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_47);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_46);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_box(0);
x_57 = l_List_mapTR_loop___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2299__spec__0(x_55, x_56);
x_58 = lean_ctor_get(x_43, 1);
lean_inc(x_58);
lean_dec(x_43);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; 
x_59 = l_List_appendTR(lean_box(0), x_57, x_56);
x_33 = x_59;
goto block_40;
}
else
{
uint8_t x_60; 
x_60 = !lean_is_exclusive(x_58);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_61 = lean_ctor_get(x_58, 0);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
lean_ctor_set_tag(x_58, 3);
lean_ctor_set(x_58, 0, x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = lean_ctor_get(x_63, 1);
lean_inc(x_67);
lean_dec(x_63);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_51);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_68);
lean_ctor_set(x_71, 1, x_70);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_66);
lean_ctor_set(x_72, 1, x_71);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_65);
lean_ctor_set(x_73, 1, x_72);
x_74 = l_List_mapTR_loop___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2299__spec__0(x_73, x_56);
x_75 = lean_ctor_get(x_61, 2);
lean_inc(x_75);
lean_dec(x_61);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = lean_ctor_get(x_75, 1);
lean_inc(x_79);
lean_dec(x_75);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_51);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_80);
lean_ctor_set(x_83, 1, x_82);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_78);
lean_ctor_set(x_84, 1, x_83);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_77);
lean_ctor_set(x_85, 1, x_84);
x_86 = l_List_mapTR_loop___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2299__spec__0(x_85, x_56);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_58);
lean_ctor_set(x_87, 1, x_56);
x_88 = l_List_appendTR(lean_box(0), x_87, x_74);
x_89 = l_List_appendTR(lean_box(0), x_88, x_86);
x_90 = l_List_appendTR(lean_box(0), x_57, x_89);
x_33 = x_90;
goto block_40;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_91 = lean_ctor_get(x_58, 0);
lean_inc(x_91);
lean_dec(x_58);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_93, 0, x_92);
x_94 = lean_ctor_get(x_91, 1);
lean_inc(x_94);
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
x_98 = lean_ctor_get(x_94, 1);
lean_inc(x_98);
lean_dec(x_94);
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec(x_98);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_51);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_99);
lean_ctor_set(x_102, 1, x_101);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_97);
lean_ctor_set(x_103, 1, x_102);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_96);
lean_ctor_set(x_104, 1, x_103);
x_105 = l_List_mapTR_loop___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2299__spec__0(x_104, x_56);
x_106 = lean_ctor_get(x_91, 2);
lean_inc(x_106);
lean_dec(x_91);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec(x_107);
x_110 = lean_ctor_get(x_106, 1);
lean_inc(x_110);
lean_dec(x_106);
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
lean_dec(x_110);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_51);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_111);
lean_ctor_set(x_114, 1, x_113);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_109);
lean_ctor_set(x_115, 1, x_114);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_108);
lean_ctor_set(x_116, 1, x_115);
x_117 = l_List_mapTR_loop___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2299__spec__0(x_116, x_56);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_93);
lean_ctor_set(x_118, 1, x_56);
x_119 = l_List_appendTR(lean_box(0), x_118, x_105);
x_120 = l_List_appendTR(lean_box(0), x_119, x_117);
x_121 = l_List_appendTR(lean_box(0), x_57, x_120);
x_33 = x_121;
goto block_40;
}
}
}
block_32:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; lean_object* x_18; size_t x_19; lean_object* x_20; size_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
if (lean_is_scalar(x_9)) {
 x_14 = lean_alloc_ctor(0, 2, 0);
} else {
 x_14 = x_9;
}
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_mk_string_unchecked("usages", 6, 6);
x_16 = lean_ctor_get(x_8, 1);
lean_inc(x_16);
lean_dec(x_8);
x_17 = lean_array_size(x_16);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_usize_of_nat(x_18);
x_20 = l_Array_mapMUnsafe_map___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2299__spec__1(x_17, x_19, x_16);
x_21 = lean_array_size(x_20);
x_22 = l_Array_mapMUnsafe_map___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2299__spec__2(x_21, x_19, x_20);
x_23 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_15);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_box(0);
if (lean_is_scalar(x_6)) {
 x_26 = lean_alloc_ctor(1, 2, 0);
} else {
 x_26 = x_6;
}
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_14);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_Json_mkObj(x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_11);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_2);
x_1 = x_5;
x_2 = x_30;
goto _start;
}
block_40:
{
lean_object* x_34; size_t x_35; lean_object* x_36; size_t x_37; lean_object* x_38; lean_object* x_39; 
x_34 = lean_array_mk(x_33);
x_35 = lean_array_size(x_34);
x_36 = lean_unsigned_to_nat(0u);
x_37 = lean_usize_of_nat(x_36);
x_38 = l_Array_mapMUnsafe_map___at___Lean_Json_opt___at_____private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1558__spec__0_spec__0(x_35, x_37, x_34);
x_39 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_39, 0, x_38);
x_13 = x_39;
goto block_32;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2299__spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___redArg(x_2);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_33; lean_object* x_41; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_6 = x_1;
} else {
 lean_dec_ref(x_1);
 x_6 = lean_box(0);
}
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_9 = x_4;
} else {
 lean_dec_ref(x_4);
 x_9 = lean_box(0);
}
x_10 = l_Lean_Lsp_RefIdent_toJson(x_7);
x_11 = l_Lean_Json_compress(x_10);
x_12 = lean_mk_string_unchecked("definition", 10, 10);
x_41 = lean_ctor_get(x_8, 0);
lean_inc(x_41);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; 
x_42 = lean_box(0);
x_13 = x_42;
goto block_32;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_43 = lean_ctor_get(x_41, 0);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_ctor_get(x_44, 1);
lean_inc(x_48);
lean_dec(x_44);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_box(0);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_49);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_47);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_46);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_box(0);
x_57 = l_List_mapTR_loop___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2299__spec__0(x_55, x_56);
x_58 = lean_ctor_get(x_43, 1);
lean_inc(x_58);
lean_dec(x_43);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; 
x_59 = l_List_appendTR(lean_box(0), x_57, x_56);
x_33 = x_59;
goto block_40;
}
else
{
uint8_t x_60; 
x_60 = !lean_is_exclusive(x_58);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_61 = lean_ctor_get(x_58, 0);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
lean_ctor_set_tag(x_58, 3);
lean_ctor_set(x_58, 0, x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = lean_ctor_get(x_63, 1);
lean_inc(x_67);
lean_dec(x_63);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_51);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_68);
lean_ctor_set(x_71, 1, x_70);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_66);
lean_ctor_set(x_72, 1, x_71);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_65);
lean_ctor_set(x_73, 1, x_72);
x_74 = l_List_mapTR_loop___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2299__spec__0(x_73, x_56);
x_75 = lean_ctor_get(x_61, 2);
lean_inc(x_75);
lean_dec(x_61);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = lean_ctor_get(x_75, 1);
lean_inc(x_79);
lean_dec(x_75);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_51);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_80);
lean_ctor_set(x_83, 1, x_82);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_78);
lean_ctor_set(x_84, 1, x_83);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_77);
lean_ctor_set(x_85, 1, x_84);
x_86 = l_List_mapTR_loop___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2299__spec__0(x_85, x_56);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_58);
lean_ctor_set(x_87, 1, x_56);
x_88 = l_List_appendTR(lean_box(0), x_87, x_74);
x_89 = l_List_appendTR(lean_box(0), x_88, x_86);
x_90 = l_List_appendTR(lean_box(0), x_57, x_89);
x_33 = x_90;
goto block_40;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_91 = lean_ctor_get(x_58, 0);
lean_inc(x_91);
lean_dec(x_58);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_93, 0, x_92);
x_94 = lean_ctor_get(x_91, 1);
lean_inc(x_94);
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
x_98 = lean_ctor_get(x_94, 1);
lean_inc(x_98);
lean_dec(x_94);
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec(x_98);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_51);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_99);
lean_ctor_set(x_102, 1, x_101);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_97);
lean_ctor_set(x_103, 1, x_102);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_96);
lean_ctor_set(x_104, 1, x_103);
x_105 = l_List_mapTR_loop___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2299__spec__0(x_104, x_56);
x_106 = lean_ctor_get(x_91, 2);
lean_inc(x_106);
lean_dec(x_91);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec(x_107);
x_110 = lean_ctor_get(x_106, 1);
lean_inc(x_110);
lean_dec(x_106);
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
lean_dec(x_110);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_51);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_111);
lean_ctor_set(x_114, 1, x_113);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_109);
lean_ctor_set(x_115, 1, x_114);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_108);
lean_ctor_set(x_116, 1, x_115);
x_117 = l_List_mapTR_loop___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2299__spec__0(x_116, x_56);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_93);
lean_ctor_set(x_118, 1, x_56);
x_119 = l_List_appendTR(lean_box(0), x_118, x_105);
x_120 = l_List_appendTR(lean_box(0), x_119, x_117);
x_121 = l_List_appendTR(lean_box(0), x_57, x_120);
x_33 = x_121;
goto block_40;
}
}
}
block_32:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; lean_object* x_18; size_t x_19; lean_object* x_20; size_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
if (lean_is_scalar(x_9)) {
 x_14 = lean_alloc_ctor(0, 2, 0);
} else {
 x_14 = x_9;
}
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_mk_string_unchecked("usages", 6, 6);
x_16 = lean_ctor_get(x_8, 1);
lean_inc(x_16);
lean_dec(x_8);
x_17 = lean_array_size(x_16);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_usize_of_nat(x_18);
x_20 = l_Array_mapMUnsafe_map___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2299__spec__1(x_17, x_19, x_16);
x_21 = lean_array_size(x_20);
x_22 = l_Array_mapMUnsafe_map___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2299__spec__2(x_21, x_19, x_20);
x_23 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_15);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_box(0);
if (lean_is_scalar(x_6)) {
 x_26 = lean_alloc_ctor(1, 2, 0);
} else {
 x_26 = x_6;
}
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_14);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_Json_mkObj(x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_11);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_2);
x_31 = l_List_mapTR_loop___at___List_mapTR_loop___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2299__spec__5_spec__5(x_5, x_30);
return x_31;
}
block_40:
{
lean_object* x_34; size_t x_35; lean_object* x_36; size_t x_37; lean_object* x_38; lean_object* x_39; 
x_34 = lean_array_mk(x_33);
x_35 = lean_array_size(x_34);
x_36 = lean_unsigned_to_nat(0u);
x_37 = lean_usize_of_nat(x_36);
x_38 = l_Array_mapMUnsafe_map___at___Lean_Json_opt___at_____private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1558__spec__0_spec__0(x_35, x_37, x_34);
x_39 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_39, 0, x_38);
x_13 = x_39;
goto block_32;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2299_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_2 = lean_mk_string_unchecked("version", 7, 7);
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = l_Lean_JsonNumber_fromNat(x_3);
x_5 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_mk_string_unchecked("references", 10, 10);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_box(0);
x_12 = l_Std_DTreeMap_Internal_Impl_foldrM___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2299__spec__4(x_11, x_10);
lean_dec(x_10);
x_13 = l_List_mapTR_loop___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2299__spec__5(x_12, x_7);
x_14 = l_Lean_Json_mkObj(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_9);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_7);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_8);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_mk_empty_array_with_capacity(x_20);
x_22 = l_List_flatMapTR_go___at_____private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonPosition____x40_Lean_Data_Lsp_Basic___hyg_221__spec__0(x_19, x_21);
x_23 = l_Lean_Json_mkObj(x_22);
return x_23;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2299__spec__1___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Array_mapMUnsafe_map___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2299__spec__1___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2299__spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2299__spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2299__spec__2_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2299__spec__2_spec__2(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2299__spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2299__spec__2(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2299__spec__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Impl_foldrM___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2299__spec__4(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonLeanIleanInfoParams() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2299_), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanImportClosureParams____x40_Lean_Data_Lsp_Internal___hyg_2364_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_mk_string_unchecked("importClosure", 13, 13);
x_3 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Basic_0__Lean_Lsp_fromJsonResolveSupport____x40_Lean_Data_Lsp_Basic___hyg_7139__spec__0(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams___lam__0____x40_Lean_Data_Lsp_Internal___hyg_2193____boxed), 1, 0);
x_7 = lean_mk_string_unchecked("Lean", 4, 4);
x_8 = lean_mk_string_unchecked("Lsp", 3, 3);
x_9 = lean_mk_string_unchecked("LeanImportClosureParams", 23, 23);
x_10 = l_Lean_Name_mkStr3(x_7, x_8, x_9);
x_11 = lean_box(1);
x_12 = lean_unbox(x_11);
lean_inc(x_6);
x_13 = l_Lean_Name_toString(x_10, x_12, x_6);
x_14 = lean_mk_string_unchecked(".", 1, 1);
x_15 = lean_string_append(x_13, x_14);
lean_dec(x_14);
x_16 = l_Lean_Name_mkStr1(x_2);
x_17 = lean_unbox(x_11);
x_18 = l_Lean_Name_toString(x_16, x_17, x_6);
x_19 = lean_string_append(x_15, x_18);
lean_dec(x_18);
x_20 = lean_mk_string_unchecked(": ", 2, 2);
x_21 = lean_string_append(x_19, x_20);
lean_dec(x_20);
x_22 = lean_string_append(x_21, x_5);
lean_dec(x_5);
lean_ctor_set(x_3, 0, x_22);
return x_3;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_23 = lean_ctor_get(x_3, 0);
lean_inc(x_23);
lean_dec(x_3);
x_24 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams___lam__0____x40_Lean_Data_Lsp_Internal___hyg_2193____boxed), 1, 0);
x_25 = lean_mk_string_unchecked("Lean", 4, 4);
x_26 = lean_mk_string_unchecked("Lsp", 3, 3);
x_27 = lean_mk_string_unchecked("LeanImportClosureParams", 23, 23);
x_28 = l_Lean_Name_mkStr3(x_25, x_26, x_27);
x_29 = lean_box(1);
x_30 = lean_unbox(x_29);
lean_inc(x_24);
x_31 = l_Lean_Name_toString(x_28, x_30, x_24);
x_32 = lean_mk_string_unchecked(".", 1, 1);
x_33 = lean_string_append(x_31, x_32);
lean_dec(x_32);
x_34 = l_Lean_Name_mkStr1(x_2);
x_35 = lean_unbox(x_29);
x_36 = l_Lean_Name_toString(x_34, x_35, x_24);
x_37 = lean_string_append(x_33, x_36);
lean_dec(x_36);
x_38 = lean_mk_string_unchecked(": ", 2, 2);
x_39 = lean_string_append(x_37, x_38);
lean_dec(x_38);
x_40 = lean_string_append(x_39, x_23);
lean_dec(x_23);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_40);
return x_41;
}
}
else
{
lean_dec(x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_3);
if (x_42 == 0)
{
lean_ctor_set_tag(x_3, 0);
return x_3;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_3, 0);
lean_inc(x_43);
lean_dec(x_3);
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_43);
return x_44;
}
}
else
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_3);
if (x_45 == 0)
{
return x_3;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_3, 0);
lean_inc(x_46);
lean_dec(x_3);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
return x_47;
}
}
}
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImportClosureParams() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanImportClosureParams____x40_Lean_Data_Lsp_Internal___hyg_2364_), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanImportClosureParams____x40_Lean_Data_Lsp_Internal___hyg_2431_(lean_object* x_1) {
_start:
{
lean_object* x_2; size_t x_3; lean_object* x_4; size_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_2 = lean_mk_string_unchecked("importClosure", 13, 13);
x_3 = lean_array_size(x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_usize_of_nat(x_4);
x_6 = l_Array_mapMUnsafe_map___at_____private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonResolveSupport____x40_Lean_Data_Lsp_Basic___hyg_7206__spec__0(x_3, x_5, x_1);
x_7 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_mk_empty_array_with_capacity(x_4);
x_14 = l_List_flatMapTR_go___at_____private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonPosition____x40_Lean_Data_Lsp_Basic___hyg_221__spec__0(x_12, x_13);
x_15 = l_Lean_Json_mkObj(x_14);
return x_15;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonLeanImportClosureParams() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanImportClosureParams____x40_Lean_Data_Lsp_Internal___hyg_2431_), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanStaleDependencyParams____x40_Lean_Data_Lsp_Internal___hyg_2481_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_mk_string_unchecked("staleDependency", 15, 15);
x_3 = l_Lean_Json_getObjValAs_x3f___at___IO_FS_Stream_readMessage_spec__2(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams___lam__0____x40_Lean_Data_Lsp_Internal___hyg_2193____boxed), 1, 0);
x_7 = lean_mk_string_unchecked("Lean", 4, 4);
x_8 = lean_mk_string_unchecked("Lsp", 3, 3);
x_9 = lean_mk_string_unchecked("LeanStaleDependencyParams", 25, 25);
x_10 = l_Lean_Name_mkStr3(x_7, x_8, x_9);
x_11 = lean_box(1);
x_12 = lean_unbox(x_11);
lean_inc(x_6);
x_13 = l_Lean_Name_toString(x_10, x_12, x_6);
x_14 = lean_mk_string_unchecked(".", 1, 1);
x_15 = lean_string_append(x_13, x_14);
lean_dec(x_14);
x_16 = l_Lean_Name_mkStr1(x_2);
x_17 = lean_unbox(x_11);
x_18 = l_Lean_Name_toString(x_16, x_17, x_6);
x_19 = lean_string_append(x_15, x_18);
lean_dec(x_18);
x_20 = lean_mk_string_unchecked(": ", 2, 2);
x_21 = lean_string_append(x_19, x_20);
lean_dec(x_20);
x_22 = lean_string_append(x_21, x_5);
lean_dec(x_5);
lean_ctor_set(x_3, 0, x_22);
return x_3;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_23 = lean_ctor_get(x_3, 0);
lean_inc(x_23);
lean_dec(x_3);
x_24 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams___lam__0____x40_Lean_Data_Lsp_Internal___hyg_2193____boxed), 1, 0);
x_25 = lean_mk_string_unchecked("Lean", 4, 4);
x_26 = lean_mk_string_unchecked("Lsp", 3, 3);
x_27 = lean_mk_string_unchecked("LeanStaleDependencyParams", 25, 25);
x_28 = l_Lean_Name_mkStr3(x_25, x_26, x_27);
x_29 = lean_box(1);
x_30 = lean_unbox(x_29);
lean_inc(x_24);
x_31 = l_Lean_Name_toString(x_28, x_30, x_24);
x_32 = lean_mk_string_unchecked(".", 1, 1);
x_33 = lean_string_append(x_31, x_32);
lean_dec(x_32);
x_34 = l_Lean_Name_mkStr1(x_2);
x_35 = lean_unbox(x_29);
x_36 = l_Lean_Name_toString(x_34, x_35, x_24);
x_37 = lean_string_append(x_33, x_36);
lean_dec(x_36);
x_38 = lean_mk_string_unchecked(": ", 2, 2);
x_39 = lean_string_append(x_37, x_38);
lean_dec(x_38);
x_40 = lean_string_append(x_39, x_23);
lean_dec(x_23);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_40);
return x_41;
}
}
else
{
lean_dec(x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_3);
if (x_42 == 0)
{
lean_ctor_set_tag(x_3, 0);
return x_3;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_3, 0);
lean_inc(x_43);
lean_dec(x_3);
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_43);
return x_44;
}
}
else
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_3);
if (x_45 == 0)
{
return x_3;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_3, 0);
lean_inc(x_46);
lean_dec(x_3);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
return x_47;
}
}
}
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanStaleDependencyParams() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanStaleDependencyParams____x40_Lean_Data_Lsp_Internal___hyg_2481_), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanStaleDependencyParams____x40_Lean_Data_Lsp_Internal___hyg_2548_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = lean_mk_string_unchecked("staleDependency", 15, 15);
x_3 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_3, 0, x_1);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_mk_empty_array_with_capacity(x_9);
x_11 = l_List_flatMapTR_go___at_____private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonPosition____x40_Lean_Data_Lsp_Basic___hyg_221__spec__0(x_8, x_10);
x_12 = l_Lean_Json_mkObj(x_11);
return x_12;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonLeanStaleDependencyParams() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanStaleDependencyParams____x40_Lean_Data_Lsp_Internal___hyg_2548_), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonOpenNamespace____x40_Lean_Data_Lsp_Internal___hyg_2624__spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_array_uget(x_3, x_2);
x_7 = lean_box(0);
lean_inc(x_6);
x_8 = l_Lean_Json_getStr_x3f(x_6);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
lean_dec(x_6);
lean_dec(x_3);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
return x_8;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_8);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_22; uint8_t x_23; 
x_13 = lean_ctor_get(x_8, 0);
x_14 = lean_array_uset(x_3, x_2, x_7);
x_22 = lean_mk_string_unchecked("[anonymous]", 11, 11);
x_23 = lean_string_dec_eq(x_13, x_22);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = l_String_toName(x_13);
x_25 = l_Lean_Name_isAnonymous(x_24);
if (x_25 == 0)
{
lean_free_object(x_8);
lean_dec(x_6);
x_15 = x_24;
goto block_21;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_24);
lean_dec(x_14);
x_26 = lean_mk_string_unchecked("expected a `Name`, got '", 24, 24);
x_27 = lean_unsigned_to_nat(80u);
x_28 = l_Lean_Json_pretty(x_6, x_27);
x_29 = lean_string_append(x_26, x_28);
lean_dec(x_28);
x_30 = lean_mk_string_unchecked("'", 1, 1);
x_31 = lean_string_append(x_29, x_30);
lean_dec(x_30);
lean_ctor_set_tag(x_8, 0);
lean_ctor_set(x_8, 0, x_31);
return x_8;
}
}
else
{
lean_object* x_32; 
lean_free_object(x_8);
lean_dec(x_13);
lean_dec(x_6);
x_32 = lean_box(0);
x_15 = x_32;
goto block_21;
}
block_21:
{
lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_usize_of_nat(x_16);
x_18 = lean_usize_add(x_2, x_17);
x_19 = lean_array_uset(x_14, x_2, x_15);
x_2 = x_18;
x_3 = x_19;
goto _start;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_42; uint8_t x_43; 
x_33 = lean_ctor_get(x_8, 0);
lean_inc(x_33);
lean_dec(x_8);
x_34 = lean_array_uset(x_3, x_2, x_7);
x_42 = lean_mk_string_unchecked("[anonymous]", 11, 11);
x_43 = lean_string_dec_eq(x_33, x_42);
lean_dec(x_42);
if (x_43 == 0)
{
lean_object* x_44; uint8_t x_45; 
x_44 = l_String_toName(x_33);
x_45 = l_Lean_Name_isAnonymous(x_44);
if (x_45 == 0)
{
lean_dec(x_6);
x_35 = x_44;
goto block_41;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_44);
lean_dec(x_34);
x_46 = lean_mk_string_unchecked("expected a `Name`, got '", 24, 24);
x_47 = lean_unsigned_to_nat(80u);
x_48 = l_Lean_Json_pretty(x_6, x_47);
x_49 = lean_string_append(x_46, x_48);
lean_dec(x_48);
x_50 = lean_mk_string_unchecked("'", 1, 1);
x_51 = lean_string_append(x_49, x_50);
lean_dec(x_50);
x_52 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_52, 0, x_51);
return x_52;
}
}
else
{
lean_object* x_53; 
lean_dec(x_33);
lean_dec(x_6);
x_53 = lean_box(0);
x_35 = x_53;
goto block_41;
}
block_41:
{
lean_object* x_36; size_t x_37; size_t x_38; lean_object* x_39; 
x_36 = lean_unsigned_to_nat(1u);
x_37 = lean_usize_of_nat(x_36);
x_38 = lean_usize_add(x_2, x_37);
x_39 = lean_array_uset(x_34, x_2, x_35);
x_2 = x_38;
x_3 = x_39;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonOpenNamespace___lam__0____x40_Lean_Data_Lsp_Internal___hyg_2624_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_mk_string_unchecked("no inductive constructor matched", 32, 32);
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonOpenNamespace___lam__1____x40_Lean_Data_Lsp_Internal___hyg_2624_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_10 = lean_mk_string_unchecked("allExcept", 9, 9);
x_11 = lean_mk_string_unchecked("namespace", 9, 9);
x_12 = l_Lean_Name_mkStr1(x_11);
x_13 = lean_mk_string_unchecked("exceptions", 10, 10);
x_14 = l_Lean_Name_mkStr1(x_13);
x_15 = lean_mk_empty_array_with_capacity(x_1);
x_16 = lean_array_push(x_15, x_12);
x_17 = lean_array_push(x_16, x_14);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = l_Lean_Json_parseTagged(x_2, x_10, x_1, x_18);
lean_dec(x_18);
lean_dec(x_10);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
lean_dec(x_4);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = l_Except_orElseLazy___redArg(x_19, x_3);
lean_dec(x_19);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_19, 0);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = l_Except_orElseLazy___redArg(x_23, x_3);
lean_dec(x_23);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_25 = lean_ctor_get(x_19, 0);
lean_inc(x_25);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 x_26 = x_19;
} else {
 lean_dec_ref(x_19);
 x_26 = lean_box(0);
}
x_57 = lean_unsigned_to_nat(0u);
lean_inc(x_4);
x_58 = lean_array_get(x_4, x_25, x_57);
lean_inc(x_58);
x_59 = l_Lean_Json_getStr_x3f(x_58);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; 
lean_dec(x_58);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_4);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
lean_dec(x_59);
x_6 = x_60;
goto block_9;
}
else
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_61 = lean_ctor_get(x_59, 0);
lean_inc(x_61);
lean_dec(x_59);
x_62 = lean_mk_string_unchecked("[anonymous]", 11, 11);
x_63 = lean_string_dec_eq(x_61, x_62);
lean_dec(x_62);
if (x_63 == 0)
{
lean_object* x_64; uint8_t x_65; 
x_64 = l_String_toName(x_61);
x_65 = l_Lean_Name_isAnonymous(x_64);
if (x_65 == 0)
{
lean_dec(x_58);
x_27 = x_64;
goto block_56;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_64);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_4);
x_66 = lean_mk_string_unchecked("expected a `Name`, got '", 24, 24);
x_67 = lean_unsigned_to_nat(80u);
x_68 = l_Lean_Json_pretty(x_58, x_67);
x_69 = lean_string_append(x_66, x_68);
lean_dec(x_68);
x_70 = lean_mk_string_unchecked("'", 1, 1);
x_71 = lean_string_append(x_69, x_70);
lean_dec(x_70);
x_6 = x_71;
goto block_9;
}
}
else
{
lean_object* x_72; 
lean_dec(x_61);
lean_dec(x_58);
x_72 = lean_box(0);
x_27 = x_72;
goto block_56;
}
}
block_56:
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_array_get(x_4, x_25, x_28);
lean_dec(x_25);
if (lean_obj_tag(x_29) == 4)
{
lean_object* x_30; size_t x_31; lean_object* x_32; size_t x_33; lean_object* x_34; 
lean_dec(x_26);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_array_size(x_30);
x_32 = lean_unsigned_to_nat(0u);
x_33 = lean_usize_of_nat(x_32);
x_34 = l_Array_mapMUnsafe_map___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonOpenNamespace____x40_Lean_Data_Lsp_Internal___hyg_2624__spec__0(x_31, x_33, x_30);
if (lean_obj_tag(x_34) == 0)
{
uint8_t x_35; 
lean_dec(x_27);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = l_Except_orElseLazy___redArg(x_34, x_3);
lean_dec(x_34);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_34, 0);
lean_inc(x_37);
lean_dec(x_34);
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_37);
x_39 = l_Except_orElseLazy___redArg(x_38, x_3);
lean_dec(x_38);
return x_39;
}
}
else
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_34);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_34, 0);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_27);
lean_ctor_set(x_42, 1, x_41);
lean_ctor_set(x_34, 0, x_42);
x_43 = l_Except_orElseLazy___redArg(x_34, x_3);
lean_dec(x_34);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_44 = lean_ctor_get(x_34, 0);
lean_inc(x_44);
lean_dec(x_34);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_27);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_45);
x_47 = l_Except_orElseLazy___redArg(x_46, x_3);
lean_dec(x_46);
return x_47;
}
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_27);
x_48 = lean_mk_string_unchecked("expected JSON array, got '", 26, 26);
x_49 = lean_unsigned_to_nat(80u);
x_50 = l_Lean_Json_pretty(x_29, x_49);
x_51 = lean_string_append(x_48, x_50);
lean_dec(x_50);
x_52 = lean_mk_string_unchecked("'", 1, 1);
x_53 = lean_string_append(x_51, x_52);
lean_dec(x_52);
if (lean_is_scalar(x_26)) {
 x_54 = lean_alloc_ctor(0, 1, 0);
} else {
 x_54 = x_26;
 lean_ctor_set_tag(x_54, 0);
}
lean_ctor_set(x_54, 0, x_53);
x_55 = l_Except_orElseLazy___redArg(x_54, x_3);
lean_dec(x_54);
return x_55;
}
}
}
block_9:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = l_Except_orElseLazy___redArg(x_7, x_3);
lean_dec(x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonOpenNamespace____x40_Lean_Data_Lsp_Internal___hyg_2624_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_11; lean_object* x_12; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonOpenNamespace___lam__0____x40_Lean_Data_Lsp_Internal___hyg_2624____boxed), 1, 0);
x_3 = lean_box(0);
x_4 = lean_mk_string_unchecked("renamed", 7, 7);
x_5 = lean_unsigned_to_nat(2u);
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonOpenNamespace___lam__1____x40_Lean_Data_Lsp_Internal___hyg_2624____boxed), 5, 4);
lean_closure_set(x_6, 0, x_5);
lean_closure_set(x_6, 1, x_1);
lean_closure_set(x_6, 2, x_2);
lean_closure_set(x_6, 3, x_3);
x_17 = lean_mk_string_unchecked("from", 4, 4);
x_18 = l_Lean_Name_mkStr1(x_17);
x_19 = lean_mk_string_unchecked("to", 2, 2);
x_20 = l_Lean_Name_mkStr1(x_19);
x_21 = lean_mk_empty_array_with_capacity(x_5);
x_22 = lean_array_push(x_21, x_18);
x_23 = lean_array_push(x_22, x_20);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = l_Lean_Json_parseTagged(x_1, x_4, x_5, x_24);
lean_dec(x_24);
lean_dec(x_4);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = l_Except_orElseLazy___redArg(x_25, x_6);
lean_dec(x_25);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_25, 0);
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = l_Except_orElseLazy___redArg(x_29, x_6);
lean_dec(x_29);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_31 = lean_ctor_get(x_25, 0);
lean_inc(x_31);
lean_dec(x_25);
x_70 = lean_unsigned_to_nat(0u);
x_71 = lean_array_get(x_3, x_31, x_70);
lean_inc(x_71);
x_72 = l_Lean_Json_getStr_x3f(x_71);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; 
lean_dec(x_71);
lean_dec(x_31);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
lean_dec(x_72);
x_7 = x_73;
goto block_10;
}
else
{
lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_74 = lean_ctor_get(x_72, 0);
lean_inc(x_74);
lean_dec(x_72);
x_75 = lean_mk_string_unchecked("[anonymous]", 11, 11);
x_76 = lean_string_dec_eq(x_74, x_75);
lean_dec(x_75);
if (x_76 == 0)
{
lean_object* x_77; uint8_t x_78; 
x_77 = l_String_toName(x_74);
x_78 = l_Lean_Name_isAnonymous(x_77);
if (x_78 == 0)
{
lean_dec(x_71);
x_32 = x_77;
goto block_69;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_77);
lean_dec(x_31);
x_79 = lean_mk_string_unchecked("expected a `Name`, got '", 24, 24);
x_80 = lean_unsigned_to_nat(80u);
x_81 = l_Lean_Json_pretty(x_71, x_80);
x_82 = lean_string_append(x_79, x_81);
lean_dec(x_81);
x_83 = lean_mk_string_unchecked("'", 1, 1);
x_84 = lean_string_append(x_82, x_83);
lean_dec(x_83);
x_7 = x_84;
goto block_10;
}
}
else
{
lean_object* x_85; 
lean_dec(x_74);
lean_dec(x_71);
x_85 = lean_box(0);
x_32 = x_85;
goto block_69;
}
}
block_69:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_unsigned_to_nat(1u);
x_34 = lean_array_get(x_3, x_31, x_33);
lean_dec(x_31);
lean_inc(x_34);
x_35 = l_Lean_Json_getStr_x3f(x_34);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
lean_dec(x_34);
lean_dec(x_32);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = l_Except_orElseLazy___redArg(x_35, x_6);
lean_dec(x_35);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_35, 0);
lean_inc(x_38);
lean_dec(x_35);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_38);
x_40 = l_Except_orElseLazy___redArg(x_39, x_6);
lean_dec(x_39);
return x_40;
}
}
else
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_35);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_42 = lean_ctor_get(x_35, 0);
x_43 = lean_mk_string_unchecked("[anonymous]", 11, 11);
x_44 = lean_string_dec_eq(x_42, x_43);
lean_dec(x_43);
if (x_44 == 0)
{
lean_object* x_45; uint8_t x_46; 
x_45 = l_String_toName(x_42);
x_46 = l_Lean_Name_isAnonymous(x_45);
if (x_46 == 0)
{
lean_free_object(x_35);
lean_dec(x_34);
x_11 = x_32;
x_12 = x_45;
goto block_16;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_45);
lean_dec(x_32);
x_47 = lean_mk_string_unchecked("expected a `Name`, got '", 24, 24);
x_48 = lean_unsigned_to_nat(80u);
x_49 = l_Lean_Json_pretty(x_34, x_48);
x_50 = lean_string_append(x_47, x_49);
lean_dec(x_49);
x_51 = lean_mk_string_unchecked("'", 1, 1);
x_52 = lean_string_append(x_50, x_51);
lean_dec(x_51);
lean_ctor_set_tag(x_35, 0);
lean_ctor_set(x_35, 0, x_52);
x_53 = l_Except_orElseLazy___redArg(x_35, x_6);
lean_dec(x_35);
return x_53;
}
}
else
{
lean_object* x_54; 
lean_free_object(x_35);
lean_dec(x_42);
lean_dec(x_34);
x_54 = lean_box(0);
x_11 = x_32;
x_12 = x_54;
goto block_16;
}
}
else
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_55 = lean_ctor_get(x_35, 0);
lean_inc(x_55);
lean_dec(x_35);
x_56 = lean_mk_string_unchecked("[anonymous]", 11, 11);
x_57 = lean_string_dec_eq(x_55, x_56);
lean_dec(x_56);
if (x_57 == 0)
{
lean_object* x_58; uint8_t x_59; 
x_58 = l_String_toName(x_55);
x_59 = l_Lean_Name_isAnonymous(x_58);
if (x_59 == 0)
{
lean_dec(x_34);
x_11 = x_32;
x_12 = x_58;
goto block_16;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_58);
lean_dec(x_32);
x_60 = lean_mk_string_unchecked("expected a `Name`, got '", 24, 24);
x_61 = lean_unsigned_to_nat(80u);
x_62 = l_Lean_Json_pretty(x_34, x_61);
x_63 = lean_string_append(x_60, x_62);
lean_dec(x_62);
x_64 = lean_mk_string_unchecked("'", 1, 1);
x_65 = lean_string_append(x_63, x_64);
lean_dec(x_64);
x_66 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_66, 0, x_65);
x_67 = l_Except_orElseLazy___redArg(x_66, x_6);
lean_dec(x_66);
return x_67;
}
}
else
{
lean_object* x_68; 
lean_dec(x_55);
lean_dec(x_34);
x_68 = lean_box(0);
x_11 = x_32;
x_12 = x_68;
goto block_16;
}
}
}
}
}
block_10:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = l_Except_orElseLazy___redArg(x_8, x_6);
lean_dec(x_8);
return x_9;
}
block_16:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = l_Except_orElseLazy___redArg(x_14, x_6);
lean_dec(x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonOpenNamespace____x40_Lean_Data_Lsp_Internal___hyg_2624__spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonOpenNamespace____x40_Lean_Data_Lsp_Internal___hyg_2624__spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonOpenNamespace___lam__0____x40_Lean_Data_Lsp_Internal___hyg_2624____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonOpenNamespace___lam__0____x40_Lean_Data_Lsp_Internal___hyg_2624_(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonOpenNamespace___lam__1____x40_Lean_Data_Lsp_Internal___hyg_2624____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonOpenNamespace___lam__1____x40_Lean_Data_Lsp_Internal___hyg_2624_(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonOpenNamespace() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonOpenNamespace____x40_Lean_Data_Lsp_Internal___hyg_2624_), 1, 0);
return x_1;
}
}
LEAN_EXPORT uint8_t l_Array_mapMUnsafe_map___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonOpenNamespace____x40_Lean_Data_Lsp_Internal___hyg_2804__spec__0___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonOpenNamespace____x40_Lean_Data_Lsp_Internal___hyg_2804__spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_5 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonOpenNamespace____x40_Lean_Data_Lsp_Internal___hyg_2804__spec__0___lam__0___boxed), 1, 0);
x_6 = lean_array_uget(x_3, x_2);
x_7 = lean_box(0);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = l_Lean_Name_toString(x_6, x_4, x_5);
x_10 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_usize_of_nat(x_11);
x_13 = lean_usize_add(x_2, x_12);
x_14 = lean_array_uset(x_8, x_2, x_10);
x_2 = x_13;
x_3 = x_14;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonOpenNamespace____x40_Lean_Data_Lsp_Internal___hyg_2804_(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; lean_object* x_14; size_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams___lam__0____x40_Lean_Data_Lsp_Internal___hyg_2193____boxed), 1, 0);
x_6 = lean_mk_string_unchecked("allExcept", 9, 9);
x_7 = lean_mk_string_unchecked("namespace", 9, 9);
x_8 = lean_box(1);
x_9 = lean_unbox(x_8);
x_10 = l_Lean_Name_toString(x_3, x_9, x_5);
x_11 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_1, 1, x_11);
lean_ctor_set(x_1, 0, x_7);
x_12 = lean_mk_string_unchecked("exceptions", 10, 10);
x_13 = lean_array_size(x_4);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_usize_of_nat(x_14);
x_16 = l_Array_mapMUnsafe_map___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonOpenNamespace____x40_Lean_Data_Lsp_Internal___hyg_2804__spec__0(x_13, x_15, x_4);
x_17 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_12);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_1);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_Json_mkObj(x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_6);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_19);
x_25 = l_Lean_Json_mkObj(x_24);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; size_t x_37; lean_object* x_38; size_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_26 = lean_ctor_get(x_1, 0);
x_27 = lean_ctor_get(x_1, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_1);
x_28 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams___lam__0____x40_Lean_Data_Lsp_Internal___hyg_2193____boxed), 1, 0);
x_29 = lean_mk_string_unchecked("allExcept", 9, 9);
x_30 = lean_mk_string_unchecked("namespace", 9, 9);
x_31 = lean_box(1);
x_32 = lean_unbox(x_31);
x_33 = l_Lean_Name_toString(x_26, x_32, x_28);
x_34 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_30);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_mk_string_unchecked("exceptions", 10, 10);
x_37 = lean_array_size(x_27);
x_38 = lean_unsigned_to_nat(0u);
x_39 = lean_usize_of_nat(x_38);
x_40 = l_Array_mapMUnsafe_map___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonOpenNamespace____x40_Lean_Data_Lsp_Internal___hyg_2804__spec__0(x_37, x_39, x_27);
x_41 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_36);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_35);
lean_ctor_set(x_45, 1, x_44);
x_46 = l_Lean_Json_mkObj(x_45);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_29);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_43);
x_49 = l_Lean_Json_mkObj(x_48);
return x_49;
}
}
else
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_1);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_51 = lean_ctor_get(x_1, 0);
x_52 = lean_ctor_get(x_1, 1);
x_53 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams___lam__0____x40_Lean_Data_Lsp_Internal___hyg_2193____boxed), 1, 0);
x_54 = lean_mk_string_unchecked("renamed", 7, 7);
x_55 = lean_mk_string_unchecked("from", 4, 4);
x_56 = lean_box(1);
x_57 = lean_unbox(x_56);
lean_inc(x_53);
x_58 = l_Lean_Name_toString(x_51, x_57, x_53);
x_59 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_59);
lean_ctor_set(x_1, 0, x_55);
x_60 = lean_mk_string_unchecked("to", 2, 2);
x_61 = lean_unbox(x_56);
x_62 = l_Lean_Name_toString(x_52, x_61, x_53);
x_63 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_63, 0, x_62);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_60);
lean_ctor_set(x_64, 1, x_63);
x_65 = lean_box(0);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_1);
lean_ctor_set(x_67, 1, x_66);
x_68 = l_Lean_Json_mkObj(x_67);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_54);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_65);
x_71 = l_Lean_Json_mkObj(x_70);
return x_71;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_72 = lean_ctor_get(x_1, 0);
x_73 = lean_ctor_get(x_1, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_1);
x_74 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams___lam__0____x40_Lean_Data_Lsp_Internal___hyg_2193____boxed), 1, 0);
x_75 = lean_mk_string_unchecked("renamed", 7, 7);
x_76 = lean_mk_string_unchecked("from", 4, 4);
x_77 = lean_box(1);
x_78 = lean_unbox(x_77);
lean_inc(x_74);
x_79 = l_Lean_Name_toString(x_72, x_78, x_74);
x_80 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_80, 0, x_79);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_76);
lean_ctor_set(x_81, 1, x_80);
x_82 = lean_mk_string_unchecked("to", 2, 2);
x_83 = lean_unbox(x_77);
x_84 = l_Lean_Name_toString(x_73, x_83, x_74);
x_85 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_85, 0, x_84);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_82);
lean_ctor_set(x_86, 1, x_85);
x_87 = lean_box(0);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_81);
lean_ctor_set(x_89, 1, x_88);
x_90 = l_Lean_Json_mkObj(x_89);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_75);
lean_ctor_set(x_91, 1, x_90);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_87);
x_93 = l_Lean_Json_mkObj(x_92);
return x_93;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonOpenNamespace____x40_Lean_Data_Lsp_Internal___hyg_2804__spec__0___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Array_mapMUnsafe_map___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonOpenNamespace____x40_Lean_Data_Lsp_Internal___hyg_2804__spec__0___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonOpenNamespace____x40_Lean_Data_Lsp_Internal___hyg_2804__spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonOpenNamespace____x40_Lean_Data_Lsp_Internal___hyg_2804__spec__0(x_4, x_5, x_3);
return x_6;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonOpenNamespace() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonOpenNamespace____x40_Lean_Data_Lsp_Internal___hyg_2804_), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanModuleQuery____x40_Lean_Data_Lsp_Internal___hyg_2922__spec__0_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_array_uget(x_3, x_2);
x_7 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonOpenNamespace____x40_Lean_Data_Lsp_Internal___hyg_2624_(x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
lean_dec(x_3);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
return x_7;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec(x_7);
x_12 = lean_box(0);
x_13 = lean_array_uset(x_3, x_2, x_12);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_usize_of_nat(x_14);
x_16 = lean_usize_add(x_2, x_15);
x_17 = lean_array_uset(x_13, x_2, x_11);
x_2 = x_16;
x_3 = x_17;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanModuleQuery____x40_Lean_Data_Lsp_Internal___hyg_2922__spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
if (lean_obj_tag(x_3) == 4)
{
lean_object* x_4; size_t x_5; lean_object* x_6; size_t x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_array_size(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_usize_of_nat(x_6);
x_8 = l_Array_mapMUnsafe_map___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanModuleQuery____x40_Lean_Data_Lsp_Internal___hyg_2922__spec__0_spec__0(x_5, x_7, x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_mk_string_unchecked("expected JSON array, got '", 26, 26);
x_10 = lean_unsigned_to_nat(80u);
x_11 = l_Lean_Json_pretty(x_3, x_10);
x_12 = lean_string_append(x_9, x_11);
lean_dec(x_11);
x_13 = lean_mk_string_unchecked("'", 1, 1);
x_14 = lean_string_append(x_12, x_13);
lean_dec(x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanModuleQuery____x40_Lean_Data_Lsp_Internal___hyg_2922_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_mk_string_unchecked("identifier", 10, 10);
lean_inc(x_1);
x_3 = l_Lean_Json_getObjValAs_x3f___at___IO_FS_Stream_readMessage_spec__2(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
lean_dec(x_1);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams___lam__0____x40_Lean_Data_Lsp_Internal___hyg_2193____boxed), 1, 0);
x_7 = lean_mk_string_unchecked("Lean", 4, 4);
x_8 = lean_mk_string_unchecked("Lsp", 3, 3);
x_9 = lean_mk_string_unchecked("LeanModuleQuery", 15, 15);
x_10 = l_Lean_Name_mkStr3(x_7, x_8, x_9);
x_11 = lean_box(1);
x_12 = lean_unbox(x_11);
lean_inc(x_6);
x_13 = l_Lean_Name_toString(x_10, x_12, x_6);
x_14 = lean_mk_string_unchecked(".", 1, 1);
x_15 = lean_string_append(x_13, x_14);
lean_dec(x_14);
x_16 = l_Lean_Name_mkStr1(x_2);
x_17 = lean_unbox(x_11);
x_18 = l_Lean_Name_toString(x_16, x_17, x_6);
x_19 = lean_string_append(x_15, x_18);
lean_dec(x_18);
x_20 = lean_mk_string_unchecked(": ", 2, 2);
x_21 = lean_string_append(x_19, x_20);
lean_dec(x_20);
x_22 = lean_string_append(x_21, x_5);
lean_dec(x_5);
lean_ctor_set(x_3, 0, x_22);
return x_3;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_23 = lean_ctor_get(x_3, 0);
lean_inc(x_23);
lean_dec(x_3);
x_24 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams___lam__0____x40_Lean_Data_Lsp_Internal___hyg_2193____boxed), 1, 0);
x_25 = lean_mk_string_unchecked("Lean", 4, 4);
x_26 = lean_mk_string_unchecked("Lsp", 3, 3);
x_27 = lean_mk_string_unchecked("LeanModuleQuery", 15, 15);
x_28 = l_Lean_Name_mkStr3(x_25, x_26, x_27);
x_29 = lean_box(1);
x_30 = lean_unbox(x_29);
lean_inc(x_24);
x_31 = l_Lean_Name_toString(x_28, x_30, x_24);
x_32 = lean_mk_string_unchecked(".", 1, 1);
x_33 = lean_string_append(x_31, x_32);
lean_dec(x_32);
x_34 = l_Lean_Name_mkStr1(x_2);
x_35 = lean_unbox(x_29);
x_36 = l_Lean_Name_toString(x_34, x_35, x_24);
x_37 = lean_string_append(x_33, x_36);
lean_dec(x_36);
x_38 = lean_mk_string_unchecked(": ", 2, 2);
x_39 = lean_string_append(x_37, x_38);
lean_dec(x_38);
x_40 = lean_string_append(x_39, x_23);
lean_dec(x_23);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_40);
return x_41;
}
}
else
{
lean_dec(x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_42; 
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_3);
if (x_42 == 0)
{
lean_ctor_set_tag(x_3, 0);
return x_3;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_3, 0);
lean_inc(x_43);
lean_dec(x_3);
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_43);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_3, 0);
lean_inc(x_45);
lean_dec(x_3);
x_46 = lean_mk_string_unchecked("openNamespaces", 14, 14);
x_47 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanModuleQuery____x40_Lean_Data_Lsp_Internal___hyg_2922__spec__0(x_1, x_46);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; 
lean_dec(x_45);
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_49 = lean_ctor_get(x_47, 0);
x_50 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams___lam__0____x40_Lean_Data_Lsp_Internal___hyg_2193____boxed), 1, 0);
x_51 = lean_mk_string_unchecked("Lean", 4, 4);
x_52 = lean_mk_string_unchecked("Lsp", 3, 3);
x_53 = lean_mk_string_unchecked("LeanModuleQuery", 15, 15);
x_54 = l_Lean_Name_mkStr3(x_51, x_52, x_53);
x_55 = lean_box(1);
x_56 = lean_unbox(x_55);
lean_inc(x_50);
x_57 = l_Lean_Name_toString(x_54, x_56, x_50);
x_58 = lean_mk_string_unchecked(".", 1, 1);
x_59 = lean_string_append(x_57, x_58);
lean_dec(x_58);
x_60 = l_Lean_Name_mkStr1(x_46);
x_61 = lean_unbox(x_55);
x_62 = l_Lean_Name_toString(x_60, x_61, x_50);
x_63 = lean_string_append(x_59, x_62);
lean_dec(x_62);
x_64 = lean_mk_string_unchecked(": ", 2, 2);
x_65 = lean_string_append(x_63, x_64);
lean_dec(x_64);
x_66 = lean_string_append(x_65, x_49);
lean_dec(x_49);
lean_ctor_set(x_47, 0, x_66);
return x_47;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_67 = lean_ctor_get(x_47, 0);
lean_inc(x_67);
lean_dec(x_47);
x_68 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams___lam__0____x40_Lean_Data_Lsp_Internal___hyg_2193____boxed), 1, 0);
x_69 = lean_mk_string_unchecked("Lean", 4, 4);
x_70 = lean_mk_string_unchecked("Lsp", 3, 3);
x_71 = lean_mk_string_unchecked("LeanModuleQuery", 15, 15);
x_72 = l_Lean_Name_mkStr3(x_69, x_70, x_71);
x_73 = lean_box(1);
x_74 = lean_unbox(x_73);
lean_inc(x_68);
x_75 = l_Lean_Name_toString(x_72, x_74, x_68);
x_76 = lean_mk_string_unchecked(".", 1, 1);
x_77 = lean_string_append(x_75, x_76);
lean_dec(x_76);
x_78 = l_Lean_Name_mkStr1(x_46);
x_79 = lean_unbox(x_73);
x_80 = l_Lean_Name_toString(x_78, x_79, x_68);
x_81 = lean_string_append(x_77, x_80);
lean_dec(x_80);
x_82 = lean_mk_string_unchecked(": ", 2, 2);
x_83 = lean_string_append(x_81, x_82);
lean_dec(x_82);
x_84 = lean_string_append(x_83, x_67);
lean_dec(x_67);
x_85 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_85, 0, x_84);
return x_85;
}
}
else
{
lean_dec(x_46);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_86; 
lean_dec(x_45);
x_86 = !lean_is_exclusive(x_47);
if (x_86 == 0)
{
lean_ctor_set_tag(x_47, 0);
return x_47;
}
else
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_47, 0);
lean_inc(x_87);
lean_dec(x_47);
x_88 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_88, 0, x_87);
return x_88;
}
}
else
{
uint8_t x_89; 
x_89 = !lean_is_exclusive(x_47);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_47, 0);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_45);
lean_ctor_set(x_91, 1, x_90);
lean_ctor_set(x_47, 0, x_91);
return x_47;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_47, 0);
lean_inc(x_92);
lean_dec(x_47);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_45);
lean_ctor_set(x_93, 1, x_92);
x_94 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_94, 0, x_93);
return x_94;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanModuleQuery____x40_Lean_Data_Lsp_Internal___hyg_2922__spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanModuleQuery____x40_Lean_Data_Lsp_Internal___hyg_2922__spec__0_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanModuleQuery____x40_Lean_Data_Lsp_Internal___hyg_2922__spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanModuleQuery____x40_Lean_Data_Lsp_Internal___hyg_2922__spec__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleQuery() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanModuleQuery____x40_Lean_Data_Lsp_Internal___hyg_2922_), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanModuleQuery____x40_Lean_Data_Lsp_Internal___hyg_3028__spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_box(0);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonOpenNamespace____x40_Lean_Data_Lsp_Internal___hyg_2804_(x_5);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_usize_of_nat(x_9);
x_11 = lean_usize_add(x_2, x_10);
x_12 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_11;
x_3 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanModuleQuery____x40_Lean_Data_Lsp_Internal___hyg_3028_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; lean_object* x_11; size_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_2 = lean_mk_string_unchecked("identifier", 10, 10);
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_4, 0, x_3);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_4);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_mk_string_unchecked("openNamespaces", 14, 14);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_array_size(x_9);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_usize_of_nat(x_11);
x_13 = l_Array_mapMUnsafe_map___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanModuleQuery____x40_Lean_Data_Lsp_Internal___hyg_3028__spec__0(x_10, x_12, x_9);
x_14 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_6);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_7);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_mk_empty_array_with_capacity(x_11);
x_21 = l_List_flatMapTR_go___at_____private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonPosition____x40_Lean_Data_Lsp_Basic___hyg_221__spec__0(x_19, x_20);
x_22 = l_Lean_Json_mkObj(x_21);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanModuleQuery____x40_Lean_Data_Lsp_Internal___hyg_3028__spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanModuleQuery____x40_Lean_Data_Lsp_Internal___hyg_3028__spec__0(x_4, x_5, x_3);
return x_6;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonLeanModuleQuery() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanModuleQuery____x40_Lean_Data_Lsp_Internal___hyg_3028_), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanQueryModuleParams____x40_Lean_Data_Lsp_Internal___hyg_3101__spec__0_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_array_uget(x_3, x_2);
x_7 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanModuleQuery____x40_Lean_Data_Lsp_Internal___hyg_2922_(x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
lean_dec(x_3);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
return x_7;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec(x_7);
x_12 = lean_box(0);
x_13 = lean_array_uset(x_3, x_2, x_12);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_usize_of_nat(x_14);
x_16 = lean_usize_add(x_2, x_15);
x_17 = lean_array_uset(x_13, x_2, x_11);
x_2 = x_16;
x_3 = x_17;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanQueryModuleParams____x40_Lean_Data_Lsp_Internal___hyg_3101__spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
if (lean_obj_tag(x_3) == 4)
{
lean_object* x_4; size_t x_5; lean_object* x_6; size_t x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_array_size(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_usize_of_nat(x_6);
x_8 = l_Array_mapMUnsafe_map___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanQueryModuleParams____x40_Lean_Data_Lsp_Internal___hyg_3101__spec__0_spec__0(x_5, x_7, x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_mk_string_unchecked("expected JSON array, got '", 26, 26);
x_10 = lean_unsigned_to_nat(80u);
x_11 = l_Lean_Json_pretty(x_3, x_10);
x_12 = lean_string_append(x_9, x_11);
lean_dec(x_11);
x_13 = lean_mk_string_unchecked("'", 1, 1);
x_14 = lean_string_append(x_12, x_13);
lean_dec(x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanQueryModuleParams____x40_Lean_Data_Lsp_Internal___hyg_3101_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_mk_string_unchecked("sourceRequestID", 15, 15);
lean_inc(x_1);
x_3 = l_Lean_Json_getObjValAs_x3f___at___IO_FS_Stream_readMessage_spec__0(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
lean_dec(x_1);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams___lam__0____x40_Lean_Data_Lsp_Internal___hyg_2193____boxed), 1, 0);
x_7 = lean_mk_string_unchecked("Lean", 4, 4);
x_8 = lean_mk_string_unchecked("Lsp", 3, 3);
x_9 = lean_mk_string_unchecked("LeanQueryModuleParams", 21, 21);
x_10 = l_Lean_Name_mkStr3(x_7, x_8, x_9);
x_11 = lean_box(1);
x_12 = lean_unbox(x_11);
lean_inc(x_6);
x_13 = l_Lean_Name_toString(x_10, x_12, x_6);
x_14 = lean_mk_string_unchecked(".", 1, 1);
x_15 = lean_string_append(x_13, x_14);
lean_dec(x_14);
x_16 = l_Lean_Name_mkStr1(x_2);
x_17 = lean_unbox(x_11);
x_18 = l_Lean_Name_toString(x_16, x_17, x_6);
x_19 = lean_string_append(x_15, x_18);
lean_dec(x_18);
x_20 = lean_mk_string_unchecked(": ", 2, 2);
x_21 = lean_string_append(x_19, x_20);
lean_dec(x_20);
x_22 = lean_string_append(x_21, x_5);
lean_dec(x_5);
lean_ctor_set(x_3, 0, x_22);
return x_3;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_23 = lean_ctor_get(x_3, 0);
lean_inc(x_23);
lean_dec(x_3);
x_24 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams___lam__0____x40_Lean_Data_Lsp_Internal___hyg_2193____boxed), 1, 0);
x_25 = lean_mk_string_unchecked("Lean", 4, 4);
x_26 = lean_mk_string_unchecked("Lsp", 3, 3);
x_27 = lean_mk_string_unchecked("LeanQueryModuleParams", 21, 21);
x_28 = l_Lean_Name_mkStr3(x_25, x_26, x_27);
x_29 = lean_box(1);
x_30 = lean_unbox(x_29);
lean_inc(x_24);
x_31 = l_Lean_Name_toString(x_28, x_30, x_24);
x_32 = lean_mk_string_unchecked(".", 1, 1);
x_33 = lean_string_append(x_31, x_32);
lean_dec(x_32);
x_34 = l_Lean_Name_mkStr1(x_2);
x_35 = lean_unbox(x_29);
x_36 = l_Lean_Name_toString(x_34, x_35, x_24);
x_37 = lean_string_append(x_33, x_36);
lean_dec(x_36);
x_38 = lean_mk_string_unchecked(": ", 2, 2);
x_39 = lean_string_append(x_37, x_38);
lean_dec(x_38);
x_40 = lean_string_append(x_39, x_23);
lean_dec(x_23);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_40);
return x_41;
}
}
else
{
lean_dec(x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_42; 
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_3);
if (x_42 == 0)
{
lean_ctor_set_tag(x_3, 0);
return x_3;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_3, 0);
lean_inc(x_43);
lean_dec(x_3);
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_43);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_3, 0);
lean_inc(x_45);
lean_dec(x_3);
x_46 = lean_mk_string_unchecked("queries", 7, 7);
x_47 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanQueryModuleParams____x40_Lean_Data_Lsp_Internal___hyg_3101__spec__0(x_1, x_46);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; 
lean_dec(x_45);
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_49 = lean_ctor_get(x_47, 0);
x_50 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams___lam__0____x40_Lean_Data_Lsp_Internal___hyg_2193____boxed), 1, 0);
x_51 = lean_mk_string_unchecked("Lean", 4, 4);
x_52 = lean_mk_string_unchecked("Lsp", 3, 3);
x_53 = lean_mk_string_unchecked("LeanQueryModuleParams", 21, 21);
x_54 = l_Lean_Name_mkStr3(x_51, x_52, x_53);
x_55 = lean_box(1);
x_56 = lean_unbox(x_55);
lean_inc(x_50);
x_57 = l_Lean_Name_toString(x_54, x_56, x_50);
x_58 = lean_mk_string_unchecked(".", 1, 1);
x_59 = lean_string_append(x_57, x_58);
lean_dec(x_58);
x_60 = l_Lean_Name_mkStr1(x_46);
x_61 = lean_unbox(x_55);
x_62 = l_Lean_Name_toString(x_60, x_61, x_50);
x_63 = lean_string_append(x_59, x_62);
lean_dec(x_62);
x_64 = lean_mk_string_unchecked(": ", 2, 2);
x_65 = lean_string_append(x_63, x_64);
lean_dec(x_64);
x_66 = lean_string_append(x_65, x_49);
lean_dec(x_49);
lean_ctor_set(x_47, 0, x_66);
return x_47;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_67 = lean_ctor_get(x_47, 0);
lean_inc(x_67);
lean_dec(x_47);
x_68 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams___lam__0____x40_Lean_Data_Lsp_Internal___hyg_2193____boxed), 1, 0);
x_69 = lean_mk_string_unchecked("Lean", 4, 4);
x_70 = lean_mk_string_unchecked("Lsp", 3, 3);
x_71 = lean_mk_string_unchecked("LeanQueryModuleParams", 21, 21);
x_72 = l_Lean_Name_mkStr3(x_69, x_70, x_71);
x_73 = lean_box(1);
x_74 = lean_unbox(x_73);
lean_inc(x_68);
x_75 = l_Lean_Name_toString(x_72, x_74, x_68);
x_76 = lean_mk_string_unchecked(".", 1, 1);
x_77 = lean_string_append(x_75, x_76);
lean_dec(x_76);
x_78 = l_Lean_Name_mkStr1(x_46);
x_79 = lean_unbox(x_73);
x_80 = l_Lean_Name_toString(x_78, x_79, x_68);
x_81 = lean_string_append(x_77, x_80);
lean_dec(x_80);
x_82 = lean_mk_string_unchecked(": ", 2, 2);
x_83 = lean_string_append(x_81, x_82);
lean_dec(x_82);
x_84 = lean_string_append(x_83, x_67);
lean_dec(x_67);
x_85 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_85, 0, x_84);
return x_85;
}
}
else
{
lean_dec(x_46);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_86; 
lean_dec(x_45);
x_86 = !lean_is_exclusive(x_47);
if (x_86 == 0)
{
lean_ctor_set_tag(x_47, 0);
return x_47;
}
else
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_47, 0);
lean_inc(x_87);
lean_dec(x_47);
x_88 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_88, 0, x_87);
return x_88;
}
}
else
{
uint8_t x_89; 
x_89 = !lean_is_exclusive(x_47);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_47, 0);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_45);
lean_ctor_set(x_91, 1, x_90);
lean_ctor_set(x_47, 0, x_91);
return x_47;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_47, 0);
lean_inc(x_92);
lean_dec(x_47);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_45);
lean_ctor_set(x_93, 1, x_92);
x_94 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_94, 0, x_93);
return x_94;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanQueryModuleParams____x40_Lean_Data_Lsp_Internal___hyg_3101__spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanQueryModuleParams____x40_Lean_Data_Lsp_Internal___hyg_3101__spec__0_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanQueryModuleParams____x40_Lean_Data_Lsp_Internal___hyg_3101__spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanQueryModuleParams____x40_Lean_Data_Lsp_Internal___hyg_3101__spec__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanQueryModuleParams____x40_Lean_Data_Lsp_Internal___hyg_3101_), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanQueryModuleParams____x40_Lean_Data_Lsp_Internal___hyg_3207__spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_box(0);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanModuleQuery____x40_Lean_Data_Lsp_Internal___hyg_3028_(x_5);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_usize_of_nat(x_9);
x_11 = lean_usize_add(x_2, x_10);
x_12 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_11;
x_3 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanQueryModuleParams____x40_Lean_Data_Lsp_Internal___hyg_3207_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_23; 
x_2 = lean_mk_string_unchecked("sourceRequestID", 15, 15);
x_23 = lean_ctor_get(x_1, 0);
lean_inc(x_23);
switch (lean_obj_tag(x_23)) {
case 0:
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_ctor_set_tag(x_23, 3);
x_3 = x_23;
goto block_22;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_3 = x_26;
goto block_22;
}
}
case 1:
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_23);
if (x_27 == 0)
{
lean_ctor_set_tag(x_23, 2);
x_3 = x_23;
goto block_22;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_23, 0);
lean_inc(x_28);
lean_dec(x_23);
x_29 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_3 = x_29;
goto block_22;
}
}
default: 
{
lean_object* x_30; 
x_30 = lean_box(0);
x_3 = x_30;
goto block_22;
}
}
block_22:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; lean_object* x_10; size_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_mk_string_unchecked("queries", 7, 7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_array_size(x_8);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_usize_of_nat(x_10);
x_12 = l_Array_mapMUnsafe_map___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanQueryModuleParams____x40_Lean_Data_Lsp_Internal___hyg_3207__spec__0(x_9, x_11, x_8);
x_13 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_5);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_6);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_mk_empty_array_with_capacity(x_10);
x_20 = l_List_flatMapTR_go___at_____private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonPosition____x40_Lean_Data_Lsp_Basic___hyg_221__spec__0(x_18, x_19);
x_21 = l_Lean_Json_mkObj(x_20);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanQueryModuleParams____x40_Lean_Data_Lsp_Internal___hyg_3207__spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanQueryModuleParams____x40_Lean_Data_Lsp_Internal___hyg_3207__spec__0(x_4, x_5, x_3);
return x_6;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonLeanQueryModuleParams() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanQueryModuleParams____x40_Lean_Data_Lsp_Internal___hyg_3207_), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIdentifier____x40_Lean_Data_Lsp_Internal___hyg_3287__spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
lean_inc(x_3);
x_4 = l_Lean_Json_getStr_x3f(x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
lean_dec(x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_4);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_mk_string_unchecked("[anonymous]", 11, 11);
x_11 = lean_string_dec_eq(x_9, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = l_String_toName(x_9);
x_13 = l_Lean_Name_isAnonymous(x_12);
if (x_13 == 0)
{
lean_dec(x_3);
lean_ctor_set(x_4, 0, x_12);
return x_4;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_12);
x_14 = lean_mk_string_unchecked("expected a `Name`, got '", 24, 24);
x_15 = lean_unsigned_to_nat(80u);
x_16 = l_Lean_Json_pretty(x_3, x_15);
x_17 = lean_string_append(x_14, x_16);
lean_dec(x_16);
x_18 = lean_mk_string_unchecked("'", 1, 1);
x_19 = lean_string_append(x_17, x_18);
lean_dec(x_18);
lean_ctor_set_tag(x_4, 0);
lean_ctor_set(x_4, 0, x_19);
return x_4;
}
}
else
{
lean_object* x_20; 
lean_dec(x_9);
lean_dec(x_3);
x_20 = lean_box(0);
lean_ctor_set(x_4, 0, x_20);
return x_4;
}
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_4, 0);
lean_inc(x_21);
lean_dec(x_4);
x_22 = lean_mk_string_unchecked("[anonymous]", 11, 11);
x_23 = lean_string_dec_eq(x_21, x_22);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = l_String_toName(x_21);
x_25 = l_Lean_Name_isAnonymous(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_3);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_24);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_24);
x_27 = lean_mk_string_unchecked("expected a `Name`, got '", 24, 24);
x_28 = lean_unsigned_to_nat(80u);
x_29 = l_Lean_Json_pretty(x_3, x_28);
x_30 = lean_string_append(x_27, x_29);
lean_dec(x_29);
x_31 = lean_mk_string_unchecked("'", 1, 1);
x_32 = lean_string_append(x_30, x_31);
lean_dec(x_31);
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_21);
lean_dec(x_3);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIdentifier____x40_Lean_Data_Lsp_Internal___hyg_3287_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_mk_string_unchecked("module", 6, 6);
lean_inc(x_1);
x_3 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIdentifier____x40_Lean_Data_Lsp_Internal___hyg_3287__spec__0(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
lean_dec(x_1);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams___lam__0____x40_Lean_Data_Lsp_Internal___hyg_2193____boxed), 1, 0);
x_7 = lean_mk_string_unchecked("Lean", 4, 4);
x_8 = lean_mk_string_unchecked("Lsp", 3, 3);
x_9 = lean_mk_string_unchecked("LeanIdentifier", 14, 14);
x_10 = l_Lean_Name_mkStr3(x_7, x_8, x_9);
x_11 = lean_box(1);
x_12 = lean_unbox(x_11);
lean_inc(x_6);
x_13 = l_Lean_Name_toString(x_10, x_12, x_6);
x_14 = lean_mk_string_unchecked(".", 1, 1);
x_15 = lean_string_append(x_13, x_14);
lean_dec(x_14);
x_16 = l_Lean_Name_mkStr1(x_2);
x_17 = lean_unbox(x_11);
x_18 = l_Lean_Name_toString(x_16, x_17, x_6);
x_19 = lean_string_append(x_15, x_18);
lean_dec(x_18);
x_20 = lean_mk_string_unchecked(": ", 2, 2);
x_21 = lean_string_append(x_19, x_20);
lean_dec(x_20);
x_22 = lean_string_append(x_21, x_5);
lean_dec(x_5);
lean_ctor_set(x_3, 0, x_22);
return x_3;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_23 = lean_ctor_get(x_3, 0);
lean_inc(x_23);
lean_dec(x_3);
x_24 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams___lam__0____x40_Lean_Data_Lsp_Internal___hyg_2193____boxed), 1, 0);
x_25 = lean_mk_string_unchecked("Lean", 4, 4);
x_26 = lean_mk_string_unchecked("Lsp", 3, 3);
x_27 = lean_mk_string_unchecked("LeanIdentifier", 14, 14);
x_28 = l_Lean_Name_mkStr3(x_25, x_26, x_27);
x_29 = lean_box(1);
x_30 = lean_unbox(x_29);
lean_inc(x_24);
x_31 = l_Lean_Name_toString(x_28, x_30, x_24);
x_32 = lean_mk_string_unchecked(".", 1, 1);
x_33 = lean_string_append(x_31, x_32);
lean_dec(x_32);
x_34 = l_Lean_Name_mkStr1(x_2);
x_35 = lean_unbox(x_29);
x_36 = l_Lean_Name_toString(x_34, x_35, x_24);
x_37 = lean_string_append(x_33, x_36);
lean_dec(x_36);
x_38 = lean_mk_string_unchecked(": ", 2, 2);
x_39 = lean_string_append(x_37, x_38);
lean_dec(x_38);
x_40 = lean_string_append(x_39, x_23);
lean_dec(x_23);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_40);
return x_41;
}
}
else
{
lean_dec(x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_42; 
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_3);
if (x_42 == 0)
{
lean_ctor_set_tag(x_3, 0);
return x_3;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_3, 0);
lean_inc(x_43);
lean_dec(x_3);
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_43);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_3, 0);
lean_inc(x_45);
lean_dec(x_3);
x_46 = lean_mk_string_unchecked("decl", 4, 4);
lean_inc(x_1);
x_47 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIdentifier____x40_Lean_Data_Lsp_Internal___hyg_3287__spec__0(x_1, x_46);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; 
lean_dec(x_45);
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_49 = lean_ctor_get(x_47, 0);
x_50 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams___lam__0____x40_Lean_Data_Lsp_Internal___hyg_2193____boxed), 1, 0);
x_51 = lean_mk_string_unchecked("Lean", 4, 4);
x_52 = lean_mk_string_unchecked("Lsp", 3, 3);
x_53 = lean_mk_string_unchecked("LeanIdentifier", 14, 14);
x_54 = l_Lean_Name_mkStr3(x_51, x_52, x_53);
x_55 = lean_box(1);
x_56 = lean_unbox(x_55);
lean_inc(x_50);
x_57 = l_Lean_Name_toString(x_54, x_56, x_50);
x_58 = lean_mk_string_unchecked(".", 1, 1);
x_59 = lean_string_append(x_57, x_58);
lean_dec(x_58);
x_60 = l_Lean_Name_mkStr1(x_46);
x_61 = lean_unbox(x_55);
x_62 = l_Lean_Name_toString(x_60, x_61, x_50);
x_63 = lean_string_append(x_59, x_62);
lean_dec(x_62);
x_64 = lean_mk_string_unchecked(": ", 2, 2);
x_65 = lean_string_append(x_63, x_64);
lean_dec(x_64);
x_66 = lean_string_append(x_65, x_49);
lean_dec(x_49);
lean_ctor_set(x_47, 0, x_66);
return x_47;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_67 = lean_ctor_get(x_47, 0);
lean_inc(x_67);
lean_dec(x_47);
x_68 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams___lam__0____x40_Lean_Data_Lsp_Internal___hyg_2193____boxed), 1, 0);
x_69 = lean_mk_string_unchecked("Lean", 4, 4);
x_70 = lean_mk_string_unchecked("Lsp", 3, 3);
x_71 = lean_mk_string_unchecked("LeanIdentifier", 14, 14);
x_72 = l_Lean_Name_mkStr3(x_69, x_70, x_71);
x_73 = lean_box(1);
x_74 = lean_unbox(x_73);
lean_inc(x_68);
x_75 = l_Lean_Name_toString(x_72, x_74, x_68);
x_76 = lean_mk_string_unchecked(".", 1, 1);
x_77 = lean_string_append(x_75, x_76);
lean_dec(x_76);
x_78 = l_Lean_Name_mkStr1(x_46);
x_79 = lean_unbox(x_73);
x_80 = l_Lean_Name_toString(x_78, x_79, x_68);
x_81 = lean_string_append(x_77, x_80);
lean_dec(x_80);
x_82 = lean_mk_string_unchecked(": ", 2, 2);
x_83 = lean_string_append(x_81, x_82);
lean_dec(x_82);
x_84 = lean_string_append(x_83, x_67);
lean_dec(x_67);
x_85 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_85, 0, x_84);
return x_85;
}
}
else
{
lean_dec(x_46);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_86; 
lean_dec(x_45);
lean_dec(x_1);
x_86 = !lean_is_exclusive(x_47);
if (x_86 == 0)
{
lean_ctor_set_tag(x_47, 0);
return x_47;
}
else
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_47, 0);
lean_inc(x_87);
lean_dec(x_47);
x_88 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_88, 0, x_87);
return x_88;
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_47, 0);
lean_inc(x_89);
lean_dec(x_47);
x_90 = lean_mk_string_unchecked("isExactMatch", 12, 12);
x_91 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Basic_0__Lean_Lsp_fromJsonChangeAnnotation____x40_Lean_Data_Lsp_Basic___hyg_2784__spec__0(x_1, x_90);
if (lean_obj_tag(x_91) == 0)
{
uint8_t x_92; 
lean_dec(x_89);
lean_dec(x_45);
x_92 = !lean_is_exclusive(x_91);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_93 = lean_ctor_get(x_91, 0);
x_94 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams___lam__0____x40_Lean_Data_Lsp_Internal___hyg_2193____boxed), 1, 0);
x_95 = lean_mk_string_unchecked("Lean", 4, 4);
x_96 = lean_mk_string_unchecked("Lsp", 3, 3);
x_97 = lean_mk_string_unchecked("LeanIdentifier", 14, 14);
x_98 = l_Lean_Name_mkStr3(x_95, x_96, x_97);
x_99 = lean_box(1);
x_100 = lean_unbox(x_99);
lean_inc(x_94);
x_101 = l_Lean_Name_toString(x_98, x_100, x_94);
x_102 = lean_mk_string_unchecked(".", 1, 1);
x_103 = lean_string_append(x_101, x_102);
lean_dec(x_102);
x_104 = l_Lean_Name_mkStr1(x_90);
x_105 = lean_unbox(x_99);
x_106 = l_Lean_Name_toString(x_104, x_105, x_94);
x_107 = lean_string_append(x_103, x_106);
lean_dec(x_106);
x_108 = lean_mk_string_unchecked(": ", 2, 2);
x_109 = lean_string_append(x_107, x_108);
lean_dec(x_108);
x_110 = lean_string_append(x_109, x_93);
lean_dec(x_93);
lean_ctor_set(x_91, 0, x_110);
return x_91;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_111 = lean_ctor_get(x_91, 0);
lean_inc(x_111);
lean_dec(x_91);
x_112 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams___lam__0____x40_Lean_Data_Lsp_Internal___hyg_2193____boxed), 1, 0);
x_113 = lean_mk_string_unchecked("Lean", 4, 4);
x_114 = lean_mk_string_unchecked("Lsp", 3, 3);
x_115 = lean_mk_string_unchecked("LeanIdentifier", 14, 14);
x_116 = l_Lean_Name_mkStr3(x_113, x_114, x_115);
x_117 = lean_box(1);
x_118 = lean_unbox(x_117);
lean_inc(x_112);
x_119 = l_Lean_Name_toString(x_116, x_118, x_112);
x_120 = lean_mk_string_unchecked(".", 1, 1);
x_121 = lean_string_append(x_119, x_120);
lean_dec(x_120);
x_122 = l_Lean_Name_mkStr1(x_90);
x_123 = lean_unbox(x_117);
x_124 = l_Lean_Name_toString(x_122, x_123, x_112);
x_125 = lean_string_append(x_121, x_124);
lean_dec(x_124);
x_126 = lean_mk_string_unchecked(": ", 2, 2);
x_127 = lean_string_append(x_125, x_126);
lean_dec(x_126);
x_128 = lean_string_append(x_127, x_111);
lean_dec(x_111);
x_129 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_129, 0, x_128);
return x_129;
}
}
else
{
lean_dec(x_90);
if (lean_obj_tag(x_91) == 0)
{
uint8_t x_130; 
lean_dec(x_89);
lean_dec(x_45);
x_130 = !lean_is_exclusive(x_91);
if (x_130 == 0)
{
lean_ctor_set_tag(x_91, 0);
return x_91;
}
else
{
lean_object* x_131; lean_object* x_132; 
x_131 = lean_ctor_get(x_91, 0);
lean_inc(x_131);
lean_dec(x_91);
x_132 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_132, 0, x_131);
return x_132;
}
}
else
{
uint8_t x_133; 
x_133 = !lean_is_exclusive(x_91);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; uint8_t x_136; 
x_134 = lean_ctor_get(x_91, 0);
x_135 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_135, 0, x_45);
lean_ctor_set(x_135, 1, x_89);
x_136 = lean_unbox(x_134);
lean_dec(x_134);
lean_ctor_set_uint8(x_135, sizeof(void*)*2, x_136);
lean_ctor_set(x_91, 0, x_135);
return x_91;
}
else
{
lean_object* x_137; lean_object* x_138; uint8_t x_139; lean_object* x_140; 
x_137 = lean_ctor_get(x_91, 0);
lean_inc(x_137);
lean_dec(x_91);
x_138 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_138, 0, x_45);
lean_ctor_set(x_138, 1, x_89);
x_139 = lean_unbox(x_137);
lean_dec(x_137);
lean_ctor_set_uint8(x_138, sizeof(void*)*2, x_139);
x_140 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_140, 0, x_138);
return x_140;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIdentifier____x40_Lean_Data_Lsp_Internal___hyg_3287__spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIdentifier____x40_Lean_Data_Lsp_Internal___hyg_3287__spec__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIdentifier() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIdentifier____x40_Lean_Data_Lsp_Internal___hyg_3287_), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanIdentifier____x40_Lean_Data_Lsp_Internal___hyg_3432_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams___lam__0____x40_Lean_Data_Lsp_Internal___hyg_2193____boxed), 1, 0);
x_3 = lean_mk_string_unchecked("module", 6, 6);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_box(1);
x_6 = lean_unbox(x_5);
lean_inc(x_2);
x_7 = l_Lean_Name_toString(x_4, x_6, x_2);
x_8 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_mk_string_unchecked("decl", 4, 4);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
x_14 = lean_unbox(x_5);
x_15 = l_Lean_Name_toString(x_13, x_14, x_2);
x_16 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_12);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_10);
x_19 = lean_mk_string_unchecked("isExactMatch", 12, 12);
x_20 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_21 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_21, 0, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_10);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_18);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_11);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_unsigned_to_nat(0u);
x_29 = lean_mk_empty_array_with_capacity(x_28);
x_30 = l_List_flatMapTR_go___at_____private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonPosition____x40_Lean_Data_Lsp_Basic___hyg_221__spec__0(x_27, x_29);
x_31 = l_Lean_Json_mkObj(x_30);
return x_31;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonLeanIdentifier() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanIdentifier____x40_Lean_Data_Lsp_Internal___hyg_3432_), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanQueryModuleResponse____x40_Lean_Data_Lsp_Internal___hyg_3516__spec__0_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_array_uget(x_3, x_2);
x_7 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIdentifier____x40_Lean_Data_Lsp_Internal___hyg_3287_(x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
lean_dec(x_3);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
return x_7;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec(x_7);
x_12 = lean_box(0);
x_13 = lean_array_uset(x_3, x_2, x_12);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_usize_of_nat(x_14);
x_16 = lean_usize_add(x_2, x_15);
x_17 = lean_array_uset(x_13, x_2, x_11);
x_2 = x_16;
x_3 = x_17;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanQueryModuleResponse____x40_Lean_Data_Lsp_Internal___hyg_3516__spec__0_spec__1_spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_3);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = lean_array_uget(x_3, x_2);
if (lean_obj_tag(x_6) == 4)
{
lean_object* x_7; size_t x_8; lean_object* x_9; size_t x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_array_size(x_7);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_usize_of_nat(x_9);
x_11 = l_Array_mapMUnsafe_map___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanQueryModuleResponse____x40_Lean_Data_Lsp_Internal___hyg_3516__spec__0_spec__0(x_8, x_10, x_7);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
lean_dec(x_3);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
return x_11;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_11, 0);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_box(0);
x_17 = lean_array_uset(x_3, x_2, x_16);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_usize_of_nat(x_18);
x_20 = lean_usize_add(x_2, x_19);
x_21 = lean_array_uset(x_17, x_2, x_15);
x_2 = x_20;
x_3 = x_21;
goto _start;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_3);
x_23 = lean_mk_string_unchecked("expected JSON array, got '", 26, 26);
x_24 = lean_unsigned_to_nat(80u);
x_25 = l_Lean_Json_pretty(x_6, x_24);
x_26 = lean_string_append(x_23, x_25);
lean_dec(x_25);
x_27 = lean_mk_string_unchecked("'", 1, 1);
x_28 = lean_string_append(x_26, x_27);
lean_dec(x_27);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanQueryModuleResponse____x40_Lean_Data_Lsp_Internal___hyg_3516__spec__0_spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_3);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = lean_array_uget(x_3, x_2);
if (lean_obj_tag(x_6) == 4)
{
lean_object* x_7; size_t x_8; lean_object* x_9; size_t x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_array_size(x_7);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_usize_of_nat(x_9);
x_11 = l_Array_mapMUnsafe_map___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanQueryModuleResponse____x40_Lean_Data_Lsp_Internal___hyg_3516__spec__0_spec__0(x_8, x_10, x_7);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
lean_dec(x_3);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
return x_11;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; 
x_15 = lean_ctor_get(x_11, 0);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_box(0);
x_17 = lean_array_uset(x_3, x_2, x_16);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_usize_of_nat(x_18);
x_20 = lean_usize_add(x_2, x_19);
x_21 = lean_array_uset(x_17, x_2, x_15);
x_22 = l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanQueryModuleResponse____x40_Lean_Data_Lsp_Internal___hyg_3516__spec__0_spec__1_spec__1(x_1, x_20, x_21);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_3);
x_23 = lean_mk_string_unchecked("expected JSON array, got '", 26, 26);
x_24 = lean_unsigned_to_nat(80u);
x_25 = l_Lean_Json_pretty(x_6, x_24);
x_26 = lean_string_append(x_23, x_25);
lean_dec(x_25);
x_27 = lean_mk_string_unchecked("'", 1, 1);
x_28 = lean_string_append(x_26, x_27);
lean_dec(x_27);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanQueryModuleResponse____x40_Lean_Data_Lsp_Internal___hyg_3516__spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
if (lean_obj_tag(x_3) == 4)
{
lean_object* x_4; size_t x_5; lean_object* x_6; size_t x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_array_size(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_usize_of_nat(x_6);
x_8 = l_Array_mapMUnsafe_map___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanQueryModuleResponse____x40_Lean_Data_Lsp_Internal___hyg_3516__spec__0_spec__1(x_5, x_7, x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_mk_string_unchecked("expected JSON array, got '", 26, 26);
x_10 = lean_unsigned_to_nat(80u);
x_11 = l_Lean_Json_pretty(x_3, x_10);
x_12 = lean_string_append(x_9, x_11);
lean_dec(x_11);
x_13 = lean_mk_string_unchecked("'", 1, 1);
x_14 = lean_string_append(x_12, x_13);
lean_dec(x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanQueryModuleResponse____x40_Lean_Data_Lsp_Internal___hyg_3516_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_mk_string_unchecked("queryResults", 12, 12);
x_3 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanQueryModuleResponse____x40_Lean_Data_Lsp_Internal___hyg_3516__spec__0(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams___lam__0____x40_Lean_Data_Lsp_Internal___hyg_2193____boxed), 1, 0);
x_7 = lean_mk_string_unchecked("Lean", 4, 4);
x_8 = lean_mk_string_unchecked("Lsp", 3, 3);
x_9 = lean_mk_string_unchecked("LeanQueryModuleResponse", 23, 23);
x_10 = l_Lean_Name_mkStr3(x_7, x_8, x_9);
x_11 = lean_box(1);
x_12 = lean_unbox(x_11);
lean_inc(x_6);
x_13 = l_Lean_Name_toString(x_10, x_12, x_6);
x_14 = lean_mk_string_unchecked(".", 1, 1);
x_15 = lean_string_append(x_13, x_14);
lean_dec(x_14);
x_16 = l_Lean_Name_mkStr1(x_2);
x_17 = lean_unbox(x_11);
x_18 = l_Lean_Name_toString(x_16, x_17, x_6);
x_19 = lean_string_append(x_15, x_18);
lean_dec(x_18);
x_20 = lean_mk_string_unchecked(": ", 2, 2);
x_21 = lean_string_append(x_19, x_20);
lean_dec(x_20);
x_22 = lean_string_append(x_21, x_5);
lean_dec(x_5);
lean_ctor_set(x_3, 0, x_22);
return x_3;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_23 = lean_ctor_get(x_3, 0);
lean_inc(x_23);
lean_dec(x_3);
x_24 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams___lam__0____x40_Lean_Data_Lsp_Internal___hyg_2193____boxed), 1, 0);
x_25 = lean_mk_string_unchecked("Lean", 4, 4);
x_26 = lean_mk_string_unchecked("Lsp", 3, 3);
x_27 = lean_mk_string_unchecked("LeanQueryModuleResponse", 23, 23);
x_28 = l_Lean_Name_mkStr3(x_25, x_26, x_27);
x_29 = lean_box(1);
x_30 = lean_unbox(x_29);
lean_inc(x_24);
x_31 = l_Lean_Name_toString(x_28, x_30, x_24);
x_32 = lean_mk_string_unchecked(".", 1, 1);
x_33 = lean_string_append(x_31, x_32);
lean_dec(x_32);
x_34 = l_Lean_Name_mkStr1(x_2);
x_35 = lean_unbox(x_29);
x_36 = l_Lean_Name_toString(x_34, x_35, x_24);
x_37 = lean_string_append(x_33, x_36);
lean_dec(x_36);
x_38 = lean_mk_string_unchecked(": ", 2, 2);
x_39 = lean_string_append(x_37, x_38);
lean_dec(x_38);
x_40 = lean_string_append(x_39, x_23);
lean_dec(x_23);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_40);
return x_41;
}
}
else
{
lean_dec(x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_3);
if (x_42 == 0)
{
lean_ctor_set_tag(x_3, 0);
return x_3;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_3, 0);
lean_inc(x_43);
lean_dec(x_3);
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_43);
return x_44;
}
}
else
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_3);
if (x_45 == 0)
{
return x_3;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_3, 0);
lean_inc(x_46);
lean_dec(x_3);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
return x_47;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanQueryModuleResponse____x40_Lean_Data_Lsp_Internal___hyg_3516__spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanQueryModuleResponse____x40_Lean_Data_Lsp_Internal___hyg_3516__spec__0_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanQueryModuleResponse____x40_Lean_Data_Lsp_Internal___hyg_3516__spec__0_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanQueryModuleResponse____x40_Lean_Data_Lsp_Internal___hyg_3516__spec__0_spec__1_spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanQueryModuleResponse____x40_Lean_Data_Lsp_Internal___hyg_3516__spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanQueryModuleResponse____x40_Lean_Data_Lsp_Internal___hyg_3516__spec__0_spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanQueryModuleResponse____x40_Lean_Data_Lsp_Internal___hyg_3516__spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanQueryModuleResponse____x40_Lean_Data_Lsp_Internal___hyg_3516__spec__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleResponse() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanQueryModuleResponse____x40_Lean_Data_Lsp_Internal___hyg_3516_), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanQueryModuleResponse____x40_Lean_Data_Lsp_Internal___hyg_3583__spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_box(0);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanIdentifier____x40_Lean_Data_Lsp_Internal___hyg_3432_(x_5);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_usize_of_nat(x_9);
x_11 = lean_usize_add(x_2, x_10);
x_12 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_11;
x_3 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanQueryModuleResponse____x40_Lean_Data_Lsp_Internal___hyg_3583__spec__1_spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; lean_object* x_9; size_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_box(0);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = lean_array_size(x_5);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_usize_of_nat(x_9);
x_11 = l_Array_mapMUnsafe_map___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanQueryModuleResponse____x40_Lean_Data_Lsp_Internal___hyg_3583__spec__0(x_8, x_10, x_5);
x_12 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_usize_of_nat(x_13);
x_15 = lean_usize_add(x_2, x_14);
x_16 = lean_array_uset(x_7, x_2, x_12);
x_2 = x_15;
x_3 = x_16;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanQueryModuleResponse____x40_Lean_Data_Lsp_Internal___hyg_3583__spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; lean_object* x_9; size_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; lean_object* x_17; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_box(0);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = lean_array_size(x_5);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_usize_of_nat(x_9);
x_11 = l_Array_mapMUnsafe_map___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanQueryModuleResponse____x40_Lean_Data_Lsp_Internal___hyg_3583__spec__0(x_8, x_10, x_5);
x_12 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_usize_of_nat(x_13);
x_15 = lean_usize_add(x_2, x_14);
x_16 = lean_array_uset(x_7, x_2, x_12);
x_17 = l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanQueryModuleResponse____x40_Lean_Data_Lsp_Internal___hyg_3583__spec__1_spec__1(x_1, x_15, x_16);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanQueryModuleResponse____x40_Lean_Data_Lsp_Internal___hyg_3583_(lean_object* x_1) {
_start:
{
lean_object* x_2; size_t x_3; lean_object* x_4; size_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_2 = lean_mk_string_unchecked("queryResults", 12, 12);
x_3 = lean_array_size(x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_usize_of_nat(x_4);
x_6 = l_Array_mapMUnsafe_map___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanQueryModuleResponse____x40_Lean_Data_Lsp_Internal___hyg_3583__spec__1(x_3, x_5, x_1);
x_7 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_mk_empty_array_with_capacity(x_4);
x_14 = l_List_flatMapTR_go___at_____private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonPosition____x40_Lean_Data_Lsp_Basic___hyg_221__spec__0(x_12, x_13);
x_15 = l_Lean_Json_mkObj(x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanQueryModuleResponse____x40_Lean_Data_Lsp_Internal___hyg_3583__spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanQueryModuleResponse____x40_Lean_Data_Lsp_Internal___hyg_3583__spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanQueryModuleResponse____x40_Lean_Data_Lsp_Internal___hyg_3583__spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanQueryModuleResponse____x40_Lean_Data_Lsp_Internal___hyg_3583__spec__1_spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanQueryModuleResponse____x40_Lean_Data_Lsp_Internal___hyg_3583__spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanQueryModuleResponse____x40_Lean_Data_Lsp_Internal___hyg_3583__spec__1(x_4, x_5, x_3);
return x_6;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonLeanQueryModuleResponse() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanQueryModuleResponse____x40_Lean_Data_Lsp_Internal___hyg_3583_), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_instInhabitedLeanQueryModuleResponse() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty(lean_box(0));
return x_1;
}
}
lean_object* initialize_Lean_Expr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Lsp_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_JsonRpc(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Data_TreeMap(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_Lsp_Internal(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Expr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Lsp_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_JsonRpc(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_TreeMap(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Lsp_instBEqRefIdent = _init_l_Lean_Lsp_instBEqRefIdent();
lean_mark_persistent(l_Lean_Lsp_instBEqRefIdent);
l_Lean_Lsp_instHashableRefIdent = _init_l_Lean_Lsp_instHashableRefIdent();
lean_mark_persistent(l_Lean_Lsp_instHashableRefIdent);
l_Lean_Lsp_instInhabitedRefIdent = _init_l_Lean_Lsp_instInhabitedRefIdent();
lean_mark_persistent(l_Lean_Lsp_instInhabitedRefIdent);
l_Lean_Lsp_instOrdRefIdent = _init_l_Lean_Lsp_instOrdRefIdent();
lean_mark_persistent(l_Lean_Lsp_instOrdRefIdent);
l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr = _init_l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr();
lean_mark_persistent(l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr);
l_Lean_Lsp_RefIdent_instToJsonRefIdentJsonRepr = _init_l_Lean_Lsp_RefIdent_instToJsonRefIdentJsonRepr();
lean_mark_persistent(l_Lean_Lsp_RefIdent_instToJsonRefIdentJsonRepr);
l_Lean_Lsp_RefIdent_instFromJson = _init_l_Lean_Lsp_RefIdent_instFromJson();
lean_mark_persistent(l_Lean_Lsp_RefIdent_instFromJson);
l_Lean_Lsp_RefIdent_instToJson = _init_l_Lean_Lsp_RefIdent_instToJson();
lean_mark_persistent(l_Lean_Lsp_RefIdent_instToJson);
l_Lean_Lsp_RefInfo_instToJsonParentDecl = _init_l_Lean_Lsp_RefInfo_instToJsonParentDecl();
lean_mark_persistent(l_Lean_Lsp_RefInfo_instToJsonParentDecl);
l_Lean_Lsp_RefInfo_instInhabitedLocation = _init_l_Lean_Lsp_RefInfo_instInhabitedLocation();
lean_mark_persistent(l_Lean_Lsp_RefInfo_instInhabitedLocation);
l_Lean_Lsp_instToJsonRefInfo = _init_l_Lean_Lsp_instToJsonRefInfo();
lean_mark_persistent(l_Lean_Lsp_instToJsonRefInfo);
l_Lean_Lsp_instFromJsonRefInfo = _init_l_Lean_Lsp_instFromJsonRefInfo();
lean_mark_persistent(l_Lean_Lsp_instFromJsonRefInfo);
l_Lean_Lsp_instModuleRefsEmptyCollection = _init_l_Lean_Lsp_instModuleRefsEmptyCollection();
lean_mark_persistent(l_Lean_Lsp_instModuleRefsEmptyCollection);
l_Lean_Lsp_instToJsonModuleRefs = _init_l_Lean_Lsp_instToJsonModuleRefs();
lean_mark_persistent(l_Lean_Lsp_instToJsonModuleRefs);
l_Lean_Lsp_instFromJsonModuleRefs = _init_l_Lean_Lsp_instFromJsonModuleRefs();
lean_mark_persistent(l_Lean_Lsp_instFromJsonModuleRefs);
l_Lean_Lsp_instFromJsonLeanIleanInfoParams = _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams();
lean_mark_persistent(l_Lean_Lsp_instFromJsonLeanIleanInfoParams);
l_Lean_Lsp_instToJsonLeanIleanInfoParams = _init_l_Lean_Lsp_instToJsonLeanIleanInfoParams();
lean_mark_persistent(l_Lean_Lsp_instToJsonLeanIleanInfoParams);
l_Lean_Lsp_instFromJsonLeanImportClosureParams = _init_l_Lean_Lsp_instFromJsonLeanImportClosureParams();
lean_mark_persistent(l_Lean_Lsp_instFromJsonLeanImportClosureParams);
l_Lean_Lsp_instToJsonLeanImportClosureParams = _init_l_Lean_Lsp_instToJsonLeanImportClosureParams();
lean_mark_persistent(l_Lean_Lsp_instToJsonLeanImportClosureParams);
l_Lean_Lsp_instFromJsonLeanStaleDependencyParams = _init_l_Lean_Lsp_instFromJsonLeanStaleDependencyParams();
lean_mark_persistent(l_Lean_Lsp_instFromJsonLeanStaleDependencyParams);
l_Lean_Lsp_instToJsonLeanStaleDependencyParams = _init_l_Lean_Lsp_instToJsonLeanStaleDependencyParams();
lean_mark_persistent(l_Lean_Lsp_instToJsonLeanStaleDependencyParams);
l_Lean_Lsp_instFromJsonOpenNamespace = _init_l_Lean_Lsp_instFromJsonOpenNamespace();
lean_mark_persistent(l_Lean_Lsp_instFromJsonOpenNamespace);
l_Lean_Lsp_instToJsonOpenNamespace = _init_l_Lean_Lsp_instToJsonOpenNamespace();
lean_mark_persistent(l_Lean_Lsp_instToJsonOpenNamespace);
l_Lean_Lsp_instFromJsonLeanModuleQuery = _init_l_Lean_Lsp_instFromJsonLeanModuleQuery();
lean_mark_persistent(l_Lean_Lsp_instFromJsonLeanModuleQuery);
l_Lean_Lsp_instToJsonLeanModuleQuery = _init_l_Lean_Lsp_instToJsonLeanModuleQuery();
lean_mark_persistent(l_Lean_Lsp_instToJsonLeanModuleQuery);
l_Lean_Lsp_instFromJsonLeanQueryModuleParams = _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams();
lean_mark_persistent(l_Lean_Lsp_instFromJsonLeanQueryModuleParams);
l_Lean_Lsp_instToJsonLeanQueryModuleParams = _init_l_Lean_Lsp_instToJsonLeanQueryModuleParams();
lean_mark_persistent(l_Lean_Lsp_instToJsonLeanQueryModuleParams);
l_Lean_Lsp_instFromJsonLeanIdentifier = _init_l_Lean_Lsp_instFromJsonLeanIdentifier();
lean_mark_persistent(l_Lean_Lsp_instFromJsonLeanIdentifier);
l_Lean_Lsp_instToJsonLeanIdentifier = _init_l_Lean_Lsp_instToJsonLeanIdentifier();
lean_mark_persistent(l_Lean_Lsp_instToJsonLeanIdentifier);
l_Lean_Lsp_instFromJsonLeanQueryModuleResponse = _init_l_Lean_Lsp_instFromJsonLeanQueryModuleResponse();
lean_mark_persistent(l_Lean_Lsp_instFromJsonLeanQueryModuleResponse);
l_Lean_Lsp_instToJsonLeanQueryModuleResponse = _init_l_Lean_Lsp_instToJsonLeanQueryModuleResponse();
lean_mark_persistent(l_Lean_Lsp_instToJsonLeanQueryModuleResponse);
l_Lean_Lsp_instInhabitedLeanQueryModuleResponse = _init_l_Lean_Lsp_instInhabitedLeanQueryModuleResponse();
lean_mark_persistent(l_Lean_Lsp_instInhabitedLeanQueryModuleResponse);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
